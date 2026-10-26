// SPDX-FileCopyrightText: 2024 blinry <mail@blinry.org>
// SPDX-FileCopyrightText: 2024 zormit <nt4u@kpvn.de>
//
// SPDX-License-Identifier: AGPL-3.0-or-later

import * as vscode from "vscode"
import * as cp from "child_process"
import * as rpc from "vscode-jsonrpc/node"
import * as path from "path"
import * as fs from "fs"
var Mutex = require("async-mutex").Mutex

import {setCursor, getCursorInfo, drawCursors} from "./cursor"

function findMarkerDirectory(dir: string, marker: string) {
    if (fs.existsSync(path.join(dir, marker))) {
        return dir
    }

    const parentDir = path.resolve(dir, "..")

    // If we are at the root directory, stop the recursion.
    if (parentDir === dir) {
        return null
    }

    return findMarkerDirectory(parentDir, marker)
}

interface Position {
    line: number
    character: number
}

interface Range {
    start: Position
    end: Position
}

interface Delta {
    range: Range
    replacement: string
}

interface Edit {
    uri: string
    revision: number
    delta: Delta[]
}

interface Cursor {
    uri: string
    ranges: Range[]
}

interface CursorFromDaemon {
    userid: string
    name?: string
    uri: string
    ranges: Range[]
}

class Revision {
    daemon = 0
    editor = 0
}

interface Configuration {
    cmd: string[]
    rootMarkers: string[]
}

interface DocumentOTState {
    revision: Revision
    content: string[]
}

class Client {
    name: string
    ot_states: {[uri: string]: DocumentOTState} = {}
    process: cp.ChildProcess
    connection: rpc.MessageConnection
    directory: string

    constructor(name: string, cmd: string[], directory: string) {
        this.name = name
        this.directory = directory

        this.process = cp.spawn(cmd[0], cmd.slice(1), {cwd: directory})

        this.process.on("error", (err) => {
            vscode.window.showErrorMessage(
                `Failed to start TeamTypeV client. Maybe the command is not in your PATH?: ${err.message}`,
            )
        })

        this.process.on("exit", () => {
            vscode.window.showErrorMessage(
                `Connection to TeamTypeV daemon in '${directory}' lost or failed to initiate. Maybe there's no daemon running there?`,
            )
        })

        if (!this.process.stdout || !this.process.stdin) {
            die("Failed to spawn TeamTypeV client (no stdin/stdout)")
        }

        this.connection = rpc.createMessageConnection(
            new rpc.StreamMessageReader(this.process.stdout),
            new rpc.StreamMessageWriter(this.process.stdin),
        )

        this.connection.onNotification("edit", (edit) => processEditFromDaemon(this, edit))
        this.connection.onNotification("cursor", (cursor) => mutex.runExclusive(() => processCursorFromDaemon(cursor)))

        // Start the connection
        this.connection.listen()
    }
}

let configurations: {[key: string]: Configuration} = {}
let clients: Client[] = []

// TODO: if we load from disk, this will also cause edits :-/
let t0 = Date.now()
const mutex = new Mutex()
interface PendingDocumentChange {
    event: vscode.TextDocumentChangeEvent
    lines: string[]
    content: string
    version: number
}

let pendingRemote: {
    uri: string
    content: string
    version: number
    changes: PendingDocumentChange[]
} | null = null

const closeType = new rpc.RequestType<{uri: string}, string, void>("close")
const editType = new rpc.RequestType<Edit, string, void>("edit")
const cursorType = new rpc.NotificationType<Cursor>("cursor")

function protocolUri(document: vscode.TextDocument): string {
    return document.uri.with({scheme: "file"}).toString()
}

const sharedContents = new Map<string, Uint8Array>()
const opening = new Set<string>()
const nativeCleanContents = new WeakMap<vscode.TextDocument, string>()
const pendingNativeCleanContents = new WeakMap<vscode.TextDocument, string>()

function rememberNativeCleanContent(document: vscode.TextDocument) {
    if (document.uri.scheme === "file" && !document.isDirty) {
        nativeCleanContents.set(document, document.getText())
        pendingNativeCleanContents.delete(document)
    }
}

/** Content events can precede the dirty-state event for the same native edit. */
function rememberNativeChange(event: vscode.TextDocumentChangeEvent) {
    const document = event.document
    if (document.uri.scheme !== "file") return
    if (event.contentChanges.length) {
        const previous = pendingNativeCleanContents.get(document)
        if (previous !== undefined) nativeCleanContents.set(document, previous)
        pendingNativeCleanContents.delete(document)
        if (!document.isDirty && nativeCleanContents.has(document)) {
            pendingNativeCleanContents.set(document, document.getText())
        }
    } else if (document.isDirty) {
        pendingNativeCleanContents.delete(document)
    } else {
        rememberNativeCleanContent(document)
    }
}

// 🧑 "their save just tells teamtype to write"
class SharedFileSystem implements vscode.FileSystemProvider {
    readonly onDidChangeFile = new vscode.EventEmitter<vscode.FileChangeEvent[]>().event
    watch() {
        return new vscode.Disposable(() => {})
    }
    stat(uri: vscode.Uri): vscode.FileStat {
        return {type: vscode.FileType.File, ctime: 0, mtime: 0, size: this.readFile(uri).byteLength}
    }
    readFile(uri: vscode.Uri): Uint8Array {
        const document = vscode.workspace.textDocuments.find((doc) => doc.uri.toString() === uri.toString())
        return (
            sharedContents.get(uri.toString()) ??
            (document ? Buffer.from(document.getText(), "utf8") : fs.readFileSync(uri.fsPath))
        )
    }
    async writeFile(uri: vscode.Uri): Promise<void> {
        await mutex.runExclusive(async () => {
            const document = vscode.workspace.textDocuments.find((doc) => doc.uri.toString() === uri.toString())
            const client = document && clientsForDocument(document)[0]
            if (!client || client.process.exitCode !== null || client.process.signalCode !== null) {
                throw vscode.FileSystemError.Unavailable("TeamTypeV daemon is disconnected")
            }
            await client.connection.sendRequest("save", {uri: protocolUri(document!)})
        })
    }
    readDirectory(): [string, vscode.FileType][] {
        return []
    }
    createDirectory(): never {
        throw vscode.FileSystemError.NoPermissions()
    }
    delete(): never {
        throw vscode.FileSystemError.NoPermissions()
    }
    rename(): never {
        throw vscode.FileSystemError.NoPermissions()
    }
}

function uriToFname(uri: string): string {
    const prefix = "file://"
    if (!uri.startsWith(prefix)) {
        console.error(`expected URI prefix for '${uri}'`)
    }
    return uri.slice(prefix.length)
}

// helpful: https://stackoverflow.com/a/54369605
function UTF16CodeUnitOffsetToCharOffset(utf16CodeUnitOffset: number, content: string): number {
    if (utf16CodeUnitOffset > content.length) {
        throw new Error(
            `Could not convert UTF-16 code unit offset ${utf16CodeUnitOffset} to char offset in string '${content}'`,
        )
    }
    return [...content.slice(0, utf16CodeUnitOffset)].length
}

function charOffsetToUTF16CodeUnitOffset(charOffset: number, content: string): number {
    let utf16Offset = 0
    let chars = [...content]
    if (charOffset > chars.length) {
        throw new Error(`Could not convert char offset ${charOffset} to UTF-16 code unit offset in string '${content}'`)
    }
    for (const char of [...content].slice(0, charOffset)) {
        utf16Offset += char.length
    }
    return utf16Offset
}

function vsCodeRangeToTeamtypevRange(content: string[], range: vscode.Range): Range {
    return {
        start: vsCodePositionToTeamtypevPosition(content, range.start),
        end: vsCodePositionToTeamtypevPosition(content, range.end),
    }
}

function vsCodePositionToTeamtypevPosition(content: string[], position: vscode.Position): Position {
    let lineText = content[position.line]
    return {
        line: position.line,
        character: UTF16CodeUnitOffsetToCharOffset(position.character, lineText),
    }
}

function teamtypevPositionToVSCodePosition(document: vscode.TextDocument, position: Position): vscode.Position {
    let lineText = document.lineAt(position.line).text
    return new vscode.Position(position.line, charOffsetToUTF16CodeUnitOffset(position.character, lineText))
}

function teamtypevRangeToVSCodeRange(document: vscode.TextDocument, range: Range): vscode.Range {
    return new vscode.Range(
        teamtypevPositionToVSCodePosition(document, range.start),
        teamtypevPositionToVSCodePosition(document, range.end),
    )
}

function teamtypevDeltasToVSCodeTextEdits(document: vscode.TextDocument, deltas: Delta[]): vscode.TextEdit[] {
    return deltas.map((delta) => {
        let range = teamtypevRangeToVSCodeRange(document, delta.range)
        return vscode.TextEdit.replace(range, delta.replacement)
    })
}

function vsCodeRangeToSelection(range: vscode.Range): vscode.Selection {
    let anchor = range.start
    let active = range.end
    return new vscode.Selection(anchor, active)
}

function openCurrentTextDocuments() {
    vscode.workspace.textDocuments.map(processUserOpen)
}

function documentForUri(uri: string): vscode.TextDocument | undefined {
    return vscode.workspace.textDocuments.find((doc) => doc.uri.scheme === "teamtypev" && protocolUri(doc) === uri)
}

// Apply given TextEdits to content of the TextDocument, and return the resulting content.
export function contentAfterEdits(document: vscode.TextDocument, edits: vscode.TextEdit[]): string {
    let result = document.getText()

    // Precompute offsets (from the original document) and keep original index
    const editsWithOffsets = edits.map((e, i) => ({
        start: document.offsetAt(e.range.start),
        end: document.offsetAt(e.range.end),
        newText: e.newText,
    }))

    // Sort by start offset descendingly.
    // If they are equal (and thus, falsy), sort by end offset descendingly.
    // Reason: If two edits are "replace character 0-0 with xxx" and "replace character 0-1 with nothing",
    // they don't overlap, but the intended resulting edit should NOT remove the first x of xxx, it should
    // remove a character from the original content.
    editsWithOffsets.sort((a, b) => b.start - a.start || b.end - a.end)

    for (const edit of editsWithOffsets) {
        result = result.slice(0, edit.start) + edit.newText + result.slice(edit.end)
    }

    return result
}

async function processEditFromDaemon(client: Client, edit: Edit) {
    try {
        await mutex.runExclusive(async () => {
            const state = client.ot_states[edit.uri]
            if (!state) return
            let revision = state.revision
            if (edit.revision !== revision.editor) {
                debug(`Received edit for revision ${edit.revision} (!= ${revision.editor}), ignoring`)
                return
            }

            debug(`Received edit ${edit.revision}`)

            const uri = edit.uri

            const document = documentForUri(uri)
            if (document) {
                let textEdits = teamtypevDeltasToVSCodeTextEdits(document, edit.delta)
                const content = contentAfterEdits(document, textEdits)
                if (content === document.getText()) {
                    revision.daemon += 1
                    return
                }
                const pending = {uri, content, version: document.version, changes: [] as PendingDocumentChange[]}
                pendingRemote = pending
                let worked = false
                try {
                    worked = await applyEdit(client, document, edit)
                } finally {
                    if (pendingRemote === pending) pendingRemote = null
                    let remoteApplied = false
                    for (const change of pending.changes) {
                        if (
                            !remoteApplied &&
                            worked &&
                            change.version === pending.version + 1 &&
                            change.content === pending.content
                        ) {
                            remoteApplied = true
                            revision.daemon += 1
                            state.content = change.lines
                        } else {
                            processLocalEdit(change.event, change.lines)
                        }
                    }
                }
                if (worked) {
                    // Attempt auto-save to avoid the situation where one user closes a modified
                    // document without saving, which will cause VS Code to undo the dirty changes.
                    document.save()
                } else {
                    debug("rejected an applyEdit, sending empty delta")

                    let theEdit: Edit = {uri, revision: revision.daemon, delta: []}
                    client.connection.sendRequest(editType, theEdit)
                    revision.editor += 1
                }
            } else {
                throw new Error(`No document for URI ${uri}, why is the daemon sending me this?`)
            }
        })
    } catch (e) {
        vscode.window.showErrorMessage(`Error while processing edit from TeamTypeV daemon: ${e}`)
    }
}

async function processCursorFromDaemon(cursor: CursorFromDaemon) {
    let uri = cursor.uri

    const document = documentForUri(uri)

    try {
        let selections: vscode.DecorationOptions[] = []
        if (document) {
            selections = cursor.ranges
                .map((r) => teamtypevRangeToVSCodeRange(document, r))
                .map(vsCodeRangeToSelection)
                .map((s) => {
                    return {
                        range: s,
                        hoverMessage: cursor.name,
                    }
                })
        }
        setCursor(cursor.userid, cursor.name || "anonymous", document?.uri ?? vscode.Uri.parse(uri), selections)
    } catch {
        // If we couldn't convert teamtypevRangeToVSCodeRange, it's probably because
        // we received the cursor message before integrating the edits, typing at the end of a line.
        // In practice, this isn't a problem, as the cursor decoration is pushed to the back automatically.
        // TODO: Make the teamtypevRangeToVSCodeRange function still return a proper range?
    }
}

async function applyEdit(client: Client, document: vscode.TextDocument, edit: Edit): Promise<boolean> {
    let edits = []
    for (const delta of edit.delta) {
        const range = teamtypevRangeToVSCodeRange(document, delta.range)
        let edit = new vscode.TextEdit(range, delta.replacement)
        debug(`Edit applied to document ${decodeURI(document.uri.toString())}`)
        edits.push(edit)
    }
    let workspaceEdit = new vscode.WorkspaceEdit()
    workspaceEdit.set(document.uri, edits)
    let worked = await vscode.workspace.applyEdit(workspaceEdit)

    return worked
}

function findOrCreateClient(name: string, directory: string): Client {
    // We re-use clients for configs with the same name and directory.
    for (let client of clients) {
        if (client.name === name && client.directory === directory) {
            return client
        }
    }

    // Otherwise, we create a new config and add it to the list of clients.
    let configuration = configurations[name]
    let client = new Client(name, configuration.cmd, directory)
    clients.push(client)
    return client
}

async function activateConfigForTextDocument(name: string, document: vscode.TextDocument, directory: string) {
    const key = document.uri.toString()
    if (opening.has(key)) return
    opening.add(key)
    try {
        await openSharedDocument(name, document, directory)
    } catch (error) {
        vscode.window.showErrorMessage(`TeamTypeV could not transfer this file: ${error}`)
    } finally {
        opening.delete(key)
    }
}

export async function openSharedDocument(name: string, document: vscode.TextDocument, directory: string) {
    const original = document
    rememberNativeCleanContent(original)
    if (!nativeCleanContents.has(original)) {
        await prepareNativeHandoff(original)
        vscode.window.showErrorMessage(
            "TeamTypeV cannot safely merge this dirty buffer because its original clean text is unknown. Its unsaved edits remain in this read-only tab; reconcile them with the file on disk before sharing.",
        )
        return
    }
    const existing = documentForUri(protocolUri(document))
    if (existing && clientsForDocument(existing).length) {
        await prepareNativeHandoff(original)
        if (original.isDirty) {
            vscode.window.showErrorMessage(
                "TeamTypeV: this file is already shared. Copy the native tab's unsaved edits into the shared tab; the native tab is now read-only.",
            )
            return
        }
        await closeNativeDocument(original)
        await vscode.window.showTextDocument(existing, {preview: false})
        return
    }
    let client = findOrCreateClient(name, directory)
    try {
        new TextDecoder("utf-8", {fatal: true}).decode(fs.readFileSync(original.uri.fsPath))
        await client.connection.sendRequest("daemonWriter", {})
        await prepareNativeHandoff(original)
    } catch (error) {
        vscode.window.showErrorMessage(`TeamTypeV cannot share this file: ${error}`)
        return
    }
    rememberNativeCleanContent(original)
    const initialContent = nativeCleanContents.get(original)!
    const sharedUri = original.uri.with({scheme: "teamtypev"})
    const transferredContent = original.getText()
    const transferredVersion = original.version
    sharedContents.set(sharedUri.toString(), Buffer.from(initialContent, "utf8"))
    document = await vscode.workspace.openTextDocument(sharedUri)
    sharedContents.delete(sharedUri.toString())
    if (document.getText() !== transferredContent) {
        const transfer = new vscode.WorkspaceEdit()
        transfer.replace(sharedUri, new vscode.Range(0, 0, document.lineCount, 0), transferredContent)
        if (!(await vscode.workspace.applyEdit(transfer))) {
            throw new Error("Could not copy the native edits; the original remains open and read-only")
        }
    }
    if (original.version !== transferredVersion) {
        vscode.window.showErrorMessage(
            "TeamTypeV: the native document changed during transfer. Its edits remain in the read-only native tab; sharing has not started.",
        )
        return
    }
    await closeNativeDocument(original)
    const uri = protocolUri(document)
    debug("OPEN " + decodeURI(uri))
    client.ot_states[uri] = {revision: new Revision(), content: getLines(document)}
    const opened = client.connection.sendRequest("open", {uri, content: initialContent, daemonWrites: true})
    const delta = handoffDelta(initialContent, transferredContent)
    const edited = delta.length ? client.connection.sendRequest(editType, {uri, revision: 0, delta}) : Promise.resolve()
    if (delta.length) client.ot_states[uri].revision.editor += 1
    await vscode.window.showTextDocument(document, {preview: false})
    await Promise.all([opened, edited])
        .then(() => {
            debug("Successfully opened. Tracking changes.")
            document.save()
        })
        .catch((error) => {
            delete client.ot_states[uri]
            throw error
        })
}

/** Preserves local edits as one operation against the native document's original version. */
function handoffDelta(before: string, after: string): Delta[] {
    const oldChars = Array.from(before)
    const newChars = Array.from(after)
    let start = 0
    while (start < oldChars.length && start < newChars.length && oldChars[start] === newChars[start]) start++
    let end = oldChars.length
    let newEnd = newChars.length
    while (end > start && newEnd > start && oldChars[end - 1] === newChars[newEnd - 1]) {
        end--
        newEnd--
    }
    if (start === end && start === newEnd) return []
    const position = (offset: number): Position => {
        const lines = oldChars.slice(0, offset).join("").split("\n")
        return {line: lines.length - 1, character: Array.from(lines[lines.length - 1]).length}
    }
    return [{range: {start: position(start), end: position(end)}, replacement: newChars.slice(start, newEnd).join("")}]
}

async function prepareNativeHandoff(original: vscode.TextDocument) {
    await vscode.window.showTextDocument(original, {preview: false})
    if (vscode.window.activeTextEditor?.document !== original) {
        throw new Error("The active editor changed before the native document could be made read-only")
    }
    await vscode.commands.executeCommand("workbench.action.files.setActiveEditorReadonlyInSession")
    if (vscode.window.activeTextEditor?.document !== original) {
        throw new Error("The active editor changed while preparing the native document")
    }
}

async function closeNativeDocument(original: vscode.TextDocument) {
    await vscode.window.showTextDocument(original, {preview: false})
    await vscode.commands.executeCommand("workbench.action.revertAndCloseActiveEditor")
    const tabs = vscode.window.tabGroups.all
        .flatMap((group) => group.tabs)
        .filter(
            (tab) => tab.input instanceof vscode.TabInputText && tab.input.uri.toString() === original.uri.toString(),
        )
    if (tabs.length && !(await vscode.window.tabGroups.close(tabs))) {
        throw new Error("TeamTypeV could not close the read-only native tabs; sharing has not started")
    }
}

async function processUserOpen(document: vscode.TextDocument) {
    rememberNativeCleanContent(document)
    // Ignore documents using the git: scheme, which is used by VS Code's Git integration.
    if (document.uri.scheme !== "file") {
        return
    }

    for (let name of Object.keys(configurations)) {
        let configuration = configurations[name]
        const filename = document.fileName
        for (let rootMarker of configuration.rootMarkers) {
            const directory = findMarkerDirectory(path.dirname(filename), rootMarker)
            if (directory) {
                activateConfigForTextDocument(name, document, directory)
            }
        }
    }
}

function clientsForDocument(document: vscode.TextDocument): Client[] {
    return clients.filter((client) => clientTracksDocument(client, document))
}

function clientTracksDocument(client: Client, document: vscode.TextDocument): boolean {
    return document.uri.scheme === "teamtypev" && Object.keys(client.ot_states).includes(protocolUri(document))
}

function processUserClose(document: vscode.TextDocument) {
    for (let client of clientsForDocument(document)) {
        const uri = protocolUri(document)
        client.connection.sendRequest(closeType, {uri})

        delete client.ot_states[uri]
    }
}

// NOTE: We might get multiple events per document.version,
// as the _state_ of the document might change (like isDirty).
function processUserEdit(event: vscode.TextDocumentChangeEvent) {
    rememberNativeChange(event)
    if (event.contentChanges.length === 0) return
    const uri = protocolUri(event.document)
    const lines = getLines(event.document)
    if (pendingRemote?.uri === uri) {
        pendingRemote.changes.push({event, lines, content: event.document.getText(), version: event.document.version})
        return
    }
    processLocalEdit(event, lines)
}

function processLocalEdit(event: vscode.TextDocumentChangeEvent, lines: string[]) {
    for (let client of clientsForDocument(event.document)) {
        try {
            let document = event.document

            const uri = protocolUri(document)

            let revision = client.ot_states[uri].revision

            let edits = vsCodeChangeEventToTeamtypevEdits(client, event)

            for (const theEdit of edits) {
                // interestingly this seems to block when it can't send
                client.connection.sendRequest(editType, theEdit).catch((e) => {
                    vscode.window.showErrorMessage(
                        `Error while sending edit to TeamTypeV daemon: ${e}. This is probably a bug in the VS Code plugin.`,
                    )
                })
                revision.editor += 1

                debug(`sent edit for dR ${revision.daemon} (having edR ${revision.editor})`)
            }

            // TODO: Make this more efficient by replacing only the changed lines.
            // The challenge with that is that we need to compute how many lines are
            // left after the edit.
            client.ot_states[uri].content = lines

            // Attempt auto-save to avoid the situation where one user closes a modified
            // document without saving, which will cause VS Code to undo the dirty changes.
            document.save()
        } catch (e) {
            vscode.window.showErrorMessage(`Error while sending edit to TeamTypeV daemon: ${e}`)
        }
    }
}

function processSelection(event: vscode.TextEditorSelectionChangeEvent) {
    for (let client of clientsForDocument(event.textEditor.document)) {
        let uri = protocolUri(event.textEditor.document)
        let content = client.ot_states[uri].content
        let ranges = event.selections.map((s) => {
            return vsCodeRangeToTeamtypevRange(content, s)
        })
        client.connection.sendNotification(cursorType, {uri, ranges})
    }
}

function vsCodeChangeEventToTeamtypevEdits(client: Client, event: vscode.TextDocumentChangeEvent): Edit[] {
    let document = event.document
    let uri = protocolUri(document)

    let ot_state = client.ot_states[uri]
    let revision = ot_state.revision

    let content = ot_state.content
    return [
        {
            uri,
            revision: revision.daemon,
            delta: event.contentChanges.map((change) => vsCodeChangeToTeamtypevDelta(content, change)),
        },
    ]
}

function vsCodeChangeToTeamtypevDelta(content: string[], change: vscode.TextDocumentContentChangeEvent): Delta {
    return {
        range: vsCodeRangeToTeamtypevRange(content, change.range),
        replacement: change.text,
    }
}

function showCursorNotification() {
    vscode.window.showInformationMessage(getCursorInfo(), {modal: true})
}

export function activate(context: vscode.ExtensionContext) {
    debug("TeamTypeV extension activated!")

    // 🧑 "Treat us as a separate project."
    configurations = vscode.workspace.getConfiguration("teamtypev").get<{[key: string]: Configuration}>("configs", {})

    context.subscriptions.push(
        vscode.workspace.registerFileSystemProvider("teamtypev", new SharedFileSystem(), {isCaseSensitive: true}),
        vscode.workspace.onDidChangeTextDocument(processUserEdit),
        vscode.workspace.onDidOpenTextDocument(processUserOpen),
        vscode.workspace.onDidCloseTextDocument(processUserClose),
        vscode.window.onDidChangeTextEditorSelection(processSelection),
        vscode.window.onDidChangeActiveTextEditor(drawCursors),
        vscode.commands.registerCommand("teamtypev.showCursors", showCursorNotification),
    )

    openCurrentTextDocuments()

    debug("End of activation")
}

export function deactivate() {
    clients.forEach((client) => {
        client.connection.dispose()
        client.process.kill()
    })
    clients = []
}

function debug(text: string) {
    // Disabled because we don't need it right now.
    // console.log(Date.now() - t0 + " " + text)
}

function die(text: string): never {
    vscode.window.showErrorMessage(text)
    throw new Error(text)
}

function updateContents(client: Client, document: vscode.TextDocument) {
    client.ot_states[protocolUri(document)].content = getLines(document)
}

function getLines(document: vscode.TextDocument): string[] {
    let lines = new Array(document.lineCount)
    for (let line = 0; line < document.lineCount; line++) {
        lines[line] = document.lineAt(line).text
    }
    return lines
}
