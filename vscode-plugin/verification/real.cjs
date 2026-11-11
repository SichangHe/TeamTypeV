// SPDX-License-Identifier: AGPL-3.0-or-later
// Loads the REAL top-level functions/consts of src/extension.ts into a vm context.
const fs = require("node:fs")
const path = require("node:path")
const vm = require("node:vm")
const ts = require("typescript")

function loadReal(names, globals = {}, file = path.join(__dirname, "../src/extension.ts")) {
    const source = fs.readFileSync(file, "utf8")
    const parsed = ts.createSourceFile("extension.ts", source, ts.ScriptTarget.Latest, true)
    const wanted = new Set(names)
    const found = new Set()
    const pieces = []
    for (const node of parsed.statements) {
        let name
        if (ts.isFunctionDeclaration(node) && node.name) name = node.name.text
        else if (ts.isVariableStatement(node)) name = node.declarationList.declarations[0].name.getText(parsed)
        if (name && wanted.has(name)) {
            found.add(name)
            pieces.push(node.getText(parsed).replace(/^export\s+/, ""))
        }
    }
    for (const n of names) if (!found.has(n)) throw new Error(`not found in extension.ts: ${n}`)
    const js = ts.transpileModule(pieces.join("\n"), {compilerOptions: {target: ts.ScriptTarget.ES2022}}).outputText
    const context = vm.createContext(globals)
    vm.runInContext(js + "\n;globalThis.__names = {" + names.map(n => `${n}: typeof ${n} === "undefined" ? undefined : ${n}`).join(",") + "}", context)
    return {context, fns: context.__names}
}
module.exports = {loadReal}
