;; SPDX-FileCopyrightText: 2025 blinry <mail@blinry.org>
;; SPDX-FileCopyrightText: 2025 zormit <nt4u@kpvn.de>
;;
;; SPDX-License-Identifier: AGPL-3.0-or-later

(require 'jsonrpc)
(require 'cl-lib)

;;; Client Management

;; Registry of active clients. Each client is a plist with:
;; :root-dir - the root directory containing .teamtypev
;; :process - the teamtypev client process
;; :connection - the JSON-RPC connection
;; :files - hash table mapping file paths to file state
;; 🧑 "Treat us as a separate project."
(defvar teamtypev--clients nil
  "List of active TeamTypeV clients.")

;;; File State (buffer-local variables)

(defvar-local teamtypev--editor-revision 0
  "Number of operations this editor has made to the current buffer.")

(defvar-local teamtypev--daemon-revision 0
  "Number of operations received from the daemon for the current buffer.")

(defvar-local teamtypev--client nil
  "The teamtypev client associated with this buffer.")

(defvar-local teamtypev--shared nil
  "Whether native writes are forbidden for this buffer.")

(defvar-local teamtypev--synced nil
  "Non-nil once the daemon acknowledged `open' for this buffer in the session.
Edits from the daemon are applied only then: before, or after a close,
they belong to another session.")

(defvar-local teamtypev--session nil
  "A fresh object per `open' request.
It tells the answer to an old request from the answer to the current one.")

(defvar-local teamtypev--shadow nil
  "The text of the buffer as the daemon knows it.
That is the content sent at open, with every edit sent or received since
applied.  Local changes are computed against it.")

(defvar-local teamtypev--ignore-changes nil
  "When non-nil, buffer changes are ignored and not sent to daemon.")

;;; Utility Functions

(defun teamtypev--find-root (file)
  "Find the root directory containing .teamtypev for FILE."
  (locate-dominating-file file ".teamtypev"))

(defun teamtypev--line-col-to-pos (line col)
  "Buffer position of zero-based LINE and character COL in the whole buffer, or nil.
Like the daemon: lines end at newline characters, COL may be at most the line length, and a
final empty line exists only after a final newline.  Ignores narrowing."
  (save-excursion
    (save-restriction
      (widen)
      (goto-char (point-min))
      (when (and (integerp line) (integerp col) (>= line 0) (>= col 0)
                 (= 0 (forward-line line))
                 (bolp))
        (let ((bol (point)))
          (when (<= col (- (line-end-position) bol))
            (+ bol col)))))))

(defun teamtypev--advance (line col text)
  "Zero-based (LINE . CHARACTER) reached by starting at LINE and COL and passing over TEXT."
  (let ((last-newline (cl-position ?\n text :from-end t)))
    (if last-newline
        (cons (+ line (cl-count ?\n text))
              (- (length text) last-newline 1))
      (cons line (+ col (length text))))))

(defun teamtypev--offset-to-line-col (text offset)
  "Zero-based (LINE . CHARACTER) of the character OFFSET in TEXT."
  (teamtypev--advance 0 0 (substring text 0 offset)))

(defun teamtypev--buffer-content ()
  "Get the entire buffer content as a string."
  (save-restriction
    (widen)
    (buffer-substring-no-properties (point-min) (point-max))))

(defun teamtypev--uri-to-path (uri)
  (url-unhex-string
    (substring uri 7))) ; Remove the 'file://' from the URI. TODO: Make more stable?

(defun teamtypev--path-to-uri (path)
  (url-encode-url
    (concat "file://" path)))

;;; Client Management

(defun teamtypev--find-or-create-client (root-dir)
  "Find or create a TeamTypeV client for ROOT-DIR."
  ;; Look for existing client for this root directory.
  (let ((client (cl-find-if (lambda (c) (string= (plist-get c :root-dir) root-dir))
                            teamtypev--clients)))
    (or client
        (teamtypev--create-client root-dir))))

(defun teamtypev--create-client (root-dir)
  "Create a new TeamTypeV client for ROOT-DIR."
  (let* ((default-directory root-dir) ; Set working directory for the process.
         (process-name (format "teamtypev-%s" root-dir))
         (process (make-process
                   :name process-name
                   :buffer nil ; Do not append output of this process to any buffer.
                   :command '("teamtypev" "client")
                   :connection-type 'pipe
                   :noquery t))
         (connection (make-instance 'jsonrpc-process-connection
                                    :process process
                                    :notification-dispatcher #'teamtypev--handle-notification
                                    :on-shutdown `(lambda (_conn)
                                                    (teamtypev--daemon-lost ,root-dir))))
         (client (list :root-dir root-dir
                       :process process
                       :connection connection
                       :files (make-hash-table :test 'equal))))
    (push client teamtypev--clients)
    (message "Connected to TeamTypeV daemon in %s" root-dir)
    client))

(defun teamtypev--daemon-lost (root-dir)
  "Tell the user the daemon for ROOT-DIR is gone and stop edits that would not be shared."
  (setq teamtypev--clients
        (cl-remove-if (lambda (c) (string= (plist-get c :root-dir) root-dir)) teamtypev--clients))
  (dolist (buffer (buffer-list))
    (with-current-buffer buffer
      (when (and teamtypev--client (string= (plist-get teamtypev--client :root-dir) root-dir))
        (setq-local teamtypev--client nil)
        (setq buffer-read-only t))))
  (message "Connection to TeamTypeV daemon in %s lost. Restart the daemon, then reopen the files." root-dir))

;;; File Operations

(defun teamtypev--file-opened ()
  "Handle opening a file in a TeamTypeV-enabled directory."
  (when buffer-file-name
    (let ((root-dir (teamtypev--find-root buffer-file-name)))
      (when root-dir
        (let ((client (teamtypev--find-or-create-client root-dir)))
          (teamtypev--open-file client buffer-file-name))))))

(cl-defun teamtypev--open-file (client filepath)
  "Open FILEPATH with CLIENT."
  (unless (memq (coding-system-base buffer-file-coding-system) '(utf-8 undecided))
    (cl-return-from teamtypev--open-file nil))
  (condition-case err
      (jsonrpc-request (plist-get client :connection) 'daemonWriter '(:check t))
    (error
     (message "TeamTypeV needs a daemon with daemon-owned saves: %S" err)
     (cl-return-from teamtypev--open-file nil)))
  ;; Lock files (`.#name`) in the shared directory would be synced as files.
  (setq-local create-lockfiles nil)
  (setq-local backup-inhibited t)
  (auto-save-mode -1)
  (when (bound-and-true-p auto-revert-mode) (auto-revert-mode -1))
  (setq-local teamtypev--client client)
  (setq-local teamtypev--editor-revision 0)
  (setq-local teamtypev--daemon-revision 0)
  (setq-local teamtypev--synced nil)
  (setq-local teamtypev--session (list 'session))
  (setq-local teamtypev--shadow (teamtypev--buffer-content))

  (let* ((uri (teamtypev--path-to-uri filepath))
         (session teamtypev--session)
         (content teamtypev--shadow)
         (connection (plist-get client :connection))
         (process (plist-get client :process)))

    ;; Requests must not block: a blocking `jsonrpc-request' returns at the response and leaves
    ;; an edit notification that follows it unread until the daemon sends more data.
    (teamtypev--track-changes)
    (jsonrpc-async-request
     connection 'open `(:uri ,uri :content ,content :daemonWrites t)
     ;; This file is dynamically bound, so the callbacks get `filepath' by backquote.
     :success-fn `(lambda (_result)
                   (when-let ((buffer (find-buffer-visiting ,filepath)))
                     (with-current-buffer buffer
                       (setq-local teamtypev--shared t)
                       ;; The daemon sends this session\'s edits after the answer to `open\'.
                       (when (eq teamtypev--session ,session)
                         (setq-local teamtypev--synced t))))
                   (message "TeamTypeV: tracking %s" ,filepath))
     :error-fn `(lambda (err)
                  (message "TeamTypeV error opening file: %S" err)
                  (when-let ((buffer (find-buffer-visiting ,filepath)))
                    (with-current-buffer buffer
                      (when (eq teamtypev--session ,session)
                        (setq-local teamtypev--client nil)
                        (setq-local teamtypev--synced nil))))))))

(defun teamtypev--close-file ()
  "Close the current file in TeamTypeV."
  (when (and teamtypev--client buffer-file-name)
    (let* ((uri (teamtypev--path-to-uri buffer-file-name))
           (connection (plist-get teamtypev--client :connection)))
      (jsonrpc-notify connection 'close `(:uri ,uri))
      (setq-local teamtypev--synced nil)
      (setq-local teamtypev--session nil)
      (setq-local teamtypev--client nil))))

;;; Change Tracking

(defun teamtypev--send-edit (start end replacement)
  "Send the edit replacing START to END (zero-based (LINE . CHARACTER) pairs) with REPLACEMENT.
With nil START the delta is empty."
  (let ((delta (if start
                   `[(:range (:start (:line ,(car start) :character ,(cdr start))
                              :end (:line ,(car end) :character ,(cdr end)))
                      :replacement ,replacement)]
                 []))
        (uri (teamtypev--path-to-uri buffer-file-name))
        (connection (plist-get teamtypev--client :connection)))
    ;; Protocol: send with the number of daemon edits applied, then count it as ours.
    (let ((revision teamtypev--daemon-revision))
      (setq-local teamtypev--editor-revision (1+ teamtypev--editor-revision))
      (jsonrpc-async-request
       connection 'edit
       `(:uri ,uri :revision ,revision :delta ,delta)
       ;; The default success callback fails on the daemon\'s string result.
       :success-fn #'ignore
       :error-fn (lambda (err) (message "TeamTypeV edit rejected: %S" err))))))

(defun teamtypev--send-difference (old new)
  "Send the edit that turns the text OLD into NEW, if they differ."
  (let* ((limit (min (length old) (length new)))
         (prefix 0)
         (suffix 0))
    (while (and (< prefix limit) (eq (aref old prefix) (aref new prefix)))
      (setq prefix (1+ prefix)))
    (while (and (< (+ prefix suffix) limit)
                (eq (aref old (- (length old) suffix 1)) (aref new (- (length new) suffix 1))))
      (setq suffix (1+ suffix)))
    (unless (and (= prefix (length old)) (= prefix (length new)))
      (teamtypev--send-edit (teamtypev--offset-to-line-col old prefix)
                            (teamtypev--offset-to-line-col old (- (length old) suffix))
                            (substring new prefix (- (length new) suffix))))))

(defun teamtypev--resync ()
  "Make the daemon's text, `teamtypev--shadow', the buffer's, by sending the difference."
  (when teamtypev--shadow
    (let ((text (teamtypev--buffer-content)))
      (unless (equal text teamtypev--shadow)
        (let ((old teamtypev--shadow))
          (setq-local teamtypev--shadow text)
          (teamtypev--send-difference old text))))))

(defun teamtypev--after-change (beg end len)
  "Send the change of the region BEG to END, which replaced LEN characters, to the daemon.
The old text is taken from `teamtypev--shadow', not from where Emacs says it changed: some commands
(`upcase-region', `replace-regexp-in-region', ...) report regions that do not match, and some
report an after-change without a before-change.  If the report does not fit what is in the buffer,
the difference is sent instead, so that the daemon never has text other than the buffer's."
  (unless teamtypev--ignore-changes
    (when (and teamtypev--client teamtypev--shadow)
      (let* ((old teamtypev--shadow)
             (text (teamtypev--buffer-content))
             (from (1- beg))
             (to (+ from len))
             (replacement (and (<= 0 from) (<= end (1+ (length text))) (substring text from (1- end))))
             (expected (and replacement (<= to (length old))
                            (concat (substring old 0 from) replacement (substring old to)))))
        (cond
         ((equal old text))             ; Nothing changed.
         ((and expected (equal expected text))
          (teamtypev--send-edit (teamtypev--offset-to-line-col old from)
                                (teamtypev--offset-to-line-col old to)
                                replacement))
         (t (teamtypev--send-difference old text)))
        (setq-local teamtypev--shadow text)))))

(defun teamtypev--track-changes ()
  "Start tracking changes for the current buffer."
  (add-hook 'after-change-functions #'teamtypev--after-change nil t))

;; 🧑 "their save just tells teamtype to write"
(defun teamtypev--save ()
  "Ask the daemon to save this shared buffer without writing it from Emacs."
  (when (or teamtypev--shared teamtypev--client)
    (unless teamtypev--client (user-error "TeamTypeV daemon is disconnected"))
    (jsonrpc-request
     (plist-get teamtypev--client :connection) 'save
     `(:uri ,(teamtypev--path-to-uri buffer-file-name)))
    (set-visited-file-modtime)
    t))

;;; Protocol Message Handlers

(defun teamtypev--handle-notification (_conn method params)
  "Handle JSON-RPC notifications from daemon."
  (cond
   ((string= method "edit")
    (teamtypev--handle-edit-notification params))
   (t
    (message "Unknown teamtypev notification: %s" method))))

(defun teamtypev--handle-edit-notification (params)
  "Handle an 'edit' notification from the daemon.

Protocol: `teamtypev--daemon-revision' counts the daemon edits applied, `teamtypev--editor-revision' our
own edits sent.  An edit is applied iff its revision equals `teamtypev--editor-revision'; otherwise the
daemon will send a transformed one.  An edit that cannot be applied is answered with an empty delta
\(counted as our own edit), so that the daemon does not think we applied it."
  (let* ((uri (plist-get params :uri))
         (revision (plist-get params :revision))
         (delta (plist-get params :delta))
         (filepath (teamtypev--uri-to-path uri))
         (buffer (find-buffer-visiting filepath)))

    (when buffer
      (with-current-buffer buffer
        (when (and teamtypev--client teamtypev--synced)
          ;; Normally a no-op: the buffer is what the daemon knows.
          (teamtypev--resync))
        ;; Edits for a buffer that is not synced (open not acknowledged yet, or closed) belong to
        ;; another session.
        (when (and teamtypev--client teamtypev--synced (eql revision teamtypev--editor-revision))
          (if (teamtypev--apply-delta delta)
              (progn
                (setq-local teamtypev--daemon-revision (1+ teamtypev--daemon-revision))
                ;; If something else changed the buffer while applying (hooks), tell the daemon.
                (teamtypev--resync))
            (message "TeamTypeV: could not apply an edit from the daemon, answering with an empty edit")
            (teamtypev--send-edit nil nil nil)))))))

(defun teamtypev--resolve-delta (delta)
  "The list of (BEG END REPLACEMENT) in buffer positions for DELTA, sorted by position, or nil.
Returns the symbol `invalid' if a position does not exist or edits overlap."
  (let ((changes
         (mapcar (lambda (change)
                   (let* ((range (plist-get change :range))
                          (start (plist-get range :start))
                          (end (plist-get range :end))
                          (replacement (plist-get change :replacement))
                          (beg (teamtypev--line-col-to-pos (plist-get start :line) (plist-get start :character)))
                          (fin (teamtypev--line-col-to-pos (plist-get end :line) (plist-get end :character))))
                     (if (and beg fin (stringp replacement))
                         (list (min beg fin) (max beg fin) replacement)
                       (throw 'teamtypev-invalid 'invalid))))
                 (append delta nil))))
    (setq changes (sort changes (lambda (a b) (or (< (car a) (car b))
                                                  (and (= (car a) (car b)) (< (cadr a) (cadr b)))))))
    (cl-loop for (a b) on changes
             when (and b (> (cadr a) (car b)))
             do (throw 'teamtypev-invalid 'invalid))
    changes))

(defun teamtypev--apply-delta (delta)
  "Apply DELTA to the current buffer.  Return non-nil if it was applied.
If it cannot be applied (a position does not exist, the buffer is read-only, ...) the buffer is unchanged.
The edits refer to the buffer before any of them, so they are applied from the end."
  (setq-local teamtypev--ignore-changes t)
  ;; An error while applying must not leave local edits ignored for good.
  (unwind-protect
      (let ((changes (catch 'teamtypev-invalid
                       (save-restriction (widen) (teamtypev--resolve-delta delta)))))
        (when (and (listp changes) teamtypev--shadow
                   (condition-case nil
                       (progn
                         (save-excursion
                           ;; The daemon's positions refer to the whole buffer, whatever is narrowed.
                           (save-restriction
                             (widen)
                             (atomic-change-group
                               (dolist (change (reverse changes))
                                 (delete-region (car change) (cadr change))
                                 (goto-char (car change))
                                 (insert (caddr change))))))
                         t)
                     (error nil)))
          ;; What the daemon expects the buffer to be now.
          (let ((expected teamtypev--shadow))
            (dolist (change (reverse changes))
              (setq expected (concat (substring expected 0 (1- (car change)))
                                     (caddr change)
                                     (substring expected (1- (cadr change))))))
            (setq-local teamtypev--shadow expected)
            t)))
    (setq-local teamtypev--ignore-changes nil)))

;;; User Interface Modifications

(defun teamtypev--verify-file-modtime (original &optional buffer)
  "Let the daemon reconcile disk changes for shared BUFFER before a save."
  (with-current-buffer (or buffer (current-buffer))
    (if (or teamtypev--client teamtypev--shared)
        t
      (funcall original buffer))))

(defun teamtypev--prevent-prompt-when-file-changes-on-disk ()
  "Disables the supersession check, which is coming up because the daemon writes to disk."
  (defun teamtypev--suppress-supersession-check (original-fn &rest args)
  "Suppress supersession checks for teamtypev-controlled buffers."
  (if teamtypev--client
      nil ; Return nil = don't prompt, proceed with edit.
      (apply original-fn args)))

  (advice-add 'ask-user-about-supersession-threat :around
              #'teamtypev--suppress-supersession-check))

;;; Setup

(defun teamtypev--setup ()
  "Set up TeamTypeV for the current Emacs session."
  (add-hook 'find-file-hook #'teamtypev--file-opened)
  (add-hook 'kill-buffer-hook #'teamtypev--close-file)
  (add-hook 'write-contents-functions #'teamtypev--save)
  (advice-add 'verify-visited-file-modtime :around #'teamtypev--verify-file-modtime)
  (teamtypev--prevent-prompt-when-file-changes-on-disk))
(teamtypev--setup)

(provide 'teamtypev)
