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

(defvar-local teamtypev--ignore-changes nil
  "When non-nil, buffer changes are ignored and not sent to daemon.")

;;; Utility Functions

(defun teamtypev--find-root (file)
  "Find the root directory containing .teamtypev for FILE."
  (locate-dominating-file file ".teamtypev"))

(defun teamtypev--line-col-to-pos (line col)
  "Convert zero-based LINE and character COL to buffer position."
  (save-excursion
    (goto-char (point-min))
    (forward-line line)
    (+ (line-beginning-position) col)))

(defun teamtypev--pos-to-line-col (pos)
  "Convert buffer POS to zero-based line and character position.
Returns a cons (LINE . CHARACTER)."
  (save-excursion
    (goto-char pos)
    (cons (- (line-number-at-pos) 1)
          (- pos (line-beginning-position)))))

(defun teamtypev--buffer-content ()
  "Get the entire buffer content as a string."
  (buffer-substring-no-properties (point-min) (point-max)))

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

  (let* ((uri (teamtypev--path-to-uri filepath))
         (content (teamtypev--buffer-content))
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
                     (with-current-buffer buffer (setq-local teamtypev--shared t)))
                   (message "TeamTypeV: tracking %s" ,filepath))
     :error-fn `(lambda (err)
                  (message "TeamTypeV error opening file: %S" err)
                  (when-let ((buffer (find-buffer-visiting ,filepath)))
                    (with-current-buffer buffer
                      (setq-local teamtypev--client nil)))))))

(defun teamtypev--close-file ()
  "Close the current file in TeamTypeV."
  (when (and teamtypev--client buffer-file-name)
    (let* ((uri (teamtypev--path-to-uri buffer-file-name))
           (connection (plist-get teamtypev--client :connection)))
      (jsonrpc-notify connection 'close `(:uri ,uri))
      (setq-local teamtypev--client nil))))

;;; Change Tracking

(defvar-local teamtypev--start-pos nil)
(defvar-local teamtypev--end-pos nil)

(defun teamtypev--before-change (beg end)
  "Store the changed region."
  (unless teamtypev--ignore-changes
    (setq-local teamtypev--start-pos (teamtypev--pos-to-line-col beg))
    (setq-local teamtypev--end-pos (teamtypev--pos-to-line-col end))))

(defun teamtypev--after-change (beg end _len)
  "Send the change to the daemon after a buffer modification."
  (unless teamtypev--ignore-changes
    (when teamtypev--client
      (let* ((new-text (buffer-substring-no-properties beg end))
             (uri (teamtypev--path-to-uri buffer-file-name))
             (delta `[(:range (:start (:line ,(car teamtypev--start-pos)
                                       :character ,(cdr teamtypev--start-pos))
                               :end (:line ,(car teamtypev--end-pos)
                                       :character ,(cdr teamtypev--end-pos)))
                       :replacement ,new-text)])
             (connection (plist-get teamtypev--client :connection)))

        (setq-local teamtypev--editor-revision (1+ teamtypev--editor-revision))

        (jsonrpc-async-request
         connection 'edit
         `(:uri ,uri :revision ,teamtypev--daemon-revision :delta ,delta)
         ;; The default success callback fails on the daemon's string result.
         :success-fn #'ignore
         :error-fn (lambda (err) (message "TeamTypeV edit rejected: %S" err)))))))

(defun teamtypev--track-changes ()
  "Start tracking changes for the current buffer."
  (add-hook 'before-change-functions #'teamtypev--before-change nil t)
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
  "Handle an 'edit' notification from the daemon."
  (let* ((uri (plist-get params :uri))
         (revision (plist-get params :revision))
         (delta (plist-get params :delta))
         (filepath (teamtypev--uri-to-path uri))
         (buffer (find-buffer-visiting filepath)))

    (when buffer
      (with-current-buffer buffer
        ;; Only apply if revision matches our editor revision
        (when (= revision teamtypev--editor-revision)
          (teamtypev--apply-delta delta)
          (setq-local teamtypev--daemon-revision (1+ teamtypev--daemon-revision)))))))

(defun teamtypev--apply-delta (delta)
  "Apply DELTA to the current buffer.
Edits are sorted by position (descending) before applying, so that
later edits don't invalidate positions of earlier edits."
  (setq-local teamtypev--ignore-changes t)
  ;; An error while applying must not leave local edits ignored for good.
  (unwind-protect
      (save-excursion
        ;; Convert all changes to buffer positions.
        (let ((changes-with-positions
               (mapcar (lambda (change)
                         (let* ((range (plist-get change :range))
                                (replacement (plist-get change :replacement))
                                (start-info (plist-get range :start))
                                (end-info (plist-get range :end))
                                (start-line (plist-get start-info :line))
                                (start-char (plist-get start-info :character))
                                (end-line (plist-get end-info :line))
                                (end-char (plist-get end-info :character))
                                (beg (teamtypev--line-col-to-pos start-line start-char))
                                (end (teamtypev--line-col-to-pos end-line end-char)))
                           (list beg end replacement)))
                       (append delta nil)))) ; Convert vector to list.
          ;; Sort by start position descending, then by end position descending.
          (setq changes-with-positions
                (sort changes-with-positions
                      (lambda (a b)
                        (or (> (car a) (car b))
                            (and (= (car a) (car b))
                                 (> (cadr a) (cadr b)))))))
          ;; Apply changes in descending order (from end to beginning).
          (dolist (change changes-with-positions)
            (let ((beg (car change))
                  (end (cadr change))
                  (replacement (caddr change)))
              (delete-region beg end)
              (goto-char beg)
              (insert replacement)))))
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
