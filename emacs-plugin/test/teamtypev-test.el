;;; teamtypev-test.el --- tests of the editor side of the daemon-editor protocol  -*- lexical-binding: t; -*-

;; SPDX-FileCopyrightText: 2026 TeamTypeV contributors
;;
;; SPDX-License-Identifier: AGPL-3.0-or-later

;; Without a daemon: `jsonrpc-async-request' is replaced by a recorder.
;; Run from emacs-plugin: emacs --batch -L . -l teamtypev -l test/teamtypev-test.el -f ert-run-tests-batch-and-exit

(require 'ert)
(require 'cl-lib)
(require 'teamtypev)

(defvar teamtypev-test--sent nil "Recorded edit requests, newest first, as (REVISION . DELTA-LIST).")
(defconst teamtypev-test--path "/tmp/teamtypev-test-dir/file.txt")

(defmacro teamtypev-test--with-buffer (content &rest body)
  "Run BODY in a synced, tracked buffer holding CONTENT."
  (declare (indent 1))
  `(let ((teamtypev-test--sent nil))
     (cl-letf (((symbol-function 'jsonrpc-async-request)
                (lambda (_conn method params &rest _)
                  (when (eq method 'edit)
                    (push (cons (plist-get params :revision) (append (plist-get params :delta) nil))
                          teamtypev-test--sent)))))
       (with-temp-buffer
         (insert ,content)
         (setq-local buffer-file-name teamtypev-test--path
                     buffer-file-truename teamtypev-test--path)
         (setq-local teamtypev--client (list :connection nil)
                     teamtypev--synced t
                     teamtypev--editor-revision 0
                     teamtypev--daemon-revision 0
                     teamtypev--shadow (teamtypev--buffer-content))
         (teamtypev--track-changes)
         ,@body))))

(defun teamtypev-test--daemon-edit (revision sl sc el ec text)
  (teamtypev--handle-edit-notification
   (list :uri (teamtypev--path-to-uri teamtypev-test--path) :revision revision
         :delta (vector (list :range (list :start (list :line sl :character sc)
                                           :end (list :line el :character ec))
                              :replacement text)))))

(defun teamtypev-test--range (edit)
  (let ((r (plist-get edit :range)))
    (list (plist-get (plist-get r :start) :line) (plist-get (plist-get r :start) :character)
          (plist-get (plist-get r :end) :line) (plist-get (plist-get r :end) :character)
          (plist-get edit :replacement))))

(defun teamtypev-test--only-edit ()
  (should (= 1 (length teamtypev-test--sent)))
  (should (= 1 (length (cdar teamtypev-test--sent))))
  (teamtypev-test--range (cadar teamtypev-test--sent)))

(ert-deftest teamtypev-narrowed-local-edit-uses-whole-buffer-positions ()
  (teamtypev-test--with-buffer "a\nb\nc"
    (narrow-to-region 5 6)
    (goto-char 5)
    (insert "x")
    (should (equal (teamtypev-test--only-edit) '(2 0 2 0 "x")))))

(ert-deftest teamtypev-replace-regexp-in-region-reports-right-ranges ()
  (teamtypev-test--with-buffer "\U0001F600\na b"
    (replace-regexp-in-region "\n" "Z\n" 1 5)
    (should (equal (teamtypev-test--only-edit) '(0 1 1 0 "Z\n")))))

(ert-deftest teamtypev-region-wide-before-change-narrow-after-change ()
  ;; `upcase-region' reports the whole region before, and only the changed part after.
  (teamtypev-test--with-buffer "éa\nbcd\n"
    (upcase-region 1 8)
    (should (equal (buffer-string) "ÉA\nBCD\n"))
    (should (equal (teamtypev--buffer-content) teamtypev--shadow))
    ;; Applying the sent edits to the old text gives the new text.
    (let ((text "éa\nbcd\n"))
      (dolist (d (reverse teamtypev-test--sent))
        (let* ((e (car (cdr d)))
               (r (teamtypev-test--range e))
               (lines (split-string text "\n"))
               (off (lambda (l c) (+ c (cl-loop for i below l sum (1+ (length (nth i lines))))))))
          (setq text (concat (substring text 0 (funcall off (nth 0 r) (nth 1 r)))
                             (nth 4 r)
                             (substring text (funcall off (nth 2 r) (nth 3 r)))))))
      (should (equal text (buffer-string))))))

(ert-deftest teamtypev-after-change-without-before-change-is-harmless ()
  (teamtypev-test--with-buffer "ab\n"
    (goto-char 2)
    (insert-buffer-substring (current-buffer) 2 2)
    (should (null teamtypev-test--sent))
    (should (= teamtypev--editor-revision 0))))

(ert-deftest teamtypev-local-edit-revisions ()
  (teamtypev-test--with-buffer "ab"
    (goto-char 1)
    (insert "x")
    (should (equal (caar teamtypev-test--sent) 0))
    (should (= teamtypev--editor-revision 1))
    (teamtypev-test--daemon-edit 1 0 0 0 0 "D")
    (should (= teamtypev--daemon-revision 1))
    (goto-char 1)
    (insert "y")
    (should (equal (caar teamtypev-test--sent) 1))
    (should (= teamtypev--editor-revision 2))
    (should (equal (buffer-string) "yDxab"))))

(ert-deftest teamtypev-stale-daemon-edit-is-ignored ()
  (teamtypev-test--with-buffer "ab"
    (insert "x")
    (teamtypev-test--daemon-edit 0 0 0 0 0 "STALE")
    (should (equal (buffer-string) "abx"))
    (should (= teamtypev--daemon-revision 0))
    (should (= 1 (length teamtypev-test--sent)))))

(ert-deftest teamtypev-daemon-edit-applies-in-narrowed-buffer-without-echo ()
  (teamtypev-test--with-buffer "a\nb\nc"
    (narrow-to-region 5 6)
    (teamtypev-test--daemon-edit 0 0 1 0 1 "\U0001F600")
    (should (equal (save-restriction (widen) (buffer-string)) "a\U0001F600\nb\nc"))
    (should (null teamtypev-test--sent))
    (should (= teamtypev--daemon-revision 1))
    (should (buffer-narrowed-p))))

(ert-deftest teamtypev-unappliable-daemon-edit-is-answered-with-empty-delta ()
  (dolist (bad '((5 0 5 0) (0 9 0 9) (1 0 1 0) (0 0 2 0)))
    (teamtypev-test--with-buffer "ab"        ; no final newline: no line 1
      (apply #'teamtypev-test--daemon-edit 0 (append bad '("X")))
      (should (equal (buffer-string) "ab"))
      (should (= teamtypev--daemon-revision 0))
      (should (= teamtypev--editor-revision 1))
      (should (equal teamtypev-test--sent '((0)))) ; revision 0 = daemon_revision, empty delta
      (should (null teamtypev--ignore-changes))
      ;; later local edits are still sent
      (insert "z")
      (should (= 2 (length teamtypev-test--sent))))))

(ert-deftest teamtypev-final-empty-line-exists-only-after-newline ()
  (teamtypev-test--with-buffer "ab\n"
    (teamtypev-test--daemon-edit 0 1 0 1 0 "X")
    (should (equal (buffer-string) "ab\nX"))
    (should (= teamtypev--daemon-revision 1))))

(ert-deftest teamtypev-apply-error-does-not-ignore-later-edits ()
  (teamtypev-test--with-buffer "ab"
    (setq buffer-read-only t)
    (teamtypev-test--daemon-edit 0 0 0 0 0 "X")
    (should (equal (buffer-string) "ab"))
    (should (null teamtypev--ignore-changes))
    (should (equal teamtypev-test--sent '((0))))))

(ert-deftest teamtypev-edits-outside-a-synced-session-are-dropped ()
  (teamtypev-test--with-buffer "ab"
    (setq-local teamtypev--synced nil)   ; open not acknowledged yet, or closed
    (teamtypev-test--daemon-edit 0 0 0 0 0 "X")
    (should (equal (buffer-string) "ab"))
    (should (= teamtypev--daemon-revision 0))
    (should (null teamtypev-test--sent))))

(ert-deftest teamtypev-open-answer-of-an-old-session-does-not-sync-the-new-one ()
  (teamtypev-test--with-buffer "ab"
    (let ((old (list 'session)) (new (list 'session)))
      (setq-local teamtypev--session new teamtypev--synced nil)
      (cl-letf (((symbol-function 'find-buffer-visiting) (lambda (_) (current-buffer))))
        (teamtypev--open-answered teamtypev-test--path old)
        (should-not teamtypev--synced)
        (teamtypev--open-answered teamtypev-test--path new)
        (should teamtypev--synced)))))

;; Randomized protocol scenarios against a reference state machine of the rules proved in
;; editor_proof: local edits, daemon edits with arbitrary revisions (fitting or not), close, reopen,
;; and answers to current and stale open requests, in random order.
(ert-deftest teamtypev-random-protocol-scenarios ()
  (dotimes (seed 150)
    (random (format "seed-%d" seed))
    (teamtypev-test--with-buffer "abc\ndef\n"
      (let ((live nil) (dr 0) (er 0) (tokens nil) (pending nil))
        (setq-local teamtypev--synced nil)
        (cl-flet ((open () (let ((tok (list 'session)))
                             (push tok tokens)
                             (setq pending tok live nil)
                             (setq-local teamtypev--session tok teamtypev--synced nil)))
                  (close () (setq pending nil live nil)
                            (setq-local teamtypev--session nil teamtypev--synced nil)))
          (open)
          (dotimes (step 40)
            (let* ((kind (1+ (random 7))) (n (length teamtypev-test--sent))
                   (ctx (format "seed %d step %d kind %d" seed step kind)))
              (cl-letf (((symbol-function 'find-buffer-visiting) (lambda (_) (current-buffer))))
                (pcase kind
                  (1 (let* ((tok (or (nth (random (max 1 (length tokens))) tokens) (list 'unknown))))
                       (setq tokens (delq tok tokens))
                       (teamtypev--open-answered teamtypev-test--path tok)
                       (when (and pending (eq tok pending))
                         (setq live t dr 0 er 0 pending nil
                               teamtypev-test--sent nil
                               n 0)
                         (setq-local teamtypev--editor-revision 0 teamtypev--daemon-revision 0
                                     teamtypev--shadow (teamtypev--buffer-content)))))
                  (2 (close))
                  (3 (when (or (null teamtypev--session) (= 1 (random 2))) (open)))
                  (4 (save-excursion (goto-char 1) (insert "x"))
                     (if live
                         (progn (should (= (length teamtypev-test--sent) (1+ n)))
                                (should (= (caar teamtypev-test--sent) dr))
                                (setq er (1+ er)))
                       (when teamtypev--synced (ert-fail ctx))))
                  (t (let* ((revs (list er er (1- er) (1+ er) 0))
                            (rev (nth (random (length revs)) revs))
                            (fits (> (random 3) 0))
                            (before (buffer-string)))
                       (if fits
                           (teamtypev-test--daemon-edit rev 0 0 0 0 "D")
                         (teamtypev-test--daemon-edit rev 40 0 40 0 "BAD"))
                       (if (and live (= rev er))
                           (if fits
                               (progn (should (equal (buffer-string) (concat "D" before)))
                                      (should (= (length teamtypev-test--sent) n))
                                      (setq dr (1+ dr)))
                             (should (equal (buffer-string) before))
                             (should (= (length teamtypev-test--sent) (1+ n)))
                             (should (equal (car teamtypev-test--sent) (cons dr nil)))
                             (setq er (1+ er)))
                         (should (equal (buffer-string) before))
                         (should (= (length teamtypev-test--sent) n)))))))
              (when live
                (should (= teamtypev--daemon-revision dr))
                (should (= teamtypev--editor-revision er))))))))))

(ert-deftest teamtypev-multibyte-positions-count-characters ()
  (teamtypev-test--with-buffer "\U0001F600éb\n"
    (teamtypev-test--daemon-edit 0 0 2 0 3 "Z")
    (should (equal (buffer-string) "\U0001F600eZb\n"))
    (goto-char (point-max))
    (insert "\u65e5")
    (should (equal (teamtypev-test--only-edit) '(1 0 1 0 "日")))))

;;; teamtypev-test.el ends here
