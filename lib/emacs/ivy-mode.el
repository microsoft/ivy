
(setq ivy-keywords '(
   "relation"
   "individual"
   "axiom"
   "conjecture"
   "schema"
   "instantiate"
   "derived"
   "concept"
   "init"
   "action"
   "state"
   "assume"
   "assert"
   "set"
   "null"
   "old"
   "from"
   "update"
   "params"
   "in"
   "match"
   "ensures"
   "requires"
   "modifies"
   "true"
   "false"
   "fresh"
   "module"
   "type"
   "if"
   "else"
   "local"
   "let"
   "call"
   "entry"
   "macro"
   "interpret"
   "forall"
   "exists"
   "returns"
   "mixin"
   "before"
   "after"
   "isolate"
   "with"
   "export"
   "delegate"
   "import"
   "include"
   "progress"
   "rely"
) )

(setq ivy-types '("bool" "int" "bv"))
(setq ivy-constants '())
(setq ivy-events '())
(setq ivy-functions '())

(setq ivy-keywords-regexp (regexp-opt ivy-keywords 'words))
(setq ivy-type-regexp (regexp-opt ivy-types 'words))
(setq ivy-constant-regexp (regexp-opt ivy-constants 'words))
(setq ivy-event-regexp (regexp-opt ivy-events 'words))
(setq ivy-functions-regexp (regexp-opt ivy-functions 'words))

(setq ivy-font-lock-keywords
      `(
        (,ivy-type-regexp . font-lock-type-face)
        (,ivy-constant-regexp . font-lock-constant-face)
        (,ivy-event-regexp . font-lock-builtin-face)
        (,ivy-functions-regexp . font-lock-function-name-face)
        (,ivy-keywords-regexp . font-lock-keyword-face)
        ))

(defvar ivy-indent-offset 4
  "*Indentation offset for `ivy-mode'.")

(defun ivy-indent-line ()
  "Indent current line for `ivy-mode'."
  (interactive)
  (let ((indent-col 0))
    (save-excursion
      (beginning-of-line)
      (condition-case nil
          (while t
            (backward-up-list 1)
            (when (looking-at "[[{]")
              (setq indent-col (+ indent-col ivy-indent-offset))))
        (error nil)))
    (save-excursion
      (back-to-indentation)
      (when (and (looking-at "[]}]") (>= indent-col ivy-indent-offset))
        (setq indent-col (- indent-col ivy-indent-offset))))
    (indent-line-to indent-col)))

;(defvar ivy-syntax-table nil "Syntax table for `ivy-mode'.")
(setq ivy-syntax-table
      (let ((synTable (make-syntax-table)))

        ;; bash style comment: “# …”
        (modify-syntax-entry ?# "< b" synTable)
        (modify-syntax-entry ?\n "> b" synTable)

        synTable))

;;;###autoload
(define-derived-mode ivy-mode text-mode "Ivy"
  "Mode for editing Ivy files."
  (make-local-variable 'ivy-indent-offset)
  (set (make-local-variable 'indent-line-function) 'ivy-indent-line)
  (set (make-local-variable 'comment-start) "#")
  (set-syntax-table ivy-syntax-table)
  (setq font-lock-defaults '((ivy-font-lock-keywords))))


; add this code to your .emacs:

; (add-to-list 'auto-mode-alist '(""\\.ivy\\'" . ivy-mode))
; (autoload 'ivy-mode "ivy" "Major mode for editing Ivy code" t) 

(provide 'ivy-mode)
