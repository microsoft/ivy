;;; ivy-mode.el --- A major mode for IVy source files

;; Copyright (c) Microsoft Corporation

;; Author: Microsoft
;; Version: 1.0
;; URL: http://github.com/Microsoft/ivy
;; Keywords: languages, ivy

;; Permission is hereby granted, free of charge, to any person
;; obtaining a copy of this software and associated documentation
;; files (the "Software"), to deal in the Software without
;; restriction, including without limitation the rights to use, copy,
;; modify, merge, publish, distribute, sublicense, and/or sell copies
;; of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:
;;
;; The above copyright notice and this permission notice shall be
;; included in all copies or substantial portions of the Software.
;;
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;; DEALINGS IN THE SOFTWARE.

;;; Commentary:

;; A major mode for editing IVy source files.

;; To use this, place this file somewhere in your emacs load-path and
;; add this code to your emacs init file:

;; (add-to-list 'auto-mode-alist '("\\.ivy\\'" . ivy-mode))
;; (autoload 'ivy-mode "ivy" "Major mode for editing IVy code" t)

;;; Code:

(defconst ivy-keywords
  '("relation"
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
    "mixord"
    "extract"
    "function"
    "class"
    "object"
    "method"
    "execute"
    "destructor"
    "some"
    "maximizing"
    "maximizing"
    "private"
    "implement"
    "using"
    "property"
    "while"
    "invariant"
    "struct"
    "definition"
    "ghost"
    "alias"
    "trusted"
    "this"
    "var"
    "instance"
    "attribute"
    "variant"
    "of"
    "proof"
    "specification"
    "implementation"
    "decreases"
    "require"
    "ensure"
    "around"
    "parameter"))

(defconst ivy-types '("bool" "int" "bv"))
(defconst ivy-constants '())
(defconst ivy-events '())
(defconst ivy-functions '())

(defconst ivy-keywords-regexp (regexp-opt ivy-keywords 'words))
(defconst ivy-type-regexp (regexp-opt ivy-types 'words))
(defconst ivy-constant-regexp (regexp-opt ivy-constants 'words))
(defconst ivy-event-regexp (regexp-opt ivy-events 'words))
(defconst ivy-functions-regexp (regexp-opt ivy-functions 'words))

(defconst ivy-font-lock-keywords
  `((,ivy-type-regexp . font-lock-type-face)
    (,ivy-constant-regexp . font-lock-constant-face)
    (,ivy-event-regexp . font-lock-builtin-face)
    (,ivy-functions-regexp . font-lock-function-name-face)
    (,ivy-keywords-regexp . font-lock-keyword-face)))

(defgroup ivy nil
  "Major mode for IVy source files."
  :group 'languages)

(defcustom ivy-indent-offset 4
  "Indentation offset for `ivy-mode'."
  :type 'integer
  :group 'ivy)

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

(defvar ivy-syntax-table
  (let ((synTable (make-syntax-table)))

    ;; bash style comment: “# …”
    (modify-syntax-entry ?# "< b" synTable)
    (modify-syntax-entry ?\n "> b" synTable)

    synTable)
  "Syntax table for `ivy-mode'.")

;;;###autoload
(define-derived-mode ivy-mode text-mode "Ivy"
  "Major mode for editing Ivy files."
  (make-local-variable 'ivy-indent-offset)
  (set (make-local-variable 'indent-line-function) 'ivy-indent-line)
  (set (make-local-variable 'comment-start) "#")
  (set-syntax-table ivy-syntax-table)
  (setq font-lock-defaults '((ivy-font-lock-keywords))))

(provide 'ivy-mode)
;; Local Variables:
;; indent-tabs-mode: nil
;; End:
;;; ivy-mode.el ends here
