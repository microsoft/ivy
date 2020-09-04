(flycheck-define-checker ivy
  "A Scala syntax checker using the Scala compiler.

See URL `https://www.scala-lang.org/'."
  :command ("ivy_check" source)
  :error-patterns
  ((error line-start (zero-or-more space) (file-name) ": line " line ": error: " (message) line-end)
   (error line-start (zero-or-more space) (file-name) ": line " line ": " (message (zero-or-more not-newline)  "FAIL") line-end)
   (error line-start (file-name) "(" line "): error: " (message) line-end)
;   (error line-start (zero-or-more space) (file-name) ": line " line ": Proof goals:" line-end (message ">" (zero-or-more not-newline) line-end)))
   (error line-start (zero-or-more space) (file-name) ": line " line ": " (message "Proof goals:" (one-or-more "\n>" (zero-or-more not-newline))) line-end))
  :modes ivy-mode)


(add-to-list 'flycheck-checkers 'ivy)

