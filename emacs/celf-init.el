;;; Begin Celf mode setup

;; Extend emacs load path, if necessary
(cond ((not (member (concat celf-root "emacs") load-path))
        (setq load-path (cons (concat celf-root "emacs") load-path))))

;; Autoload libraries when Celf-related major modes are started.
(autoload 'celf-mode "celf" "Major mode for editing Celf source." t)
(autoload 'celf-server "celf" "Run an inferior Celf server." t)
(autoload 'celf-sml "celf" "Run an inferior Celf-SML process." t)
(autoload 'celf-info "celf" "Browse Celf User's Guide." t)

;; Switch buffers to Celf mode based on filename extension,
;; which is one of .elf, .quy, .thm, or .cfg.
(setq auto-mode-alist
      (cons '("\\.xlf$" . celf-mode)
	    (cons '("\\.clf$" . celf-mode)
		  (cons '("\\.quy$" . celf-mode)
			(cons '("\\.thm$" . celf-mode)
			      (cons '("\\.cfg$" . celf-mode)
				    auto-mode-alist))))))

;; Default Celf server program location
(setq celf-server-program
      (concat celf-root "bin/celf-server"))

;; Default Celf SML program location
(setq celf-sml-program
      (concat celf-root "bin/celf-sml"))

;; Default documentation location (in info format)
(setq celf-info-file
      (concat celf-root "doc/info/celf.info"))

;; Automatically highlight Celf sources using font-lock
(add-hook 'celf-mode-hook 'celf-font-fontify-buffer)

;;; End Celf mode setup
