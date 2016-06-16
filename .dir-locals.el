((coq-mode . ((eval . (flet
                          ((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
                        (setq coq-load-path
                              `((rec ,(pre ".") "RTS")
                                ))))
              (coq-prog-args . ("-emacs-U")))))

