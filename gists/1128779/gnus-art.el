(defun gnus-article-add-button (from to fun &optional data text)
  "Create a button between FROM and TO with callback FUN and data DATA."
  (when gnus-article-button-face
    (gnus-overlay-put (gnus-make-overlay from to nil t)
		      'face gnus-article-button-face))
  (gnus-add-text-properties
   from to
   (nconc (and gnus-article-mouse-face
	       (list gnus-mouse-face-prop gnus-article-mouse-face))
	  (list 'gnus-callback fun)
	  (and data (list 'gnus-data data))))
  (widget-convert-button 'link from to :action 'gnus-widget-press-button
			 :help-echo (or text "Follow the link")
			 :keymap gnus-url-button-map
			 :button-keymap gnus-widget-button-keymap))