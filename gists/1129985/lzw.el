(eval-when-compile
  (require 'cl))

(defun lzw-compress-string (uncompressed)
  "Compress a string to a list of output symbols."
  ;; Build the dictionary.
  (let* ((dict-size 256)
	 (dictionary
	  (let ((dict (make-hash-table :size dict-size :test 'equal)))
	    (dotimes (i dict-size)
	      (puthash (char-to-string i) (char-to-string i) dict))
	    dict)))
    (with-temp-buffer
      (let ((w ""))
	(dolist (c (string-to-list uncompressed))
	  (let ((wc (concat w (char-to-string c))))
	    (if (gethash wc dictionary)
		(setq w wc)
	      (insert (gethash w dictionary))
	      ;; Add wc to the dictionary.
	      (puthash wc (char-to-string dict-size) dictionary)
	      (setq dict-size (1+ dict-size)
		    w (char-to-string c)))))
	;; Output the code for w.
	(if w
	    (insert (gethash w dictionary))))
      (buffer-string))))
 
(defun lzw-decompress-string (compressed)
  "Decompress a list of output ks to a string."
  ;; Build the dictionary.
  (let* ((dict-size 256)
	 (dictionary
	  (let ((dict (make-hash-table :size dict-size :test 'equal)))
	    (dotimes (i dict-size)
	      (puthash (char-to-string i) (char-to-string i) dict))
	    dict)))
    (with-temp-buffer
      (let* ((compr-list (string-to-list compressed))
	     (w (char-to-string (pop compr-list))))
	(insert w)
	(dolist (k compr-list)
	  (let ((entry
		 (or (gethash (char-to-string k) dictionary)
		     (if (= k dict-size)
			 (concat w (aref w 0))
		       (error "Bad compressed k: %s" k)))))
	    (insert entry)
	    
	    ;; Add w+entry[0] to the dictionary.
	    (puthash (char-to-string dict-size)
		     (concat w (char-to-string (aref entry 0)))
		     dictionary)
	    (setq dict-size (1+ dict-size)
		  w entry))))
      (buffer-string))))

;;; ox-lzw.el ends here
