(defun char-mapping (key char)
  (bind-key key `(lambda () (interactive) (insert ,char))))

(char-mapping "A-L" "Γ")
(char-mapping "A-l" "λ x → ")
(char-mapping "A-:" " ∷ ")
(char-mapping "A-r" " → ")
(char-mapping "A-~" " ≅ ")
(char-mapping "A-=" " ≡ ")
