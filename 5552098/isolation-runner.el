         (request
          "http://localhost:6000/interactive/start"
          :type "POST"
          :headers '(("Content-Type"    . "application/json")
                     ("X-RESTAPI-TOKEN" . "N7Ci-HwzQ3anc-xlybn8BQ"))
          :data (json-encode
                 '(("siiSourceFiles" .
                    (("main.hs" .
                      "import Control.Monad (replicateM_)\nimport Data.Char\nmain = do\n  putStrLn \"Hello\"\n  replicateM_ 2 $ getLine >>= putStrLn . map toUpper\n")))
                   ("siiDataFiles" . (("foo" . "bar")))
                   ("siiApproot" . nil)))
          :parser 'json-read
          :success (function*
                    (lambda (&key data &allow-other-keys)
                      (message "Received data: %S" data))))
