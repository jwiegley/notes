src/Idris/DeepSeq.hs:46:10: error:
    • Could not deduce (NFData CT.Options)
        arising from a use of ‘Control.DeepSeq.$dmrnf’
      from the context: NFData a
        bound by the instance declaration at src/Idris/DeepSeq.hs:46:10-43
    • In the expression: Control.DeepSeq.$dmrnf @Docstring a
      In an equation for ‘rnf’: rnf = Control.DeepSeq.$dmrnf @Docstring a
      In the instance declaration for ‘NFData (Docstring a)’
   |
46 | instance NFData a => NFData (D.Docstring a)
   |          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

src/Idris/DeepSeq.hs:59:10: error:
    • Could not deduce (NFData CT.ListType)
        arising from a use of ‘Control.DeepSeq.$dmrnf’
      from the context: NFData a
        bound by the instance declaration at src/Idris/DeepSeq.hs:59:10-39
    • In the expression: Control.DeepSeq.$dmrnf @Block a
      In an equation for ‘rnf’: rnf = Control.DeepSeq.$dmrnf @Block a
      In the instance declaration for ‘NFData (Block a)’
   |
59 | instance NFData a => NFData (D.Block a)
   |          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
