-- | A data structure that preserves the exact syntax of a Nix file, as it
--   relates to the expressions parsed from within that file. This structure,
--   when rendered, must always reconstitute the exact input it was parsed
--   from.
--
--   This type is also a monoid, which can be used to "build up" synthesized
--   Nix files.
data NSyntaxF e r
  = NSynEmpty                   -- an empty source file
  | NSynGlue r r                -- glue two syntactic constructs together
  | NSynOrig Text r
    -- ^ Preserves exact original input. For example, 'NSynComment' only
    --   contains the text of the comment, not its placement or quantity of
    --   hash marks. This syntax is preserved by wrapping with 'NSynOrig'.
  | NSynComment Text            -- textual comment
  | NSynSpace Text              -- just whitespace
  | NSynSyntax Text             -- syntax without a corresponding expression
  | NSynExpr e                  -- an expression that was parsed here
  | NSynBracket r r r
    -- ^ When a constructed is "bracketed", it will have some kind of prolog,
    --   content, and epilog, such as: @{ inherit foo; }@. This could be
    --   rendered as:
    --
    -- @@
    --   NSynBracket
    --     (NSynGlue (NSynSyntax "{") (NSynSpace " "))
    --     (NSynBracket
    --       (NSynGlue (NSynSyntax "inherit") (NSynSpace " "))
    --       (NSynSyntax "foo")
    --       (NSynGlue (NSynSyntax ";")))
    --     (NSynGlue (NSynSpace " ") (NSynSyntax "{"))
    -- @@
    --
    --   Note that many equivalent representations are possible, but they must
    --   all render to the same source file.
