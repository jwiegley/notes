back_end ()
  -> llvm_backend (does initialization and setup work)
  -> generate_LLVM_output_file
     - allocates LLVM Module
     - top-level initiator of all the global-scope AST walks
       - pragmas
       - constants
       - types
       - routines (declarations only)
         -> dump_scope_routines
            -> dump_routine_decl
               - register LLVM function name and type
       - variables (without initializers)
       - variables (with initializers)
       - routines (definitions)