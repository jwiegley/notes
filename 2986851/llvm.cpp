/* Compilation of byte code to LLVM IR.
   Copyright (C) 2012 BoostPro Computing, Inc.

This file is not part of GNU Emacs. */

/* Created by John Wiegley <johnw@boostpro.com> */

#define GNULIB_defined_struct_option 1

extern "C" {
#include <config.h>
#include <setjmp.h>
#include "lisp.h"

#undef free
#undef malloc
#undef realloc

void	*malloc(size_t);
void	*realloc(void *, size_t);
void	 free(void *);
}

#include <llvm/LLVMContext.h>
#include <llvm/Module.h>
#include <llvm/PassManager.h>
#include <llvm/Function.h>
#include <llvm/CallingConv.h>
#include <llvm/DerivedTypes.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/Analysis/Passes.h>
#include <llvm/Target/TargetData.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Assembly/PrintModulePass.h>
#include <llvm/Support/IRBuilder.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/JIT.h>

using namespace llvm;

static Module *TheModule = NULL;
static LLVMContext *Context;
static IRBuilder<> *Builder;
static FunctionPassManager *TheFPM;
static ExecutionEngine *TheExecutionEngine;

extern "C" {
void *
llvm_compile_byte_code (Lisp_Object bytestr, Lisp_Object vector,
                        Lisp_Object maxdepth, Lisp_Object args_template,
                        ptrdiff_t nargs, Lisp_Object *args)
{
  if (! TheModule)
    {
      InitializeNativeTarget();
      Context = &getGlobalContext();
      TheModule = new Module("Emacs-LLVM-JIT", *Context);
      Builder = new IRBuilder<>(*Context);

      // Create the JIT.  This takes ownership of the module.
      TheExecutionEngine = EngineBuilder(TheModule).create();

      FunctionPassManager OurFPM(TheModule);

      // Set up the optimizer pipeline.  Start with registering info
      // about how the target lays out data structures.
      OurFPM.add(new TargetData(*TheExecutionEngine->getTargetData()));
      // Provide basic AliasAnalysis support for GVN.
      OurFPM.add(createBasicAliasAnalysisPass());
      // Do simple "peephole" optimizations and bit-twiddling optzns.
      OurFPM.add(createInstructionCombiningPass());
      // Reassociate expressions.
      OurFPM.add(createReassociatePass());
      // Eliminate Common SubExpressions.
      OurFPM.add(createGVNPass());
      // Simplify the control flow graph (deleting unreachable blocks, etc).
      OurFPM.add(createCFGSimplificationPass());

      OurFPM.doInitialization();

      // Set the global so the code gen can use this.
      TheFPM = &OurFPM;
    }

  Type ** LispTypes = (Type **)malloc(nargs * sizeof(Type *));
  LispTypes[0] = Type::getInt32Ty(*Context);
  LispTypes[1] = NULL;

  FunctionType *FT =
    FunctionType::get(/* Result=   */ Type::getInt32Ty(*Context),
                      /* Params=   */ ArrayRef<Type *>(LispTypes, nargs),
                      /* isVarArg= */ false);

  static char Name[32];
  sprintf(Name, "__emacs_%p", &bytestr);

  Function *F = Function::Create(FT, Function::ExternalLinkage, Name,
                                 TheModule);

#if 0
  // Validate the generated code, checking for consistency.
  verifyFunction(*F);
#endif

#if 0
  // Optimize the function.
  TheFPM->run(*F);
#endif

  // JIT the function, returning a function pointer.
  return 1 ? NULL : TheExecutionEngine->getPointerToFunction(F);
}
} // extern "C"
