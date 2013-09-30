{-# OPTIONS_GHC -optc-D__STDC_LIMIT_MACROS #-}
{-# LINE 1 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
{-# LANGUAGE
{-# LINE 2 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
  DeriveDataTypeable,
  StandaloneDeriving,
  GeneralizedNewtypeDeriving
  #-}
-- | Define types which correspond cleanly with some simple types on the C/C++ side.
-- Encapsulate hsc macro weirdness here, supporting higher-level tricks elsewhere.
module LLVM.General.Internal.FFI.LLVMCTypes where


{-# LINE 11 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 12 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 13 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 14 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 15 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 16 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 17 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 18 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 19 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 20 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 21 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 22 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

{-# LINE 23 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

import Language.Haskell.TH.Quote

import Data.Data
import Data.Bits
import Foreign.C
import Foreign.Storable


{-# LINE 51 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

deriving instance Data CUInt

newtype LLVMBool = LLVMBool CUInt

newtype CPPOpcode = CPPOpcode CUInt
  deriving (Eq, Ord, Show, Typeable, Data)

newtype ICmpPredicate = ICmpPredicate CUInt
  deriving (Eq, Ord, Show, Typeable, Data)
iCmpPredEQ  :: ICmpPredicate
iCmpPredEQ  = ICmpPredicate 32
iCmpPredNE  :: ICmpPredicate
iCmpPredNE  = ICmpPredicate 33
iCmpPredUGT  :: ICmpPredicate
iCmpPredUGT  = ICmpPredicate 34
iCmpPredUGE  :: ICmpPredicate
iCmpPredUGE  = ICmpPredicate 35
iCmpPredULT  :: ICmpPredicate
iCmpPredULT  = ICmpPredicate 36
iCmpPredULE  :: ICmpPredicate
iCmpPredULE  = ICmpPredicate 37
iCmpPredSGT  :: ICmpPredicate
iCmpPredSGT  = ICmpPredicate 38
iCmpPredSGE  :: ICmpPredicate
iCmpPredSGE  = ICmpPredicate 39
iCmpPredSLT  :: ICmpPredicate
iCmpPredSLT  = ICmpPredicate 40
iCmpPredSLE  :: ICmpPredicate
iCmpPredSLE  = ICmpPredicate 41

{-# LINE 73 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype FCmpPredicate = FCmpPredicate CUInt
  deriving (Eq, Ord, Show, Typeable, Data)
fCmpPredFalse  :: FCmpPredicate
fCmpPredFalse  = FCmpPredicate 0
fCmpPredOEQ  :: FCmpPredicate
fCmpPredOEQ  = FCmpPredicate 1
fCmpPredOGT  :: FCmpPredicate
fCmpPredOGT  = FCmpPredicate 2
fCmpPredOGE  :: FCmpPredicate
fCmpPredOGE  = FCmpPredicate 3
fCmpPredOLT  :: FCmpPredicate
fCmpPredOLT  = FCmpPredicate 4
fCmpPredOLE  :: FCmpPredicate
fCmpPredOLE  = FCmpPredicate 5
fCmpPredONE  :: FCmpPredicate
fCmpPredONE  = FCmpPredicate 6
fCmpPredORD  :: FCmpPredicate
fCmpPredORD  = FCmpPredicate 7
fCmpPredUNO  :: FCmpPredicate
fCmpPredUNO  = FCmpPredicate 8
fCmpPredUEQ  :: FCmpPredicate
fCmpPredUEQ  = FCmpPredicate 9
fCmpPredUGT  :: FCmpPredicate
fCmpPredUGT  = FCmpPredicate 10
fCmpPredUGE  :: FCmpPredicate
fCmpPredUGE  = FCmpPredicate 11
fCmpPredULT  :: FCmpPredicate
fCmpPredULT  = FCmpPredicate 12
fCmpPredULE  :: FCmpPredicate
fCmpPredULE  = FCmpPredicate 13
fCmpPredUNE  :: FCmpPredicate
fCmpPredUNE  = FCmpPredicate 14
fcmpPredTrue  :: FCmpPredicate
fcmpPredTrue  = FCmpPredicate 15

{-# LINE 94 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype MDKindID = MDKindID CUInt
  deriving (Storable)

newtype MemoryOrdering = MemoryOrdering CUInt
  deriving (Eq, Typeable, Data)

{-# LINE 101 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
memoryOrderingNotAtomic :: MemoryOrdering
memoryOrderingNotAtomic = MemoryOrdering 0
memoryOrderingUnordered :: MemoryOrdering
memoryOrderingUnordered = MemoryOrdering 1
memoryOrderingMonotonic :: MemoryOrdering
memoryOrderingMonotonic = MemoryOrdering 2
memoryOrderingAcquire :: MemoryOrdering
memoryOrderingAcquire = MemoryOrdering 4
memoryOrderingRelease :: MemoryOrdering
memoryOrderingRelease = MemoryOrdering 5
memoryOrderingAcquireRelease :: MemoryOrdering
memoryOrderingAcquireRelease = MemoryOrdering 6
memoryOrderingSequentiallyConsistent :: MemoryOrdering
memoryOrderingSequentiallyConsistent = MemoryOrdering 7
memoryOrderingP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "NotAtomic" -> memoryOrderingNotAtomic
    "Unordered" -> memoryOrderingUnordered
    "Monotonic" -> memoryOrderingMonotonic
    "Acquire" -> memoryOrderingAcquire
    "Release" -> memoryOrderingRelease
    "AcquireRelease" -> memoryOrderingAcquireRelease
    "SequentiallyConsistent" -> memoryOrderingSequentiallyConsistent
    x -> error $ "bad quasiquoted FFI constant for memoryOrdering: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 102 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype Linkage = Linkage CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 106 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
linkageExternal :: Linkage
linkageExternal = Linkage 0
linkageAvailableExternally :: Linkage
linkageAvailableExternally = Linkage 1
linkageLinkOnceAny :: Linkage
linkageLinkOnceAny = Linkage 2
linkageLinkOnceODR :: Linkage
linkageLinkOnceODR = Linkage 3
linkageLinkOnceODRAutoHide :: Linkage
linkageLinkOnceODRAutoHide = Linkage 4
linkageWeakAny :: Linkage
linkageWeakAny = Linkage 5
linkageWeakODR :: Linkage
linkageWeakODR = Linkage 6
linkageAppending :: Linkage
linkageAppending = Linkage 7
linkageInternal :: Linkage
linkageInternal = Linkage 8
linkagePrivate :: Linkage
linkagePrivate = Linkage 9
linkageDLLImport :: Linkage
linkageDLLImport = Linkage 10
linkageDLLExport :: Linkage
linkageDLLExport = Linkage 11
linkageExternalWeak :: Linkage
linkageExternalWeak = Linkage 12
linkageGhost :: Linkage
linkageGhost = Linkage 13
linkageCommon :: Linkage
linkageCommon = Linkage 14
linkageLinkerPrivate :: Linkage
linkageLinkerPrivate = Linkage 15
linkageLinkerPrivateWeak :: Linkage
linkageLinkerPrivateWeak = Linkage 16
linkageP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "External" -> linkageExternal
    "AvailableExternally" -> linkageAvailableExternally
    "LinkOnceAny" -> linkageLinkOnceAny
    "LinkOnceODR" -> linkageLinkOnceODR
    "LinkOnceODRAutoHide" -> linkageLinkOnceODRAutoHide
    "WeakAny" -> linkageWeakAny
    "WeakODR" -> linkageWeakODR
    "Appending" -> linkageAppending
    "Internal" -> linkageInternal
    "Private" -> linkagePrivate
    "DLLImport" -> linkageDLLImport
    "DLLExport" -> linkageDLLExport
    "ExternalWeak" -> linkageExternalWeak
    "Ghost" -> linkageGhost
    "Common" -> linkageCommon
    "LinkerPrivate" -> linkageLinkerPrivate
    "LinkerPrivateWeak" -> linkageLinkerPrivateWeak
    x -> error $ "bad quasiquoted FFI constant for linkage: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 107 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype Visibility = Visibility CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 111 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
visibilityDefault :: Visibility
visibilityDefault = Visibility 0
visibilityHidden :: Visibility
visibilityHidden = Visibility 1
visibilityProtected :: Visibility
visibilityProtected = Visibility 2
visibilityP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "Default" -> visibilityDefault
    "Hidden" -> visibilityHidden
    "Protected" -> visibilityProtected
    x -> error $ "bad quasiquoted FFI constant for visibility: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 112 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype CallConv = CallConv CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 116 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
callConvC :: CallConv
callConvC = CallConv 0
callConvFast :: CallConv
callConvFast = CallConv 8
callConvCold :: CallConv
callConvCold = CallConv 9
callConvP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "C" -> callConvC
    "Fast" -> callConvFast
    "Cold" -> callConvCold
    x -> error $ "bad quasiquoted FFI constant for callConv: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 117 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype ValueSubclassId = ValueSubclassId CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 121 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
valueSubclassIdArgument :: ValueSubclassId
valueSubclassIdArgument = ValueSubclassId 0
valueSubclassIdBasicBlock :: ValueSubclassId
valueSubclassIdBasicBlock = ValueSubclassId 1
valueSubclassIdFunction :: ValueSubclassId
valueSubclassIdFunction = ValueSubclassId 2
valueSubclassIdGlobalAlias :: ValueSubclassId
valueSubclassIdGlobalAlias = ValueSubclassId 3
valueSubclassIdGlobalVariable :: ValueSubclassId
valueSubclassIdGlobalVariable = ValueSubclassId 4
valueSubclassIdUndefValue :: ValueSubclassId
valueSubclassIdUndefValue = ValueSubclassId 5
valueSubclassIdBlockAddress :: ValueSubclassId
valueSubclassIdBlockAddress = ValueSubclassId 6
valueSubclassIdConstantExpr :: ValueSubclassId
valueSubclassIdConstantExpr = ValueSubclassId 7
valueSubclassIdConstantAggregateZero :: ValueSubclassId
valueSubclassIdConstantAggregateZero = ValueSubclassId 8
valueSubclassIdConstantDataArray :: ValueSubclassId
valueSubclassIdConstantDataArray = ValueSubclassId 9
valueSubclassIdConstantDataVector :: ValueSubclassId
valueSubclassIdConstantDataVector = ValueSubclassId 10
valueSubclassIdConstantInt :: ValueSubclassId
valueSubclassIdConstantInt = ValueSubclassId 11
valueSubclassIdConstantFP :: ValueSubclassId
valueSubclassIdConstantFP = ValueSubclassId 12
valueSubclassIdConstantArray :: ValueSubclassId
valueSubclassIdConstantArray = ValueSubclassId 13
valueSubclassIdConstantStruct :: ValueSubclassId
valueSubclassIdConstantStruct = ValueSubclassId 14
valueSubclassIdConstantVector :: ValueSubclassId
valueSubclassIdConstantVector = ValueSubclassId 15
valueSubclassIdConstantPointerNull :: ValueSubclassId
valueSubclassIdConstantPointerNull = ValueSubclassId 16
valueSubclassIdMDNode :: ValueSubclassId
valueSubclassIdMDNode = ValueSubclassId 17
valueSubclassIdMDString :: ValueSubclassId
valueSubclassIdMDString = ValueSubclassId 18
valueSubclassIdInlineAsm :: ValueSubclassId
valueSubclassIdInlineAsm = ValueSubclassId 19
valueSubclassIdPseudoSourceValue :: ValueSubclassId
valueSubclassIdPseudoSourceValue = ValueSubclassId 20
valueSubclassIdFixedStackPseudoSourceValue :: ValueSubclassId
valueSubclassIdFixedStackPseudoSourceValue = ValueSubclassId 21
valueSubclassIdInstruction :: ValueSubclassId
valueSubclassIdInstruction = ValueSubclassId 22
valueSubclassIdP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "Argument" -> valueSubclassIdArgument
    "BasicBlock" -> valueSubclassIdBasicBlock
    "Function" -> valueSubclassIdFunction
    "GlobalAlias" -> valueSubclassIdGlobalAlias
    "GlobalVariable" -> valueSubclassIdGlobalVariable
    "UndefValue" -> valueSubclassIdUndefValue
    "BlockAddress" -> valueSubclassIdBlockAddress
    "ConstantExpr" -> valueSubclassIdConstantExpr
    "ConstantAggregateZero" -> valueSubclassIdConstantAggregateZero
    "ConstantDataArray" -> valueSubclassIdConstantDataArray
    "ConstantDataVector" -> valueSubclassIdConstantDataVector
    "ConstantInt" -> valueSubclassIdConstantInt
    "ConstantFP" -> valueSubclassIdConstantFP
    "ConstantArray" -> valueSubclassIdConstantArray
    "ConstantStruct" -> valueSubclassIdConstantStruct
    "ConstantVector" -> valueSubclassIdConstantVector
    "ConstantPointerNull" -> valueSubclassIdConstantPointerNull
    "MDNode" -> valueSubclassIdMDNode
    "MDString" -> valueSubclassIdMDString
    "InlineAsm" -> valueSubclassIdInlineAsm
    "PseudoSourceValue" -> valueSubclassIdPseudoSourceValue
    "FixedStackPseudoSourceValue" -> valueSubclassIdFixedStackPseudoSourceValue
    "Instruction" -> valueSubclassIdInstruction
    x -> error $ "bad quasiquoted FFI constant for valueSubclassId: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 122 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype DiagnosticKind = DiagnosticKind CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 126 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
diagnosticKindError :: DiagnosticKind
diagnosticKindError = DiagnosticKind 0
diagnosticKindWarning :: DiagnosticKind
diagnosticKindWarning = DiagnosticKind 1
diagnosticKindNote :: DiagnosticKind
diagnosticKindNote = DiagnosticKind 2
diagnosticKindP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "Error" -> diagnosticKindError
    "Warning" -> diagnosticKindWarning
    "Note" -> diagnosticKindNote
    x -> error $ "bad quasiquoted FFI constant for diagnosticKind: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 127 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype AsmDialect = AsmDialect CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 131 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
asmDialectATT :: AsmDialect
asmDialectATT = AsmDialect 0
asmDialectIntel :: AsmDialect
asmDialectIntel = AsmDialect 1
asmDialectP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "ATT" -> asmDialectATT
    "Intel" -> asmDialectIntel
    x -> error $ "bad quasiquoted FFI constant for asmDialect: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 132 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype RMWOperation = RMWOperation CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 136 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
rmwOperationXchg :: RMWOperation
rmwOperationXchg = RMWOperation 0
rmwOperationAdd :: RMWOperation
rmwOperationAdd = RMWOperation 1
rmwOperationSub :: RMWOperation
rmwOperationSub = RMWOperation 2
rmwOperationAnd :: RMWOperation
rmwOperationAnd = RMWOperation 3
rmwOperationNand :: RMWOperation
rmwOperationNand = RMWOperation 4
rmwOperationOr :: RMWOperation
rmwOperationOr = RMWOperation 5
rmwOperationXor :: RMWOperation
rmwOperationXor = RMWOperation 6
rmwOperationMax :: RMWOperation
rmwOperationMax = RMWOperation 7
rmwOperationMin :: RMWOperation
rmwOperationMin = RMWOperation 8
rmwOperationUMax :: RMWOperation
rmwOperationUMax = RMWOperation 9
rmwOperationUMin :: RMWOperation
rmwOperationUMin = RMWOperation 10
rmwOperationP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "Xchg" -> rmwOperationXchg
    "Add" -> rmwOperationAdd
    "Sub" -> rmwOperationSub
    "And" -> rmwOperationAnd
    "Nand" -> rmwOperationNand
    "Or" -> rmwOperationOr
    "Xor" -> rmwOperationXor
    "Max" -> rmwOperationMax
    "Min" -> rmwOperationMin
    "UMax" -> rmwOperationUMax
    "UMin" -> rmwOperationUMin
    x -> error $ "bad quasiquoted FFI constant for rmwOperation: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 137 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype RelocModel = RelocModel CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 141 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
relocModelDefault :: RelocModel
relocModelDefault = RelocModel 0
relocModelStatic :: RelocModel
relocModelStatic = RelocModel 1
relocModelPIC :: RelocModel
relocModelPIC = RelocModel 2
relocModelDynamicNoPic :: RelocModel
relocModelDynamicNoPic = RelocModel 3
relocModelP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "Default" -> relocModelDefault
    "Static" -> relocModelStatic
    "PIC" -> relocModelPIC
    "DynamicNoPic" -> relocModelDynamicNoPic
    x -> error $ "bad quasiquoted FFI constant for relocModel: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 142 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype CodeModel = CodeModel CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 146 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
codeModelDefault :: CodeModel
codeModelDefault = CodeModel 0
codeModelJITDefault :: CodeModel
codeModelJITDefault = CodeModel 1
codeModelSmall :: CodeModel
codeModelSmall = CodeModel 2
codeModelKernel :: CodeModel
codeModelKernel = CodeModel 3
codeModelMedium :: CodeModel
codeModelMedium = CodeModel 4
codeModelLarge :: CodeModel
codeModelLarge = CodeModel 5
codeModelP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "Default" -> codeModelDefault
    "JITDefault" -> codeModelJITDefault
    "Small" -> codeModelSmall
    "Kernel" -> codeModelKernel
    "Medium" -> codeModelMedium
    "Large" -> codeModelLarge
    x -> error $ "bad quasiquoted FFI constant for codeModel: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 147 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype CodeGenOptLevel = CodeGenOptLevel CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 151 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
codeGenOptLevelNone :: CodeGenOptLevel
codeGenOptLevelNone = CodeGenOptLevel 0
codeGenOptLevelLess :: CodeGenOptLevel
codeGenOptLevelLess = CodeGenOptLevel 1
codeGenOptLevelDefault :: CodeGenOptLevel
codeGenOptLevelDefault = CodeGenOptLevel 2
codeGenOptLevelAggressive :: CodeGenOptLevel
codeGenOptLevelAggressive = CodeGenOptLevel 3
codeGenOptLevelP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "None" -> codeGenOptLevelNone
    "Less" -> codeGenOptLevelLess
    "Default" -> codeGenOptLevelDefault
    "Aggressive" -> codeGenOptLevelAggressive
    x -> error $ "bad quasiquoted FFI constant for codeGenOptLevel: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 152 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype FloatABIType = FloatABIType CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 156 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
floatABIDefault :: FloatABIType
floatABIDefault = FloatABIType 0
floatABISoft :: FloatABIType
floatABISoft = FloatABIType 1
floatABIHard :: FloatABIType
floatABIHard = FloatABIType 2
floatABIP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "Default" -> floatABIDefault
    "Soft" -> floatABISoft
    "Hard" -> floatABIHard
    x -> error $ "bad quasiquoted FFI constant for floatABI: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 157 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype FPOpFusionMode = FPOpFusionMode CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 161 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
fpOpFusionModeFast :: FPOpFusionMode
fpOpFusionModeFast = FPOpFusionMode 0
fpOpFusionModeStandard :: FPOpFusionMode
fpOpFusionModeStandard = FPOpFusionMode 1
fpOpFusionModeStrict :: FPOpFusionMode
fpOpFusionModeStrict = FPOpFusionMode 2
fpOpFusionModeP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "Fast" -> fpOpFusionModeFast
    "Standard" -> fpOpFusionModeStandard
    "Strict" -> fpOpFusionModeStrict
    x -> error $ "bad quasiquoted FFI constant for fpOpFusionMode: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 162 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype TargetOptionFlag = TargetOptionFlag CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 166 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
targetOptionFlagPrintMachineCode :: TargetOptionFlag
targetOptionFlagPrintMachineCode = TargetOptionFlag 0
targetOptionFlagNoFramePointerElim :: TargetOptionFlag
targetOptionFlagNoFramePointerElim = TargetOptionFlag 1
targetOptionFlagNoFramePointerElimNonLeaf :: TargetOptionFlag
targetOptionFlagNoFramePointerElimNonLeaf = TargetOptionFlag 2
targetOptionFlagLessPreciseFPMADOption :: TargetOptionFlag
targetOptionFlagLessPreciseFPMADOption = TargetOptionFlag 3
targetOptionFlagUnsafeFPMath :: TargetOptionFlag
targetOptionFlagUnsafeFPMath = TargetOptionFlag 4
targetOptionFlagNoInfsFPMath :: TargetOptionFlag
targetOptionFlagNoInfsFPMath = TargetOptionFlag 5
targetOptionFlagNoNaNsFPMath :: TargetOptionFlag
targetOptionFlagNoNaNsFPMath = TargetOptionFlag 6
targetOptionFlagHonorSignDependentRoundingFPMathOption :: TargetOptionFlag
targetOptionFlagHonorSignDependentRoundingFPMathOption = TargetOptionFlag 7
targetOptionFlagUseSoftFloat :: TargetOptionFlag
targetOptionFlagUseSoftFloat = TargetOptionFlag 8
targetOptionFlagNoZerosInBSS :: TargetOptionFlag
targetOptionFlagNoZerosInBSS = TargetOptionFlag 9
targetOptionFlagJITEmitDebugInfo :: TargetOptionFlag
targetOptionFlagJITEmitDebugInfo = TargetOptionFlag 10
targetOptionFlagJITEmitDebugInfoToDisk :: TargetOptionFlag
targetOptionFlagJITEmitDebugInfoToDisk = TargetOptionFlag 11
targetOptionFlagGuaranteedTailCallOpt :: TargetOptionFlag
targetOptionFlagGuaranteedTailCallOpt = TargetOptionFlag 12
targetOptionFlagDisableTailCalls :: TargetOptionFlag
targetOptionFlagDisableTailCalls = TargetOptionFlag 13
targetOptionFlagRealignStack :: TargetOptionFlag
targetOptionFlagRealignStack = TargetOptionFlag 14
targetOptionFlagEnableFastISel :: TargetOptionFlag
targetOptionFlagEnableFastISel = TargetOptionFlag 15
targetOptionFlagPositionIndependentExecutable :: TargetOptionFlag
targetOptionFlagPositionIndependentExecutable = TargetOptionFlag 16
targetOptionFlagEnableSegmentedStacks :: TargetOptionFlag
targetOptionFlagEnableSegmentedStacks = TargetOptionFlag 17
targetOptionFlagUseInitArray :: TargetOptionFlag
targetOptionFlagUseInitArray = TargetOptionFlag 18
targetOptionFlagP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "PrintMachineCode" -> targetOptionFlagPrintMachineCode
    "NoFramePointerElim" -> targetOptionFlagNoFramePointerElim
    "NoFramePointerElimNonLeaf" -> targetOptionFlagNoFramePointerElimNonLeaf
    "LessPreciseFPMADOption" -> targetOptionFlagLessPreciseFPMADOption
    "UnsafeFPMath" -> targetOptionFlagUnsafeFPMath
    "NoInfsFPMath" -> targetOptionFlagNoInfsFPMath
    "NoNaNsFPMath" -> targetOptionFlagNoNaNsFPMath
    "HonorSignDependentRoundingFPMathOption" -> targetOptionFlagHonorSignDependentRoundingFPMathOption
    "UseSoftFloat" -> targetOptionFlagUseSoftFloat
    "NoZerosInBSS" -> targetOptionFlagNoZerosInBSS
    "JITEmitDebugInfo" -> targetOptionFlagJITEmitDebugInfo
    "JITEmitDebugInfoToDisk" -> targetOptionFlagJITEmitDebugInfoToDisk
    "GuaranteedTailCallOpt" -> targetOptionFlagGuaranteedTailCallOpt
    "DisableTailCalls" -> targetOptionFlagDisableTailCalls
    "RealignStack" -> targetOptionFlagRealignStack
    "EnableFastISel" -> targetOptionFlagEnableFastISel
    "PositionIndependentExecutable" -> targetOptionFlagPositionIndependentExecutable
    "EnableSegmentedStacks" -> targetOptionFlagEnableSegmentedStacks
    "UseInitArray" -> targetOptionFlagUseInitArray
    x -> error $ "bad quasiquoted FFI constant for targetOptionFlag: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 167 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype TypeKind = TypeKind CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 171 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
typeKindVoid :: TypeKind
typeKindVoid = TypeKind 0
typeKindHalf :: TypeKind
typeKindHalf = TypeKind 1
typeKindFloat :: TypeKind
typeKindFloat = TypeKind 2
typeKindDouble :: TypeKind
typeKindDouble = TypeKind 3
typeKindX86_FP80 :: TypeKind
typeKindX86_FP80 = TypeKind 4
typeKindFP128 :: TypeKind
typeKindFP128 = TypeKind 5
typeKindPPC_FP128 :: TypeKind
typeKindPPC_FP128 = TypeKind 6
typeKindLabel :: TypeKind
typeKindLabel = TypeKind 7
typeKindInteger :: TypeKind
typeKindInteger = TypeKind 8
typeKindFunction :: TypeKind
typeKindFunction = TypeKind 9
typeKindStruct :: TypeKind
typeKindStruct = TypeKind 10
typeKindArray :: TypeKind
typeKindArray = TypeKind 11
typeKindPointer :: TypeKind
typeKindPointer = TypeKind 12
typeKindVector :: TypeKind
typeKindVector = TypeKind 13
typeKindMetadata :: TypeKind
typeKindMetadata = TypeKind 14
typeKindX86_MMX :: TypeKind
typeKindX86_MMX = TypeKind 15
typeKindP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "Void" -> typeKindVoid
    "Half" -> typeKindHalf
    "Float" -> typeKindFloat
    "Double" -> typeKindDouble
    "X86_FP80" -> typeKindX86_FP80
    "FP128" -> typeKindFP128
    "PPC_FP128" -> typeKindPPC_FP128
    "Label" -> typeKindLabel
    "Integer" -> typeKindInteger
    "Function" -> typeKindFunction
    "Struct" -> typeKindStruct
    "Array" -> typeKindArray
    "Pointer" -> typeKindPointer
    "Vector" -> typeKindVector
    "Metadata" -> typeKindMetadata
    "X86_MMX" -> typeKindX86_MMX
    x -> error $ "bad quasiquoted FFI constant for typeKind: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 172 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype ParamAttr = ParamAttr CUInt
  deriving (Eq, Read, Show, Bits, Typeable, Data, Num)

{-# LINE 176 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
paramAttrZExt :: ParamAttr
paramAttrZExt = ParamAttr 1
paramAttrSExt :: ParamAttr
paramAttrSExt = ParamAttr 2
paramAttrInReg :: ParamAttr
paramAttrInReg = ParamAttr 8
paramAttrStructRet :: ParamAttr
paramAttrStructRet = ParamAttr 16
paramAttrNoAlias :: ParamAttr
paramAttrNoAlias = ParamAttr 64
paramAttrByVal :: ParamAttr
paramAttrByVal = ParamAttr 128
paramAttrNoCapture :: ParamAttr
paramAttrNoCapture = ParamAttr 2097152
paramAttrNest :: ParamAttr
paramAttrNest = ParamAttr 256
paramAttrP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "ZExt" -> paramAttrZExt
    "SExt" -> paramAttrSExt
    "InReg" -> paramAttrInReg
    "StructRet" -> paramAttrStructRet
    "NoAlias" -> paramAttrNoAlias
    "ByVal" -> paramAttrByVal
    "NoCapture" -> paramAttrNoCapture
    "Nest" -> paramAttrNest
    x -> error $ "bad quasiquoted FFI constant for paramAttr: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 177 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype FunctionAttr = FunctionAttr CUInt
  deriving (Eq, Read, Show, Bits, Typeable, Data, Num)

{-# LINE 181 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
functionAttrNoReturn :: FunctionAttr
functionAttrNoReturn = FunctionAttr 4
functionAttrNoUnwind :: FunctionAttr
functionAttrNoUnwind = FunctionAttr 32
functionAttrReadNone :: FunctionAttr
functionAttrReadNone = FunctionAttr 512
functionAttrReadOnly :: FunctionAttr
functionAttrReadOnly = FunctionAttr 1024
functionAttrNoInline :: FunctionAttr
functionAttrNoInline = FunctionAttr 2048
functionAttrAlwaysInline :: FunctionAttr
functionAttrAlwaysInline = FunctionAttr 4096
functionAttrOptimizeForSize :: FunctionAttr
functionAttrOptimizeForSize = FunctionAttr 8192
functionAttrStackProtect :: FunctionAttr
functionAttrStackProtect = FunctionAttr 16384
functionAttrStackProtectReq :: FunctionAttr
functionAttrStackProtectReq = FunctionAttr 32768
functionAttrAlignment :: FunctionAttr
functionAttrAlignment = FunctionAttr 2031616
functionAttrNoRedZone :: FunctionAttr
functionAttrNoRedZone = FunctionAttr 4194304
functionAttrNoImplicitFloat :: FunctionAttr
functionAttrNoImplicitFloat = FunctionAttr 8388608
functionAttrNaked :: FunctionAttr
functionAttrNaked = FunctionAttr 16777216
functionAttrInlineHint :: FunctionAttr
functionAttrInlineHint = FunctionAttr 33554432
functionAttrStackAlignment :: FunctionAttr
functionAttrStackAlignment = FunctionAttr 469762048
functionAttrReturnsTwice :: FunctionAttr
functionAttrReturnsTwice = FunctionAttr 536870912
functionAttrUWTable :: FunctionAttr
functionAttrUWTable = FunctionAttr 1073741824
functionAttrNonLazyBind :: FunctionAttr
functionAttrNonLazyBind = FunctionAttr 2147483648
functionAttrP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "NoReturn" -> functionAttrNoReturn
    "NoUnwind" -> functionAttrNoUnwind
    "ReadNone" -> functionAttrReadNone
    "ReadOnly" -> functionAttrReadOnly
    "NoInline" -> functionAttrNoInline
    "AlwaysInline" -> functionAttrAlwaysInline
    "OptimizeForSize" -> functionAttrOptimizeForSize
    "StackProtect" -> functionAttrStackProtect
    "StackProtectReq" -> functionAttrStackProtectReq
    "Alignment" -> functionAttrAlignment
    "NoRedZone" -> functionAttrNoRedZone
    "NoImplicitFloat" -> functionAttrNoImplicitFloat
    "Naked" -> functionAttrNaked
    "InlineHint" -> functionAttrInlineHint
    "StackAlignment" -> functionAttrStackAlignment
    "ReturnsTwice" -> functionAttrReturnsTwice
    "UWTable" -> functionAttrUWTable
    "NonLazyBind" -> functionAttrNonLazyBind
    x -> error $ "bad quasiquoted FFI constant for functionAttr: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 182 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}

newtype FloatSemantics = FloatSemantics CUInt
  deriving (Eq, Read, Show, Typeable, Data)

{-# LINE 186 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
floatSemanticsIEEEhalf :: FloatSemantics
floatSemanticsIEEEhalf = FloatSemantics 0
floatSemanticsIEEEsingle :: FloatSemantics
floatSemanticsIEEEsingle = FloatSemantics 1
floatSemanticsIEEEdouble :: FloatSemantics
floatSemanticsIEEEdouble = FloatSemantics 2
floatSemanticsIEEEquad :: FloatSemantics
floatSemanticsIEEEquad = FloatSemantics 3
floatSemanticsPPCDoubleDouble :: FloatSemantics
floatSemanticsPPCDoubleDouble = FloatSemantics 4
floatSemanticsx87DoubleExtended :: FloatSemantics
floatSemanticsx87DoubleExtended = FloatSemantics 5
floatSemanticsBogus :: FloatSemantics
floatSemanticsBogus = FloatSemantics 6
floatSemanticsP = QuasiQuoter {
  quoteExp = undefined,
  quotePat = \s -> dataToPatQ (const Nothing) $ case s of
    "IEEEhalf" -> floatSemanticsIEEEhalf
    "IEEEsingle" -> floatSemanticsIEEEsingle
    "IEEEdouble" -> floatSemanticsIEEEdouble
    "IEEEquad" -> floatSemanticsIEEEquad
    "PPCDoubleDouble" -> floatSemanticsPPCDoubleDouble
    "x87DoubleExtended" -> floatSemanticsx87DoubleExtended
    "Bogus" -> floatSemanticsBogus
    x -> error $ "bad quasiquoted FFI constant for floatSemantics: " ++ x,
  quoteType = undefined,
  quoteDec = undefined
 }

{-# LINE 187 "src/LLVM/General/Internal/FFI/LLVMCTypes.hsc" #-}
