Require Import LinearScan.Lib.
Require Import LinearScan.IntMap.
Require Import LinearScan.UsePos.
Require Import LinearScan.Interval.
Require Import LinearScan.Blocks.
Require Import LinearScan.State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Resolve.

Variable maxReg : nat.          (* max number of registers *)
Definition PhysReg : predArgType := 'I_maxReg.

Variables blockType1 blockType2 opType1 opType2 accType : Set.

Variable binfo : BlockInfo blockType1 blockType2 opType1 opType2.
Variable oinfo : OpInfo maxReg accType opType1 opType2.

Record LoopState := {
  activeBlocks     : IntSet;
  visitedBlocks    : IntSet;
  loopHeaderBlocks : seq BlockId; (* loop index -> block id *)
  loopEndBlocks    : seq BlockId;
  forwardBranches  : IntMap (seq BlockId); (* block id -> block ids *)
  backwardBranches : IntMap (seq BlockId); (* block id -> block ids *)
  loopParents      : IntMap (seq nat)      (* block id -> loop indices *)
}.

Definition modifyActiveBlocks (f : IntSet -> IntSet) (st : LoopState) :
  LoopState :=
  {| activeBlocks     := f (activeBlocks st)
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopParents      := loopParents st |}.

Definition modifyVisitedBlocks (f : IntSet -> IntSet) (st : LoopState) :
  LoopState :=
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := f (visitedBlocks st)
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopParents      := loopParents st |}.

Definition modifyLoopHeaderBlocks (f : seq BlockId -> seq BlockId)
  (st : LoopState) : LoopState :=
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := f (loopHeaderBlocks st)
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopParents      := loopParents st |}.

Definition modifyLoopEndBlocks (f : seq BlockId -> seq BlockId)
  (st : LoopState) : LoopState :=
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := f (loopEndBlocks st)
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := backwardBranches st
   ; loopParents      := loopParents st |}.

Definition modifyForwardBranches
  (f : IntMap (seq BlockId) -> IntMap (seq BlockId)) (st : LoopState) :
  LoopState :=
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := f (forwardBranches st)
   ; backwardBranches := backwardBranches st
   ; loopParents      := loopParents st |}.

Definition modifyBackwardBranches
  (f : IntMap (seq BlockId) -> IntMap (seq BlockId)) (st : LoopState) :
  LoopState :=
  {| activeBlocks     := activeBlocks st
   ; visitedBlocks    := visitedBlocks st
   ; loopHeaderBlocks := loopHeaderBlocks st
   ; loopEndBlocks    := loopEndBlocks st
   ; forwardBranches  := forwardBranches st
   ; backwardBranches := f (backwardBranches st)
   ; loopParents      := loopParents st |}.

Definition remainingBlocks (bs : seq blockType1) (st : LoopState) : nat :=
  size bs - IntSet_size (visitedBlocks st).

Program Fixpoint findLoopEnds (b : blockType1) (bs : seq blockType1)
  (st : LoopState) {measure (remainingBlocks bs st)} : LoopState :=
  let bid := blockId binfo b in
  let st1 := modifyVisitedBlocks (IntSet_insert bid) st in
  let st2 := modifyActiveBlocks (IntSet_insert bid) st1 in
  let st3 :=
    (flip foldl st2 $ fun st3 sux =>
      if IntSet_member sux (activeBlocks st3)
      then
        modifyLoopHeaderBlocks (fun xs => sux :: xs) $
        modifyLoopEndBlocks (fun xs => bid :: xs) $
        modifyForwardBranches (fun xs => bid :: xs) $
        modifyLoopEndBlocks (fun xs => bid :: xs) $
      else st3)
    (blockSuccessors binfo b) in
  modifyActiveBlocks (IntSet_delete bid) st3.

End Resolve.