module Bug where

{-@ type Nat = {v:Int|0 <= v} @-}
type Nat = Int

{-@ type Height = Nat @-}
type Height = Nat

{-@ data HashOfBlock = NonExistentBlock | HashOfBlock Block @-}

data HashOfBlock = NonExistentBlock | HashOfBlock Block

{-@ hash_block :: b:Block -> {v:HashOfBlock|b_height b == hbHeight v} @-}

hash_block :: Block -> HashOfBlock
hash_block x = HashOfBlock x

{-@
data Block = Block
  { b_height :: Height,
    b_parent :: {v:HashOfBlock|hbHeight v + 1 == b_height}
  }
@-}

data Block = Block
  { b_height :: Height,
    b_parent :: HashOfBlock
  }

{-@ measure hbHeight @-}

hbHeight :: HashOfBlock -> Height
hbHeight NonExistentBlock = 0
hbHeight (HashOfBlock (Block h _)) = h
