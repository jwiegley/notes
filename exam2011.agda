--    Assessed exercises for course L108.  
--    Michaelmas 2011.
--    Student name: (write name here)  
--    Assessor: Sam Staton (sam.staton@cl.cam.ac.uk)

--    THERE ARE 25 MARKS IN TOTAL.
--    There are 22 goals, one of which is optional.

--    Emacs shortcuts: 
--    Save : Ctrl-x-s        Load : Ctrl-c-l
--    Case split : Ctrl-c-c  

--    Please change file name to exam-crsid, 
--    replacing crsid with your crsid
--    e.g. exam-ss368. 
--    You will also need to change the following line. 
module exam2011 where

------------------------------------------------------
-- Section 1 : Simple exercises 
------------------------------------------------------

  -- Definition of binary products
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field fst : A
          snd : B
  open _×_  -- the symbol × is obtained by \x

  -- Definition of one-element type
  record One : Set where
    constructor *
  open One

  -- First, an illustration: 
  -- Suppose the question says 
  -- illustration : {A B : Set} → A × B → B × A
  -- illustration = ? 
  -- Then you could answer as follows.
  illustration : {A B : Set} → A × B → B × A
  illustration p = snd p , fst p
  -- Alternatively, you could put 
  illustration' : {A B : Set} → A × B → B × A
  illustration' = \ p -> snd p , fst p
  -- (Get a backslash by pressing \ twice.)
  -- Or if you think unicode looks nicer:
  illustration'' : {A B : Set} → A × B → B × A
  illustration'' = λ p → snd p , fst p
  -- (Get λ by \lambda and → by \-> or \to.)
  

  -- Now here are 14 simple exercises: test1 -- test14.
  -- EACH IS WORTH ONE MARK. 
  test1 : {A : Set} → A → A × A
  test1 = {!!}

  test2 : {A B C : Set} → A × (B × C) → (A × B) × C
  test2 = {!!}

  test3 : {A B C D : Set} → (A × B) × (C × D) → (A × C) × (B × D)
  test3 = {!!}

  test4 : {A : Set} → One
  test4 = {!!}

  test5 : {A : Set} → A → One × A
  test5 = {!!}

  test6 : {A B C : Set} → (A → B → C) → (A × B → C)
  test6 = {!!} 
  
  test7 : {A B C : Set} → (A × B → C) → (A → B → C)
  test7 = {!!} 

  test8 : {A B C : Set} → (A → B) → (A → C) → (A → (B × C))
  test8 = {!!}

  test9 : {A B C : Set} → (A → (B × C)) → (A → B) × (A → C)
  test9 = {!!} 

  test10 : {A B C : Set} → ((A → B) × A) → B
  test10 = {!!}

  test11 : {A B C : Set} → B → (A → (B × A))
  test11 = {!!}

  test12 : {A B C : Set} → A × (B → C) → (B → (A × C))
  test12 = {!!} 

  test13 : {A B : Set} → ((A → A) → B) → B
  test13 = {!!}

  test14 : {A B C D : Set} → ((A × (B × C) → (A × B) × C) → D) → D
  test14 = {!!}

------------------------------------------------------
-- Section 2 : Negation and constructivism. 
------------------------------------------------------

  -- Definition of the empty type. It has no inhabitants.
  data ∅ : Set where    -- get ∅ by typing \emptyset
    
  -- The empty set is initial which is proved by an 
  -- "absurd pattern"
  absurd : {A : Set} → ∅ → A
  absurd ()
 
  -- Definition of double-negation. 
  -- NB We think of ∅ as meaning FALSE
  ¬¬ : Set → Set       -- get ¬ by typing \neg
  ¬¬ A = (A → ∅) → ∅

  -- A simple exercise
  -- THIS IS FOR ONE MARK.
  test15 : {A : Set} → A → ¬¬ A
  test15 = {!!}

  -- A more difficult exercise. 
  -- Recall that Peirce's law is not provable.
  -- In this exercise you prove its double negation.
  -- THIS IS FOR ONE MARK.
  peirce : {A B : Set} → ¬¬ (((A → B) → A) → A)
  peirce = {!!}

------------------------------------------------------
-- Section 3 : Formalization of type theory and substitution
------------------------------------------------------

  -- A datatype inhabited by product types
  infixl 6 _∧_
  data Ty : Set where
    α : Ty                  -- get α by typing \alpha
    β : Ty
    True : Ty
    _∧_ : Ty → Ty → Ty    -- get ∧ by typing \and

  -- Lists
  infixr 5 _::_ 
  data List (A : Set) : Set where
    []  : List A
    _::_ : A → List A → List A

  -- A shorthand for singleton lists
  [_] : {A : Set} → A → List A
  [ x ] = x :: []

  -- A context is a list of types
  Ctx : Set 
  Ctx = List Ty 
  
  -- A datatype of members of the context.
  -- The idea is that A ∈ Γ is a set containing
  -- all the variables of type A in Γ. 
  -- (Get ∈ by \in and Γ by \Gamma.)
  data _∈_ : (A : Ty) (Γ : Ctx) → Set where
    Hd : {Γ : Ctx} {A : Ty} → A ∈ (A :: Γ)
    Tl : {Γ : Ctx} {A B : Ty} → A ∈ Γ → A ∈ (B :: Γ)

  -- The next datatype is designed so that 
  -- the inhabitants of Γ ⊢ A are exactly the terms t
  -- for which Γ ⊢ t : A.
  -- (Get ⊢ by \|- , π by \pi and ₁ by \_1  )
  infix 4 _⊢_ 
  data _⊢_ (Γ : Ctx) : Ty → Set where
    var : {A : Ty} → A ∈ Γ → Γ ⊢ A
    π₁ : {A B : Ty} → Γ ⊢ A ∧ B → Γ ⊢ A
    π₂ : {A B : Ty} → Γ ⊢ A ∧ B → Γ ⊢ B
    _,_ : {A B : Ty} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
    * : Γ ⊢ True

  demo1 : α :: β :: [] ⊢ β ∧ α
  demo1 = var (Tl Hd) , var Hd

  demo2 : [ α ∧ α ] ⊢ α 
  demo2 = π₂ (var Hd)

  demo3 : [ α ∧ α ] ⊢ α 
  demo3 = π₂ (π₁ (var Hd , *))

  -- Define substitution on well-typed terms.
  -- Hint : do a case split on the first argument (t)
  -- THIS IS FOR TWO MARKS.
  subst : {A B : Ty} {Γ : Ctx} → A :: Γ ⊢ B → Γ ⊢ A → Γ ⊢ B
  subst t u = {!!}

  -- This is a datatype whose inhabitants are 
  -- equality proofs for the type theory
  -- (Get ≡ by \==)
  infix 4 _⊢_≡_
  data _⊢_≡_ (Γ : Ctx) : {A : Ty} → Γ ⊢ A → Γ ⊢ A → Set where
    refl : {A : Ty} {t : Γ ⊢ A} → Γ ⊢ t ≡ t
    symm : {A : Ty} {t u : Γ ⊢ A} → Γ ⊢ t ≡ u → Γ ⊢ u ≡ t
    trans : {A : Ty} {t v : Γ ⊢ A} → (u : Γ ⊢ A) → Γ ⊢ t ≡ u → Γ ⊢ u ≡ v → Γ ⊢ t ≡ v
    cong, : {A B : Ty} {t t' : Γ ⊢ A} {u u' : Γ ⊢ B} → Γ ⊢ t ≡ t' → Γ ⊢ u ≡ u' → Γ ⊢ (t , u) ≡ (t' , u')
    congπ₁ : {A B : Ty} {t t' : Γ ⊢ A ∧ B} → Γ ⊢ t ≡ t' → Γ ⊢ (π₁ t) ≡ (π₁ t') 
    congπ₂ : {A B : Ty} {t t' : Γ ⊢ A ∧ B} → Γ ⊢ t ≡ t' → Γ ⊢ π₂ t ≡ π₂ t' 
    βπ₁ : {A B : Ty} {t : Γ ⊢ A} {u : Γ ⊢ B} → Γ ⊢ π₁ (t , u) ≡ t
    βπ₂ : {A B : Ty} {t : Γ ⊢ A} {u : Γ ⊢ B} → Γ ⊢ π₂ (t , u) ≡ u
    η* : (t :  Γ ⊢ True) → Γ ⊢ t ≡ *
    η, : {A B : Ty} {t : Γ ⊢ A ∧ B} → Γ ⊢ t ≡ (π₁ t , π₂ t)

  -- An illustration of equality judgements.
  demo4 : [ α ∧ α ] ⊢ demo2 ≡ demo3
  demo4 = congπ₂ (symm (βπ₁))

  -- Note, if you were writing rules, you would write demo4 like this:
  -- 
  --     --------------------------------------- βπ₁
  --     Γ ⊢ π₁ (var Hd , *) ≡ var Hd : α ∧ α  
  --     --------------------------------------- symm
  --     Γ ⊢ var Hd ≡ π₁ (var Hd , *) : α ∧ α 
  --     ------------------------------------------ congπ₂
  --     Γ ⊢ π₂ (var Hd) ≡ π₂ (π₁ (var Hd , *)) : α 

  -- Now you try, FOR ONE MARK:
  test16 : [ True ] ⊢ π₁ (* , var Hd) ≡ var Hd
  test16 = {!!}

  -- Two lemmas for showing that substitution is invariant under equality.
  -- You need to think about which parameter to do the case split on. 
  -- There is a total of THREE MARKS for the two lemmas.

  lemma1 : {Γ : Ctx} {A B : Ty} → (t t' : Γ ⊢ A) → (u : A :: Γ ⊢ B) → 
          Γ ⊢ t ≡ t' → Γ ⊢ (subst u t) ≡ (subst u t')
  lemma1 = {!!}

  lemma2 : {Γ : Ctx} (A B : Ty) → (t : Γ ⊢ A) → (u u' : A :: Γ ⊢ B) → 
          A :: Γ ⊢ u ≡ u' → Γ ⊢ (subst u t) ≡ (subst u' t)
  lemma2 = {!!}

  -- Bring the two lemmas together with this theorem.
  -- It should only take one line.
  -- The theorem is for ONE MARK.

  theorem : (Γ : Ctx) (A B : Ty) → (t t' : Γ ⊢ A) → (u u' : A :: Γ ⊢ B) → 
          Γ ⊢ t ≡ t' → A :: Γ ⊢ u ≡ u' → Γ ⊢ (subst u t) ≡ (subst u' t')
  theorem = {!!}

------------------------------------------------------
-- Section 4 : Interpretation of type theory.
-- You will now interpret the type theory in the Agda types.
------------------------------------------------------

  -- Agda type of natural numbers. 
  data ℕ : Set where  -- get ℕ by \bn
    Zero : ℕ
    Succ : ℕ → ℕ 

  -- Interpretation of types as sets
  -- I chose to interpret the base types as ℕ.
  [[_]]T : Ty → Set
  [[ α ]]T = ℕ 
  [[ β ]]T = ℕ 
  [[ True ]]T = One 
  [[ A ∧ B ]]T = [[ A ]]T × [[ B ]]T
 
  -- Interpretation of contexts as sets 
  [[_]]Γ : Ctx → Set
  [[ Γ ]]Γ = {A : Ty} → (A ∈ Γ) → [[ A ]]T

  -- A handy function
  weaken : {Γ : Ctx} {A : Ty} → [[ A :: Γ ]]Γ → [[ Γ ]]Γ
  weaken v n = v (Tl n)

  -- Interpretation of terms.
  -- Do this for TWO MARKS.
  [[_]]t : {Γ : Ctx} {A : Ty} → Γ ⊢ A → [[ Γ ]]Γ → [[ A ]]T
  [[ t ]]t v = {!!}

------------------------------------------------------
-- Section 5 : Soundness of the interpretation
-- THIS SECTION IS OPTIONAL and there are no marks for it.
------------------------------------------------------
 
  -- Equality of elements of a set
  data _==_ {A : Set} (a : A) : A → Set where
    refl : a == a

  -- Equality of functions ("extensional")
  _===_ : {A B : Set} → (A → B) → (A → B) → Set
  _===_ {A} {B} f g = (a : A) → f a == g a

  -- Try proving this soundness theorem if you like.
  soundness : (Γ : Ctx) (A : Ty) → (t u : Γ ⊢ A) → Γ ⊢ t ≡ u → [[ t ]]t === [[ u ]]t
  soundness = {!!}

