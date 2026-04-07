
```
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Lect16 where

  -- ----------------------------------------------------------------------
  -- library code 

  -- natural numbers
  data Nat : Set where
    Z : Nat
    1+ : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}

  _+_ : Nat → Nat → Nat
  Z + m = m
  (1+ n) + m = 1+ (n + m)

  infixr 10 _+_

  data Either (A B : Set) : Set where
    Inl : (x : A) → Either A B
    Inr : (y : B) → Either A B

  -- pairs
  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      first : A
      second : B
  open _×_ public
  infixr 10 _×_

  record Unit : Set where
    constructor <>

  data Void : Set where

  abort : ∀ {C : Set} → Void → C
  abort ()

  -- existential quantifier
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field   
      first : A
      second : B first
  open Σ public
  infixr 10 _,_

  syntax Σ A (\ x  -> B) = Σ[ x ∈ A ] B

  -- lists
  data List (A : Set) : Set where
    [] : List A
    _::_ : (x : A) (xs : List A) → List A

  infixr 99 _::_ 

  data Bool : Set where
    True : Bool
    False : Bool

  {-# BUILTIN BOOL  Bool  #-}
  {-# BUILTIN TRUE  True  #-}
  {-# BUILTIN FALSE False #-}

  postulate {- Agda Primitive -}
    Char : Set

  {-# BUILTIN CHAR Char #-}

  primitive
    primCharToNat : Char → Nat
    primCharEquality : Char → Char → Bool

  data Equals (A : Set) : (a : A) → A → Set where
    Refl : (a : A) → Equals A a a

  sym : {A : Set} (n m : A) → Equals A n m → Equals A m n 
  sym n n (Refl n) = Refl n
  
  trans : {A : Set} (x y z : A) → Equals A x y → Equals A y z → Equals A x z 
  trans x x p (Refl x) eq2 = eq2

  cong : {A B : Set} (f : A → B) (x y : A) → Equals A x y → Equals B (f x) (f y)
  cong f x x (Refl x) = Refl (f x)

  {-# BUILTIN EQUALITY Equals #-}

  primitive
    primEraseEquality : ∀ {A : Set} {x y : A} → Equals _ x y → Equals _ x y

  equalChar : (x y : Char) → Either (Equals Char x y) (Equals Char x y → Void)
  equalChar x y with primCharEquality x y
  ... | True = Inl (primEraseEquality equalChar-true) where
    postulate equalChar-true : _
  ... | False = Inr equalChar-false where
    postulate equalChar-false : _

  ¬ : Set → Set
  ¬ A = (A → Void)

  Decision : Set → Set
  Decision A = Either A (¬ A)

  data Maybe (A : Set) : Set where
    Some : A → Maybe A
    None : Maybe A

  append : {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys
```

# Recursion Permission and Simple Exmaple

```
  data _<_ : Nat → Nat → Set where
    Lt0 : (n : Nat) → 0 < (1+ n)
    LtS : (n m : Nat) → n < m → 1+ n < 1+ m

  _≤_ : Nat → Nat → Set
  x ≤ y = x < 1+ y

  data RecursionPermission (n : Nat) : Set where
    RP : ((m : Nat) → m < n → RecursionPermission m) → RecursionPermission n

  split-<-1+ : (m n : Nat) → m < (1+ n) → Either (Equals _ m n) (m < n)
  split-<-1+ 0 Z (Lt0 _) = Inl (Refl _)
  split-<-1+ 0 (1+ n) (Lt0 _) = Inr (Lt0 _)
  split-<-1+ (1+ m) (1+ n) (LtS _ _ p) with split-<-1+ m n p
  ...                                | Inl eq = Inl (cong 1+ _ _ eq)
  ...                                | Inr lt = Inr (LtS _ _ lt)

  well-founded : (n : Nat) → RecursionPermission n
  well-founded Z = RP \ _ ()
  well-founded (1+ n) with well-founded n
  ... | RP IH = RP help where
    help : (m : Nat) → m < (1+ n) → RecursionPermission m
    help m lt with split-<-1+ m n lt
    ... | Inl (Refl _) = (RP IH)
    ... | Inr lt = IH m lt

  postulate
    filter-less : Nat → List Nat → List Nat
    filter-greater : Nat → List Nat → List Nat
    
  {-
  quicksort : List Nat → List Nat
  quicksort [] = []
  quicksort (x :: xs) = append (quicksort (filter-less x xs)) (x :: quicksort (filter-greater x xs))
  -}
  
  length : {A : Set} → List A → Nat
  length [] = 0
  length (x :: xs) = 1+ (length xs)

  quicksort' : (l : List Nat) → RecursionPermission (length l) → List Nat
  quicksort' [] (RP smaller) = []
  quicksort' (x :: xs) (RP smaller) =
    append (quicksort' (filter-less x xs) (smaller _ {!!}))
           (x :: quicksort' (filter-greater x xs) (smaller _ {!!}))

  quicksort : List Nat → List Nat
  quicksort l = quicksort' l (well-founded _)

```

See Lect17-starter.lagda for the regular expression material that we talked about after this. 
