
```
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Lect14-starter where

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

  equalChar : (x y : Char) → Either (Equals Char x y) (Equals Char x y → Void)
  equalChar x y with primCharEquality x y
  ... | True = Inl equalChar-true where
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

  data _<_ : Nat → Nat → Set where
    Lt0 : (n : Nat) → 0 < (1+ n)
    LtS : (n m : Nat) → n < m → 1+ n < 1+ m

  data _≤_ : Nat → Nat → Set where
    Le0 : (n : Nat) → 0 ≤ n
    LeS : (n m : Nat) → n ≤ m → 1+ n ≤ 1+ m
```

```
  data RegExp : Set where
    Lit : Char → RegExp
    Wild : RegExp
    _·_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \cdot 
    _∨_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \vee

  infixr 2 _·_
  infixr 3 _∨_

  append : {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys

  Splitting : List Char → Set
  Splitting l = Σ[ p1 ∈ List Char ] Σ[ p2 ∈ List Char ] Equals _ (append p1 p2) l

  front : (l : List Char) → Splitting l → List Char
  front _ (p1 , _) = p1

  back : (l : List Char) → Splitting l → List Char
  back _ (_ , p2 , _) = p2

  addx-single : (x : Char) (xs : List Char) → Splitting xs → Splitting (x :: xs)
  addx-single x xs (p1 , p2 , appends) = x :: p1 , p2 , cong (λ H → x :: H) (append p1 p2) xs appends

  addx-many : (x : Char) (xs : List Char) → List (Splitting xs) → List (Splitting (x :: xs))
  addx-many x xs [] = []
  addx-many x xs (s :: ss) = addx-single x xs s :: addx-many x xs ss

  split : (l : List Char) → List (Splitting l)
  split [] = ([] , [] , Refl []) :: []
  split (x :: xs) = (([] , x :: xs , Refl (x :: xs))) :: addx-many x xs (split xs) 

  test-split = split ('a' :: 'b' :: 'c' :: [])

  mutual
    SplittingWorks : (s : List Char) → Splitting s → RegExp → RegExp → Set
    SplittingWorks s sp r1 r2 = (front s sp ∈L r1) × (back s sp ∈L r2)

    _∈L_ : List Char → RegExp → Set
    s ∈L (Lit c) = Equals _ s (c :: [])
    s ∈L Wild = Unit
    s ∈L (r1 ∨ r2) = Either (s ∈L r1) (s ∈L r2)
    s ∈L (r1 · r2) = Σ[ sp ∈ Splitting s ] SplittingWorks s sp r1 r2

  decide-EqualsList1 :( c : Char) (s : List Char) 
                     → Decision (Equals _ (c :: []) s)
  decide-EqualsList1 c [] = Inr (\ ())
  decide-EqualsList1 c (x :: []) with equalChar c x
  ... | Inl eq = Inl (cong (\ H → H :: []) _ _ eq)
  ... | Inr neq = Inr ((λ { (Refl _) → neq (Refl _) }))
  decide-EqualsList1 c (x :: x₁ :: s) = Inr (\ ())

  change-string : (s1 s2 : List Char) (r : RegExp) → Equals _ s1 s2 → s1 ∈L r → s2 ∈L r
  change-string _ _ _ (Refl _) inr = inr 

  match : (r : RegExp) (s : List Char) → Maybe (s ∈L r)
  match (Lit c) s with decide-EqualsList1 c s
  ... | Inl eq = Some (sym _ _ eq)
  ... | Inr neq = None
  match Wild s = Some <>
  match (r1 · r2) s = {!!}
  match (r1 ∨ r2) s with (match r1 s)
  ... | Some inr1 = Some (Inl inr1)
  ... | None with match r2 s
  ...           | Some inr2 = Some (Inr inr2)
  ...           | None = None

  example : RegExp
  example = Wild · ((Lit '.' · Lit 'c' · Lit 'o' · Lit 'm') ∨ (Lit '.' · Lit 'e' · Lit 'd' · Lit 'u'))

  test1 = match example ('w' :: 'e' :: 's' :: 'l' :: 'e' :: 'y' :: 'a' :: 'n' :: '.' :: 'e' :: 'd' :: 'u' :: [])

  test2 = match example ('.' :: 'e' :: 'd' :: 'u' :: '.' :: 'e' :: 'd' :: 'u' :: [])
```
