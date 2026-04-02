
```
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

module Lect17-starter where

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
```

# Regexp Definitions 

```
  data RegExp : Set where
    Lit : Char → RegExp
    _·_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \cdot 
    _∨_ : (r1 : RegExp) (r2 : RegExp) → RegExp -- type \vee
    _+ : RegExp → RegExp -- accepts ONE or more

  infix 1 _+
  infixr 2 _·_
  infixr 3 _∨_

  append : {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys

  -- see Homework 5
  postulate
    append-assoc : {A : Set} (xs ys zs : List A) → Equals _ (append (append xs ys) zs) (append xs (append ys zs))
    append-rh-[] : {A : Set} (xs : List A) → Equals _ xs (append xs []) 

  Splitting : List Char → Set
  Splitting l = Σ[ p1 ∈ List Char ] Σ[ p2 ∈ List Char ] Equals _ (append p1 p2) l

  front : (l : List Char) → Splitting l → List Char
  front _ (p1 , _) = p1

  back : (l : List Char) → Splitting l → List Char
  back _ (_ , p2 , _) = p2

  mutual
    SplittingWorks : (s : List Char) → Splitting s → RegExp → RegExp → Set
    SplittingWorks s sp r1 r2 = (front s sp ∈L r1) × (back s sp ∈L r2)
  
    data _∈L_ : List Char → RegExp → Set where
      InLit : (c : Char) → c :: [] ∈L (Lit c)
      In∨Left : (s : List Char) (r1 r2 : RegExp) → s ∈L r1 → s ∈L (r1 ∨ r2)
      In∨Right : (s : List Char) (r1 r2 : RegExp) → s ∈L r2 → s ∈L (r1 ∨ r2)
      In· : (s : List Char) (r1 r2 : RegExp) (sp : Splitting s) → SplittingWorks s sp r1 r2 → s ∈L (r1 · r2)
      In+Split : (s : List Char) (r : RegExp) (sp : Splitting s) → SplittingWorks s sp r (r +) → s ∈L (r +)
```


# Stack-based RegExp Matcher

```
  Stack : Set
  Stack = List RegExp

  mutual
    SplittingWorksStack : (s : List Char) (sp : Splitting s) (r : RegExp) (k : Stack) → Set
    SplittingWorksStack s sp r k = (front _ sp) ∈L r × (back _ sp) ∈S k

    data _∈S_ : List Char → Stack → Set where
      In[] : [] ∈S []
      In:: : (s : List Char) (sp : Splitting s) (r : RegExp) (k : Stack)
           → SplittingWorksStack s sp r k
           → s ∈S (r :: k)

  WorkingSplitting : List Char → RegExp → Stack → Set
  WorkingSplitting s r k = Σ[ sp ∈ Splitting s ] SplittingWorksStack s sp r k

  mutual
    match : (r : RegExp) (k : Stack) (s : List Char) → Maybe (WorkingSplitting s r k)
    match (r1 · r2) k s with match r1 (r2 :: k) s
    ...                    | None = None
    ...                    | Some ( (f1 , b' , Refl _) , f1inr1 , In:: _ (f2 , b , Refl _) _ _ (f2inr2 , bink)) =
                                    Some ((append f1 f2 , b , append-assoc f1 f2 b) ,
                                          In· _ _ _ (f1 , f2 , Refl _) (f1inr1 , f2inr2) ,
                                          bink)
    match r k s = {!r!}
```

# Exercises

* Add a regular expression WildChar that matches any single character,
  define its language, and define the matcher for it.

* Add a regular expression r1 ∧ r2 that matches any string that itself
  matches both r1 and r2, and define its language, and try to define the
  matcher for it.

* Change the type of the matcher to Decision (WorkingSplitting s r k)
  and prove completeness too.
