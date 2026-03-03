

```
module Lect12-starter where

  -- ----------------------------------------------------------------------
  -- library code 

  -- natural numbers
  data Nat : Set where
    Z : Nat
    1+ : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}

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
    _::_ : A → List A → List A

  infixr 99 _::_ 

  mutual
    Even : Nat → Set
    Even Z = Unit
    Even (1+ n) = Odd n
  
    Odd : Nat → Set
    Odd Z = Void
    Odd (1+ n) = Even n

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
    primToUpper : Char → Char

  data Maybe (A : Set) : Set where
    Some : A → Maybe A
    None : Maybe A

  double : Nat → Nat
  double Z = Z
  double (1+ n) = 1+ (1+ (double n))

  _+_ : Nat → Nat → Nat
  _+_ Z m = m
  _+_ (1+ n) m = 1+ (_+_ n m)

  parity : (n : Nat) -> Either (Even n) (Odd n)
  parity Z = Inl <> 
  parity (1+ n) with (parity n)
  ... | Inl nIsEven = Inr nIsEven
  ... | Inr nIsOdd = Inl nIsOdd

  data Equals (A : Set) : (a : A) → A → Set where
    Refl : (a : A) → Equals A a a

  sym : {A : Set} (n m : A) → Equals A n m → Equals A m n 
  sym n n (Refl n) = Refl n
  
  trans : {A : Set} (x y z : A) → Equals A x y → Equals A y z → Equals A x z 
  trans x x p (Refl x) eq2 = eq2

  cong : {A B : Set} (f : A → B) (x y : A) → Equals A x y → Equals B (f x) (f y)
  cong f x x (Refl x) = Refl (f x)

  1+-Z-disjoint : (n : Nat) → Equals Nat 0 (1+ n) → Void
  1+-Z-disjoint n ()

  Z-1+-disjoint : (n : Nat) → Equals Nat (1+ n) 0 → Void
  Z-1+-disjoint n ()

  1+-injective : (n m : Nat) → Equals Nat (1+ n) (1+ m) → Equals Nat n m
  1+-injective n n (Refl (1+ n)) = Refl n 

  1+-congruence : (n m : Nat) → Equals Nat n m → Equals Nat (1+ n) (1+ m)
  1+-congruence n n (Refl n) = (Refl (1+ n))

  add-k-to-equals : (k n m :  Nat) → Equals Nat n m → Equals Nat (k + n) (k + m)
  add-k-to-equals k n n (Refl n) = Refl (k + n)


```

# Lists of length n as a subset type

```
  module Subset where
    length : List Char → Nat
    length [] = 0
    length (x :: xs) = 1+ (length xs)
  
```

# Lists of length n as an inductive family

```
  module IF1 where
```

# Using underscores to avoid writing inferable arguments

```
  module IF2 where
```


# Using implicit arguments

```
  module IF3 where
```

# Polymorphic lists 

```
  module IF4 where
    data ListOfLength (A : Set) : Nat → Set where
```

# Excercises

## Uppercase

Write a functon uppercase-all that makes every character in the input list uppercase.  Use primToUpper : Char → Char.  

```
    uppercase-all : {n : Nat} → ListOfLength Char n → ListOfLength Char n
    uppercase-all = {!!}

{-
    example : Equals _ (uppercase-all (Cons 'a' (Cons 'b' Empty))) (Cons 'A' (Cons 'B' Empty))
    example = Refl _
-}
```

## Decreasing/Increasing 

Redo the decreasing function from Homework 3 for today's definition of ListOfLength.

```
    decreasing : (n : Nat) → ListOfLength Nat n
    decreasing = {!!}
```

Write a function increasing that produces the list in increasing order:

```
    increasing : (n : Nat) → ListOfLength Nat n
    increasing n = {!!}
```


## Zip/unzip

Write a function zip that makes a pair of lists into a list of pairs, so
that [x1,x2,x3,...] and [y1,y2,y3,...] gets made into
[(x1,y1),(x2,y2),(x3,y3),...].  Hint: this type makes some corner case
inputs impossible.

```
    zip : {A B : Set} {n : Nat} → (ListOfLength A n) → (ListOfLength B n) → ListOfLength (A × B) n
    zip = {!!}
```

Write a converse function unzip that makes a list of pairs into a
pair of lists.

```
    unzip : {A B : Set} {n : Nat} → ListOfLength (A × B) n → (ListOfLength A n) × (ListOfLength B n)
    unzip = {!!}
```

Prove that these two functions are inverse to each other:

```
    zip-unzip1 : {A B : Set} {n : Nat} (xs : ListOfLength A n) (ys : ListOfLength B n)
              → Equals _ (first (unzip (zip xs ys))) xs 
    zip-unzip1 = {!!}

    zip-unzip2 : {A B : Set} {n : Nat} (xs : ListOfLength A n) (ys : ListOfLength B n)
              → Equals _ (second (unzip (zip xs ys))) ys
    zip-unzip2 = {!!}

    unzip-zip : {A B : Set} {n : Nat} (xs : ListOfLength (A × B) n) 
              → Equals _ (zip (first (unzip xs)) (second (unzip xs))) xs
    unzip-zip = {!!}
```
