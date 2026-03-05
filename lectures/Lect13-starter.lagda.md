In this class, we will get more practice with inductive families.  

```
module Lect13-starter where

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
    EvenRec : Nat → Set
    EvenRec Z = Unit
    EvenRec (1+ n) = Odd n
  
    Odd : Nat → Set
    Odd Z = Void
    Odd (1+ n) = EvenRec n

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

  parity : (n : Nat) -> Either (EvenRec n) (Odd n)
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

# Even as an inductive family

Here is yet another definition of Even n:
* 0 is even
* if n is even, then 2+n is even

Here is how we can represent this as an inductive family.

```
  module Explicit where
    data Even : Nat → Set where
      Even0 : Even 0
      Even2+ : (n : Nat) → Even n → Even (1+ (1+ n))
```

Notice that we simply don't say anything about 1, which means that 1 is
not even, because there is no datatype constructor whose type is Even(1+
0).

Prove that this definition holds iff the recursive definition that we
have used previously:

```
    torec : (n : Nat) → Even n → EvenRec n
    torec Z Even0 = <>
    torec (1+ n) (Even2+ n1 e) = torec n1 e

    fromrec : (n : Nat) → EvenRec n → Even n 
    fromrec Z <> = Even0
    fromrec (1+ (1+ n)) e = Even2+ n (fromrec n e)
```

# Implicit arguments

Agda can usually infer the number n in a program of type Even n, so we
can make n an implicit argument to Even2+.  Redo the above
correspondence with EvenRec for this definition 

```
  module Implicit where
    data Even : Nat → Set where
      Even0 : Even 0
      Even2+ : {n : Nat} → Even n → Even (1+ (1+ n)) -- {n : Nat} makes n an implicit argument 
 
    torec : {n : Nat} → Even n → EvenRec n
    torec Even0 = <>
    torec (Even2+ e) = torec e

    fromrec : (n : Nat) → EvenRec n → Even n 
    fromrec Z <> = Even0
    fromrec (1+ n) e = fromrec (1+ n) e
```

Note that n is an implicit argument in the former but not the latter.  Why?  
-- The latter needs to be case analyzed. 

# List of length

Returning to the ListOfLength type from last time, we will generalize
from ListOfLength n being a list of Characters of length n to a type
ListOfLength A n, which represents a list whose elements have type A and
which has length n.

```
  data ListOfLength (A : Set) : Nat → Set where
    Empty    : ListOfLength A 0
    Cons  : {n : Nat} → A → ListOfLength A n → ListOfLength A (1+ n)
```

When you put (A : Set) as a parameter to a datatype, it becomes an
implicit argument to each of the datatype's constructors.  So we can
just write Cons for every type.

```
  example1 : ListOfLength Nat 3
  example1 = Cons 1 (Cons 2 (Cons 3 Empty))

  example2 : ListOfLength Char 3
  example2 = Cons 'a' (Cons 'b' (Cons 'c' Empty))
```

Because A is an implicit argument to all of the functions, the code from
last time is unchanged.

```
  append : {n m : Nat} {A : Set} → ListOfLength A n → ListOfLength A m → ListOfLength A (n + m)
  append Empty ys = ys
  append (Cons x xs) ys = Cons x (append xs ys) 

  data Position : Nat → Set where
    Here : {n : Nat} → Position (1+ n)
    There : {n : Nat} → Position n → Position (1+ n)

  get : {n : Nat} {A : Set} → ListOfLength A n → Position n → A
  get (Cons x xs) (Here ) = x
  get (Cons x xs) (There i) = get xs i
```

## Uppercase

Write a functon uppercase-all that makes every character in the input list uppercase.  Use primToUpper : Char → Char.  

```
  uppercase-all : {n : Nat} → ListOfLength Char n → ListOfLength Char {!!}
  uppercase-all l = {!!}

  example : Equals _ (uppercase-all (Cons 'a' (Cons 'b' Empty))) (Cons 'A' (Cons 'B' Empty))
  example = {! Refl _ !}
```

## Decreasing 

Redo the decreasing function from Homework 3 for today's definition of ListOfLength.

```
  decreasing : (n : Nat) → ListOfLength Nat {!!}
  decreasing n = {!!}

  example-decreasing : Equals _ (decreasing 3) (Cons 2 (Cons 1 (Cons 0 Empty)))
  example-decreasing = {! Refl _ !}
```

## Reverse

Write the naive O(n^2) list reversal algorithm from Homework 5  
  reverse [] = []  
  reverse (x :: xs) = append (reverse xs) (x :: [])  
for ListOfLength.

You will need to use the following lemma, which says that if n=m then a list of length n is also a list of length m.  
```
  transport-length : {n m : Nat} {A : Set} (p : Equals Nat n m) → ListOfLength A n → ListOfLength A m
  transport-length (Refl n) l = l
```

```
  reverse : {n : Nat} {A : Set} → ListOfLength A n → ListOfLength A {!!}
  reverse = {!!}

  example-reverse : Equals (ListOfLength Nat 3) (reverse (Cons 1 (Cons 2 (Cons 3 Empty)))) (Cons 3 (Cons 2 (Cons 1 Empty)))
  example-reverse = {! Refl _ !}
```

## Zip/unzip

Write a function zip that makes a pair of lists into a list of pairs, so
that [x1,x2,x3,...] and [y1,y2,y3,...] get made into
[(x1,y1),(x2,y2),(x3,y3),...].  

```
  zip : {A B : Set} {n : Nat} → ListOfLength A {!!} → ListOfLength B {!!} → ListOfLength (A × B) {!!}
  zip xs ys = {!!}
```

Write converse functions unzip-first and unzip-second that make a list
of pairs [(x1,y1),(x2,y2),(x3,y3),...] into a pair of lists
[x1,x2,x3,...] and [y1,y2,y3,...].

```
  unzip-first : {A B : Set} {n : Nat} → ListOfLength (A × B) {!!} → ListOfLength A {!!} 
  unzip-first l = {!!}

  unzip-second : {A B : Set} {n : Nat} → ListOfLength (A × B) n → (ListOfLength B n)
  unzip-second l = {!!}
```

Prove that these two functions are inverse to each other:

```
  zip-unzip1 : {A B : Set} {n : Nat} (xs : ListOfLength A {!!}) (ys : ListOfLength B {!!})
             → Equals _ (unzip-first (zip xs ys)) xs 
  zip-unzip1 = {!!}

  zip-unzip2 : {A B : Set} {n : Nat} (xs : ListOfLength A {!!}) (ys : ListOfLength B {!!})
              → Equals _ (unzip-second (zip xs ys)) ys
  zip-unzip2 = {!!}

  unzip-zip : {A B : Set} {n : Nat} (xs : ListOfLength (A × B) n) 
            → Equals _ (zip (unzip-first xs) (unzip-second xs)) xs
  unzip-zip = {!!}
```

## Filter

Write a filter-evens function that keeps all and only the even numbers
in a list of length n.  You will need to think about what the result
type should be.

```
  filter-evens : {n : Nat} → ListOfLength Nat n → {!!}
  filter-evens l = {!!}
```

## Map, Filter

Generalize uppercase-all to a map higher-order function.
Generalize filter-evens to a filter higher-order function.  
