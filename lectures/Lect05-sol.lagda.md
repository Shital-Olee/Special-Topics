
In this class, you will practice recursion and induction.  

```
module Lect05-sol where
  -- ----------------------------------------------------------------------
  -- library code 

  -- natural numbers
  data Nat : Set where
    Z : Nat
    1+ : Nat -> Nat

  {-# BUILTIN NATURAL Nat #-}

  data Either (A B : Set) : Set where
    Inl : A → Either A B
    Inr : B → Either A B

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
```

# Some examples from Lecture 4.

Type them in with me.

```
  double : Nat → Nat
  double 0 = 0
  double (1+ n) = 1+ (1+ (double n))

  mutual
    Even : Nat → Set
    Even 0 = Unit
    Even (1+ n) = Odd n
  
    Odd : Nat → Set
    Odd 0 = Void
    Odd (1+ n) = Even n

  parity : (n : Nat) -> Either (Even n) (Odd n)
  parity 0 = Inl <> 
  parity (1+ n) = case (parity n) where
    case : Either (Even n) (Odd n) → Either (Even (1+ n)) (Odd (1+ n))
    case (Inl nIsEven) =  Inr nIsEven 
    case (Inr nIsOdd) = Inl nIsOdd 

  test = parity 9
```

You can do C-c C-n (>Agda: Compute Normal Form) to run tests.  For
example, do C-c C-n, then type test, and then type enter, and you should
see whether 9 is even or odd (Inl <> means even, Inr <> means odd).

# Curried functions

One way to represent a multi-input function is by making the function
take a pair of inputs:

```
  plus : Nat × Nat → Nat
  plus (Z , y) = y
  plus (1+ x , y) = 1+ (plus (x , y)) 
```

However, the idomatic way to do multi-input functions in Agda is using
  "curried" functions (named after a mathematician named Haskell Curry)
  instead:
```
  plus-curried : Nat → Nat → Nat
  plus-curried Z y = y
  plus-curried (1+ x) y = 1+ (plus-curried x y)
```

If you want, you can see this as notation for a 2-input function:

* To write a 2-input function's type, you write A → B → C, which means
  that A and B are inputs and C is the output.

* To use f : A → B → C, you write f x y, with the x and y as the
  inputs. If x and y are complicated expressions, write f (e1) (e2) to
  group the inputs appropriately. For example
  plus-curried (plus-curried 1 2) (plus-curried 3 4)
  is the same as
  plus( plus(1,2) , plus(3,4)).  

Formally, a Curried function type is a right-associated nesting of the
function type, i.e. Nat → Nat → Nat means Nat → (Nat → Nat).  So you can
also **partially apply** a function to specify one input but not the
other.  For example, (plus 3) : Nat → Nat is the function that adds 3 to its input.  

## Problem 1

The following propositions are analogous to some of the homework
problems, but they are curried here, while the homework problems are
uncurried.  Prove these versions:
```
  module Logic (P Q R S T : Set) where
    -- R ⊃ (S ∨ T) ⊃ ((R ∧ S) ∨ (R ∧ T))
    distrib∧∨-curried : R → (Either S T) → (Either (R × S) (R × T))
    distrib∧∨-curried r (Inl x) = Inl (r , x)
    distrib∧∨-curried r (Inr x) = Inr (r , x)

    -- P ⊃ Q ⊃ R ⊃ (P ∧ (Q ∧ R)), which means P ⊃ (Q ⊃ (R ⊃ (P ∧ (Q ∧ R))))
    make-pair : P → Q → R → (P × (Q × R)) 
    make-pair p q r = (p , (q , r))
```

# Induction: Less than or equal to

The type n ≤ m is supposed to represent proofs that n is less than or
equal to m, analogously to how Even n and Odd n represent proofs that n
is even or odd.  Define n ≤ m as a function that computes a type (Set)
by recursion on n and m.

```
  _≤_ : Nat → Nat → Set
  Z ≤ m = Unit
  1+ n ≤ Z = Void
  1+ n ≤ 1+ m = n ≤ m
```

Prove that ≤ is reflexive, i.e. every number is less than or equal to itself.

```
  ≤-refl : (x : Nat) → x ≤ x 
  ≤-refl Z = <>
  ≤-refl (1+ x) = ≤-refl x 
```

Prove that ≤ is transitive, i.e. if x ≤ y and y ≤ z then x ≤ z.

```
  ≤-trans : (x y z : Nat) → x ≤ y → y ≤ z → x ≤ z
  ≤-trans Z Z Z e1 e2 = <>
  ≤-trans Z Z (1+ z) e1 e2 = <>
  ≤-trans Z (1+ y) Z e1 e2 = <>
  ≤-trans Z (1+ y) (1+ z) e1 e2 = <>
  ≤-trans (1+ x) Z Z e1 e2 = e1
  ≤-trans (1+ x) Z (1+ z) e1 e2 = abort e1
  ≤-trans (1+ x) (1+ y) Z e1 e2 = abort e2
  ≤-trans (1+ x) (1+ y) (1+ z) e1 e2 = ≤-trans x y z e1 e2
```

Prove the following theorem about the double function, which says that
doubling a number only makes it bigger.  You will need to state and
prove a lemma about ≤ (try doing the proof of the theorem and see what
you need to know).

```
  lemma : (x : Nat) → x ≤ 1+ x
  lemma Z = <>
  lemma (1+ x) = lemma x

  double-≤ : (x : Nat) → x ≤ double x
  double-≤ Z = <>
  double-≤ (1+ x) = ≤-trans x (double x) (1+ (double x)) (double-≤ x) (lemma (double x))
```

