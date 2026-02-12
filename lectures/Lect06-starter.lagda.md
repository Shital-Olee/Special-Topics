```
module Lect06-starter where

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

  -- end library code

  -- ----------------------------------------------------------------------
  -- code from lecture/HW

  double : Nat → Nat
  double Z = Z
  double (1+ n) = 1+ (1+ (double n))

  Equals : Nat → Nat → Set
  Equals Z Z = Unit
  Equals Z (1+ n) = Void
  Equals (1+ n) Z = Void
  Equals (1+ n) (1+ m) = Equals n m

  mutual
    Even : Nat → Set
    Even Z = Unit
    Even (1+ n) = Odd n
  
    Odd : Nat → Set
    Odd Z = Void
    Odd (1+ n) = Even n

  parity : (n : Nat) -> Either (Even n) (Odd n)
  parity Z = Inl <> -- type checks because Even 0 = Unit
  parity (1+ n) = swap (parity n) where
    swap : Either (Even n) (Odd n) → Either (Odd n) (Even n)
    swap (Inl nIsEven) = Inr nIsEven
    swap (Inr nIsOdd) = Inl nIsOdd
  
  -- HW problem
  postulate
    refl : (n : Nat) → Equals n n
    sym : (n m : Nat) → Equals n m → Equals m n
```

# Lists
  
Lists are defined by a datatype with two constructors, [] and ::.  
E.g. the list [1,2,3] would be written  
1 :: (2 :: (3 :: []))  
or 1 :: 2 :: 3 :: []  

Here's a function defined by recursion on a list:

```
  addone : List Nat → List Nat
  addone [] = []
  addone (x :: xs) = 1+ x :: addone xs
```

# Linear Search 

First, we define booleans and options as special cases of Either:

```
  Bool : Set
  Bool = Either Unit Unit
  
  True False : Bool
  True = Inl <>
  False = Inr <>

  not : Bool → Bool
  not (Inl <>) = False
  not (Inr <>) = True

  Maybe : Set → Set
  Maybe A = Either A Unit

  Some : ∀ {A} → A → Maybe A
  Some x = Inl x

  None : ∀ {A} → Maybe A
  None = Inr <>

```

The linear search algorithm finds an element in a list/array by looping
over the entire data structure until it finds one.  Here, we will linear
search for an even number in a list of numbers.  Here's a standard
implementation:

```
  is-even : Nat -> Bool
  is-even = {!!}

  find-even : List Nat → Maybe Nat
  find-even = {!!}
```

What kind of bugs might we make in this code?

```
  module Buggy where
```

```
    find-even1-bug : List Nat → Maybe Nat
    find-even1-bug = {!!}
```

```
    find-even2-bug : List Nat → Maybe Nat
    find-even2-bug = {!!}
```

```
    find-even3-bug : List Nat → Maybe Nat
    find-even3-bug = {!!}
```

In what follows, we will refine the type of find-even to make these bugs
impossible.

# Verifying result is even 

To do this, we'll use our first example of an existential type.
∃ x : Nat. P[x] is written Σ[ x ∈ Nat ] P[x].  Values are pairs of an n
such that P[n] is true.  Use first and second or pattern-matching to get
out the witness/proof.

Using this, we define a type of even numbers as a pair of a number with
a proof that it is even:

```
  EvenNumber : Set
  EvenNumber = {!!}

  two : EvenNumber
  two = (2 , <>)

  three : EvenNumber
  three = (3 , {!impossible!})
```

Here's a first attempt: 

```
  find-even1 : List Nat → Maybe EvenNumber
  find-even1 = {!!}
```

Unfortunately, casing on is-even doesn't give us enough information.  In
princple, knowing that (is-even x) is equal to the true boolean should
tell us that the proposition Even x is true.  We could prove this, but
instead we can just use the more informative parity function in place of
is-even to get the information we want:

```
  find-even1' : List Nat → Maybe EvenNumber
  find-even1' = {!!}
```

Now, if we try to make the same bug as in find-even1 above, we can't
finish the code, because we can't prove that x is even in the odd case:

```
  find-even1-nobug : List Nat → Maybe EvenNumber
  find-even1-nobug = ?
```

# Also verifying membership

Next, we'll try to fix the bug from find-even2-bug above.  

The predicate In n l means that the number n is in the list l.
Informally:  
* n is not in []  
* n is in x :: xs iff n = x or n is in xs  

```
  In : Nat → List Nat → Set
  In = {!!}
```

This time, we can define "an even number that is in the list l" as the
following extended subset type:

```
  EvenNumberIn : List Nat → Set
  EvenNumberIn l = {!!}
```

Here's a lemma that we will need below:

```
  in-:: : (x : Nat) (xs : List Nat) → EvenNumberIn xs → EvenNumberIn (x :: xs)
  in-:: x xs inxs = {!!}
```

Now we can write a more precisely typed version of find-even:

```
  find-even2 : (l : List Nat) → Maybe (EvenNumberIn l)
  find-even2 = {!!}
```

If we try to make the bug from find-even2-bug above, we get stuck and can't
finish the proof:

```
  find-even2-nobug : (l : List Nat) → Maybe (EvenNumberIn l)
  find-even2-nobug = {!!}
```

What is find-even2 computing?  Run these by doing C-c C-n (>Agda:
Normalize) and think about it.

```
  find-even2-test0 = find-even2 (2 :: (3 :: (4 :: [])))
  find-even2-test1 = find-even2 (1 :: (2 :: (3 :: (4 :: []))))
  find-even2-test2 = find-even2 (7 :: (1 :: (2 :: (3 :: (4 :: [])))))
  find-even2-test3 = find-even2 (9 :: (7 :: (1 :: (2 :: (3 :: (4 :: []))))))
  find-even2-test4 = find-even2 (11 :: (13 :: (9 :: (7 :: (1 :: (2 :: (3 :: (4 :: []))))))))
```

A proof of In x l is a weird way of writing the *position* of x in l,
where Inr (Inr (Inr ... (Inl _))) means that it is in position k where k
is the number of Inr's (indexing starting with 0).

# Also verifying correctness of the false case

The final piece is to check that the function doesn't miss any even
numbers and return None when there is an even number in the list. To do
this, we define a predicate meaning that every number in the list is
odd:

```
  AllOdd : List Nat → Set
  AllOdd = {!!}
```

```
  find-even3 : (l : List Nat) → Either (EvenNumberIn l) (AllOdd l)
  find-even3 = {!!}
```

Logically, this type corresponds to the statement, "for every list l,
either there is an even number in l, or all of the numbers in l are
odd".  Computatonally, linear search is one program that proves this
theorem.

Now, if we try to make the same bug as in find-even3-bug above, where we
attempt to return the recursive result on xs (without checking the head
of the list x), we can't prove that every number in x::xs is odd:

```
  find-even3-nobug : (l : List Nat) → Either (EvenNumberIn l) (AllOdd l)
  find-even3-nobug = {!!}
```

# Extrinsic verifcation

The above is an example of what is called "intrinsic verification": the
code and the proof are the same function, with a fancy type.

We can also check the same specification using "extrinsic verification",
where you separately prove a property of an existing piece of code.  

To simplify one aspect of the proof, we'll rewrite find-even so that it
uses parity in place of the boolean-valued is-even:

```
  is-even' : Nat -> Bool
  is-even' n with parity n
  ... | Inl _ = True
  ... | Inr _ = False

  find-even' : List Nat → Maybe Nat
  find-even' [] = None
  find-even' (x :: xs) = case (is-even' x) where
    case : Bool → Maybe Nat
    case (Inl <>) = Inl x
    case (Inr <>) = find-even' xs
```
