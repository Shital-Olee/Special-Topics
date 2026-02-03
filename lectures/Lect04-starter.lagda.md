
```
module Lect04-starter where

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

# Template for Recursion as a Higher-order Function

Here are a couple of examples of a recursive function: 

```
  successor2 : Nat → Nat
  successor2 = {!!}

  double : Nat → Nat
  double = {!!}
```

In general, the template for structural recursion is 
```
  f : {C : Set} → Nat → C
  f Z = {!the base case!}
  f (1+ n) = {! the inductive case, uses n and f(n) !}
```

(For now, read the {C : Set} as making f polymorphic.)  For example, for
double we fill in the first hole with Z and the second with 1+ (1+ the
recursive call).  For sucessor2 we fill in the first hole with 1 and the
second with 1+ the recursive call.

We can write the type of this template as a higher-order function as follows:
```
  natrec : {C : Set} → C → (Nat → C → C) → Nat → C
  natrec = {!!}
```

# Anonymous and Local Functions

Using this, we can redefine the above functions:
```
  sucessor2-again : Nat → Nat
  sucessor2-again x = {!!}

  double-again : Nat → Nat
  double-again x = {!!}
```

To fill in the inputs to natrec, we have used an anonymous function,
which is written (λ inputs → body).  To type that symbol do \lambda.  In place of the anonymous function,
we could have used a named local function like this: 
```
  double-again-again : Nat → Nat
  double-again-again x = {!!}
```

Another place where anonymous functions are used is when constructing a
value of a type that includes a function type nested inside of another
type constructor like × or Either.  For example, on the homework, you
are proving ((P ⊃ Q) ∧ (P ⊃ R)) ⊃ (P ⊃ (Q ∧ R)).  What if we do the
converse?

```
  -- (P ⊃ (Q ∧ R)) ⊃ ((P ⊃ Q) ∧ (P ⊃ R))
  distrib⊃∧2 : {!!}
  distrib⊃∧2 = {!!}
```

We need to output two functions, so it is natural to write them as
anonymous functions.  We also could write them as named local helper
functions.  

```
  -- (P ⊃ (Q ∧ R)) ⊃ ((P ⊃ Q) ∧ (P ⊃ R))
  distrib⊃∧2-again : {!!}
  distrib⊃∧2-again  = {!!}
```

The {P} {Q} {R} names the types P and Q and R so that we can use them in
the types of the helper functions.

# Computing types 

One new thing in Agda is that we can define *types* by recursion too.
For example, even and odd can be defined by mutual recursion on natural numbers.

These definitions mean that types like Even n *compute* to other types.
For example, the type Even 2 is equal to Unit, and Even 3 is equal to Void.

```
  mutual
    Even : Nat → Set
    Even = {!!}
  
    Odd : Nat → Set
    Odd = {!!}
```

# Props-as-types for ∀: Dependent Function Type

Next, we will extend our propositions-as-types dictionary to include the
universal quantifier ∀x:A.P(x).

How do you prove a ∀?  You assume a variable x:A and prove P(x) for that
variable.  How do you use ∀x:A.P(x)?  Well, if you have a particular
a:A, you can conclude P(a).

What type does that sound like?  It's the function type again, just like
for implication!  A proof of ∀x:A.P(x) is a function that for every x:A
delivers a proof of P(x).

This is called a "dependent function type" because the P(x) "depends" on
the function's input x.  In Agda, the dependent function type is written
(x : A) → P[x] (where P[x] is some type that mentions x; there are no
actual square brackets in the syntax).

For example, the (false) statement that every number is even is written
(x : Nat) → Even x.  The (false) statement that every number is odd is
written (x : Nat) → Odd x. The (true) statement that every number is
either even or odd is written (x : Nat) → Either (Even x) (Odd x).  

A regular function type A → B is sometimes called a "simple" or
"non-dependent" function type, to contrast it with the "dependent"
function type (x:A) → B[x].  In agda, the simple function type is just
notation for a dependent function type where the variable for the input
doesn't occur in the codomain, e.g. Nat → Nat is the same as (x : Nat) →
Nat.

The way you write and use elements of dependent function types is the
exact same syntax as for simple functions: you can define them using
named functions, named local functions in a where, or anonymous
functions, and you use them via function application.  In particular, if
f : (x : A) → B[x] then f(a) : B[a].

# Induction

The principle of mathematical induction says that to prove ∀n:Nat.P(n),
it suffices to prove P(0), and to prove that ∀n:Nat.P(n)⊃P(n+1).

For example, here is a proof that every number is even or odd: 
```
  parity : (n : Nat) -> Either (Even n) (Odd n)
  parity n = {!!}

  test = parity 3
```

Notice that **a proof by induction is a recursive function**.  

Because the function case is defined locally inside the parity function,
it can refer to the input variable n of the function.

Why is it called parity? Because we can run it!  What happens when you
run parity 3?  Well, parity 3 has type Either (Even 3) (Odd 3), which
computes to Either Void Unit, so the type of the function tells us it
must return Inr <>, because we know that Even 3 ≡ Void and Odd 3 ≡ Unit
and there is no element of type Void.

But suppose we didn't know that; here's how it actually runs
```
{-
  parity 0
≡ Inl <>

  parity 1
≡ case (parity 0)
≡ case (Inl <>)
≡ Inr <>

  parity 2
≡ case (parity 0)
≡ case (Inr <>)
≡ Inl <>

  parity 3
≡ case (parity 0)
≡ case (Inl <>)
≡ Inr <>

-}
```
If you read Inl <> as true and Inr <> as false, then the function
returns true when the number is even, and returns false when the number
is odd.  So *the proof that every number is even or odd is also a function that computes whether the number is even or odd*.

To explain this analogy in general, we can also move the case outside, in which case we get
```
  parity-again : (n : Nat) -> Either (Even n) (Odd n)
  parity-again = {!!}
```
Notice that if we define P(n) ≡ Either (Even n) (Odd n), then this has exactly the form of mathematical induction:
base-case has type P(0), and case has type (n : Nat) → P(n) → P(1+n), and then the function proves (n : Nat) → P(n).   

So, in general, we can abstract this as a higher-oder function:
```
  nat-elim : {!!}
  nat-elim = {!!}
```

In the special case where P is a constant predicate and doesn't mention
n, we get exactly the type we gave to the generic recursion principle
above:
```
  natrec-again : {C : Set} → C → (Nat → C → C) → Nat → C
  natrec-again = {!!}
```
Therefore, under propositions as types, recursion and induction are really the same concept.  

# Negation

We can represent negation (not) by defining not A to be A → Void.  

```
  ¬ : Set → Set
  ¬ A = A → Void
```

Here's an example of proving a negation:

```
  even-not-odd : (x : Nat) → Even x → ¬ (Odd x)
  even-not-odd = {!!}
```

Note that a negation is just a function type, so you can use it like any
other function type.  For example, we can prove that Odd numbers are not
even just by swapping the inputs.

```
  odd-not-even : (x : Nat) → Odd x → ¬ (Even x)
  odd-not-even = {!!}
```

# Props as types for ∃

```
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field 
      first : A
      second : B first

  syntax Σ A (\ x  -> B) = Σ[ x ∈ A ] B


  data _==_ {A : Set} (x : A) : A → Set where
    refl : x == x
```

```
  Even' : Nat → Set
  Even' n = {!!}

  Odd' : Nat → Set
  Odd' n = {!!}
```

What would a function of this type compute?
```
  mystery : (n : Nat) → Either (Even' n) (Odd' n)
  mystery = {!!}
```

# Negation and Disjunction

How does ¬ ¬ (Either (Even n) (Odd n)) differ from (Either (Even n) (Odd n))?
