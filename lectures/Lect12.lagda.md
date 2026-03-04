
In this lecture, we will introduce the final couple of features of Agda
that we will use this semester: inductive families and implicit arguments.  


```
module Lect12 where

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

Before proceeding to inductive families, let's recall the ListOfLength
type from Homework 3.  The idea is that ListOfLength n represents a list
of length n.  We defined this as follows:

```
  module Subset where
    length : List Char → Nat
    length [] = 0
    length (x :: xs) = 1+ (length xs)
  
    ListOfLength : Nat → Set
    ListOfLength n = Σ[ l ∈ List Char ] (Equals Nat (length l) n)
```

How can we use ListOfLength n to prevent bugs?

* First, functions that construct lists like [] and :: and append need
  to tell you the length of their outputs in terms of the length of
  their inputs.  For example, :: constructs a list with one more element
  than the list given as input.

* Second, functions that use a list get to exploit the knowledge about
  the length of their input.  A standard example of this is the get
  function from Homework 3, where getting an element at a particular
  position can check that the specified position really exists in the
  list, preventing array access out of bounds errors.

As an example of the first point, here's the append function for
ListOfLength.  Note that the type tells you what the length of the
append of two lists is supposed to be: the sum of the lengths of the
inputs.

```
    append : (n m : Nat) → ListOfLength n → ListOfLength m → ListOfLength (n + m)
    append 0 m ([] , Refl 0) (ys , lengthys) = ys , lengthys
    append (1+ n) m (x :: xs , lengthxs) ys = (x :: first rec) , 1+-congruence _ _ (second rec) where
      rec = append n m (xs , 1+-injective _ _ lengthxs) ys
```

Here, rec : ListOfLength (n+m) stands for the result of the recursive
call on xs and ys.  The witness first rec is the actualy list that you
get by appending the list part of xs with the list part of ys, while
second rec : Equals _ (length (first rec)) (n + m) is the proof that
this has the right length.  Then we return x :: first rec as the witness
for appending x::xs and ys, and a proof that it has length 1+n + m.

If you squint, you can see the essence of the append function  
  
  append [] ys = ys  
  append (x :: xs) ys = x :: append xs ys  
  
hiding in the code, but there is a lot of extra decoration for proving
that the length works out correctly.  For example, in the [], we have to
pattern-match the proof of Equals _ (length []) n to learn that n is 0.
In the :: case, we need to use injectivity and conguence of 1+ to do the
length proofs.

As an example of the second point, here's a bounds-checked get function.
First, we define a type of positions in a list of length n.  The idea is
that there should be exactly n positions, which we might number
0,1,2,...,n-1, in a list of length n.  Here is a direct way to define
this type:

```
    Position : Nat → Set
    Position 0 = Void
    Position (1+ n) = Either Unit (Position n)
```

The idea with this definition is that there are no positions in a list
of length 0, while for a list of length (1+n), there is one more
position (Inl <>) than the positions in a list of length n (which are
included in Position (1+n) by Inr).

Now we can define get as follows:

```
    get : (n : Nat) → ListOfLength n → Position n → Char
    get 0      l                    ()
    get (1+ n) (x :: xs , lengthxs) (Inl <>) = x
    get (1+ n) (x :: xs , lengthxs) (Inr i) = get n (xs , 1+-injective _ _ lengthxs) i 
```

This says that the element at position 0 (Inl <>) is x, while the
element at position 1+i (Inr i) is obtained by the recursive call, which
gets the element at position i (which has type Position n) in the list
xs (which has type ListOfLength n).  Note that the case for get 0 is
impossible, because there are no programs of type Position 0.

Here are some examples that put these two functions together: appending
a list of length 3 and a list of length 2 gives a list of length 5, so
we are allowed to access the 0th and 4th elements to get 'a' and 'e'.
However, if we try to access a later element, there is no way to write
the position, so an access that is out of bounds is not well-typed.

```
    example1 : Equals _ (get _ (append 3 2 ('a' :: 'b' :: 'c' :: [] , Refl _) ('d' :: 'e' :: [] , Refl _)) (Inl <>)) 'a'
    example1 = Refl _

    example2 : Equals _ (get _ (append 3 2 ('a' :: 'b' :: 'c' :: [] , Refl _) ('d' :: 'e' :: [] , Refl _)) (Inr (Inr (Inr (Inr (Inl <>)))))) 'e'
    example2 = Refl _

    nonexample : Equals _
                  (get _
                       (append 3 2 ('a' :: 'b' :: 'c' :: [] , Refl _) ('d' :: 'e' :: [] , Refl _))
                       ( (Inr (Inr (Inr (Inr (Inr {!!}) )))) ))
                  {!!}
    nonexample = {!!}
```

# Lists of length n as an inductive family

```
  module IF1 where
```

Next, we will redo the above example using what's called an "inductive
family", which is short for an "inductively defined family of types".
This is also called an "indexed datatype".  

```
    data ListOfLength : Nat → Set where
      Empty    : ListOfLength 0
      Cons  : (n : Nat) → Char → ListOfLength n → ListOfLength (1+ n)
```

The idea for an inductive family definition of ListOfLength is that,
rather than pairing a regular list with a proof about its length, we
directly define a datatype whose constructors tell us the lengths of the
lists they produce.  The advantage of this is that, when we
pattern-match on such a datatype, Agda will propograte the information
about the lengths behind the scenes.  For example, here is the append
function:

```
    append : (n m : Nat) → ListOfLength n → ListOfLength m → ListOfLength (n + m)
    append 0 m Empty ys = ys
    append (1+ n) m (Cons n x xs) ys = Cons (n + m) x (append n m xs ys)
```

Comparing this with the code above, all of the pattern matching on Refl
and injectivity and congruence on equality proofs is done behind the
scenes.

We can also define the type of positions as an inductive family:

```
    data Position : Nat → Set where
      Here : (n : Nat) → Position (1+ n)
      There : (n : Nat) → Position n → Position (1+ n)
```

The two constructors Here and There correspond respectively to Inl and
Inr for the above definition.  Notice that we do not explicitly need to
say that Position 0 is Void, because when defining an inductive family,
you only say which instances of the type are true/inhabited by a
program, not what's false.

When defining the get function, pattern-matching on the Position n tells
us that n must be of the form 1+n', because none of the datatype
constructors for Position (Here and There) construct a Position 0.
Because n must be 1+n', the ListOfLength (1+ n') must be a Cons, and so
we can proceed using x and xs.  The index information in the inductive
family thus makes the Empty list case impossible. 

```
    get : (n : Nat) → ListOfLength n → Position n → Char
    get (1+ n') (Cons n' x xs) (Here n') = x
    get (1+ n') (Cons n' x xs) (There n' i) = get n' xs i
```

Here's how the above examples work: 

```
    example1 : Equals _ (get _ (append _ _ (Cons _ 'a' (Cons _ 'b' (Cons _ 'c' Empty))) (Cons _ 'd' (Cons _ 'e' Empty))) (Here _)) 'a'
    example1 = Refl _

    example2 : Equals _ (get _ (append _ _ (Cons _ 'a' (Cons _ 'b' (Cons _ 'c' Empty))) (Cons _ 'd' (Cons _ 'e' Empty)))
                               (There _ (There _ (There _ (There _ (Here _))))))
                        'e'
    example2 = Refl _
```

# Using underscores to avoid writing inferable arguments

For an inductive family like ListOfLength, Position, Equals, etc., Agda
treats the type itself as being injective.  For example, ListOfLength n
= ListOfLength m implies n = m.  This means that Agda can often infer
the arguments to a function that show up in the function's type.  When
there is a unique program that you can write in a certain spot, you can
replace it with an _.  The _ means "define this to be the unique program
that has to go here".  You can also put in a goal and use C-c C-s
(solve) to have Agda insert the term that goes there.  Here's how the
functions look with _'s for all of the lengths.

NOTE: if Agda colors a _ yellow/brown, that means it cannot infer the
value in that spot, and you should fill it in yourself.

```
  module IF2 where
    data ListOfLength : Nat → Set where
      Empty    : ListOfLength 0
      Cons  : (n : Nat) → Char → ListOfLength n → ListOfLength (1+ n)

    append : (n m : Nat) → ListOfLength n → ListOfLength m → ListOfLength (n + m)
    append _ _ Empty ys = ys
    append _ _ (Cons _ x xs) ys = Cons _ x (append _ _ xs ys)

    data Position : Nat → Set where
      Here : (n : Nat) → Position (1+ n)
      There : (n : Nat) → Position n → Position (1+ n)

    get : (n : Nat) → ListOfLength n → Position n → Char
    get _ (Cons _ x xs) (Here _) = x
    get _ (Cons _ x xs) (There _ i) = get _ xs i
```

For example, consider the recursive call (append _ _ xs ys) in the
append function.  Above, we wrote (append n m xs ys) explicitly.
However, the type of the append function "coordinates" n and m
with xs and ys: the first input to append must be the number that shows up in the type of xs, and the second input must be the number that shows up in the type of ys.
When we call the append function recursively, xs : ListOfLength n and ys : ListOfLength
m, so we can replace them with an _ when we call the append function.
Because n amd m don't show up in the code at all, we can also replace their definitions on the left-hand side with an _.

As a more concrete example, suppose we have
```
    example : ListOfLength 6 → ListOfLength 7
    example xs = Cons 6 'a' xs 

    example2 : ListOfLength 6 → ListOfLength 7
    example2 xs = Cons _ 'a' xs 
```
The only number that can be provied to Cons to construct a list of length 7 = 1+ 6 is 6, so we can replace it with an _.

# Implicit arguments

In the above code, we replaced all of the length variables with _'s.
When a function input is likely to be replaced with _, we can instead
use an "implicit argument", which is written as the function type {x : A
} → B(x) instead of the usual "explicit argument" function type (x : A) → B(x).

These are conceptually exactly the same, except an implicit argument is
by default filled in with _ without writing anything in the syntax of
the program.  So the following means the same thing as the above version with _'s:  

```
  module IF3 where
    data ListOfLength : Nat → Set where
      Empty    : ListOfLength 0
      Cons  : {n : Nat} → Char → ListOfLength n → ListOfLength (1+ n)

    append : {n m : Nat} → ListOfLength n → ListOfLength m → ListOfLength (n + m)
    append Empty ys = ys
    append (Cons x xs) ys = Cons x (append xs ys) 

    data Position : Nat → Set where
      Here : {n : Nat} → Position (1+ n)
      There : {n : Nat} → Position n → Position (1+ n)

    get : {n : Nat} → ListOfLength n → Position n → Char
    get (Cons x xs) (Here ) = x
    get (Cons x xs) (There i) = get xs i

    example1 : Equals _ (get (append (Cons 'a' (Cons 'b' (Cons 'c' Empty))) (Cons 'd' (Cons 'e' Empty))) Here) 'a'
    example1 = Refl _

    example2 : Equals _ (get (append (Cons 'a' (Cons 'b' (Cons 'c' Empty))) (Cons 'd' (Cons 'e' Empty))) (There (There (There (There (Here)))))) 'e'
    example2 = Refl _

    nonexample : Equals _
                  (get (append (Cons 'a' (Cons 'b' (Cons 'c' Empty))) (Cons 'd' (Cons 'e' Empty)))
                       (There (There (There (There (There {!impossible!}))))))
                  {!!}
    nonexample = {!!}
```

We've now gotten the code to look just like it would have looked without
the length information!  But an out-of-bounds access is still prevented,
because Agda checks the length information in the implicit arguments
behind the scenes.  This is one example where the combination of
inductive families and implicit arguments makes the code a lot nicer
than the version with explicit equality proofs that we started with.  
