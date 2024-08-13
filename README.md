This repository contains the supplementary material for the paper
*Partial Compiler Calculation with Skew Bisimilarity*. The material
includes Agda formalisations of all calculations in the paper along
with the all the required background theory, i.e. definitions and laws
for (ordered) skew bisimilarity, and additional calculations mentioned
in the paper.

To typecheck all Agda files, use the included makefile by simply
invoking `make` in this directory. All source files in this directory
have been typechecked using version 2.6.3 of Agda and version 1.7.2 of
the Agda standard library.

# Files

## Choice Trees

[CTree.agda](CTree.agda): This is the top-level module containing all
definitions and properties concerning choice trees:

- [Definitions.agda](CTree/Definitions.agda): Definition of
  choice trees and some basic operations on them.
- [Parallel.agda](CTree/Parallel.agda): Definition of the
  parallel composition operators and concurrent effect handlers.
- [Transitions.agda](CTree/Transitions.agda): Definition of the
  labelled transition system semantics of choice trees.
- [Bisimilarity.agda](CTree/Bisimilarity.agda): Definition of the
  bisimilarity relation (including its ordered variant) and its
  properties.
- [SkewBisimilarity.agda](CTree/SkewBisimilarity.agda): Definition of
  the skew bisimilarity relation (including its ordered variant) and
  its properties.
- [IndexedBisimilarity.agda](CTree/IndexedBisimilarity.agda):
  Definition of the step-indexed bisimilarity relation (including its
  ordered variant) and its properties. This is in fact a formalisation
  of a generalised version of step-indexed bisimilarity (parametrised
  on the set of safe transitions) so that both step-indexed (ordered)
  bisimilarity and step-indexed (ordered) skew bisimilarity are
  instances of this generalised version of step-indexed bisimilarity.
- [SkewIndexedBisimilarity.agda](CTree/SkewIndexedBisimilarity.agda):
  Definition of the step-indexed skew bisimilarity relation (including its
  ordered variant) and its properties.

## Codensity Choice Trees

[CCTree.agda](CCTree.agda): This is the top-level module containing all
definitions and properties concerning codensity choice trees:

- [Definitions.agda](CCTree/Definitions.agda): Definition of codensity
  choice trees and all operations on them.
- [IndexedBisimilarity.agda](CCTree/IndexedBisimilarity.agda):
  Definition of both the bisimilarity and the step-indexed
  bisimilarity relation and their properties. 
- [SkewIndexedBisimilarity.agda](CCTree/SkewIndexedBisimilarity.agda):
  Definition of both the skew bisimilarity and the step-indexed skew
  bisimilarity relation (including their ordered variants) and their
  properties.

## Memory model

  [Memory.agda](Memory.agda) contains the definition of the memory
  model for the calculation of register machines.

## Compiler calculations from the paper

- [Calculations/Stack/Cond.agda](Calculations/Stack/Cond.agda): Simple
  arithmetic language extended with conditionals (section 2);
  the calculation uses choice trees instead of `Maybe`.
- [Calculations/Stack/CondPrint.agda](Calculations/Stack/CondPrint.agda): Simple
  arithmetic language extended with conditionals and print effect (section 4).
- [Calculations/Memory/Print.agda](Calculations/Memory/Print.agda):
  Simple arithmetic language extended with print effect targeting a
  register machine (section 5).

## Additional compiler calculations

### Stack machines

- [Calculations/Stack/Lambda.agda](Calculations/Stack/Lambda.agda):
  Simply typed call-by-value lambda calculus.
- [Calculations/Stack/LambdaFix.agda](Calculations/Stack/LambdaFix.agda):
  Simply typed call-by-value lambda calculus extended with a
  fixed-point combinator.
- [Calculations/Stack/LambdaBoolFix.agda](Calculations/Stack/LambdaBoolFix.agda):
  Simply typed call-by-value lambda calculus extended with
  conditionals and a fixed-point combinator.
- [Calculations/Stack/RaTT.agda](Calculations/Stack/RaTT.agda): Simply
  RaTT calculus (https://doi.org/10.1145/3342523) in a simplified
  version (http://dx.doi.org/10.1017/S0956796822000132).
- [Calculations/Stack/LambdaConcur.agda](Calculations/Stack/LambdaConcur.agda):
  Simply typed concurrent call-by-value lambda calculus with
  channel-based communication.

### Register machines

- [Calculations/Memory/Print.agda](Calculations/Memory/Print.agda):
  Simple arithmetic language with a print effect.
- [Calculations/Memory/Loop.agda](Calculations/Memory/Loop.agda):
  Simple arithmetic language with a degenerate loop primitive (to
  illustrate calculation for non-terminating languages).
- [Calculations/Memory/Concur.agda](Calculations/Memory/Concur.agda):
  Simple arithmetic language with a degenerate loop primitive
  and concurrency
- [Calculations/Memory/Lambda.agda](Calculations/Memory/Lambda.agda):
  Simply typed call-by-value lambda calculus.
- [Calculations/Memory/LambdaConcur.agda](Calculations/Memory/LambdaConcur.agda):
  Simply typed concurrent call-by-value lambda calculus with
  channel-based communication.

## Termination arguments

In some cases, Agda's termination checker rejects the definition of
the virtual machine `exec`. In these cases, the termination checker is
disabled for `exec` (using the `TERMINATING` pragma). As an example,
we show how to prove that `exec` is in fact terminating for the
concurrent lambda calculus in
[Calculations/Terminating/LambdaConcur.agda](Calculations/Terminating/LambdaConcur.agda).

# Agda formalisation vs. paper proofs

In the paper, we use an idealised Haskell-like syntax for all
definitions. Here we outline how this idealised syntax is translated
into Agda.

## Identifier names

The paper uses Haskell conventions for identifier names, which are
different in Agda. For examples, constructors must start with a upper
case letter in Haskell, whereas constructors typically start with a
lower case letter in Agda. As a consequence the constructors of the
`CTree` type are named slightly differently in the Agda code (see
below).

## Sized coinductive types

In the paper, we use the ∞-notation to distinguish coinductive
constructors from inductive constructors. In particular, we use this
for the `CTree` type:

```haskell
data CTree e a where
   Now  :: a -> CTree e a
   (⊕) :: CTree e a -> CTree e a -> CTree e a
   Zero :: CTree e a
   Eff  :: e b -> (b -> CTree e a) -> CTree e a
   Later :: ∞ (CTree e a) -> CTree e a
```

In Agda we use coinductive record types to represent coinductive data
types. Moreover, we use sized types to help the termination checker to
recognise productive corecursive function definitions. Therefore, the
`CTree` type has an additional parameter of type `Size`:

```agda
mutual
  data CTree (E : Set → Set) (A : Set) (i : Size) : Set₁ where
    now  : (v : A) → CTree E A i
    _⊕_  : (p q : CTree E A i) → CTree E A i
    ∅    : CTree E A i
    eff  : ∀ {B} → (e : E B) → (c : B → CTree E A i) → CTree E A i
    later : (p : ∞CTree E A i) → CTree E A i

  record ∞CTree (E : Set → Set) (A : Set) (i : Size) : Set₁ where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → CTree E A j
```

## Partial pattern matching in do notation

The Haskell syntax in the paper uses partial pattern matching in do
notation, e.g. in the following fragment from section 3.1:

```haskell
eval (Add x y) = do N n <- eval x
                    N m <- eval y
                    return (N (n + m))
```

To represent partial pattern matching in Agda, we use an auxiliary
function (`getN : ∀ {i} → Value → CTree e ℕ i` for the code
fragment above) that performs the pattern matching and behaves like
the `fail` method if pattern matches fails:

```agda
eval (Add x y) = do n ← eval x >>= getN
                    m ← eval y >>= getN
                    return (N (n + m))
```