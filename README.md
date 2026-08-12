# Agda formalisation for the paper [*Safety First: How to Safely Disregard Unsafe Behaviour in Compiler Calculations*](https://bahr.io/pubs/entries/partialcalc.html)

The material includes Agda formalisations of all
calculations in the paper along with the all the required background
theory, i.e. definitions and laws for (ordered) skew bisimilarity, and
additional calculations mentioned in the paper.

The formalisation depends on Agda and its standard library. All source
files in this directory have been typechecked with:

- Agda 2.8.0 ([installation instructions](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html))
- Agda standard library 2.3 ([installation instructions](https://github.com/agda/agda-stdlib/blob/v2.3/doc/installation-guide.md))

To typecheck all Agda files, use the included makefile by simply
invoking `make` in this directory. This typechecks
[Everything.agda](Everything.agda), which transitively imports every
file listed below. The `--sized-types` option is the only
feature-enabling option the formalisation uses. Run `make audit` for a
full inventory of the features that would keep the development from
typechecking with `--safe` (see "Unsafe features" below).

# Files


## Maybe Monad

  [Maybe.agda](Maybe.agda) contains the `Maybe` monad and
  the relation `⊥=` that section 2 of the paper uses to calculate a
  compiler in the presence of unsafe behaviour, together with the
  monad laws and the congruence and preorder laws for `⊥=`.

## Preorders

  [Preorder.agda](Preorder.agda) contains the type class `Ord` of
  preorders `⊑` that the ordered relations are parametrised on,
  together with the instances used in the calculations and the
  discrete preorder `≡-Ord` (see "Notation key for the relation
  symbols" below).

## Choice Trees

[CTree.agda](CTree.agda): This is the top-level module containing all
definitions and properties concerning choice trees:

- [Definitions.agda](CTree/Definitions.agda): Definition of
  choice trees and some basic operations on them.
- [Parallel.agda](CTree/Parallel.agda): Definition of the
  parallel composition operators and concurrent effect handlers.
- [Transitions.agda](CTree/Transitions.agda): Definition of the
  labelled transition system semantics of choice trees.
- [Stuck.agda](CTree/Stuck.agda): The effect transformer `Stuck`,
  which adds a stuck operation to an effect signature, and the
  resulting type `CTree⊥` of partial choice trees (see "The Stuck
  effect" below).
- [Safe.agda](CTree/Safe.agda): The safety predicates `safe` and
  `safeP` on partial choice trees, i.e. the side conditions of
  Proposition 1 (ii) and Corollary 3.
- [Bisimilarity.agda](CTree/Bisimilarity.agda): Definition of the
  bisimilarity relation (including its ordered variant) and its
  properties.
- [BisimilarityLaws.agda](CTree/BisimilarityLaws.agda): The monad and
  functor laws, and the congruence laws for `>>=`, `⊕` and `map`,
  stated for bisimilarity (rather than for its step-indexed
  approximation) exactly as section 3.3 of the paper states them.
- [SkewBisimilarity.agda](CTree/SkewBisimilarity.agda): Definition of
  the skew bisimilarity relation (including its ordered variant) and
  its properties (including Proposition 1, Proposition 2, and
  Corollary 3).
- [IndexedBisimilarity.agda](CTree/IndexedBisimilarity.agda):
  Definition of the step-indexed bisimilarity relation (including its
  ordered variant) and its properties. This is in fact a formalisation
  of a generalised version of step-indexed bisimilarity (parametrised
  on the set of safe transitions) so that both step-indexed (ordered)
  bisimilarity and step-indexed (ordered) skew bisimilarity are
  instances of this generalised version of step-indexed bisimilarity.
- [SkewIndexedBisimilarity.agda](CTree/SkewIndexedBisimilarity.agda):
  Definition of the step-indexed skew bisimilarity relation (including
  its ordered variant) and its properties (including step-indexed
  versions of Proposition 1, Proposition 2, and Corollary 3).
- [Maybe.agda](CTree/Maybe.agda): The correspondence between
  skew bisimilarity and the relation `⊥=` on `Maybe` from section 2 of
  the paper, which section 3.4 states informally (see "The `⊥=`
  relation and skew bisimilarity" below).

## Codensity Choice Trees

[CCTree.agda](CCTree.agda): This is the top-level module containing all
definitions and properties concerning codensity choice trees:

- [Definitions.agda](CCTree/Definitions.agda): Definition of codensity
  choice trees and all operations on them.
- [Transitions.agda](CCTree/Transitions.agda): Definition of the
  labelled transition system semantics of codensity choice trees,
  obtained from that of choice trees via `⟦_⟧`.
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

[Calculations.agda](Calculations.agda) is the top-level module that
imports every calculation listed below.

- [Calculations/Maybe/Cond.agda](Calculations/Maybe/Cond.agda): Simple
  arithmetic language extended with conditionals (section 2), using
  the `Maybe` monad and the relation `⊥=` exactly as the paper does.
  The resulting definitions are those of figure 1.
- [Calculations/Stack/Cond.agda](Calculations/Stack/Cond.agda): The
  same language and the same calculation (section 2), but using choice
  trees and skew bisimilarity instead of `Maybe` and `⊥=`.
- [Calculations/Stack/CondPrintFlip.agda](Calculations/Stack/CondPrintFlip.agda):
  Simple arithmetic language extended with conditionals,
  non-determinism, and print effect (section 4).
- [Calculations/Memory/Print.agda](Calculations/Memory/Print.agda):
  Simple arithmetic language extended with print effect targeting a
  register machine (section 5).

## Additional compiler calculations

The following files formalise additional compiler calculations,
including the calculations that produced the compilers given in
appendices A to C in the paper.

### Stack machines

- [Calculations/Stack/Lambda.agda](Calculations/Stack/Lambda.agda):
  Simply typed call-by-value lambda calculus.
- [Calculations/Stack/LambdaFix.agda](Calculations/Stack/LambdaFix.agda):
  Simply typed call-by-value lambda calculus extended with a
  fixed-point combinator.
- [Calculations/Stack/LambdaBoolFix.agda](Calculations/Stack/LambdaBoolFix.agda):
  Simply typed call-by-value lambda calculus extended with
  conditionals and a fixed-point combinator.
- [Calculations/Stack/Rattus.agda](Calculations/Stack/Rattus.agda):
  Rattus calculus (http://dx.doi.org/10.1017/S0956796822000132)
  discussed in section 4.4.1 and appendix A.
- [Calculations/Stack/LambdaConcur.agda](Calculations/Stack/LambdaConcur.agda):
  Simply typed concurrent call-by-value lambda calculus with
  channel-based communication discussed in section 4.4.2 and appendix
  B.

### Register machines

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
  channel-based communication discussed in section 5.5 and appendix C

## Termination arguments

In some cases, Agda's termination checker rejects the definition of
the virtual machine `exec`. In these cases, the termination checker is
disabled for `exec` (using the `TERMINATING` pragma). Each such `exec`
is proved terminating separately in
[Calculations/Terminating](Calculations/Terminating): we give a
variant `exec'` that Agda accepts *without* the pragma, and prove that
`exec` and `exec'` are bisimilar. There are seven virtual machines
that need the pragma, and all seven are discharged this way:

| `exec` defined with `TERMINATING`                                              | termination proof                                                                                      |
| ------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------ |
| [Calculations/Stack/Lambda.agda](Calculations/Stack/Lambda.agda)               | [Calculations/Terminating/Stack/Lambda.agda](Calculations/Terminating/Stack/Lambda.agda)               |
| [Calculations/Stack/LambdaFix.agda](Calculations/Stack/LambdaFix.agda)         | [Calculations/Terminating/Stack/LambdaFix.agda](Calculations/Terminating/Stack/LambdaFix.agda)         |
| [Calculations/Stack/LambdaBoolFix.agda](Calculations/Stack/LambdaBoolFix.agda) | [Calculations/Terminating/Stack/LambdaBoolFix.agda](Calculations/Terminating/Stack/LambdaBoolFix.agda) |
| [Calculations/Stack/LambdaConcur.agda](Calculations/Stack/LambdaConcur.agda)   | [Calculations/Terminating/Stack/LambdaConcur.agda](Calculations/Terminating/Stack/LambdaConcur.agda)   |
| [Calculations/Stack/Rattus.agda](Calculations/Stack/Rattus.agda)               | [Calculations/Terminating/Stack/Rattus.agda](Calculations/Terminating/Stack/Rattus.agda)               |
| [Calculations/Memory/Lambda.agda](Calculations/Memory/Lambda.agda)             | [Calculations/Terminating/Memory/Lambda.agda](Calculations/Terminating/Memory/Lambda.agda)             |
| [Calculations/Memory/LambdaConcur.agda](Calculations/Memory/LambdaConcur.agda) | [Calculations/Terminating/Memory/LambdaConcur.agda](Calculations/Terminating/Memory/LambdaConcur.agda) |

In each case the proof consists of a fuel-carrying `exec'`, a lemma
`execBisim` relating `exec` and `exec'` at every step index, and a
conclusion `bisimilar : DNE → ∀ c s → exec c s ~ exec' _ c s`.

The two machine models need different fuel. For the **stack machines**,
`exec'` is given a natural number that bounds the size of the current
code together with the code of the closures on the stack (`csize c +
fsize e`); every instruction either consumes fuel or is guarded by
`later`. That measure is unavailable for the **register machines**,
because the return address lives in a register rather than on the
stack, and the memory is an abstract map, so the size of the code that
`RET` jumps to cannot be bounded. What can be bounded is how often such
a jump happens: of the instructions that fetch their continuation from
memory rather than making the code argument structurally smaller, `APP`
is guarded by `later`, leaving `RET` as the only one that needs fuel --
and `RET` pops an entry off the lambda stack `l`. So for the register
machines the fuel is just `length l`,
and Agda accepts `exec'` by a lexicographic argument on the fuel and
the code.

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

## Notation key for the relation symbols

The formalisation defines a fair number of infix relations, but every
one of them is an abbreviation of a single underlying relation, marked
along four orthogonal dimensions. Each dimension contributes one
marker to the name, so a symbol can be decoded one marker at a time:

- `~` vs. `≲` : `≲` is the **ordered** variant: it compares return
  values using a preorder `⊑` (given by an `Ord A` instance, see
  [Preorder.agda](Preorder.agda)) rather than by equality. `~` is
  *defined* as `≲` instantiated with the discrete preorder `≡-Ord`, so
  every `≲`-law specialises to a `~`-law. The paper writes `≅` where
  the Agda code writes `~`. 
- hat, as in `≲̂` and `~̂` : the relation on **generalised** choice
  trees `CTree' E A` -- either an ordinary tree `p ↑` or a
  continuation `wait B c` awaiting an input -- rather than on `CTree E
  A ∞`. `CTree'` is exactly the state space of the labelled transition
  system of Fig. 2; see
  [CTree/Transitions.agda](CTree/Transitions.agda).
- `[ i ]` : the **step-indexed** approximation at index `i : ℕ`, as in
  §4.4.1 of the paper. Without it, the relation is the coinductive
  one.
- `! L` : **generalised** over an explicit effect predicate `L : epred
  E`, which says which effects count as safe (§4's "locally safe" is
  `lsafe L`).
- `⊥` prefix : the **skew** variant, i.e. the same dimension as `! L`
  with the argument fixed: `⊥` abbreviates `L = NotStuckEff`, and no
  marker at all abbreviates `L = AnyEff`. So the relation only
  constrains the left-hand side when it is locally safe.

Reading `_⊥≲̂[_]_` marker by marker, for instance, gives "step-indexed
ordered skew bisimilarity on generalised choice trees".

Combining the markers gives the complete inventory of relations on
choice trees. Each entry lists the unordered relation first and the
ordered one second:

|                                        | on `CTree`       | on `CTree'`        | step-indexed, on `CTree` | step-indexed, on `CTree'` |
| -------------------------------------- | ---------------- | ------------------ | ------------------------ | ------------------------- |
| general, `L` explicit                  | `_~_!_`, `_≲_!_` | `_~̂_!_`, `_≲̂_!_` | `_~_[_]_`, `_≲_[_]_`     | `_~̂_[_]_`, `_≲̂_[_]_`    |
| `L = AnyEff` (paper's `≅`)             | `_~_`, `_≲_`     | `_~̂_`, `_≲̂_`     | `_~[_]_`, `_≲[_]_`       | `_~̂[_]_`, `_≲̂[_]_`      |
| `L = NotStuckEff` (paper's `⊥≅`, `⊥≲`) | `_⊥~_`, `_⊥≲_`   | `_⊥~̂_`, `_⊥≲̂_`   | `_⊥~[_]_`, `_⊥≲[_]_`     | `_⊥~̂[_]_`, `_⊥≲̂[_]_`    |

The coinductive relations are defined in
[CTree/Bisimilarity.agda](CTree/Bisimilarity.agda) and
[CTree/SkewBisimilarity.agda](CTree/SkewBisimilarity.agda); the
step-indexed ones in
[CTree/IndexedBisimilarity/Definitions.agda](CTree/IndexedBisimilarity/Definitions.agda)
and
[CTree/SkewIndexedBisimilarity.agda](CTree/SkewIndexedBisimilarity.agda).
Only the record `_≲̂_!_` and the datatype `_≲̂_[_]_` are primitive;
the other 22 are abbreviations for them.

Codensity choice trees carry the same relations -- `_~[_]_`, `_~_`,
`_≲[_]_`, `_≲_`, `_⊥~[_]_`, `_⊥~_`, `_⊥≲[_]_`, `_⊥≲_` in
[CCTree/IndexedBisimilarity.agda](CCTree/IndexedBisimilarity.agda) and
[CCTree/SkewIndexedBisimilarity.agda](CCTree/SkewIndexedBisimilarity.agda)
-- defined by applying `⟦_⟧` to the `return` continuation, as
described under "Codensity choice trees" in the next section.

Lemma names follow the same scheme: a lemma about a relation is named
after that relation's markers, followed by the name of the law. The
step-indexed variant inserts an `i` directly after the relation
symbol. So `~>>=-cong` is the `>>=`-congruence for `~`,
`⊥≲i>>=-cong` is the `>>=`-congruence for step-indexed `⊥≲`, and
`≲ilater` is the `Later`-congruence for step-indexed `≲`. Lemmas
named `X-Y` (with both sides a relation, e.g. `⊥≲-≲`, `~i-~`,
`⊥~-⊥~i`) convert from relation `X` to relation `Y`.

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
  data CTree (E : Set → Set₁) (A : Set) (i : Size) : Set₁ where
    now   : (v : A) → CTree E A i
    later : (p : ∞CTree E A i) → CTree E A i
    _⊕_   : (p q : CTree E A i) → CTree E A i
    ∅     : CTree E A i
    eff   : ∀ {B} → (e : E B) → (c : B → CTree E A i) → CTree E A i

  record ∞CTree (E : Set → Set₁) (A : Set) (i : Size) : Set₁ where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → CTree E A j
```

## Universe levels of effect signatures

In the paper, an effect signature is simply a type constructor of type
`Type -> Type`. In Agda, we have to be more careful about universe
levels and effect signatures are thus of type `Set → Set₁`.

## Partial pattern matching in do notation

The Haskell syntax in the paper uses partial pattern matching in do
notation, e.g. in the following fragment from section 3.1:

```haskell
eval (Add x y) = do N n <- eval x
                    N m <- eval y
                    return (N (n + m))
```

To represent partial pattern matching in Agda, we use an auxiliary
function (`getN : ∀ {i e} → Value → CTree⊥ e ℕ i` for the code
fragment above) that performs the pattern matching and behaves like
the `fail` method if pattern matches fails:

```agda
eval (Add x y) = do n ← eval x >>= getN
                    m ← eval y >>= getN
                    return (N (n + m))
```

## Codensity choice trees

In the paper, codensity choice trees are presented directly as the
codensity monad:

```haskell
type CCTree e a = forall r . (a -> CTree e r) -> CTree e r
```

In Agda, we instead use a *deep embedding*: `CCTree` (see
[CCTree/Definitions.agda](CCTree/Definitions.agda)) is a data type
with one constructor per operation on codensity choice trees (`now`,
`later`, `_⊕_`, `∅`, `eff`, `_>>=_`, the parallel composition `_∥ʳ_`,
and `interpSt`), together with a denotation function

```agda
⟦_⟧ : CCTree E A i → ∀ {R} → (A → CTree E R i) → CTree E R i
```

that interprets such a tree into the codensity monad. That is, `⟦ p ⟧
k` corresponds to the codensity application `p k` in the paper. We use
this deep embedding to satisfy Agda's positivity and productivity
(sizing) requirements, which the negative occurrence in the codensity
function type would otherwise violate. This is the same representation
used in [*Calculating Compilers for
Concurrency*](http://dx.doi.org/10.1145/3607855) which introduced
codensity choice trees.

The data type itself is private and its constructors are primed
(`now'`, `later'`, ...); the unprimed names listed above are the
exported wrappers, and they are what the calculations use.

Accordingly, the (step-indexed, possibly skew) bisimilarity relations
on codensity choice trees are defined by applying `⟦_⟧` to the `return`
continuation (e.g. `p ⊥≲[ i ] q` iff `⟦ p ⟧ return ⊥≲[ i ] ⟦ q ⟧
return`).

## The Stuck effect

In the paper, the possibility of getting stuck is modelled by a
separate algebraic effect `Stuck` (with a single operation `Stuck ::
Stuck Void`) that is added to an effect signature `e` using the
coproduct `⊎`, so that partial choice trees have type `CTreeB e a =
CTree (Stuck ⊎ e) a`.

In Agda (see [CTree/Stuck.agda](CTree/Stuck.agda)), we instead use an
effect transformer `Stuck` that takes an effect signature `E` and adds
a stuck operation to it:

```agda
data Stuck (E : Set → Set₁) : Set → Set₁ where
  stuckEff : Stuck E ⊥
  notStuck : ∀ {A} → E A → Stuck E A

CTree⊥ E A i = CTree (Stuck E) A i
```

Thus `Stuck E` plays the role of `Stuck ⊎ e`: the operation
`stuckEff` corresponds to `Inl Stuck` and `notStuck e` corresponds to
`Inr e` (and `Void` is the empty type `⊥`).

## The `⊥=` relation and skew bisimilarity

Section 3.4 of the paper introduces skew bisimilarity `⊥~` as "a
weaker bisimilarity relation that corresponds to the `⊥=` relation on
`Maybe`" of section 2.
[CTree/Maybe.agda](CTree/Maybe.agda) makes that
correspondence precise. `Maybe` embeds into partial choice trees by

```agda
⟪_⟫ : ∀ {E A} → Maybe A → CTree⊥ E A ∞
⟪ nothing ⟫ = stuck
⟪ just v ⟫ = return v
```

which sends the unsafe behaviour of the `Maybe` monad to the unsafe
behaviour of a partial choice tree. The embedding is a monad morphism
(`⟪⟫->>=`), and `⊥=` is exactly the restriction of `⊥~` along it:

```agda
⊥=-⊥~ : ∀ {E A} {p q : Maybe A} → p ⊥= q → ⟪_⟫ {E} p ⊥~ ⟪ q ⟫
⊥~-⊥= : ∀ {E A} {p q : Maybe A} → ⟪_⟫ {E} p ⊥~ ⟪ q ⟫ → p ⊥= q
```

Under this correspondence the two defining clauses of `⊥=` become two
laws of `⊥~`: the (`⊥=`-`Nothing`) law becomes `⊥~stuck` in
[CTree/SkewBisimilarity.agda](CTree/SkewBisimilarity.agda) (`⊥~istuck`
for its step-indexed version), and the (`⊥=`-`Just`) law becomes
reflexivity.

## `ℕ` instead of `Int`

For simplicity, the Agda formalisation uses the type `ℕ` to represent
numbers in the source and target languages rather than `ℤ`, which
would more closely correspond to the type `Int` used in the paper.

# Unsafe features

The formalisation uses sized types, so it cannot be typechecked with
`--safe`. As a mechanical substitute for that check, the makefile has
an `audit` target that lists every feature in the development that
`--safe` would reject:

```
make audit
```

The `--sized-types` option is the only feature-enabling option in the
development. The only other option reported by the audit is `--safe`.
The seven `TERMINATING` pragmas used in the formalisation each have a
separate termination proof, and the one classical principle the
development uses is an explicit assumption rather than a postulate, as
described next.

# Use of classical reasoning

**The development contains no postulate.** It does use one classical
principle -- double-negation elimination -- but as an explicit
assumption rather than an axiom. It is declared in
[CTree/Bisimilarity.agda](CTree/Bisimilarity.agda) as

```agda
DNE : Setω
DNE = ∀ {l} {A : Set l} → ¬ ¬ A → A
```

and the handful of results that need it simply take an argument of
type `DNE`. Since that argument is explicit, the assumption is visible
in the type of each such result and, transitively, in the type of
everything that uses it. Grepping for `DNE` lists every affected
statement.

Classical reasoning is needed in exactly one place: to show that
step-indexed bisimilarity implies bisimilarity. The lemmas that
provide this are

```agda
≲i-≲   : DNE → ∀ {E L A j} {{_ : Ord A}} {p q : CTree' E A} → (∀ i → p ≲̂ L [ i ] q) → (p ≲̂ L ! q) {j}
~i-~   : DNE → ...
⊥≲i-⊥≲ : DNE → ...      -- the same, for skew bisimilarity
⊥~i-⊥~ : DNE → ...
```

Double-negation elimination is well known to be consistent with Agda's
type theory, so a reader who wishes to discharge the assumption may
safely postulate it.
