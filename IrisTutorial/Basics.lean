import VersoManual
import BookGen.Meta.Lean

import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open BookGen
open Iris Iris.BI

set_option pp.rawOnError true

#doc (Manual) "Basics of Iris" =>

# Introduction

In short, Iris is a *higher-order concurrent separation logic
framework*. That is quite a mouthful, so let us break it down.

Firstly, the *framework* part means that Iris is not tied to any
single programming language — it consists of a base logic and can be
instantiated with any language one sees fit.

Secondly, a separation logic is a logic used to reason about programs
by introducing a notion of resource ownership. The idea is that one
must own a resource before one can interact with it. Ownership is
generally exclusive but can be transferred. To support this notion,
separation logic introduces a new connective called separating
conjunction, written `P ∗ Q`. This asserts ownership of the resources
described by propositions `P` and `Q`, and, in particular, `P` and `Q`
describe separate resources. So what is a resource? In Iris, we may
define our own notion of resources by creating a so-called *resource
algebra*, which we discuss later. For languages with a heap, a
canonical example of a resource is a heap fragment. Owning a resource
then amounts to controlling a fragment of the heap, allowing one to
read and update the associated locations.

Thirdly, a concurrent separation logic (CSL) extends on the above by
adding rules supporting concurrent constructions, such as `Fork`. As
ownership is exclusive, a program that spawns threads must decide how
to separate and delegate its resources to its threads, so that they
may perform their desired actions.

Finally, *higher-order* refers to the fact that predicates may depend
on other predicates. Being a program logic means that programs are
proved correct with respect to some specification — a description of
the program's behavior and interaction with resources. As programs are
usually composed of other programs, we would want our specifications
to be generic so that they may be used in a myriad of contexts. Having
support for higher-order predicates means that program specifications
can be parametrized by arbitrary propositions. This allows one to
write specifications for libraries independently of their clients —
the clients will instantiate the propositions to specialize the
specification to fit their needs.

In this chapter, we introduce basic separation logic in Iris.

# Iris in Lean

The type of propositions in Iris is `IProp GF`. All proofs in Iris
are performed in a context with a `GF : BundledGFunctors`, used to
specify available resources. The details of `GF` will come later when
we introduce resource algebras. For now, just remember to work inside
a `variable {GF}` block. This corresponds directly to the Rocq
tutorial's `Section proofs.  Context {Σ : gFunctors}.` — Lean's
`BundledGFunctors` plays the role of Rocq's `gFunctors`.

```savedImport
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
```

```savedLean
open Iris Iris.BI
```

```savedLean
namespace Basics
variable {GF : BundledGFunctors}
```

Iris provides two kinds of propositional statements:

* `⊢ P` asks whether `P` holds with no assumptions;
* `P ⊢ Q` asks whether `Q` holds assuming `P`.

In Lean, we work in the *Iris Proof Mode* (IPM/MoSeL). The practical
implication is that we get a new context, called the spatial context,
in addition to the usual Lean context, now called the non-spatial
context. Hypotheses from both contexts can be used to prove the goal.

The regular Lean tactics can still be used when we work within the
non-spatial context, but, in general, we shall use new tactics that
work natively with the spatial context. These new tactics start with
the letter `i`: instead of `intro H` we use `iintro H`, and instead of
`apply H` we use `iapply H`. Note that identifiers for hypotheses in
the spatial context are ordinary Lean identifiers — unlike the Rocq
version of Iris, the Lean port uses identifiers rather than strings.

To see this in action we will prove the statement `P ⊢ P`, for all
`P`.

```savedLean
theorem asm (P : IProp GF) : P ⊢ P := by
  iintro H
  iexact H
```

The tactic `iintro` adds `P` to the spatial context with the
identifier `H`. To finish the proof, one would normally use either
`exact` or `apply`. So in Iris, we use either `iexact` or `iapply`.

## Technical Details

In Lean, the context and the goal form a sequent (writing `⊢ₓ` for the
Lean entailment to distinguish it from the Iris entailment `⊢`):

```
H₁ : Φ₁, ..., Hₙ : Φₙ  ⊢ₓ  Ψ
```

This is equivalent to the proposition `Φ₁ ∧ ... ∧ Φₙ ⊢ₓ Ψ`.

The Iris Proof Mode mimics this in the sense that the spatial context
and the goal form an Iris sequent:

```
H₁ : Φ₁, ..., Hₙ : Φₙ  ⊢  Ψ
```

However, as Iris is a separation logic, this is equivalent to the
entailment `Φ₁ ∗ ... ∗ Φₙ ⊢ Ψ`.

Technically, since Iris is built on top of Lean, proving an Iris
entailment in Lean corresponds to proving `⊢ₓ (P ⊢ Q)`. In other
words, the spatial context is part of the Lean goal. This is the
reason why the regular Lean tactics no longer suffice. The new tactics
work with both the non-spatial and the spatial contexts.

Iris propositions include many of the usual logical connectives such
as conjunction `P ∧ Q`. The Lean port overloads these notations
directly on the `IProp GF` type, so — unlike the Rocq version — no
`%I` scope annotation is needed.

# Basic Separation Logic

The core connective in separation logic is the *separating
conjunction*, written `P ∗ Q`, for propositions `P` and `Q`.
Separating conjunction differs from regular conjunction, particularly
in its introduction rule:

```
       P₁ ⊢ Q₁     P₂ ⊢ Q₂
       ─────────────────────
         P₁ ∗ P₂ ⊢ Q₁ ∗ Q₂
```

That is, if we want to prove `Q₁ ∗ Q₂`, we must decide which of our
owned resources we use to prove `Q₁` and which we use to prove `Q₂`.
To see this in action, let us prove that separating conjunction is
commutative.

```savedLean
theorem sep_comm (P Q : IProp GF) : P ∗ Q ⊢ Q ∗ P := by
  iintro ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · iexact HP
```

To eliminate a separating conjunction we use the cases pattern
`⟨HP, HQ⟩` in `iintro` — analogous to Lean's anonymous-constructor
notation.

Unlike `∧`, `∗` is not idempotent. Specifically, there are Iris
propositions for which `¬(P ⊢ P ∗ P)`. Because of this, it is
generally not possible to use `isplit` to introduce `∗`. The
`isplit` tactic would duplicate the spatial context and is therefore
not available when the context is non-empty.

Instead, Iris introduces the tactics `isplitl` and `isplitr`. These
allow you to specify how you want to separate your resources to prove
each subgoal. The hypotheses listed in brackets — *space-separated*,
e.g. `[HP HQ]` — are passed to the left subgoal (for `isplitl`), and
the remaining to the right; conversely for `isplitr`.

Separating conjunction has an analogue to implication which, instead
of introducing the antecedent to the assumptions with conjunction,
introduces it with separating conjunction. This connective is written
as `P -∗ Q` and pronounced "magic wand" or simply "wand". Separation
is so widely used that `P -∗ Q` is treated specially; instead of
writing `P ⊢ Q`, we can write `P -∗ Q`, with the `⊢` being implicit.
That is, `⊢ P -∗ Q` is notationally equivalent to `P -∗ Q`.

Writing a wand instead of entailment makes currying more natural. Here
is the Iris version of modus ponens. It is provable using only
`iintro` and `iapply`.

```savedLean
theorem modus_ponens (P Q : IProp GF) : P -∗ (P -∗ Q) -∗ Q := by
  iintro HP HPQ
  iapply HPQ
  iexact HP
```

Just as with Lean tactics, Iris allows nesting of introduction
patterns. In fact, like Lean, Iris supports patterns of the form
`⟨H1, H2, H3⟩` as a shorthand for nested `⟨H1, ⟨H2, H3⟩⟩`.

Note that `∗` is right-associative, so `P ∗ Q ∗ R` is parsed
as `P ∗ (Q ∗ R)`.

```savedLean
theorem sep_assoc_1 (P Q R : IProp GF) :
    P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R := by
  iintro ⟨HP, HQ, HR⟩
  isplitl [HP HQ]
  · isplitl [HP]
    · iexact HP
    · iexact HQ
  · iexact HR
```

Manually splitting a separation can become tedious. To alleviate this,
we can use the `iframe` tactic. This tactic pairs up hypotheses with
pieces of a separation sequence.

```savedLean
theorem sep_comm_v2 (P Q : IProp GF) : P ∗ Q ⊢ Q ∗ P := by
  iintro ⟨HP, HQ⟩
  iframe
```

Bi-entailment of Iris propositions is denoted `P ⊣⊢ Q`. It is an
equivalence relation, and most connectives preserve it. Bi-entailment
is defined as the conjunction of `P -∗ Q` and `Q -∗ P`, so it can be
decomposed using the `isplit` tactic (which is permitted here because
the spatial context is empty at the point of splitting).

For hypotheses with multiple curried wands, we use the *proof-mode
term* syntax of `iapply`: the form `iapply H $$ pat₁ … patₙ` supplies
arguments for the wand premises of `H`.

```savedLean
theorem wand_adj_1 (P Q R : IProp GF) :
    (P -∗ Q -∗ R) ∗ P ∗ Q ⊢ R := by
  iintro ⟨H, HP, HQ⟩
  iapply H $$ HP HQ
```

Hypotheses that fit arguments exactly can be supplied directly without
generating a trivial subgoal.

```savedLean
theorem wand_adj (P Q R : IProp GF) :
    (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R) := by
  isplit
  · iintro H ⟨HP, HQ⟩
    iapply H $$ HP HQ
  · iintro H HP HQ
    iapply H
    isplitl [HP]
    · iexact HP
    · iexact HQ
```

Disjunctions `∨` are treated just like disjunctions in Lean. The
introduction pattern `(HP | HQ)` allows us to eliminate a disjunction,
while the tactics `ileft` and `iright` let us introduce them.

```savedLean
theorem or_comm (P Q : IProp GF) : Q ∨ P ⊢ P ∨ Q := by
  iintro (HQ | HP)
  · iright; iexact HQ
  · ileft;  iexact HP
```

We can even prove the usual elimination rule for or-elimination
written with separation. This version is, however, not very useful, as
it does not allow the two cases to share resources.

```savedLean
theorem or_elim (P Q R : IProp GF) :
    (P -∗ R) -∗ (Q -∗ R) -∗ P ∨ Q -∗ R := by
  iintro H1 H2 (HP | HQ)
  · iapply H1 $$ HP
  · iapply H2 $$ HQ
```

Separating conjunction distributes over disjunction (for the same
reason as ordinary conjunction).

```savedLean
theorem sep_or_distr (P Q R : IProp GF) :
    P ∗ (Q ∨ R) ⊣⊢ P ∗ Q ∨ P ∗ R := by
  isplit
  · iintro ⟨HP, HQ | HR⟩
    · ileft;  iframe
    · iright; iframe
  · iintro (⟨HP, HQ⟩ | ⟨HP, HR⟩)
    · isplitl [HP]
      · iexact HP
      · ileft; iexact HQ
    · isplitl [HP]
      · iexact HP
      · iright; iexact HR
```

Iris has existential and universal quantifiers over any Lean type.
Existential quantifiers are proved using the `iexists` tactic.
Elimination of existentials uses the pattern `%x` (with a `%` in front
of the bound variable) to move it to the pure (Lean) context.

```savedLean
theorem sep_ex_distr {α : Type} (P : IProp GF) (Φ : α → IProp GF) :
    (P ∗ ∃ x, Φ x) ⊣⊢ ∃ x, P ∗ Φ x := by
  isplit
  · iintro ⟨HP, %x, HΦ⟩
    iexists x
    iframe
  · iintro ⟨%x, HP, HΦ⟩
    isplitl [HP]
    · iexact HP
    · iexists x
      iexact HΦ
```

Likewise, forall quantification works almost as in Lean. To introduce
a universally quantified variable in the Iris context, you use the
intro pattern `%x`. To specialise a hypothesis at a concrete value
`x`, you write `H $$ %x`.

```savedLean
theorem sep_all_distr {α : Type} (P Q : α → IProp GF) :
    (∀ x, P x) ∗ (∀ x, Q x) -∗ (∀ x, P x ∗ Q x) := by
  iintro ⟨HP, HQ⟩ %x
  isplitl [HP]
  · iapply HP
  · iapply HQ
```

```savedLean
end Basics
```
