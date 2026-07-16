import VersoManual
import BookGen.Meta.Lean

import Iris.Instances.UPred
import Iris.ProofMode
import Iris.HeapLang
import Iris.HeapLang.Lib.Par
import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.ProofMode

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open BookGen

set_option pp.rawOnError true

#doc (Manual) "The Later Modality and Recursive Functions" =>

# Introduction

Iris is a step-indexed logic, meaning it has a built-in notion of
time. This can be expressed with the later modality `▷ P` signifying
that `P` holds after one time step. With the reading of propositions
as describing owned resources, `▷ P` asserts that we will own the
resources described by `P` after one time step.

The later modality is used quite extensively in Iris. We have already
seen that it is used to define Hoare triples, but it has many more
uses. For instance, it is a prime tool for reasoning about recursive
programs. It can be used to write specifications that capture the
minimum number of steps taken by a program. It is also an integral
part of working with invariants, which we introduce in a later
chapter.

```savedImport
import Iris.Instances.UPred
import Iris.ProofMode
import Iris.HeapLang
import Iris.HeapLang.Lib.Par
import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.ProofMode
```

```savedLean
section later_general
open Iris
variable (σ : BundledGFunctors)
```

# Basics of later modality

The later modality is monotone, meaning that if we know `P ⊢ Q`, then
we can also conclude `▷ P ⊢ ▷ Q`. In words, if we know that `P`
entails `Q`, then we also know that if we get `P` after one step, we
will also get `Q` after one step. This is captured by the `inext`
tactic, which introduces a later while stripping laters from our
hypotheses.

```savedLean
theorem later_mono (P Q : IProp σ): (Q ⊢ P) → (▷ Q ⊢ ▷ P) := by
  intro qp
  iintro q
  inext
  iapply qp $$ q
```

The `inext` tactic is actually a specialisation of the more general
`imodintro` tactic, which works with all modalities. The `imodintro`
tactic can be invoked with the introduction pattern `!>`, making it
less verbose to handle the later modality.

```savedLean
theorem later_mono' (P Q : IProp σ) : (Q ⊢ P) → (▷ Q ⊢ ▷ P) := by
  intro qp
  iintro q !>
  iapply qp $$ q
```

The later modality weakens propositions; owning resources now is
stronger than owning them later. In other words, `P ⊢ ▷ P`. This means
that we can always remove a later from the goal, regardless of whether
our hypotheses have a later.

```savedLean
theorem later_weak (P : IProp σ) : P ⊢ ▷ P := by
  iintro p
  inext
  itrivial
```

The later modality distributes over `∧`, `∨`, `∗`, and is preserved
by `∃` and `∀`. This means we can destruct these constructs
regardless of being prefaced by any laters.

```savedLean
theorem later_sep (P Q: IProp σ): ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q := by
  isplit
  . iintro ⟨p, q⟩
    iframe
  . iintro ⟨p, q⟩ !>
    iframe
```

As a consequence of monotonicity, weakening, and distribution over
`∗`, the `inext` tactic can simply ignore hypotheses in the context
that do not have a later on them.

```savedLean
theorem later_impl (P Q : IProp σ) : P ∗ ▷ (P -∗ Q) -∗ ▷ Q := by
  -- Exercise
  sorry
```

```savedLean
end later_general
```
