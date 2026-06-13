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

#doc (Manual) "Pure Propositions" =>

The implementation of Iris in Lean has a unique class of propositions
called *pure*. This class arises from the fact that Lean propositions
can be embedded into the logic of Iris. Any Lean proposition `φ : Prop`
can be turned into an Iris proposition through the pure embedding
`⌜φ⌝ : IProp GF`. This allows us to piggyback on much of the
functionality and theory developed for the logic of Lean. The
proposition `⌜φ⌝` is thus an Iris proposition, and we can use it as
we would any other Iris proposition.

```savedImport
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
```

```savedLean
open Iris Iris.BI
```

```savedLean
namespace Pure
variable {GF : BundledGFunctors}
```

```savedLean
theorem asm_pure (φ : Prop) : ⌜φ⌝ ⊢@{IProp GF} ⌜φ⌝ := by
  iintro H
  iexact H
```

When stating lemmas that do not depend on generic Iris propositions
mentioning `GF`, we have to specify the carrier type. The Lean
ascription syntax `⊢@{IProp GF} P` plays the same role as the Rocq
local notation `⊢@{iPropI Σ} P` used in the original tutorial.

A pure proposition is then any Iris proposition `P` for which there
exists a Lean proposition `φ`, such that `P ⊣⊢ ⌜φ⌝`.

Pure propositions can be introduced using `ipureintro`. This exits
the Iris Proof Mode (discarding the spatial context) and turns the
goal into a Lean proposition.

```savedLean
theorem eq_5_5 : ⊢@{IProp GF} ⌜5 = 5⌝ := by
  ipureintro
  rfl
```

To eliminate a pure proposition, we can use the cases pattern `%name`
(matching Rocq's `"%name"`). This moves the proposition into the
non-spatial Lean context as a Lean proposition.

```savedLean
theorem eq_elm {α : Type} (P : α → IProp GF) (x y : α) :
    ⌜x = y⌝ -∗ P x -∗ P y := by
  iintro %Heq HP
  rw [← Heq]
  iexact HP
```

It is quite easy to show that the propositions `⌜5 = 5⌝` and
`⌜x = y⌝` from above are pure. However, it can become quite
burdensome for more complicated Iris propositions. Fortunately, Iris
has machinery (the `IntoPure` / `FromPure` classes in the Rocq
version, and the corresponding instances in iris-lean) that identifies
pure propositions automatically — `ipureintro` makes use of them.

`True` is pure.

```savedLean
theorem true_intro : ⊢@{IProp GF} True := by
  ipureintro
  trivial
```

Conjunction preserves pureness.

```savedLean
theorem and_pure : ⊢@{IProp GF} ⌜5 = 5⌝ ∧ ⌜8 = 8⌝ := by
  ipureintro
  exact ⟨rfl, rfl⟩
```

Separating conjunction preserves pureness.

```savedLean
theorem sep_pure : ⊢@{IProp GF} ⌜5 = 5⌝ ∗ ⌜8 = 8⌝ := by
  ipureintro
  exact ⟨rfl, rfl⟩
```

Wand preserves pureness.

```savedLean
theorem wand_pure {α : Type} (x y : α) :
    ⊢@{IProp GF} ⌜x = y⌝ -∗ ⌜y = x⌝ := by
  ipureintro
  intro Heq
  exact Heq.symm
```

Arbitrary Iris propositions are not pure.

```savedLean
theorem abstr_not_pure (P : IProp GF) : ⊢ P -∗ ⌜8 = 8⌝ := by
  iintro _HP
  ipureintro
  rfl
```

The pure embedding allows us to state an important property, namely
*soundness*: anything proved inside the Iris logic is as true as
anything proved in Lean. In iris-lean this is witnessed by the
soundness theorems for `UPred`.

`⌜_⌝` turns Lean propositions into Iris propositions, while `⊢ _`
turns Iris propositions into Lean propositions. These operations are
not inverses, but they are related.

```savedLean
theorem pure_adj1 (φ : Prop) : φ → ⊢@{IProp GF} ⌜φ⌝ := by
  intro H
  ipureintro
  exact H
```

```savedLean
theorem pure_adj2 (P : IProp GF) : ⌜⊢ P⌝ -∗ P := by
  iintro %H
  iapply H
```

```savedLean
end Pure
```
