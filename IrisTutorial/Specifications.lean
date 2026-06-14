import VersoManual
import BookGen.Meta.Lean

import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.HeapLang
import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.ProofMode
import Iris.HeapLang.Lib.Par

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open BookGen
open Iris Iris.BI Iris.HeapLang

set_option pp.rawOnError true

#doc (Manual) "Specifications" =>

# Introduction

Now that we have seen basic separation logic in Iris and introduced
a suitable language, HeapLang, we are finally ready to start
reasoning about programs. HeapLang ships with a program logic
defined using Iris. We can access the logic through the proof-mode
package, which also defines tactics to alleviate working with the
logic.

The program logic for HeapLang relies on a basic notion of a
resource: the resource of heaps. Recall that `GF` specifies the
available resources. To make the resource of heaps available, we
require an instance of `HeapLangGS hlc GF` throughout this section.
We declare it as a `variable` so that every definition and theorem
below has the resource of heaps available.

```savedImport
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.HeapLang
import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.ProofMode
import Iris.HeapLang.Lib.Par
```

```savedLean
open Iris Iris.BI Iris.HeapLang
```

```savedLean
namespace Specifications
variable {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]
```

# Weakest Precondition

The first construct for specifying program behaviour is the
*weakest precondition*. In Iris, a weakest precondition has the
form `WP e {{ v, Φ v }}`. This asserts that if the HeapLang program
`e` terminates at some value `v`, then `v` satisfies the predicate
`Φ`. The double curly brackets are the *postcondition*.

A natural first example is a pure arithmetic expression such as
`#1 + #2 * #3 + #4 + #5`, symbolically executed with the
`wp_pure`/`wp_pures` tactics, which iterate the
`wp_pure_step_fupd` rule. However, iris-lean's HeapLang only
provides `PureExec` instances for β-reduction, `if`/`case`/`inj`,
pair projections, and `≤` on integers. The arithmetic operators
have no `PureExec` instance, so `wp_pure` cannot fire on `#2 * #3`
or any of the additions.

```
-- TODO (upstream — iris-lean): register `PureExec` instances for
-- the arithmetic binops on `BaseLit.int` (and ideally also on
-- bit-wise / shift operators). Until then `arith_spec` cannot be
-- proved in the natural way.

-- Reference implementation (to port once the prerequisite lands):
--   Example arith : expr := #1 + #2 * #3 + #4 + #5.
--   Lemma arith_spec : ⊢ WP arith {{ v, ⌜v = #16⌝ }}.
--   Proof. rewrite /arith. wp_op. wp_pure. wp_pures.
--          iModIntro. iPureIntro. reflexivity. Qed.
```

To showcase the tactics that *do* work, here is the same shape of
proof on a program that only uses β-reduction and `if`:

```savedLean
def boolish : Exp := hl(
  (λ b, if b then #1 else #0) #true)
```

```savedLean
theorem boolish_spec : ⊢@{IProp GF} WP boolish {{ v, ⌜v = hl_val(#1)⌝ }} := by
  unfold boolish
  wp_pures
  itrivial
```

The tactic `wp_pures` symbolically executes all pure steps for
which a `PureExec` instance exists. Each step internally applies
the `wp_pure_step_fupd` rule from `Iris.ProgramLogic.Lifting`,
which says (informally):

```
e₁ →pure e₂
──────────────────────────────────
WP e₂ {{ Φ }} ⊢ WP e₁ {{ Φ }}
```

After every pure step has fired, the goal is reduced to proving the
postcondition behind a fancy-update modality `|={⊤}=>`; `itrivial`
discharges the residual proposition `⌜#1 = #1⌝`.

The `lambda` program from the previous chapter mixes lambda
application with arithmetic. Because of the same `PureExec` gap, we
cannot symbolically evaluate it end-to-end in iris-lean today.

```savedLean
def lambda : Exp :=
  hl(let add5 := (λ x, x + #5);
     let double := (λ x, x * #2);
     let compose := (λ f g, λ x, g (f x));
     compose add5 double #5)
```

```
-- TODO (upstream — iris-lean): same as above — `lambda` contains
-- `+` and `*`. The lambda β-reductions all work via
-- `wp_pure`/`wp_pures`, but the arithmetic reductions do not.

-- Reference implementation (to port once the prerequisite lands):
--   Lemma lambda_spec : ⊢ WP lambda {{ v, ⌜v = #20⌝ }}.
--   Proof. rewrite /lambda. wp_pures. done. Qed.
```

A purely β-driven analogue does prove cleanly:

```savedLean
def hofun : Exp :=
  hl(let myId := (λ x, x);
     let myApply := (λ f x, f x);
     myApply myId #5)
```

```savedLean
theorem hofun_spec : ⊢@{IProp GF} WP hofun {{ v, ⌜v = hl_val(#5)⌝ }} := by
  unfold hofun
  wp_pures
  itrivial
```

# Resources

In this section, we introduce our first notion of a resource: the
resource of heaps. As mentioned in the basics chapter, propositions
in Iris describe / assert ownership of resources. To describe
resources in the resource of heaps, we use the *points-to*
predicate, written `l ↦ some v`. The value carries an `Option`
because the heap model also tracks deallocated locations: `some v`
means the location currently holds `v`. Intuitively, `l ↦ some v`
describes all
heap fragments that have value `v` stored at location `l`. The
proposition
`l1 ↦ some hl_val(#1) ∗ l2 ↦ some hl_val(#2)`
then describes all heap fragments that map `l1` to `1` and `l2` to
`2`.

A running example for this section is

```
let: "x" := ref #1 in
"x" <- !"x" + #2 ;;
!"x"
```

which both touches the heap *and* performs an addition. We can
state and partly prove it in iris-lean, but the addition step is
blocked by the same `PureExec` gap as above; see the per-step
breakdown below.

```savedLean
def prog : Exp := hl(
  let x := ref(#1);
  x ← !x + #2;
  !x)
```

```
-- TODO (upstream — iris-lean): the addition `!x + #2` blocks the
-- proof. The `wp_alloc`/`wp_load`/`wp_store` rules apply fine; the
-- missing piece is reducing `(#1 : Int) + (#2 : Int)` via
-- `wp_pure`. Until `PureExec` for `+` lands, `prog_spec` cannot be
-- proved cleanly.

-- Reference implementation (to port once the prerequisite lands):
--   Lemma prog_spec : ⊢ WP prog {{ v, ⌜v = #3⌝ }}.
--   Proof.
--     rewrite /prog.
--     wp_alloc l as "Hl".
--     wp_let. wp_load. wp_op. wp_store. wp_load.
--     iModIntro. done.
--   Qed.
```

To at least demonstrate the heap primitives in isolation, here is a
trivial program that allocates and then immediately reads.

```savedLean
def writeread : Exp := hl(
  let x := ref(#7);
  !x)
```

```savedLean
theorem writeread_spec :
    ⊢@{IProp GF} WP writeread {{ v, ⌜v = hl_val(#7)⌝ }} := by
  unfold writeread
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %l Hl
  wp_pures
  iapply wp_load $$ Hl
  iintro !> _Hl
  itrivial
```

Each `iapply wp_alloc` / `iapply wp_load` consumes the relevant
primitive law and the surrounding `wp_pures` advances past the
`let` β-reductions.

HeapLang also provides the `cmpXchg(_, _, _)` instruction. The
primitive-law lemmas `wp_cmpXchg_fail` and `wp_cmpXchg_true` cover
the two outcomes, with the choice between them dispatched by side
conditions on whether the stored value equals the test value.

```
-- TODO (upstream — iris-lean): port a `wp_cmpxchg` lemma (and a
-- matching tactic) that branches on the equality decision in a
-- single step. The current iris-lean only ships the two
-- outcome-specific lemmas `wp_cmpXchg_fail` and `wp_cmpXchg_true`.

-- Reference implementation (to port once the prerequisite lands):
--   Example cmpXchg_0_to_10 (l : loc) : expr := (CmpXchg #l #0 #10).
--   Lemma cmpXchg_0_to_10_spec (l : loc) (v : val) :
--     l ↦ v -∗
--     WP (cmpXchg_0_to_10 l) {{ u, (⌜v = #0⌝ ∗ l ↦ #10) ∨
--                                  (⌜v ≠ #0⌝ ∗ l ↦ v) }}.
--   Proof.
--     iIntros "Hl". wp_cmpxchg as H1 | H2.
--     - iLeft.  by iFrame.
--     - iRight. by iFrame.
--   Qed.
```

The points-to predicate is *not* duplicable. That is, for every
location `l`, there can only exist one full-fraction points-to
associated with it. iris-lean exposes this via the
`HeapView`-level disjointness lemmas; we omit the detailed proof.

# Composing Programs and Proofs

To compose specifications, we use `wp_bind` to focus on a
sub-expression and `wp_wand` (a generic WP lemma in
`Iris.ProgramLogic.WeakestPre`) to weaken the postcondition.

The idiomatic style is to give a *postcondition-generic*
specification — one parametric in `Φ` — that can be applied with
`iapply`. Here is that idiom applied to our `writeread` program
from the previous section.

```savedLean
theorem writeread_spec_2 (Φ : Val → IProp GF) :
    (∀ v, ⌜v = hl_val(#7)⌝ -∗ Φ v) -∗ WP writeread {{ v, Φ v }} := by
  iintro HΦ
  unfold writeread
  wp_bind ref(_)
  iapply wp_alloc
  iintro !> %l Hl
  wp_pures
  iapply wp_load $$ Hl
  iintro !> _Hl
  iapply HΦ
  itrivial
```

```
-- TODO (upstream — iris-lean): port a `wp_apply` convenience
-- tactic that combines `wp_bind` + `iapply`. The hand-written
-- composition currently used in client proofs works but is
-- more verbose than a single `wp_apply writeread_spec_2` would be.

-- Reference implementation, composing two specs (to port once the
-- prerequisite lands):
--   Lemma prog_add_2_spec'' : ⊢ WP prog + #2 {{ v, ⌜v = #5⌝ }}.
--   Proof.
--     wp_apply prog_spec_2.
--     iIntros "%w ->". wp_pure. done.
--   Qed.
```

# Hoare Triples

Having studied weakest preconditions, we shift our focus onto
another construct for specifying program behaviour: *Hoare triples*.
The weakest precondition does not explicitly specify which
conditions must hold before executing the program; it only talks
about the postcondition. Hoare triples build on weakest
preconditions by requiring us to explicitly mention the
precondition.

A Hoare triple is written `{{{ P }}} e {{{ x .. y, RET v ; Q }}}`.
It desugars to

```
□ (∀ Φ, P -∗ ▷ (∀ x .. y, Q -∗ Φ v) -∗ WP e {{ w, Φ w }})
```

iris-lean does not yet ship the `{{{ P }}} e {{{ ... }}}` sugar, so
in this port we write the desugared wand-rolled form directly. One
loss: we don't get the persistence `□` automatically; we either add
it by hand or skip it when the spec only needs to be applied once.

Consider a function that swaps two values.

```savedLean
def swap : Val := hl_val(λ x y,
  let v := !x;
  x ← !y;
  y ← v)
```

```
-- TODO (upstream — iris-lean): port the Hoare-triple notation
-- `{{{ P }}} e {{{ x .. , RET v ; Q }}}`. Until then a Hoare-
-- triple-styled specification must be written out as the
-- desugared wand-rolled WP. (The proof itself uses `wp_pures` +
-- `wp_load`/`wp_store`, all of which work today — only the
-- statement-level sugar is missing.)

-- Reference implementation (to port once the prerequisite lands):
--   Lemma swap_spec (l1 l2 : loc) (v1 v2 : val) :
--     {{{ l1 ↦ v1 ∗ l2 ↦ v2 }}}
--       swap #l1 #l2
--     {{{ RET #(); l1 ↦ v2 ∗ l2 ↦ v1 }}}.
--   Proof.
--     iIntros "%Φ [H1 H2] HΦ".
--     rewrite /swap.
--     wp_pures. wp_load. wp_load. wp_store. wp_store.
--     iApply "HΦ". by iFrame.
--   Qed.
```

A convention in Iris is to *write* specifications using Hoare
triples but *prove* them by converting them to weakest preconditions.
This convention applies equally to the iris-lean port; once the
notation lands, the chapter's `swap_spec` and `swap_swap_spec` will
translate without issue, because every primitive law they use is
already in `Iris.HeapLang.PrimitiveLaws`.

# Concurrency

We finish this chapter with a final example that illustrates how
ownership of resources can be transferred between threads. The
program forks two threads that each write to a separate location.

iris-lean's port of the `par` library
(`Iris.HeapLang.Lib.Par`) provides:

* the parallel-composition operator `e1 ‖ e2`, which runs `e1` and
  `e2` concurrently and returns the pair of their results;
* the `wp_par` lemma which lifts pairs of WP specifications for
  the two threads to a WP specification of their composition;
* the `SpawnG GF` class capturing the resources `par` needs.

```savedLean
section ParExamples
variable [Spawn.SpawnG GF]
open Iris.HeapLang.Par
```

```savedLean
def parWrite (l1 l2 : Loc) : Exp :=
  hl((v(#l1) ← #21) ‖ (v(#l2) ← #2))
```

```savedLean
theorem parWrite_spec (l1 l2 : Loc) (v1 v2 : Val) :
    l1 ↦ some v1 -∗ l2 ↦ some v2 -∗
    WP (parWrite l1 l2)
      {{ v, l1 ↦ some hl_val(#21) ∗ l2 ↦ some hl_val(#2) }} := by
  iintro Hl1 Hl2
  unfold parWrite
  iapply wp_par
      (fun _ => iprop(l1 ↦ some hl_val(#21)))
      (fun _ => iprop(l2 ↦ some hl_val(#2)))
      $$ [Hl1] [Hl2] []
  · iapply wp_store $$ Hl1
    iintro !> Hl1
    iexact Hl1
  · iapply wp_store $$ Hl2
    iintro !> Hl2
    iexact Hl2
  · iintro %v1' %v2' ⟨H1, H2⟩
    iframe
```

Each thread's WP is a separate subgoal of `iapply wp_par`. The
`$$ [Hl1] [Hl2] []` annotation explicitly partitions the spatial
context: `Hl1` goes to the first thread, `Hl2` to the second, and
the postcondition-handler subgoal receives nothing (it is closed
purely from the values returned by the two threads).

```savedLean
end ParExamples
```

A fuller `par_client` example wraps this pattern inside a larger
`let` chain that also multiplies the two final values to assert
`21 * 2 = 42`. That multiplication still depends on a `PureExec`
instance for `*` on integers, which iris-lean does not yet ship.

```
-- TODO (upstream — iris-lean): once `PureExec` for arithmetic
-- lands, restore the full `par_client` postcondition with
-- `⌜life = 42⌝`. The `wp_par`-level reasoning above is the
-- complete one — only the post-join arithmetic check is blocked.

-- Rocq tutorial reference:
--   Example par_client : expr :=
--     let: "l1" := ref #0 in
--     let: "l2" := ref #0 in
--     (("l1" <- #21) ||| ("l2" <- #2)) ;;
--     let: "life" := !"l1" * !"l2" in
--     ("l1", "l2", "life").
--   Lemma par_client_spec :
--     {{{ True }}}
--       par_client
--     {{{ l1 l2 life, RET (#l1, #l2, #life);
--         l1 ↦ #21 ∗ l2 ↦ #2 ∗ ⌜life = 42⌝ }}}.
```

```savedLean
end Specifications
```
