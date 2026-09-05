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

A natural first example is a pure arithmetic expression. The
`wp_pure` and `wp_pures` tactics symbolically execute pure steps,
including integer arithmetic.

```savedLean
def arith : Exp := hl(#1 + #2 * #3 + #4 + #5)

theorem arith_spec : ⊢@{IProp GF} WP arith {{ v, ⌜v = hl_val(#16)⌝ }} := by
  unfold arith
  wp_op
  wp_pures
  itrivial
```

The same tactic also handles β-reduction and conditionals:

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

The `lambda` program from the previous chapter combines lambda
application with arithmetic:

```savedLean
def lambda : Exp :=
  hl(let add5 := (λ x, x + #5);
     let double := (λ x, x * #2);
     let compose := (λ f g, λ x, g (f x));
     compose add5 double #5)
```

```savedLean
theorem lambda_spec : ⊢@{IProp GF} WP lambda {{ v, ⌜v = hl_val(#20)⌝ }} := by
  unfold lambda
  wp_pures
  itrivial
```

Here is a higher-order example using only β-reduction:

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

which both touches the heap and performs an addition.

```savedLean
def prog : Exp := hl(
  let x := ref(#1);
  x ← !x + #2;
  !x)
```

```savedLean
theorem prog_spec : ⊢@{IProp GF} WP prog {{ v, ⌜v = hl_val(#3)⌝ }} := by
  unfold prog
  wp_alloc l with Hl
  wp_pures
  wp_load
  wp_pures
  wp_store
  wp_load
  itrivial
```

The allocation tactic names the fresh location and its points-to
hypothesis. The load and store tactics find that hypothesis in the
proof-mode context and update it as the program executes.

For comparison, here is a program that allocates and immediately reads.

```savedLean
def writeread : Exp := hl(
  let x := ref(#7);
  !x)
```

```savedLean
theorem writeread_spec :
    ⊢@{IProp GF} WP writeread {{ v, ⌜v = hl_val(#7)⌝ }} := by
  unfold writeread
  wp_alloc l with Hl
  wp_pures
  wp_load
  itrivial
```

The surrounding `wp_pures` advances past the `let` β-reductions.

HeapLang also provides `cmpXchg(_, _, _)`. The `wp_cmpxchg` tactic
creates success and failure branches and names their equality and
inequality assumptions.

```savedLean
def cmpXchg_0_to_10 (l : Loc) : Exp := hl(cmpXchg(#l, #0, #10))

theorem cmpXchg_0_to_10_spec (l : Loc) (v : Val) :
    l ↦ some v -∗ WP (cmpXchg_0_to_10 l)
      {{ _u, (⌜v = hl_val(#0)⌝ ∗ l ↦ some hl_val(#10)) ∨
             (⌜v ≠ hl_val(#0)⌝ ∗ l ↦ some v) }} := by
  iintro Hl
  unfold cmpXchg_0_to_10
  wp_cmpxchg with Heq Hne
  · change (v.isUnboxed || true) = true
    simp
  · imodintro
    ileft
    iframe
    itrivial
  · imodintro
    iright
    iframe
    itrivial
```

The points-to predicate is *not* duplicable. That is, for every
location `l`, there can only exist one full-fraction points-to
associated with it. iris-lean exposes this via the
`HeapView`-level disjointness lemmas; we omit the detailed proof.

# Composing Programs and Proofs

The tactic `wp_apply` finds the evaluation context in which a
specification applies, focuses on that sub-expression, and applies the
specification. A postcondition-generic WP lemma is one way to expose a
program's result to its caller:

```savedLean
theorem writeread_spec_2 (Φ : Val → IProp GF) :
    (∀ v, ⌜v = hl_val(#7)⌝ -∗ Φ v) -∗ WP writeread {{ v, Φ v }} := by
  iintro HΦ
  unfold writeread
  wp_alloc l with Hl
  wp_pures
  wp_load
  imodintro
  iapply HΦ
  itrivial
```

```savedLean
theorem writeread_add_2_spec :
    ⊢@{IProp GF} WP hl(&writeread + #2) {{ v, ⌜v = hl_val(#9)⌝ }} := by
  wp_apply writeread_spec_2 with %w %hw
  subst w
  wp_pures
  itrivial
```

# Hoare Triples

Having studied weakest preconditions, we shift our focus onto
another construct for specifying program behaviour: *Hoare triples*.
The weakest precondition does not explicitly specify which
conditions must hold before executing the program; it only talks
about the postcondition. Hoare triples build on weakest
preconditions by requiring us to explicitly mention the
precondition.

A Hoare triple is written `{{ P }} e {{ x .. y, RET v; Q }}`.
It desugars to

```
□ (∀ Φ, P -∗ ▷ (∀ x .. y, Q -∗ Φ v) -∗ WP e {{ w, Φ w }})
```

Inside an Iris proposition, the notation includes the outer `□`, so
triples are persistent. As a Lean theorem statement it elaborates to the
universally quantified WP rule, introduced with `iintro %Φ`.

Consider a function that swaps two values.

```savedLean
def swap : Val := hl_val(λ x y,
  let v := !x;
  x ← !y;
  y ← v)
```

```savedLean
theorem swap_spec (l1 l2 : Loc) (v1 v2 : Val) :
    {{ l1 ↦ some v1 ∗ l2 ↦ some v2 }} hl(&swap #l1 #l2)
    {{ RET hl_val(#()); l1 ↦ some v2 ∗ l2 ↦ some v1 }} := by
  iintro %Φ ⟨H1, H2⟩ HΦ
  unfold swap
  wp_pures
  wp_load
  wp_load
  wp_store
  wp_store
  imodintro
  iapply HΦ
  iframe

theorem swap_swap_spec (l1 l2 : Loc) (v1 v2 : Val) :
    {{ l1 ↦ some v1 ∗ l2 ↦ some v2 }} hl(&swap #l1 #l2; &swap #l1 #l2)
    {{ RET hl_val(#()); l1 ↦ some v1 ∗ l2 ↦ some v2 }} := by
  iintro %Φ H HΦ
  wp_apply swap_spec $$ H with ⟨H1, H2⟩
  wp_pures
  wp_apply swap_spec $$ [H1 H2] with H
  · iframe
  · iapply HΦ $$ H
```

A convention in Iris is to write reusable specifications as Hoare
triples and prove them by introducing the postcondition and executing
program steps. The second proof uses `wp_apply` to compose two calls
without unfolding `swap`.

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
      {{ _v, l1 ↦ some hl_val(#21) ∗ l2 ↦ some hl_val(#2) }} := by
  iintro Hl1 Hl2
  unfold parWrite
  wp_pures
  wp_apply wp_par
      (fun _ => iprop(l1 ↦ some hl_val(#21)))
      (fun _ => iprop(l2 ↦ some hl_val(#2)))
      $$ [Hl1] [Hl2] []
  · wp_store
    itrivial
  · wp_store
    itrivial
  · iintro %v1' %v2' ⟨H1, H2⟩
    iframe
```

Each thread's WP is a separate subgoal of `iapply wp_par`. The
`$$ [Hl1] [Hl2] []` annotation explicitly partitions the spatial
context: `Hl1` goes to the first thread, `Hl2` to the second, and
the postcondition-handler subgoal receives nothing (it is closed
purely from the values returned by the two threads).

A larger client allocates both locations, runs the writes in parallel,
and multiplies the final values. Its triple returns both locations and
the computed integer, together with ownership of the final heap.

```savedLean
def par_client : Exp := hl%
  let l1 := ref(#0);
  let l2 := ref(#0);
  ((l1 ← #21) ‖ (l2 ← #2));
  let life := !l1 * !l2;
  (l1, l2, life)

theorem par_client_spec :
    {{ True }} par_client
    {{ (l1 l2 : Loc) (life : Int), RET hl_val((#l1, #l2, #life));
       l1 ↦ some hl_val(#21) ∗ l2 ↦ some hl_val(#2) ∗ ⌜life = 42⌝ }} := by
  iintro %Φ - HΦ
  unfold par_client
  wp_alloc l1 with Hl1
  wp_pures
  wp_alloc l2 with Hl2
  wp_pures
  wp_apply wp_par (fun _ => l1 ↦ some hl_val(#21))
      (fun _ => l2 ↦ some hl_val(#2)) $$ [Hl1] [Hl2] [HΦ]
  · wp_store; itrivial
  · wp_store; itrivial
  · iintro %r1 %r2 ⟨Hl1, Hl2⟩
    inext
    wp_pures
    wp_load
    wp_load
    wp_pures
    imodintro
    iapply HΦ
    iframe
    itrivial

end ParExamples
```

```savedLean
end Specifications
```
