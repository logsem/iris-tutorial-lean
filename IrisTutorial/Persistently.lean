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

#doc (Manual) "The Persistently Modality" =>

# Introduction

In separation logic, propositions are generally not duplicable.
This is because resources are generally exclusive. However,
resources do not _have_ to be exclusive. A great example of this
is *read-only memory*. There is no danger in letting many threads
access the same location simultaneously if they can only read from
it. Hence, it would not make sense to require that ownership of
those locations be exclusive. Motivated by this, we introduce a
new modality denoted the *persistently* modality, written `□ P`,
for propositions `P`. The proposition `□ P` describes the same
resources as `P`, except it does not claim that the resources are
exclusive — hence `□ P` can be duplicated. Persistent propositions
hence act like propositions in an intuitionistic logic, which is
why iris-lean's proof mode also refers to the corresponding
context as the *intuitionistic context*.

A proposition is persistent when `P ⊢ □ P`. That is, assuming
`P`, we need to show that `P` does not rely on any exclusive
resources. Persistency is preserved by most connectives, so proving
that a proposition is persistent is usually a matter of showing
that the mentioned resources are shareable. Which resources are
shareable depends on the specific notions of resources being used.
For the resource of heaps, a location can be marked as read-only,
making it shareable. The associated points-to predicate hence
becomes persistent. We will see an example of this later.

Propositions that do not rely on resources altogether are trivially
persistent. We have already given those types of propositions a
name: *pure*. This is also why we do not have to split the
non-spatial context when using `isplitl`/`isplitr`; all pure
propositions are persistent, hence duplicable.

Of course, not all persistent propositions are pure (e.g.
persistent points-to predicates). Thus, the Iris Proof Mode
provides a third context just for persistent propositions, called
the *intuitionistic* context. Pure propositions can go in all
three contexts. Persistent propositions can go in the spatial or
intuitionistic context. And all other propositions are limited to
the spatial context only. iris-lean uses the typeclass
`Iris.BI.Persistent` to identify persistent propositions.

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
namespace Persistently
variable {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]
```

The cases pattern `#H` moves a persistent hypothesis into the
intuitionistic context.

```savedLean
theorem pers_context (P Q : IProp GF) [Persistent P] :
    P -∗ Q -∗ P ∗ Q := by
  iintro #HP HQ
  isplitr [HQ]
  · iexact HP
  · iexact HQ
```

The intuitionistic context is shared across both subgoals of an
`isplitl`/`isplitr`: `HP` remains available after the split.

By contrast, putting `HP` into the spatial context discards
persistency:

```savedLean
theorem not_in_pers_context (P Q : IProp GF) [Persistent P] :
    P -∗ Q -∗ P ∗ Q := by
  iintro HP HQ
  isplitr [HQ]
  · iexact HP
  · iexact HQ
```

Persistent propositions are duplicable.

```savedLean
theorem pers_dup (P : IProp GF) [Persistent P] : P ⊢ P ∗ P := by
  iintro #HP
  isplit
  · iexact HP
  · iexact HP
```

Persistent propositions satisfy several nice properties simply by
being duplicable (`P ⊢ P ∗ P`). For example, `P ∧ Q` and `P ∗ Q`
coincide when either `P` or `Q` is persistent; likewise, `P → Q`
and `P -∗ Q` coincide when `P` is persistent. The relevant iris-
lean lemmas are `Iris.BI.persistent_and_sep` and
`Iris.BI.impl_wand`.

The Iris Proof Mode knows these facts and allows `isplit` to
introduce `∗` when one of its arguments is persistent.

# Proving Persistency

To prove a proposition `□ P`, we must prove `P` without assuming
any exclusive resources. In other words, we have to throw away the
spatial context when proving `P`.

```savedLean
theorem pers_intro (P Q : IProp GF) [Persistent P] :
    P ∗ Q ⊢ □ P := by
  iintro ⟨#HP, _HQ⟩
  imodintro
  iexact HP
```

The `imodintro` tactic introduces a modality in the goal. In this
case, since the modality is a `□`, it throws away the spatial
context.

Since the only difference between `□ P` and `P` is that the former
does not claim the resources are exclusive, it follows that the
persistently modality is idempotent.

```savedLean
theorem pers_idemp (P : IProp GF) : □ □ P ⊣⊢ □ P := by
  isplit
  · iintro #HP
    -- Iris already knows that `□` is idempotent, so it
    -- automatically removes all persistently modalities from a
    -- proposition when adding it to the intuitionistic context.
    -- One may think of all propositions in the intuitionistic
    -- context as having an implicit `□` in front.
    iexact HP
  · iintro #HP
    imodintro
    iexact HP
```

Only propositions that are instances of the `Persistent` typeclass
can be added to the intuitionistic context. As with the typeclasses
for pure propositions, `Persistent` can automatically identify
most persistent propositions.

```savedLean
theorem pers_sep (P Q : IProp GF) : □ P ∗ □ Q ⊣⊢ □ (P ∗ Q) := by
  isplit
  · iintro ⟨#HP, #HQ⟩
    imodintro
    iframe HP HQ
  · iintro #⟨HP, HQ⟩
    iframe HP HQ
```

Note the intuitionistic-pattern variant `#⟨HP, HQ⟩` that destructs
a persistent separation directly in the cases pattern.

Persistency is preserved by quantifications.

```savedLean
theorem pers_all {α : Type} (P : α → IProp GF) [∀ x, Persistent (P x)] :
    (∀ x, □ P x) ⊢ ∀ y, P y ∗ P y := by
  iintro #Hp %y
  isplitl
  · iapply Hp
  · iapply Hp
```

For simple predicates such as the one below, Lean's typeclass
resolution can automatically infer the `Persistent` instance.

```savedLean
def myPredicate (x : Val) : IProp GF := iprop(⌜x = hl_val(#5)⌝)

instance myPredicate_persistent (x : Val) :
    Persistent (myPredicate (GF := GF) x) := by
  unfold myPredicate
  infer_instance
```

For more complicated predicates, such as ones defined as a
fixpoint, the `Persistent` instance cannot be inferred
automatically. The following predicate asserts that all values in
a given list are equal to `hl_val(#5)`.

```savedLean
def myPredFix : List Val → IProp GF
  | []       => iprop(True)
  | x :: xs' => iprop(⌜x = hl_val(#5)⌝ ∗ myPredFix xs')
```

Adding such a predicate to the intuitionistic context requires us
to register a `Persistent` instance manually, by induction on the
list.

```savedLean
instance myPredFix_persistent (xs : List Val) :
    Persistent (myPredFix (GF := GF) xs) := by
  induction xs with
  | nil =>
      unfold myPredFix; infer_instance
  | cons x xs' ih =>
      unfold myPredFix; infer_instance
```

With the instance in place, iris-lean now recognises `myPredFix`
as persistent.

```savedLean
theorem first_is_5 (x : Val) (xs : List Val) :
    myPredFix (GF := GF) (x :: xs) -∗
    ⌜x = hl_val(#5)⌝ ∗ myPredFix (x :: xs) := by
  -- After `iintro #H`, the hypothesis `H : myPredFix (x :: xs)`
  -- sits in the intuitionistic context. Since `myPredFix` unfolds
  -- by pattern-matching, we can `change` the hypothesis-to-be so
  -- the destructure exposes the head element.
  show myPredFix (GF := GF) (x :: xs) -∗
       iprop(⌜x = hl_val(#5)⌝ ∗ myPredFix (x :: xs))
  change iprop(⌜x = hl_val(#5)⌝ ∗ myPredFix xs) -∗
         iprop(⌜x = hl_val(#5)⌝ ∗
               (iprop(⌜x = hl_val(#5)⌝ ∗ myPredFix xs)))
  iintro #⟨Hx, Hxs⟩
  iframe Hx Hxs
```

# Examples of Persistent Propositions

Thus far, the only basic persistent propositions we have seen are
pure propositions, such as equalities. Two further examples are
Hoare triples and persistent points-to predicates.

## Hoare Triples

All Hoare triples are persistent. This is because Hoare triples in
Iris are defined as

```
□ (∀ Φ, P -∗ ▷ (∀ x .. y, Q -∗ Φ v) -∗ WP e {{ w, Φ w }})
```

— with an outermost `□`, so Hoare triples can be duplicated and
reused. Intuitively, a Hoare triple `{{ P }} e {{ v, RET v; Φ v }}` does
not claim ownership of any resources; it merely states that *if*
we own the resources described by `P`, then we can safely run `e`,
and we get the resources described by `Φ` if it terminates. If we
can get ownership of those resources multiple times, we should be
able to run `e` multiple times.

Here the client calls an unknown increment function twice. Its
specification is persistent, so both calls can use the same `Hinc`
hypothesis while passing ownership of the counter from one call to the
next.

```savedLean
def counter (inc : Val) : Exp := hl%
  let c := ref(#0);
  &inc c;
  &inc c;
  !c

theorem counter_spec (inc : Val) :
    {{ ∀ (l : Loc) (z : Int),
       {{ l ↦ some hl_val(#z) }} hl(&inc #l)
       {{ v, RET v; l ↦ some hl_val(#(z + 1 : Int)) }} }}
      (counter inc)
    {{ v, RET v; ⌜v = hl_val(#2)⌝ }} := by
  iintro %Φ #Hinc HΦ
  unfold counter
  wp_alloc l with Hl
  wp_pures
  wp_apply Hinc $$ Hl with %v Hl
  wp_pures
  wp_apply Hinc $$ Hl with %v' Hl
  wp_pures
  wp_load
  imodintro
  iapply HΦ
  itrivial
```

## Persistent Points-to

The resource of heaps is more sophisticated than what we have been
letting on. The general shape of a points-to predicate is actually
`l ↦{dq} v`, where `dq` is a *discarded fraction*
(iris-lean's `DFrac`: either `.own q` for a real fraction
`q ∈ (0,1]`, or `.discard` for the persistent variant). The
predicate `l ↦ v` is shorthand for `l ↦{DFrac.own 1} v`. The basic
idea is that points-to predicates can be split up and recombined,
allowing ownership of points-to predicates to be shared. iris-lean
provides this through the `Fractional` / `AsFractional`
typeclasses.

The proof mode can split a full points-to into two halves and combine
them again. `icombine` adds their fractions:

```savedLean
theorem pt_split (l : Loc) (v : Val) :
    l ↦ some v ⊣⊢@{IProp GF}
      l ↦{.own (1 : Qp).half} some v ∗ l ↦{.own (1 : Qp).half} some v := by
  isplit
  · iintro ⟨Hl1, Hl2⟩
    iframe
  · iintro ⟨Hl1, Hl2⟩
    icombine Hl1 Hl2 as Hl
    iexact Hl
```

Crucially, a store operation can only take place if the *entire*
fraction is owned, i.e. `dq = .own 1`. However, load operations
can occur for any fraction. Fractional points-to predicates are
especially useful in scenarios where a location is read by
multiple threads in parallel but later only used by a single
thread.

This allows two threads to read a location before the parent thread
recovers full ownership and writes to it.

```savedLean
section ParReadWrite
variable [Spawn.SpawnG GF]
open Iris.HeapLang.Par

def par_read_write (l : Loc) : Exp := hl%
  let r := (!#l ‖ !#l);
  #l ← #5

theorem par_read_write_spec (l : Loc) (v : Val) :
    {{ l ↦ some v }} (par_read_write l)
    {{ RET hl_val(#()); l ↦ some hl_val(#5) }} := by
  iintro %Φ Hl HΦ
  icases pt_split $$ Hl with ⟨Hl1, Hl2⟩
  unfold par_read_write
  wp_pures
  wp_apply wp_par (fun _ => l ↦{.own (1 : Qp).half} some v)
      (fun _ => l ↦{.own (1 : Qp).half} some v) $$ [Hl1] [Hl2] [HΦ]
  · wp_load; imodintro; iexact Hl1
  · wp_load; imodintro; iexact Hl2
  · iintro %r1 %r2 ⟨Hl1, Hl2⟩
    inext
    icombine Hl1 Hl2 as Hl
    wp_pures
    wp_store
    imodintro
    iapply HΦ $$ Hl

end ParReadWrite
```

If one owns a fraction of a points-to predicate, one can decide to
*discard* the fraction. This means that it is no longer possible
to recombine points-to predicates to get the full fraction. As
such, the value in the points-to predicate can never be changed
again — the location has become read-only. The persistent
points-to is written `l ↦{.discard} v`. It is persistent.

The lemma that makes a points-to persistent is
`Iris.pointsTo_persist`:

```
⊢@{IProp GF} l ↦{dq} v ==∗ l ↦{.discard} v
```

There are some caveats as to when we can discard fractions; the
proposition `P ==∗ Q` is equivalent to `P -∗ |==> Q`, where `|==>`
is the *update* modality. The `imod` tactic can usually remove
this modality, e.g. when the goal is a weakest precondition.

```savedLean
theorem pt_persist (l : Loc) (v : Val) :
    l ↦ some v -∗
    WP hl(!v(#l))
      {{ w, ⌜w = v⌝ ∗ l ↦{.discard} some v }} := by
  iintro Hl
  imod pointsTo_persist $$ Hl with #Hl'
  wp_load
  imodintro
  iframe Hl'
  itrivial
```

The discarded points-to is persistent, so `#Hl'` moves it into the
intuitionistic context. The chapter's final example allocates a location,
makes it persistent, and shares it between two arithmetic computations.

```savedLean
section ParRead
variable [Spawn.SpawnG GF]
open Iris.HeapLang.Par

def par_read : Exp := hl%
  let l := ref(#7);
  let r := (!l + #14 ‖ !l * #3);
  fst(r) + snd(r)

theorem par_read_spec :
    {{ (True : IProp GF) }} par_read
    {{ v, RET v; ⌜v = hl_val(#42)⌝ }} := by
  iintro %Φ - HΦ
  unfold par_read
  wp_alloc l with Hl
  imod pointsTo_persist $$ Hl with #Hl
  wp_pures
  wp_apply wp_par
      (fun w => iprop(⌜w = hl_val(#21)⌝))
      (fun w => iprop(⌜w = hl_val(#21)⌝))
      $$ [] [] [HΦ]
  · wp_load
    wp_pures
    itrivial
  · wp_load
    wp_pures
    itrivial
  · iintro %w1 %w2 ⟨%H1, %H2⟩
    subst H1; subst H2
    inext
    wp_pures
    imodintro
    iapply HΦ
    itrivial
end ParRead
```

Both threads access the same intuitionistic hypothesis `Hl`. Their
postconditions establish `7 + 14 = 21` and `7 * 3 = 21`; after the
join, the final pure steps establish `21 + 21 = 42`.

```savedLean
end Persistently
```
