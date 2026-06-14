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
Hoare triples and persistent points-to predicates. The points-to
part we can cover here; the Hoare-triples part depends on an
upstream gap.

## Hoare Triples

All Hoare triples are persistent. This is because Hoare triples in
Iris are defined as

```
□ (∀ Φ, P -∗ ▷ (∀ x .. y, Q -∗ Φ v) -∗ WP e {{ w, Φ w }})
```

— with an outermost `□`, so Hoare triples can be duplicated and
reused. Intuitively, a Hoare triple `{{{ P }}} e {{{ Φ }}}` does
not claim ownership of any resources; it merely states that *if*
we own the resources described by `P`, then we can safely run `e`,
and we get the resources described by `Φ` if it terminates. If we
can get ownership of those resources multiple times, we should be
able to run `e` multiple times.

```
-- TODO (upstream — iris-lean): the example below relies on the
-- Hoare-triple notation `{{{ P }}} e {{{ ... }}}` (missing) and
-- on a `wp_apply` convenience tactic (also missing).

-- Reference implementation (to port once the prerequisites land):
--   Example counter (inc : val) : expr :=
--     let: "c" := ref #0 in
--     inc "c" ;; inc "c" ;; !"c".
--
--   Lemma counter_spec (inc : val) :
--     {{{ ∀ (l : loc) (z : Z),
--           {{{ l ↦ #z }}} inc #l {{{ v, RET v; l ↦ #(z + 1) }}} }}}
--       counter inc
--     {{{ v, RET v; ⌜v = #2⌝ }}}.
--   Proof.
--     iIntros (Φ) "#Hinc_spec HΦ".
--     rewrite /counter.
--     wp_alloc l as "Hl". wp_let.
--     wp_apply ("Hinc_spec" with "Hl"). iIntros (v) "Hl". wp_seq.
--     wp_apply ("Hinc_spec" with "Hl"). iIntros (v') "Hl". wp_seq.
--     wp_load. by iApply "HΦ".
--   Qed.
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

```
-- TODO (upstream — iris-lean): the proof below uses `pt_split`
-- with a fractional points-to. In iris-lean the spelling is
-- `l ↦{.own (1/2)} v` and the `iCombine`/`iDestruct` automation
-- for fractional splits is still maturing. The point is that
-- `pointsto_fractional` / `pointsto_combine` already exist as
-- lemmas (see `Iris.BI.Lib.GenHeap`); an ergonomic version awaits
-- the iris-lean `iCombine` and fractional-pattern tactics.

-- Reference implementation (to port once the prerequisites land):
--   Lemma pt_split l v : l ↦ v ⊣⊢ (l ↦{# 1/2 } v) ∗ (l ↦{# 1/2 } v).
--   Proof.
--     iSplit.
--     - iIntros "Hl".
--       iDestruct "Hl" as "[Hl1 Hl2]".
--       iFrame.
--     - iIntros "[Hl1 Hl2]".
--       iCombine "Hl1" "Hl2" as "Hl".
--       iFrame.
--   Qed.
```

Crucially, a store operation can only take place if the *entire*
fraction is owned, i.e. `dq = .own 1`. However, load operations
can occur for any fraction. Fractional points-to predicates are
especially useful in scenarios where a location is read by
multiple threads in parallel but later only used by a single
thread.

```
-- TODO (upstream — iris-lean): `par_read_write` requires
-- ergonomic fractional-points-to manipulation (splitting `l ↦ v`
-- into `l ↦{.own (1/2)} v ∗ l ↦{.own (1/2)} v` and recombining
-- after the parallel composition). The underlying lemmas
-- (`pointsto_fractional`, `pointsto_combine`) are present in
-- `Iris.BI.Lib.GenHeap`, but `iCombine`-style automation is not
-- yet there. `wp_par` itself works fine (see Specifications
-- chapter); the missing piece is the fractional bookkeeping.

-- Reference implementation (to port once the prerequisites land):
--   Example par_read_write (l : loc) : expr :=
--     let: "r" := (!#l ||| !#l) in
--     #l <- #5.
--   Lemma par_read_write_spec (l : loc) (v : val) :
--     {{{ l ↦ v }}}
--       par_read_write l
--     {{{ RET #(); l ↦ #5 }}}.
--   Proof. ... uses (wp_par t_post t_post) ... Qed.
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
  imod pointsTo_persist $$ Hl with Hl'
  iapply wp_load $$ Hl'
  iintro !> Hl'
  iframe
  itrivial
```

Note: iris-lean does not yet register `Persistent (l ↦{.discard} v)`
as an instance, so a discarded points-to cannot be moved into the
intuitionistic context with `#`. The lemmas treat `↦{.discard}` as
a (duplicable, but spatially-managed) hypothesis. Once the
`Persistent` instance lands, the proof above will be eligible for
the cleaner `imod ... with #Hl'` pattern.

As a more elaborate example, here is a parallel program where two
threads both read from the *same* location. The key idea is that
once the points-to is made *persistent* (`↦{.discard}`), it can be
shared across both threads. (We keep the example to a plain read;
wrapping the result in arithmetic is not possible here because
iris-lean still lacks `PureExec` for `+` / `*`.)

```savedLean
section ParRead
variable [Spawn.SpawnG GF]
open Iris.HeapLang.Par

def parRead (l : Loc) : Exp := hl((!v(#l)) ‖ (!v(#l)))

theorem parRead_spec (l : Loc) (v : Val) :
    l ↦{.discard} some v ∗ l ↦{.discard} some v -∗
    WP (parRead l) {{ w, ⌜w = hl_val((&v, &v))⌝ }} := by
  iintro ⟨Hl1, Hl2⟩
  unfold parRead
  iapply wp_par
      (fun w => iprop(⌜w = v⌝))
      (fun w => iprop(⌜w = v⌝))
      $$ [Hl1] [Hl2] []
  · iapply wp_load $$ Hl1
    iintro !> _Hl
    itrivial
  · iapply wp_load $$ Hl2
    iintro !> _Hl
    itrivial
  · iintro %w1 %w2 ⟨%H1, %H2⟩
    subst H1; subst H2
    itrivial
end ParRead
```

Ideally we would write the precondition as a single
`l ↦{.discard} some v` and let iris-lean duplicate it across both
threads automatically. That requires registering a
`Persistent (l ↦{.discard} v)` instance — see TODO below.

```
-- TODO (upstream — iris-lean): register a
-- `Persistent (l ↦{DFrac.discard} v)` instance in
-- `Iris.BI.Lib.GenHeap`. Once registered, the `parRead_spec`
-- proof above can be tightened so the caller passes a single
-- discarded points-to and iris-lean splits it automatically.

-- Reference implementation, full version with arithmetic
-- (to port once the prerequisites land):
--   Example par_read : expr :=
--     let: "l" := ref #7 in
--     let: "r" := ( (!"l" + #14) ||| (!"l" * #3) ) in
--     Fst "r" + Snd "r".
--   Lemma par_read_spec :
--     {{{ True }}} par_read {{{ v, RET v; ⌜v = #42⌝ }}}.
```

```
-- TODO (upstream — iris-lean): once `PureExec` for arithmetic
-- lands, restore the full `par_read` example with its
-- `21 * 2 = 42` postcondition.

-- Reference implementation (to port once the prerequisites land):
--   Example par_read : expr :=
--     let: "l" := ref #7 in
--     let: "r" := ( (!"l" + #14) ||| (!"l" * #3) ) in
--     Fst "r" + Snd "r".
--   Lemma par_read_spec :
--     {{{ True }}} par_read {{{ v, RET v; ⌜v = #42⌝ }}}.
```

```savedLean
end Persistently
```
