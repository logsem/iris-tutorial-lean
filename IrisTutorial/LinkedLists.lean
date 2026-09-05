import VersoManual
import BookGen.Meta.Lean

import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.HeapLang
import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.ProofMode

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open BookGen
open Iris Iris.BI Iris.HeapLang

set_option pp.rawOnError true

#doc (Manual) "Linked Lists" =>

# Introduction

In this chapter, we study several functions on linked lists. To do
this, we must first agree on what a linked list is. In HeapLang, we
can implement linked lists as chains of pointers. We define this
formally with a predicate, which we denote `isList`. This predicate
turns a list of values `xs` into a predicate describing the structure
of the linked list in the heap.

```savedImport
import Iris.BI
import Iris.ProofMode
import Iris.Instances.IProp
import Iris.HeapLang
import Iris.HeapLang.PrimitiveLaws
import Iris.HeapLang.ProofMode
```

```savedLean
open Iris Iris.BI Iris.HeapLang
```

```savedLean
namespace LinkedLists
variable {hlc} {GF : BundledGFunctors} [HeapLangGS hlc GF]
```

A linked list is either empty — represented by the value `none()` — or
a pointer to a node. A node is a location `hd` storing a pair
`(x, l')`: the head value `x` and the rest of the list `l'`. We capture
this as a predicate defined by recursion on the Lean-level list `xs` of
values it represents.

```savedLean
def isList (l : Val) : List Val → IProp GF
  | [] => iprop% ⌜l = hl_val(none())⌝
  | x :: xs => iprop% ∃ hd l', ⌜l = hl_val(some(#(.loc hd)))⌝ ∗
      hd ↦ some hl_val((&x, &l')) ∗ isList l' xs
```

Because `isList` is defined by pattern matching, the two cases hold
definitionally. We record them as proof-mode lemmas, which lets us
unfold and refold the predicate during proofs.

```savedLean
theorem isList_nil {l} :
    isList (GF := GF) l [] ⊣⊢ iprop(⌜l = hl_val(none())⌝) := .rfl
```

```savedLean
theorem isList_cons {l x xs} :
    isList (GF := GF) l (x :: xs) ⊣⊢
      iprop(∃ hd l', ⌜l = hl_val(some(#(.loc hd)))⌝ ∗
        hd ↦ some hl_val((&x, &l')) ∗ isList l' xs) := .rfl
```

Here `some(_)` / `none()` are the value-level injections, and
`#(.loc hd)` turns a heap location `hd : Loc` into a HeapLang value.

# Append

The `append` function recursively descends `l1`, updating the links in
place. Eventually it reaches the tail `none()`, where it returns `l2`.

```savedLean
def append : Val := hl_val%
  rec append l1 l2 :=
    match l1 with
    | none() => l2
    | some(hd) =>
        let x := fst(!hd);
        let l1' := snd(!hd);
        let r := append l1' l2;
        hd ← (x, r);
        some(hd)
```

If `l1` and `l2` represent the lists `xs` and `ys` respectively, then
`append l1 l2` returns a list representing `xs ++ ys`.

Following the convention from the specifications chapter, we state the
specification as a Hoare triple and use `wp_apply` at recursive calls.

```savedLean
theorem append_spec (l1 l2 : Val) (xs ys : List Val) :
    {{ isList (GF := GF) l1 xs ∗ isList l2 ys }} hl(&append &l1 &l2)
    {{ v, RET v; isList v (xs ++ ys) }} := by
  iintro %Φ ⟨Hl1, Hl2⟩ HΦ
  iloeb as IH generalizing %l1 %xs %Φ
  wp_bind (&append _)
  wp_rec
  cases xs with
  | nil =>
    icases isList_nil $$ Hl1 with %heq; subst heq
    wp_pures; imodintro
    simp only [List.nil_append]
    iapply HΦ $$ Hl2
  | cons x xs =>
    icases isList_cons $$ Hl1 with ⟨%hd, %l', %heq, Hpt, Hl⟩
    subst heq; wp_pures
    wp_load
    wp_pures
    wp_load
    wp_pures
    wp_apply IH $$ Hl Hl2 with %r Hr
    wp_pures
    wp_store
    wp_pures
    imodintro
    iapply HΦ
    simp only [List.cons_append]
    rw [isList]
    iexists hd, r
    iframe
    itrivial
```

The proof proceeds by Löb induction (`iloeb`), generalising over `l1`,
`xs`, and `Φ` so the induction hypothesis `IH` is strong enough for the
recursive call. The curried recursive function is stepped with
`wp_bind (&append _)` followed by `wp_rec`, which unfolds one call and
β-reduces past the first argument. At the recursive call we focus the
sub-expression with `wp_apply IH`, which also applies the induction hypothesis.

# Reverse

We implement `reverse` using a helper, `reverse_append`, which takes
`l` and `acc` and returns the list `rev l ++ acc` — reversing `l` onto
the front of `acc` by re-threading the existing nodes.

```savedLean
def reverse_append : Val := hl_val%
  rec reverse_append l acc :=
    match l with
    | none() => acc
    | some(hd) =>
        let x := fst(!hd);
        let l' := snd(!hd);
        hd ← (x, acc);
        reverse_append l' (some(hd))
```

```savedLean
def reverse : Val := hl_val%
  λ l, &reverse_append l (none())
```

The specification of the helper threads the accumulator through the
induction. Unlike `append`, the accumulator `acc` and its list `ys`
change on every recursive call, so we generalise over them too.

```savedLean
theorem reverse_append_spec (l acc : Val) (xs ys : List Val) :
    {{ isList (GF := GF) l xs ∗ isList acc ys }} hl(&reverse_append &l &acc)
    {{ v, RET v; isList v (xs.reverse ++ ys) }} := by
  iintro %Φ ⟨Hl, Hacc⟩ HΦ
  iloeb as IH generalizing %l %acc %xs %ys %Φ
  wp_bind (&reverse_append _)
  wp_rec
  cases xs with
  | nil =>
    icases isList_nil $$ Hl with %heq; subst heq
    wp_pures; imodintro
    simp only [List.reverse_nil, List.nil_append]
    iapply HΦ $$ Hacc
  | cons x xs =>
    icases isList_cons $$ Hl with ⟨%hd, %l', %heq, Hpt, Hl⟩
    subst heq; wp_pures
    wp_load
    wp_pures
    wp_load
    wp_pures
    wp_store
    wp_pures
    ihave Hnode : isList hl_val(some(#(.loc hd))) (x :: ys) $$ [Hpt Hacc]
    · rw [isList]
      iexists hd, acc
      iframe
      itrivial
    wp_apply IH $$ Hl Hnode with %v Hv
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    iapply HΦ $$ Hv
```

Now we use the helper's specification to prove `reverse`. The empty
accumulator represents the empty list, so `reverse l` returns the
reverse of `l`.

```savedLean
theorem reverse_spec (l : Val) (xs : List Val) :
    {{ isList (GF := GF) l xs }} hl(&reverse &l)
    {{ v, RET v; isList v xs.reverse }} := by
  iintro %Φ Hl HΦ
  wp_rec
  wp_pures
  ihave Hacc : isList hl_val(none()) ([] : List Val) $$ []
  · iapply isList_nil
    itrivial
  wp_apply reverse_append_spec $$ [Hl Hacc] with %v Hv
  · iframe
  · simp only [List.append_nil]
    iapply HΦ $$ Hv
```

# Folding Over a List

The specifications so far have been rather concrete. Now we give a very
general specification for `fold_right`.

```savedLean
def fold_right : Val := hl_val%
  rec fold_right f v l :=
    match l with
    | none() => v
    | some(hd) =>
        let x := fst(!hd);
        let l' := snd(!hd);
        f x (fold_right f v l')
```

The specification has many moving parts, so let us go through them.

* `l` is a linked list representing `xs`, as stated by `isList l xs` in
  the precondition.
* `P` is a predicate that all values in `xs` should satisfy, written as
  the big separating conjunction `[∗list] _k ↦ x ∈ xs, P x` (the index
  `_k` is unused here).
* `I` (think *invariant*) relates a list to the result of the fold; the
  base value satisfies `I [] a`.
* `f` is the folding function, assumed to satisfy a (persistent)
  Hoare triple: given `P x` and `I ys a'`, the
  call `f x a'` returns `r` with `I (x :: ys) r`.
* The result `r` of the whole fold satisfies `I xs r`.
* Importantly, the original list is left unchanged, so `isList l xs`
  reappears in the postcondition.

The assumption for `f` is a family of Hoare triples. These are persistent,
so `#Hf` can be reused at every step of the induction.

```savedLean
theorem fold_right_spec
    (P : Val → IProp GF) (I : List Val → Val → IProp GF) (f a l : Val) (xs : List Val) :
    (∀ (x a' : Val) ys,
      {{ P x ∗ I ys a' }} hl(&f &x &a') {{ r, RET r; I (x :: ys) r }}) -∗
    {{ isList (GF := GF) l xs ∗ ([∗list] _k ↦ x ∈ xs, P x) ∗ I [] a }}
      hl(&fold_right &f &a &l)
    {{ r, RET r; isList l xs ∗ I xs r }} := by
  iintro #Hf !> %Φ ⟨Hl, HP, HI⟩ HΦ
  iloeb as IH generalizing %l %a %xs %Φ
  wp_bind (&fold_right _)
  wp_rec
  cases xs with
  | nil =>
    icases isList_nil $$ Hl with %heq; subst heq
    wp_pures; imodintro
    iapply HΦ
    iframe HI
    iapply isList_nil
    itrivial
  | cons x xs =>
    icases isList_cons $$ Hl with ⟨%hd, %l', %heq, Hpt, Hl⟩
    subst heq
    icases BI.BigSepL.bigSepL_cons $$ HP with ⟨HP0, HPs⟩
    wp_pures
    wp_load
    wp_pures
    wp_load
    wp_pures
    wp_apply IH $$ Hl HPs HI with %r ⟨Hl, Hr⟩
    wp_apply Hf $$ [HP0 Hr] with %r' Hr'
    · iframe
    · iapply HΦ
      iframe Hr'
      rw [isList]
      iexists hd, l'
      iframe
      itrivial
```

# Arithmetic-dependent specifications

Two further functions on lists are worth defining: `inc`, which
increments every element in place, and `sum_list`, which sums a list by
folding addition over it.

```savedLean
def inc : Val := hl_val%
  rec inc l :=
    match l with
    | none() => #0
    | some(hd) =>
        let x := fst(!hd);
        let l' := snd(!hd);
        hd ← (x + #1, l');
        inc l'
```

```savedLean
def sum_list : Val := hl_val%
  λ l,
    let f := (λ x y, x + y);
    &fold_right f #0 l
```

Both functions use integer arithmetic, which `wp_pures` can execute.
As further exercises, specify and prove that `inc` increments every
integer in the list and that `sum_list` returns their sum. The
load/store and fold specifications above provide the building blocks.

```savedLean
end LinkedLists
```
