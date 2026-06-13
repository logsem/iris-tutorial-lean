import VersoManual
import BookGen.Meta.Lean

import Iris.HeapLang

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open BookGen
open Iris.HeapLang

set_option pp.rawOnError true

#doc (Manual) "HeapLang" =>

# Introduction

HeapLang is an untyped concurrent programming language with a heap.
It is an ML-like language, sporting many of the usual constructs such
as let expressions, lambda abstractions, and recursive functions. It
also supports higher-order functions. The evaluation order is right
to left and it is a call-by-value language.

The syntax for HeapLang is fairly standard, but there are some quirks
as we are working inside Lean. As the features of HeapLang are fairly
standard, the focus in this chapter is mainly on showcasing the
syntax of the language through simple examples.

The Lean port of HeapLang in iris-lean differs from the Rocq version
in two notable ways:

1. Expressions live in the type `Iris.HeapLang.Exp`, and are written
   inside an embedded DSL `hl( ... )` rather than via top-level
   notation. Values are inside `hl_val(...)`.
2. Variable names are still strings underneath, but you do not need
   to quote them: write `x` rather than `"x"`.

# The HeapLang Interpreter (Optional)

The Rocq port of Iris ships a rudimentary HeapLang interpreter in
`iris.unstable.heap_lang`. At the time of this writing, iris-lean
does **not** include an interpreter, so the `Compute (exec ...)`
incantations that appear in the Rocq tutorial cannot be run directly
in Lean. We still see, however, that HeapLang expressions are pieces
of syntax we can inspect with `#check`.

TODO (upstream — iris-lean): once an `exec` evaluator lands, restore
the `#eval exec 10 ...` lines that the Rocq tutorial uses to display
runtime values for each example below.

# Pure Constructs

```savedImport
import Iris.HeapLang
```

```savedLean
open Iris.HeapLang
```

```savedLean
namespace HeapLangExamples
```

HeapLang has native support for integers and booleans. With these,
we can do basic arithmetic and control flow. Note that values in
HeapLang are prefixed by a `#`.

```savedLean
def arith : Exp := hl(#1 + #2 * #3)
```

The expected result of evaluating `arith` is `7`.

```savedLean
def booleans : Exp := hl((#1 + #2 * #3 = #7) && #true || (#true = #false))
```

The expected result is `#true`.

```savedLean
-- TODO (upstream — iris-lean): use the unit literal here once the
-- `hl` DSL gains a sugared form for `Val.lit BaseLit.unit` (Rocq: `#()`).
def if_then_else : Exp := hl(if #true then #1 else #0)
```

In the Rocq version of this example, the consequent is the unit
value `#()`; iris-lean does not yet have a sugared spelling for the
unit literal, so we use an integer here instead.

HeapLang supports let expressions. Technically, let expressions are
not native to HeapLang — they are sugar for application of a lambda
to its argument. Note that variables in HeapLang are strings; in
the Lean DSL, you write them as plain identifiers, and they elaborate
to `Exp.var "x"`.

```savedLean
def lets : Exp := hl(
  let a := #4;
  let b := #2;
  a + b)
```

HeapLang has native support for pairs, with tuples being notation for
nested pairs.

```savedLean
def pairs : Exp := hl(
  let p := (#40, #1 + #1);
  fst(p) + snd(p))
```

```savedLean
def tuples : Exp := hl(
  let t1 := (#1, #2, #3, #4);
  let t2 := (((#1, #2), #3), #4);
  snd(fst(fst(t1))) = snd(fst(fst(t2))))
```

We can also do pattern matching using sums. A common use case of
sums is the *option* construction.

```savedLean
def sums : Exp := hl(
  let r := injr(#1);
  match r with
  | injl(_) => #0
  | injr(n) => n + #1
  )
```

```savedLean
def «option» : Exp := hl(
  let r := some(#1);
  match r with
  | none() => #0
  | some(n) => n + #1
  )
```

Finally, we have lambda abstractions and recursive functions. As
with let expressions, lambda abstractions are also a derived
construct — they are recursive functions that do not recurse. In
HeapLang, functions are first-class citizens, which gives support
for higher-order functions.

```savedLean
def lambda : Exp :=
  hl(let add5 := (λ x, x + #5);
     let double := (λ x, x * #2);
     let compose := (λ f g, λ x, g (f x));
     compose add5 double #5)
```

```savedLean
def recursion : Exp :=
  hl(let fac := (rec f n := if n = #0 then #1 else n * f (n - #1));
     (fac #4, fac #5))
```

# References

References are dynamically allocated through the `ref(_)` construct.
Given a value, `ref(_)` finds a fresh location on the heap and
stores the value there. The location is then returned.

```savedLean
def alloc : Exp := hl(
  let l1 := ref(#0);
  let l2 := ref(#0);
  (l1, l2))
```

After allocation, we can read and update the value at the returned
location `l` with `!l` and `l ← v`, respectively. (The Rocq port
spells the store as `l <- v`; iris-lean uses the left-arrow `←`.)

```savedLean
def load : Exp := hl(
  let l := ref(#5);
  !l)
```

```savedLean
def store : Exp := hl(
  let l := ref(#5);
  l ← #6;
  !l)
```

To allow for synchronisation between threads, HeapLang provides a
single primitive called compare-and-exchange, written
`cmpXchg(l, v1, v2)`. This instruction atomically reads the contents
of location `l`, checks if it is equal to `v1`, and, in case of
equality, updates `l` to contain `v2`. The instruction returns a
pair `(v, b)`, with `v` being the original value stored at `l`, and
`b` a boolean indicating whether the location was updated.

```savedLean
def cmpxchg_fail : Exp := hl(
  let l := ref(#5);
  cmpXchg(l, #6, #7))
```

```savedLean
def cmpxchg_suc : Exp := hl(
  let l := ref(#5);
  cmpXchg(l, #5, #7))
```

iris-lean also provides a variant of `cmpXchg` called
compare-and-set, written `cas(l, v1, v2)`. The only difference is
that `cas` only returns the boolean.

```savedLean
-- TODO (upstream — iris-lean): use the unit literal in the success
-- branches once the `hl` DSL gains a `#()` form (Rocq tutorial uses it).
def cas_example : Exp := hl(
  let l := ref(#5);
  if cas(l, #6, #7) then #0 else
    let a := !l;
    if cas(l, #5, #7) then
      let b := !l;
      (a, b)
    else
      #0)
```

The Rocq tutorial returns the unit value `#()` from the success
branches; we substitute `#0` here for the same reason as in the
`if_then_else` example above.

# Concurrency

HeapLang has only one primitive for concurrency: `fork(_)`. The
instruction `fork(e)` creates a new thread which executes `e`. The
invoking thread continues execution after creation. If the
computation of `e` terminates, then the resulting value is simply
thrown away. Hence, `e` is only run for its side effects.

```savedLean
def forkEx : Exp := hl(
  let l := ref(#5);
  fork(l ← #7);
  !l)
```

From the `fork` primitive, we can implement several other
constructions for concurrency. The Rocq version of HeapLang ships
with two such constructions, `spawn` and `par`, which are derived
from `fork`. At the time of writing, iris-lean has not yet ported
these libraries; the equivalent examples in the Rocq tutorial
(`Example spawn` and `Example par`) therefore have no direct Lean
counterpart in this chapter.

TODO (upstream — iris-lean): once the `spawn` / `par` libraries are
ported, add the two corresponding examples here. The Rocq versions
are reproduced below as reference for the port.

```
(* Rocq tutorial — to be ported once iris-lean has spawn/par *)
Example spawn_ex : expr :=
  let: "l" := ref #5 in
  let: "handle" := spawn (λ: "_", "l" <- #6;; #2) in
  let: "res" := spawn.join "handle" in
  let: "v" := !"l" in
  ("res", "v").
(* Evaluates to (2, 6). *)

Example par_ex : expr :=
  let: "l" := ref #5 in
  let: "res" := (!"l" + #1) ||| (!"l" + #2) in
  Fst "res" + Snd "res".
(* Evaluates to 13. *)
```

```savedLean
end HeapLangExamples
```
