import VersoManual
import BookGen.Meta.Lean

-- The Iris Tutorial chapters
import IrisTutorial.Basics
import IrisTutorial.Pure
import IrisTutorial.Lang
import IrisTutorial.Specifications
import IrisTutorial.Persistently
import IrisTutorial.LinkedLists
import IrisTutorial.Later
import IrisTutorial.Arrays
import IrisTutorial.GrPredicates
import IrisTutorial.ResourceAlgebra
import IrisTutorial.Invariants
import IrisTutorial.Timeless
import IrisTutorial.StructuredConc
import IrisTutorial.Counter
import IrisTutorial.SpinLock
import IrisTutorial.TicketLock
import IrisTutorial.TicketLockAdvanced
import IrisTutorial.Adequacy
import IrisTutorial.MergeSort
import IrisTutorial.CustomRa
import IrisTutorial.Ofe

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open BookGen

set_option pp.rawOnError true


#doc (Manual) "The Iris Tutorial in Lean" =>

%%%
authors := ["Lars Birkedal", "Simon Gregersen", "Mathias Adam Møller",
            "Mathias Pedersen", "Amin Timany",
            "(Lean port: Zongyuan Liu)"]
%%%

{index}[Iris]
This is a Lean port of the
[Iris tutorial](https://github.com/logsem/iris-tutorial)
originally developed at Aarhus University as a Rocq tutorial for
the [Iris separation logic framework](https://iris-project.org/).

The exposition is intended for a broad range of readers from advanced
undergraduates to PhD students and researchers. We assume that readers
are already motivated to learn Iris and thus present the material in a
bottom-up fashion, rather than starting out with cool motivating
examples. The tutorial material is intended to be self-contained. No
specific background in logic or programming languages is assumed but
some familiarity with basic programming language theory and discrete
mathematics will be beneficial. Additionally, basic knowledge of the
Lean prover is assumed; this port replaces the Rocq proofs of the
original with Lean 4 proofs against the
[iris-lean](https://github.com/leanprover-community/iris-lean) port of
Iris.

# Recommended Learning Path

To get a good understanding of the fundamental concepts of Iris, it is
recommended to study the following chapters in the given order.

{include 1 IrisTutorial.Basics}

{include 1 IrisTutorial.Pure}

{include 1 IrisTutorial.Lang}

{include 1 IrisTutorial.Specifications}

{include 1 IrisTutorial.Persistently}

{include 1 IrisTutorial.LinkedLists}

{include 1 IrisTutorial.Later}

{include 1 IrisTutorial.Arrays}

{include 1 IrisTutorial.ResourceAlgebra}

{include 1 IrisTutorial.Invariants}

{include 1 IrisTutorial.Timeless}

{include 1 IrisTutorial.StructuredConc}

{include 1 IrisTutorial.Counter}

{include 1 IrisTutorial.SpinLock}

{include 1 IrisTutorial.TicketLock}

{include 1 IrisTutorial.Adequacy}

# Additional Material

{include 1 IrisTutorial.GrPredicates}

{include 1 IrisTutorial.MergeSort}

{include 1 IrisTutorial.CustomRa}

{include 1 IrisTutorial.Ofe}

{include 1 IrisTutorial.TicketLockAdvanced}


# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
