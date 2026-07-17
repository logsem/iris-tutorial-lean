/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Zongyuan Liu
-/

import Std.Data.HashMap
import VersoManual
import IrisTutorialBook

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open BookGen


-- Computes the path of this very `main`, to ensure that examples get names relative to it
open Lean Elab Term Command in
#eval show CommandElabM Unit from do
  let here := (← liftTermElabM (readThe Lean.Core.Context)).fileName
  elabCommand (← `(private def $(mkIdent `mainFileName) : System.FilePath := $(quote here)))

/--
Extract the marked exercises and example code.
-/
partial def buildExercises (mode : Mode) (cfg : Config) (_state : TraverseState) (text : Part Manual) : BuildLogT IO Unit := do
  let .multi := mode
    | pure ()
  let logger ← readThe (Logger IO)
  saveExampleCode logger cfg text

where
  saveExampleCode (logger : Verso.Logger IO) (cfg : Config) (text : Part Manual) : IO Unit := do
    let code := (← part logger text |>.run {}).snd
    let dest := cfg.destination / "example-code"
    let some mainDir := mainFileName.parent
      | throw <| IO.userError "Can't find directory of `BookGenMain.lean`"

    IO.FS.createDirAll <| dest
    for ⟨fn, f⟩ in code do
      -- Make sure the path is relative to that of this one
      if let some fn' := fn.dropPrefix? mainDir.toString then
        let fn' := fn'.toString.dropWhile (· ∈ System.FilePath.pathSeparators : Char → Bool)
        let fn := dest / fn'.copy
        fn.parent.forM IO.FS.createDirAll
        if (← fn.pathExists) then IO.FS.removeFile fn
        IO.FS.writeFile fn f
      else
        logger.reportError s!"Couldn't save example code. The path '{fn}' is not underneath '{mainDir}'."
  part (logger : Verso.Logger IO) : Part Manual → StateT (HashMap String String) IO Unit
    | .mk _ _ _ intro subParts => do
      for b in intro do block logger b
      for p in subParts do part logger p
  block (logger : Verso.Logger IO) : Block Manual → StateT (HashMap String String) IO Unit
    | .other which contents => do
      if which.name == ``Block.savedLean then
        let .arr #[.str fn, .str code] := which.data
          | logger.reportError s!"Failed to deserialize saved Lean data {which.data}"
        modify fun saved =>
          let prior := saved[fn]?.getD ""
          saved.insert fn (prior ++ code ++ "\n")

      if which.name == ``Block.savedImport then
        let .arr #[.str fn, .str code] := which.data
          | logger.reportError s!"Failed to deserialize saved Lean import data {which.data}"
        modify fun saved =>
          let prior := saved[fn]?.getD ""
          saved.insert fn (code.trimAsciiEnd.copy ++ "\n" ++ prior)

      for b in contents do block logger b
    | .concat bs | .blockquote bs =>
      for b in bs do block logger b
    | .ol _ lis | .ul lis =>
      for li in lis do
        for b in li.contents do block logger b
    | .dl dis =>
      for di in dis do
        for b in di.desc do block logger b
    | .para .. | .code .. => pure ()


/-- Overrides Verso's default styling, which lumps comments in with numbers,
punctuation, etc. under the generic code color. -/
def extraStyle : String := "
.hl.lean .comment {
  color: #6a9955;
  font-style: italic;
}
"

open Verso.Output.Html in
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1
  extraHead := #[{{<style>{{Verso.Output.Html.text false extraStyle}}</style>}}]

def main := manualMain (%doc IrisTutorialBook) (extraSteps := [buildExercises]) (config := config)
