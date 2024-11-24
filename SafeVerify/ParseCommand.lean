/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean

open Lean Elab Parser

-- This is just `FrontendM.State` + `FrontendM.Context` smushed together, to keep things simple.
structure State where
  input : String
  inputCtx : InputContext
  parserState : ModuleParserState
  commandState : Command.State
  cmdPos : String.Pos := parserState.pos
  commands : Array Syntax := #[]

def parseHeader (input : String) : IO State  := unsafe do
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  enableInitializersExecution
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let commandState := Command.mkState env messages {}
  return { input, inputCtx, parserState, commandState }

def step (s : State) : IO (Option State) := do
  let (done, s') ← Frontend.processCommand.run { inputCtx := s.inputCtx} |>.run { commandState := s.commandState, parserState := s.parserState, cmdPos := s.cmdPos }
  if done then
    return none
  else
    return some { s' with input := s.input, inputCtx := s.inputCtx }

def replaceInput (s : State) (newInput : String) : State :=
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext newInput fileName
  let parserState := { : ModuleParserState }
  { s with input := (Substring.mk s.input 0 s.parserState.pos).toString ++ newInput, inputCtx, parserState, cmdPos := 0 }

/-- Warning: this will invalidate *all* `State`s which share the same header, resulting in undefined behaviour. -/
def freeRegions (s : State) : IO Unit := unsafe do
  s.commandState.env.freeRegions

