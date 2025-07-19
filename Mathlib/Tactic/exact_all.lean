/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Tactic.LibrarySearch
import Lean.Meta.Tactic.TryThis
import Mathlib
-- import Mathlib.Tactic.MinImports

/-!
# Library search

This file defines `exact??`
-/


namespace Lean.Meta.LibrarySearch

builtin_initialize registerTraceClass `Tactic.librarySearch
builtin_initialize registerTraceClass `Tactic.librarySearch.lemmas

open SolveByElim Lean.Meta.LibrarySearch

open LazyDiscrTree (InitEntry findMatches)

private def addImport (name : Name) (constInfo : ConstantInfo) :
    MetaM (Array (InitEntry (Name × DeclMod))) :=
  forallTelescope constInfo.type fun _ type => do
    let e ← InitEntry.fromExpr type (name, DeclMod.none)
    let a := #[e]
    if e.key == .const ``Iff 2 then
      let a := a.push (←e.mkSubEntry 0 (name, DeclMod.mp))
      let a := a.push (←e.mkSubEntry 1 (name, DeclMod.mpr))
      pure a
    else
      pure a

/-- Stores import discrimination tree. -/
private def LibSearchState := IO.Ref (Option (LazyDiscrTree (Name × DeclMod)))

private builtin_initialize defaultLibSearchState : IO.Ref (Option (LazyDiscrTree (Name × DeclMod))) ← do
  IO.mkRef .none

private instance : Inhabited LibSearchState where
  default := defaultLibSearchState

private builtin_initialize ext : EnvExtension LibSearchState ←
  registerEnvExtension (IO.mkRef .none)

/--
The maximum number of constants an individual task may perform.

The value was picked because it roughly corresponded to 50ms of work on the
machine this was developed on.  Smaller numbers did not seem to improve
performance when importing Std and larger numbers (<10k) seemed to degrade
initialization performance.
-/
private def constantsPerImportTask : Nat := 6500

set_option autoImplicit true in
private def librarySearchEmoji : Except ε (Option α) → String
| .error _ => bombEmoji
| .ok (some _) => crossEmoji
| .ok none => checkEmoji

/--
An exception ID that indicates further speculation on candidate lemmas should stop
and current results should be returned.
-/
private builtin_initialize abortSpeculationId : InternalExceptionId ←
  registerInternalExceptionId `Lean.Meta.LibrarySearch.abortSpeculation

section LibrarySearch

set_option autoImplicit true in
private def emoji (e : Except ε α) := if e.toBool then checkEmoji else crossEmoji

private def isVar (e : Expr) : Bool :=
  match e with
  | .bvar _ => true
  | .fvar _ => true
  | .mvar _ => true
  | _ => false

/--
Tries to apply the given lemma (with symmetry modifier) to the goal,
then tries to close subsequent goals using `solveByElim`.
If `solveByElim` succeeds, `[]` is returned as the list of new subgoals,
otherwise the full list of subgoals is returned.
-/
private def librarySearchLemma (cfg : ApplyConfig) (act : List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool) (cand : Candidate)  : MetaM (List MVarId) := do
  let ((goal, mctx), (name, mod)) := cand
  let ppMod (mod : DeclMod) : MessageData :=
        match mod with | .none => "" | .mp => " with mp" | .mpr => " with mpr"
  withTraceNode `Tactic.librarySearch (return m!"{emoji ·} trying {name}{ppMod mod} ") do
    setMCtx mctx
    let lem ← mkLibrarySearchLemma name mod
    let newGoals ← goal.apply lem cfg
    try
      act newGoals
    catch _ =>
      if ← allowFailure goal then
        pure newGoals
      else
        failure

/--
Sequentially invokes a tactic `act` on each value in candidates on the current state.

The tactic `act` should return a list of meta-variables that still need to be resolved.
If this list is empty, then no variables remain to be solved, and `tryOnEach` returns
`none` with the environment set so each goal is resolved.

If the action throws an internal exception with the `abortSpeculationId` id then
further computation is stopped and intermediate results returned. If any other
exception is thrown, then it is silently discarded.
-/
def tryOnEachAll
    (act : Candidate → MetaM (List MVarId))
    (candidates : Array Candidate)
    (numSuggestions : Nat := 3) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  let mut a := #[]
  let s ← saveState
  logInfo m!"candidates"
  for c in candidates do
    match ← (tryCatch (Except.ok <$> act c) (pure ∘ Except.error)) with
    | .error e =>
      restoreState s
      if isAbortSpeculation e then
        break
    | .ok remaining =>
      logInfo m!"remaining: {remaining}"
      if remaining.isEmpty then
        let ctx ← getMCtx
        a := a.push (remaining, ctx)
        if a.size = numSuggestions then
          return .some a
      restoreState s
  logInfo m!"a is: {a.size}"
  return .some a

private def librarySearch' (goal : MVarId)
    (tactic : List MVarId → MetaM (List MVarId))
    (allowFailure : MVarId → MetaM Bool)
    (leavePercentHeartbeats : Nat)
    (numSuggestions : Nat := 3) :
    MetaM (Option (Array (List MVarId × MetavarContext))) := do
  withTraceNode `Tactic.librarySearch (return m!"{librarySearchEmoji ·} {← goal.getType}") do
  profileitM Exception "librarySearch" (← getOptions) do
    -- Create predicate that returns true when running low on heartbeats.
    let candidates ← librarySearchSymm libSearchFindDecls goal
    let cfg : ApplyConfig := { allowSynthFailures := true }
    let shouldAbort ← mkHeartbeatCheck leavePercentHeartbeats
    let act := fun cand => do
        if ←shouldAbort then
          abortSpeculation
        librarySearchLemma cfg tactic allowFailure cand
    tryOnEachAll act candidates numSuggestions

end LibrarySearch

open Lean Meta LibrarySearch
open Elab Tactic Term TryThis

/--
Implementation of the `exact?` tactic.

* `ref` contains the input syntax and is used for locations in error reporting.
* `required` contains an optional list of terms that should be used in closing the goal.
-/
def exact?? (ref : Syntax) (required : Option (Array (TSyntax `term))) (numSuggestions : Nat := 2) :
    TacticM Unit := do
  let mvar ← getMainGoal
  let initialState ← saveState
  let (_, goal) ← (← getMainGoal).intros
  goal.withContext do
    let required := (← (required.getD #[]).mapM getFVarId).toList.map .fvar
    let tactic := fun exfalso =>
      solveByElim required (exfalso := exfalso) (maxDepth := 6)
    let allowFailure := fun g => do
      let g ← g.withContext (instantiateMVars (.mvar g))
      return required.all fun e => e.occurs g
    try
      let _ ← tactic true [goal]
      addExactSuggestion ref (← instantiateMVars (.mvar mvar)).headBeta
        (checkState? := initialState)
      restoreState initialState
    finally
      logInfo m!"I'm here"
      -- clean this up
      match (← librarySearch' goal (tactic false) allowFailure 10 numSuggestions) with
      | some suggestions =>
        if suggestions.isEmpty then
          throwError "`exact??` could not close the goal"
        reportOutOfHeartbeats `apply? ref
        for (_, suggestionMCtx) in suggestions do
          withMCtx suggestionMCtx do
            addExactSuggestion ref (← instantiateMVars (.mvar mvar)).headBeta
              (checkState? := initialState) (addSubgoalsMsg := true) (tacticErrorAsInfo := true)
      | none => admitGoal goal (synthetic := false)

syntax "exact??" (ppSpace num ppSpace)? (" using " (colGt ident),+)? : tactic

elab_rules : tactic
  | `(tactic| exact?? $[ $n?]?) => do
    match n? with
    | some n => exact?? (← getRef) none n.getNat
    | none => exact?? (← getRef) none

def foo {α : Type} (x : α) : α := x
theorem foo_def {α : Type} (x : α) : foo x = x := rfl
theorem foo_def2 {α : Type} (x : α) : foo x = x := rfl
theorem foo_def3 {α : Type} (x : α) : x = foo x := rfl
theorem foo_def4 {α : Type} (x : α) : x = x → foo x = x := fun _ ↦ rfl
theorem foo_def5 {α : Type} (x : α) : foo x = x := rfl
theorem foo_def6 {α : Type} (x : α) : foo x = x := rfl
theorem foo_def7 {α : Type} (x : α) : foo x = x := rfl
theorem foo_def8 {α : Type} (x : α) : foo x = x := rfl
theorem foo_def9 {α : Type} (x : α) : foo x = x := rfl
theorem foo_def10 {α : Type} (x : α) : foo x = x := rfl
theorem foo_test {α : Type} (x : α) : Function.Bijective (id : ℝ → ℝ) := by exact??

-- theorem foo_test' (x : Nat) : foo x = x + 1 := by apply?

end Lean.Meta.LibrarySearch
