import Lean
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Category.Cat

open Lean Meta Elab Tactic Qq

universe v u

namespace Test

-- same here (as in function below)
private def throwAppBuilderException {α} (op : Name) (msg : MessageData) : MetaM α :=
  throwError "AppBuilder for '{op}', {msg}"

private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType ← instantiateTypeLevelParams cinfo us
  return (f, fType)

-- I should just be able to use standard version of this?
private def withAppBuilderTrace {α} {β} [ToMessageData α] [ToMessageData β]
    (f : α) (xs : β) (k : MetaM Expr) : MetaM Expr :=
  let emoji | .ok .. => checkEmoji | .error .. => crossEmoji
  withTraceNode `Meta.appBuilder (return m!"{emoji ·} f: {f}, xs: {xs}") do
    try
      let res ← k
      trace[Meta.appBuilder.result] res
      pure res
    catch ex =>
      trace[Meta.appBuilder.error] ex.toMessageData
      throw ex

-- This basically just tries to synthesize all mvars. Then
private def mkAppMFinal (methodName : Name) (f : Expr) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
  logInfo m!"f: {f}"
  let result ← instantiateMVars (mkAppN f args)
  logInfo m!"result: {result}"
  -- if (← hasAssignableMVar result) then throwAppBuilderException methodName ("result contains metavariables" ++ indentExpr result)
  return result

private partial def mkAppOptMAux (f : Expr) (xs : Array (Option Expr)) : Nat → Array Expr → Nat → Array MVarId → Expr → MetaM Expr
  -- if its a forall expression
  | i, args, j, instMVars, Expr.forallE n d b bi => do
    -- substitute args into d (which is the type of the next argument?)
    let d  := d.instantiateRevRange j args.size args
    -- if havent applied all arguments already (?)
    if h : i < xs.size then
      match xs.get ⟨i, h⟩ with
      -- if we don't want to apply this argument
      | none =>
        -- if its an instance argument, add to argument list + add to instMVar list
        match bi with
        -- | BinderInfo.instImplicit => do
        --   let mvar ← mkFreshExprMVar d MetavarKind.synthetic n
        --   mkAppOptMAux f xs (i+1) (args.push mvar) j (instMVars.push mvar.mvarId!) b
        -- else add to argument list + proceed
        | _                       => do
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          mkAppOptMAux f xs (i+1) (args.push mvar) j instMVars b
      -- if we want to apply this argument
      | some x =>
        let xType ← inferType x
        -- TODO: whats d (type of next argument)
        if (← isDefEq d xType) then
          mkAppOptMAux f xs (i+1) (args.push x) j instMVars b
        else
          throwAppTypeMismatch (mkAppN f args) x
    -- if all arguments have already been supplied?
    else
      mkAppMFinal `mkAppOptM f args instMVars
  -- else
  | i, args, j, instMVars, type => do
    let type := type.instantiateRevRange j args.size args
    let type ← whnfD type
    -- now it can somehow be a forall thing again?
    if type.isForall then
      mkAppOptMAux f xs i args args.size instMVars type
    -- if we are on the final argument
    else if i == xs.size then
      -- TODO: understand
      mkAppMFinal `mkAppOptM f args instMVars
    -- TODO
    else do
      let xs : Array Expr := xs.foldl
        (fun r x? => match x? with | none => r | some x => r.push x) #[]
      throwAppBuilderException `mkAppOptM ("too many arguments provided to" ++ indentExpr f ++
        Format.line ++ "arguments" ++ xs)

/--
  Similar to `mkAppM`, but it allows us to specify which arguments are provided explicitly using `Option` type.
  Example:
  Given `Pure.pure {m : Type u → Type v} [Pure m] {α : Type u} (a : α) : m α`,
  ```
  mkAppOptM `Pure.pure #[m, none, none, a]
  ```
  returns a `Pure.pure` application if the instance `Pure m` can be synthesized, and the universe match.
  Note that,
  ```
  mkAppM `Pure.pure #[a]
  ```
  fails because the only explicit argument `(a : α)` is not sufficient for inferring the remaining arguments,
  we would need the expected type. -/
def mkAppOptM (constName : Name) (xs : Array (Option Expr)) : MetaM Expr := do
  withAppBuilderTrace constName xs do withNewMCtxDepth do
    let (f, fType) ← mkFun constName
    mkAppOptMAux f xs 0 #[] 0 #[] fType

/-- Similar to `mkAppOptM`, but takes an `Expr` instead of a constant name. -/
def mkAppOptM' (f : Expr) (xs : Array (Option Expr)) : MetaM Expr := do
  let fType ← inferType f
  withAppBuilderTrace f xs do withNewMCtxDepth do
    mkAppOptMAux f xs 0 #[] 0 #[] fType


variable {C : Type u} [CategoryTheory.Bicategory C]

#eval mkAppOptM ``CategoryTheory.Pseudofunctor.mapComp_assoc_right_hom
  #[none, none, none, none, none, none, none, none, none, none, none, none]

end Test
