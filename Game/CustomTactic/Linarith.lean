import Mathlib.Tactic.Linarith

open Mathlib.Tactic in

@[inherit_doc Mathlib.Tactic.linarith]
syntax (name := Game.linarith) "linarith" "!"? linarithArgsRest : tactic

-- This is copied from the Mathlib tactic `linarith` where the `only` keyword has been
-- made mandatory
open Lean Mathlib Syntax Elab Tactic in
elab_rules (kind := Game.linarith) : tactic
  | `(tactic| linarith $[!%$bang]? $cfg:optConfig only%$o [$args,*]) => withMainContext do
    let args ← (args.getElems).mapM (elabLinarithArg `linarith)
    let cfg := (← elabLinarithConfig cfg).updateReducibility bang.isSome
    commitIfNoEx do liftMetaFinishingTactic <| Linarith.linarith true args.toList cfg
  | `(tactic| linarith $[!%$bang]? $cfg:optConfig) => throwError "In this game, `linarith` requires to specify `only` explicitly: Write `linarith only []`"
