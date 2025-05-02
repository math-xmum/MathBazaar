import Mathlib.Data.Finset.Insert
import Lean


open Lean Meta

/--
The class holds the function to convert a type to an expression in meta programming.
-/
class ToExprM (α : Type u) where
  toExprM : α → MetaM Expr
  toTypeExprM : MetaM Expr

/--
Instance for any type that has a function toExpr, we can convert it to an expression.
-/
instance [h:ToExpr α] : ToExprM α where
  toExprM := fun x => pure (toExpr x)
  toTypeExprM := pure (h.toTypeExpr)

open Lean.Meta

/--
The realization of ToExprM for Finset.
-/
unsafe instance Finset.toExprM
    {α : Type u} [ToLevel.{u}] [ToExprM α] [DecidableEq α] : ToExprM (Finset α) where
  toTypeExprM := do
    let type ← ToExprM.toTypeExprM α
    mkAppM ``Finset #[type]
  toExprM :=
  let rec toExprAux {α : Type u} [ToLevel.{u}] [inst:ToExprM α]: List α  → MetaM Expr := fun x => do
    let type ← ToExprM.toTypeExprM α
    let finsettype ← mkAppM ``Finset #[type]
    logInfo m!"{← ppExpr type}"
    match x with
    | []    => pure <| mkAppN (.const ``Finset.empty [toLevel.{u}]) #[type]
    | [a]   => mkAppOptM ``Singleton.singleton #[none,finsettype,none,(←inst.toExprM a)]
    | a::as => mkAppM ``Insert.insert #[(←inst.toExprM a),(←toExprAux as)]
  fun x => (toExprAux x.val.unquot)

/--
The upgraded version of eval% utilizing the ToExprM class.
-/
syntax (name := eval_exprm) "evalm% " term : term

@[term_elab eval_exprm, inherit_doc eval_exprm]
unsafe def elabEvalExpr : Lean.Elab.Term.TermElab
| `(term| evalm% $stx) => fun exp => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize stx exp
  let e ← instantiateMVars e
  let ee ← Meta.mkAppM ``ToExprM.toExprM #[e]
  let eetype ← inferType ee
  let ee ← Lean.Meta.evalExpr (MetaM Expr) eetype ee (safety := .unsafe)
  return (←ee)
| _ => fun _ => Elab.throwUnsupportedSyntax

/-
section test
#check @Singleton.singleton (ℕ) (Finset ℕ) _ 1
#check ({1,2} : Finset ℕ)

#check evalm% ({} : Finset ℕ )
#check evalm% ({({2^10,1} : Finset ℕ),{2^3,2^5}}: Finset (Finset ℕ))

lemma a: ({2^10,1} : Finset ℕ) = evalm% ({2^10,1} : Finset ℕ):= by rfl

def twopowers (n : ℕ) : Finset ℕ := match n with
| 0 => {1}
| n+1 => {2^(n+1)} ∪ twopowers n

#eval twopowers 10

example (x : ℕ ): x∈ twopowers 10 → x=1 ∨ x %2 =0:= by
  intro hx
  have hh : twopowers 10 = evalm% twopowers 10 := by native_decide
  rw [hh] at hx
  fin_cases hx <;> simp


#check a

end test
-/
