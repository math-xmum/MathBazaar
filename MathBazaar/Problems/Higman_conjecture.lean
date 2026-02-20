import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Defs

open Polynomial 

variable (n : ℕ) (F : Type*) [One F] [Zero F]

/-- The property of being a unitriangular matrix: 
    Upper triangular with 1s on the diagonal. -/
def is_unitriangular (M : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i j, j < i → M i j = 0) ∧ (∀ i, M i i = 1)

/-- The type of unitriangular matrices over a finite field F. -/
def UnitriangularGroup :=
  { M : Matrix (Fin n) (Fin n) F // is_unitriangular n F M }



/-- Defining the Group structure for U_n(F). 
    We provide the multiplication, identity, and inverse rules. -/
instance [Field F] [Fintype F] : Group (UnitriangularGroup n F) where
  mul A B := ⟨A.1 * B.1, by 
    -- Proof that product of unitriangular matrices is unitriangular
    sorry⟩
  one := ⟨1, by 
    -- Proof that identity matrix is unitriangular
    sorry⟩
  inv A := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry


/-- 
Higman's Conjecture (1.1):
The number of conjugacy classes of U_n(F_q) is given by a polynomial 
in q with integer coefficients.
-/
def HigmanConjecture (n : ℕ) : Prop :=
  ∃ (P : ℤ[X]), ∀ (F : Type*) [Field F] [Fintype F],
    let q : ℤ := Nat.card F
    let G := UnitriangularGroup n F
    (Nat.card (ConjClasses G) : ℤ) = P.eval q

theorem HigmanHolds (Hn : n > 1): HigmanConjecture n := sorry


/-- 
Weak Higman's Conjecture (PORC):
The number of conjugacy classes of U_n(F_q) is a Polynomial of q where q = p^m for a fixed p. 
-/
def WeakHigmanConjecture (p : ℕ ) [Fact p.Prime] : Prop :=
  ∃ (P : ℤ[X]), 
    ∀ (F : Type*) [Field F] [Fintype F],
      let q := Fintype.card F
      let G := UnitriangularGroup n F
      (∃ (m : ℕ ), q = p^m) → 
      (Nat.card (ConjClasses G) : ℤ) = P.eval (q : ℤ)

 theorem WeakHigmanHolds (Hn : n > 1) (p:ℕ) [Fact p.Prime]: WeakHigmanConjecture n p:= sorry