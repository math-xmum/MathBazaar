/-
Copyright (c) 2024 Simplex Theory. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuhui Wang, Jiajun Ma, Haocheng Wang
-/
import Mathlib.Data.EReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Simplex Theory

This file formalizes core concepts in simplex theory, particularly focusing on mixed strategies
in game theory and their topological properties. It includes definitions of probability simplices
and their fundamental properties.

## Main Definitions

- `S`: The probability simplex over type `α`, consisting of probability distributions.
- `S''`: The set-theoretic definition of the probability simplex.
- `pure`: Pure (degenerate) probability distributions concentrated on a single element.
- `wsum`: Weighted sum of a function with respect to a probability distribution.
- `linear_comb`: Linear combination of two probability distributions.

## Main Results

- `exists_nonzero`: Every probability distribution has at least one positive component.
- `SisCompactSpace`: The probability simplex is compact in the product topology.
- `ge_iff_simplex_ge`: Characterization of pointwise inequalities via simplex inequalities.
- `le_iff_simplex_le`: Characterization of pointwise inequalities via simplex inequalities.
- `sup_eq_wsum_sup`: The supremum over the simplex equals the pointwise supremum.

## Implementation Notes

The simplex is defined as a subtype of functions from `α` to `ℝ` satisfying non-negativity
and normalization constraints. The topology is induced from the product topology on `α → ℝ`.
Compactness follows from the Heine-Borel theorem applied to closed and bounded sets.

## Tags

simplex, probability, game theory, topology, compactness
-/

open Classical

/-!
## Basic Definitions

We use `S` to denote a mixed strategy (probability distribution).
-/

variable (α : Type*) [Fintype α]

/-- The probability simplex over type `α`: non-negative functions that sum to 1. -/
def S := { x : α→ ℝ // (∀ i:α, 0 ≤ x i)  ∧  Finset.sum Finset.univ x = 1}

/-- Set-theoretic definition of the probability simplex. -/
def S'' := {x :α → ℝ  | (∀ i:α, 0 ≤ x i)  ∧  (Finset.sum (Finset.univ) x = 1)}

namespace S

variable {α : Type*} [Fintype α]

/-!
### Basic Properties and Instances
-/

/-- The simplex as a subtype equals its set-theoretic definition. -/
lemma subset_subtype: S α =  ↑(S'' α) := rfl

/-- Coercion from simplex elements to functions. -/
instance coe_fun : CoeFun (S α) fun _ => α → ℝ :=
  ⟨fun x => (x.val : α → ℝ )⟩

/-- All components of a simplex element are non-negative. -/
lemma non_neg {i : α } {x : S α} : 0 ≤  x i := x.prop.1 i

/-- The sum of all components equals 1. -/
lemma sum_one (x : S α) : Finset.sum Finset.univ x = 1 := x.prop.2

/-- Every probability distribution has at least one positive component. -/
lemma exists_nonzero {α : Type* } [Fintype α]  (x: S α) : ∃ i, x i > 0 := by
  by_contra h
  simp only [gt_iff_lt, not_exists, not_lt, nonpos_iff_eq_zero] at h
  have : Finset.sum Finset.univ x = 0 := by
    apply Finset.sum_eq_zero
    intros i _
    have : 0 ≤ x i  := by apply non_neg
    have : x i ≤ 0 := h i
    linarith
  simp only  [sum_one,one_ne_zero] at this

/-!
### Pure Strategies and Basic Constructions
-/

/-- Pure (degenerate) probability distribution concentrated on element `i`. -/
@[simp]
noncomputable def pure (i : α) : S α  := ⟨fun j => if i=j then 1 else 0,
 by
  constructor
  · intro j
    by_cases H: i=j
    repeat simp [H]
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]⟩

/-- The simplex is inhabited when the underlying type is inhabited. -/
noncomputable instance SInhabited_of_Inhabited {α : Type*} [Fintype α] [Inhabited α]: Inhabited (S α) where
  default := pure (default : α)

/-- The simplex is nonempty when the underlying type is inhabited. -/
noncomputable instance SNonempty_of_Inhabited {α : Type*} [Fintype α] [Inhabited α]: Nonempty (S α) :=
  Nonempty.intro (default : S α)

/-- Pure strategy gives probability 1 to the target element. -/
lemma pure_eq_one {a b : α}: a = b → pure a b = 1 := by
  intro h
  simp [pure, ite_eq_left_iff, zero_ne_one,h]

/-- Pure strategy gives probability 0 to non-target elements. -/
lemma pure_eq_zero {a b : α}: a ≠ b → pure a b = 0 := by
  intro h
  simp [pure, ite_eq_right_iff,h]

/-!
### Weighted Sums and Expectations
-/

/-- Weighted sum (expectation) of function `f` with respect to distribution `x`. -/
noncomputable def wsum {α : Type*} [Fintype α] (x : S α) (f : α → ℝ ) :=
  Finset.sum Finset.univ (fun i:α => (x i) * (f i))

/-- Weighted sum is positive when all function values are positive. -/
lemma wsum_pos {α : Type*} [Fintype α] {x : S α} {f : α → ℝ } (H : ∀ i, f i >0) : wsum x f > 0:= by
  have h' : ∀ i, (x i : ℝ) * (f i : ℝ) ≥  0 := by
    intro i
    exact mul_nonneg (by simp [S.non_neg]) (le_of_lt (H i))
  simp only [wsum]
  let ⟨j, Hjj⟩ := exists_nonzero x
  have h'' : (x j : ℝ) * (f j : ℝ) > 0 := by exact mul_pos (Hjj) (H j)
  have H'' : (Finset.sum (Finset.univ \ {j}) fun i => (x i) * f i) + (Finset.sum {j} fun i => (x i) * f i)
      = (Finset.sum Finset.univ fun i => (x i) * f i) := by
    apply Finset.sum_sdiff
    simp only [Finset.subset_univ]
  rw [<-H'',add_comm]
  apply add_pos_of_pos_of_nonneg
  rw [Finset.sum_singleton]
  exact h''
  apply Finset.sum_nonneg
  simp only [Finset.mem_univ, not_true, Finset.mem_sdiff, Finset.mem_singleton, true_and, gt_iff_lt,
    NNReal.coe_pos]
  intro i _
  exact h' i

/-- Linear combination of two probability distributions. -/
def linear_comb {α : outParam Type*} [Fintype α] (t: {t :ℝ // 0≤ t ∧  t≤ 1}) (a : S α) (b : S α) : S α :=
  ⟨fun i => (t * (a i) + (1-t) * (b i)), by
  constructor
  · intro i
    apply add_nonneg
    apply mul_nonneg
    simp [t.prop.1]
    simp [S.non_neg]
    apply mul_nonneg
    simp [t.prop.2]
    simp [S.non_neg]
  · let f : α → ℝ := fun i => (t :ℝ) * (a i :ℝ)
    have sumf : Finset.sum Finset.univ f = t := by
      rw [<-Finset.mul_sum]
      simp [S.sum_one]
    let g : α → Real  := fun i => (1 -(t: ℝ)) * (b i :ℝ)
    have sumg : Finset.sum Finset.univ g = 1-t := by
      rw [<-Finset.mul_sum]
      simp [S.sum_one]
    have fg_eq : (fun i : α  =>(f i + g i) )= fun i => t * a i + (1 -(t: ℝ)) * (b i :ℝ) := by dsimp
    rw [<-fg_eq, Finset.sum_add_distrib, sumf,sumg]
    simp only [add_sub_cancel]⟩

/-!
### Topological Structure
-/

/-- The simplex inherits its topology from the product topology on `α → ℝ`. -/
instance : TopologicalSpace (S α) := TopologicalSpace.induced (fun x => x.val) (Pi.topologicalSpace)

/-- Projection maps are continuous. -/
lemma projection_isContinuous {i: α} : Continuous (fun (x: S α ) => (x i :ℝ)) := by
  let proj := fun y : α → ℝ => y i
  have Cproj : Continuous proj := continuous_apply i
  let inc := fun x : S α => x.val
  have Cinc : Continuous inc := continuous_induced_dom
  have : (fun (x: S α ) => (x i :ℝ))  = proj ∘ inc := by
    ext x
    rfl
  exact Continuous.comp Cproj Cinc

/-- Real numbers form a proper space. -/
instance proper_real : ProperSpace ℝ := ProperSpace.of_locallyCompactSpace ℝ

/-- Product of proper spaces is proper. -/
instance proper_pi : ProperSpace (α→ ℝ ) := by
  apply pi_properSpace

/-!
### Geometric Properties
-/

/-- Elements of the simplex have non-negative components. -/
lemma x_ge_zero {x : α → ℝ} {b : α} (h : x ∈ S'' α ) :  0 ≤  x b := by
  rw [S'',Set.mem_setOf] at h
  exact h.1 b

/-- Each component of a simplex element is at most 1. -/
lemma x_le_one {x : α → ℝ} {b:α} (h : x ∈ S'' α ): x b ≤ 1 := by
  rw [S'', Set.mem_setOf] at h
  rw [<-h.2]
  apply Finset.single_le_sum (by
    simp only [Finset.mem_univ, forall_true_left]
    exact h.1) (by
    simp only [Finset.mem_univ])

/-- The simplex is bounded in the product metric. -/
lemma Simplex.isBounded [Inhabited α] : Bornology.IsBounded (S'' α) := by
  rw [Metric.isBounded_iff_subset_ball (fun _ => 0)]
  use (2:ℝ)
  intro x hx
  simp only [Metric.mem_ball]
  rw [dist_pi_def]
  norm_cast
  simp only [bot_eq_zero', zero_lt_two, Finset.sup_lt_iff, Finset.mem_univ, forall_true_left]
  intro b
  rw [nndist_dist, Real.dist_eq,<-NNReal.coe_lt_coe,NNReal.coe_two,Real.coe_toNNReal _ (by simp)]
  simp only [sub_zero]
  rw [abs_of_nonneg]
  have hb:= @x_le_one _ _ _ b hx
  apply lt_of_le_of_lt hb
  norm_cast
  apply x_ge_zero
  exact hx

/-- The simplex is sequentially closed. -/
lemma SisClosed :IsClosed (S'' α):= by
  rw [<- isSeqClosed_iff_isClosed]
  rw [isSeqClosed_iff]
  apply superset_antisymm
  exact subset_seqClosure
  rw [seqClosure_eq_closure]
  intro x hx
  rw [mem_closure_iff_seq_limit] at hx
  let ⟨y,hy1,hy2⟩ := hx
  simp only [S'',Set.mem_setOf_eq]
  rw [tendsto_pi_nhds] at hy2
  constructor
  · intro a
    have hy22 := hy2 a
    rw [Filter.Tendsto] at hy22
    apply ge_of_tendsto hy22
    apply Filter.Eventually.of_forall
    intro i
    let ⟨h1,_⟩ := hy1 i
    exact h1 a
  · have h1:= tendsto_finset_sum (Finset.univ: Finset α) (fun i _ => hy2 i)
    have hy1:= fun b => (hy1 b).2
    simp only [hy1, gt_iff_lt, not_lt] at h1
    rw [tendsto_const_nhds_iff] at h1
    rw [h1]

/-- The simplex is compact (closed and bounded in a proper space). -/
instance SisCompactSpace [Inhabited α]: CompactSpace (S α) := by
  simp only [subset_subtype]
  rw [<-isCompact_iff_compactSpace]
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨SisClosed, Simplex.isBounded⟩

end S

/-!
### Auxiliary Lemmas
-/

/-- Finite inhabited types have nonempty universal finsets. -/
lemma Inhabited.toFinsetNonempty (α : Type*) [Inhabited α] [Fintype α ]: Finset.Nonempty (@Finset.univ α  _)  := by
  use Inhabited.default
  simp only [Finset.mem_univ]

namespace S
variable {I: Type*} [Fintype I]

/-!
### Properties of Weighted Sums
-/

/-- Weighted sum with respect to a pure strategy equals the function value. -/
lemma sum_pure {f: I→ℝ} {a:I} :
  Finset.sum Finset.univ (fun i => (S.pure a i) * f i) = f a := by
    have : f a= (S.pure a a) * f a := by simp [ite_true, ENNReal.toReal_one, one_mul]
    rw [this]
    apply Finset.sum_eq_single
    · intro b _ h3
      simp only [S.pure, ite_mul, one_mul, zero_mul, ite_eq_right_iff,S.pure_eq_zero (Ne.symm h3)]
      simp only [Ne.symm h3, IsEmpty.forall_iff]
    · intro h1
      exfalso
      simp only [Finset.mem_univ, not_true] at h1

/-- Weighted sum with respect to a pure strategy. -/
lemma wsum_pure (f: I→ℝ) (a:I) :
  wsum (S.pure a) f = f a := by rw [wsum,sum_pure]

/-- Weighted sum of a constant function equals the constant. -/
lemma wsum_const (b:ℝ) :
  ∀ x: S I, wsum x (fun _ => b) = b :=
    by intro x; simp [wsum,<-Finset.sum_mul,sum_one]

/-- Weighted sum respects function equality. -/
lemma wsum_congr (h : ∀ (i : I), f i = g i) : ∀ x, wsum x f = wsum x g := by
  intro x
  simp [wsum,h]

/-- Weighted sum of a constant function (alternative form). -/
lemma wsum_const' {b:ℝ}  {f: I→ℝ} (H: ∀ a:I, f a = b) :
  ∀ x: S I, wsum x f = b :=
    by intro x; simp [wsum,H,<-Finset.sum_mul,sum_one]

/-- Weighted sum preserves pointwise inequalities. -/
lemma wsum_le_of_le {f g: I→ℝ} (H: ∀ (a:I), (f a) ≤ g a) : ∀ x: S I, (wsum x f) ≤ (wsum x g)  := by
  intro x
  have : ∀ i∈ Finset.univ, x i * f i ≤ x i * g i := fun i _ =>
    mul_le_mul_of_nonneg_left (H i) (non_neg)
  simp [wsum,Finset.sum_le_sum this]

/-- Weighted sum is continuous in the probability distribution. -/
lemma wsum_isContinuous {f: I→ℝ} : Continuous (fun x : S I => wsum x f) :=
 continuous_finset_sum _ (fun _ _ => (Continuous.mul (projection_isContinuous) (continuous_const)))

/-!
### Characterization Theorems
-/

/-- Pointwise lower bounds are equivalent to simplex lower bounds. -/
lemma ge_iff_simplex_ge {f : I → ℝ} {v : ℝ}: (∀ i:I , f i ≥ v) ↔ ∀ x : S I, (wsum x f) ≥ v := by
  constructor
  · intro hi x
    rw [wsum,ge_iff_le]
    calc
      v = Finset.sum Finset.univ fun i => x i * v := by
        simp only [<-Finset.sum_mul, S.sum_one, NNReal.coe_one, one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (ge_iff_le.1 (hi i)) (non_neg)
  · intro HI i
    have := HI (pure i)
    rw [wsum_pure] at this
    exact this

/-- Pointwise upper bounds are equivalent to simplex upper bounds. -/
lemma le_iff_simplex_le {f : I → ℝ} {v : ℝ}: (∀ i:I , f i ≤  v) ↔ ∀ x : S I, (wsum x f) ≤  v := by
  constructor
  · intro hi x
    rw [wsum,<-ge_iff_le]
    calc
      v = Finset.sum Finset.univ fun i => x i * v := by
        simp only [<-Finset.sum_mul]
        simp only [S.sum_one, NNReal.coe_one, one_mul]
      _ ≥   _ := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (ge_iff_le.1 (hi i)) (non_neg)
  · intro HI i
    have := HI (pure i)
    rw [wsum_pure] at this
    exact this

variable [Inhabited I]

/-- Finite inhabited types have nonempty universal finsets. -/
lemma fintypenonempty (α : Type*) [Inhabited α] [Fintype α ]: Finset.Nonempty (@Finset.univ α  _)  := by
  use Inhabited.default
  simp only [Finset.mem_univ]

/-!
### Supremum Characterization

The following lemmas establish the relationship between pointwise suprema and suprema over the simplex.
-/

-- Existence and properties of supremum-achieving elements.
omit [Fintype I] [Inhabited I] in
lemma Finset.exists_sup'_image' (f : I → ℝ) (H: Finset.Nonempty s) : ∃ i∈ s,
(Finset.sup' s H f = f i ∧ ∀ j ∈ s, f j ≤ f i)  := by
  obtain ⟨i,Hi⟩ := Finset.exists_max_image s f H
  use i
  exact  ⟨Hi.1,⟨by
      apply le_antisymm
      · apply Finset.sup'_le H f Hi.2
      · apply Finset.le_sup' f Hi.1,
    Hi.2 ⟩ ⟩

-- Existence of supremum-achieving elements.
omit [Fintype I] [Inhabited I] in
lemma Finset.exists_sup'_image (f : I → ℝ) (H: Finset.Nonempty s) : ∃ i∈ s,
Finset.sup' s H f = f i   := by
  obtain ⟨i,Hi⟩ := Finset.exists_sup'_image' f H
  use i
  exact ⟨Hi.1,Hi.2.1⟩

/-- The pointwise supremum equals the supremum over the simplex. -/
lemma sup_eq_wsum_sup {f : I → ℝ}: Finset.sup' Finset.univ (Inhabited.toFinsetNonempty I) f = iSup (fun (x: S I) => wsum x f) := by
  have non_empty:=Inhabited.toFinsetNonempty I
  obtain ⟨i,⟨_,Hi2,Hi3⟩⟩ := Finset.exists_sup'_image' f non_empty
  rw [Hi2]
  have Hi3 : ∀ j:I, f j≤ f i := by simp [Hi3]
  have Hi3' := le_iff_simplex_le.1 Hi3
  apply le_antisymm
  · have wsum_fi := wsum_pure f i
    rw [<-wsum_fi]
    have H : BddAbove (Set.range (fun x => wsum x f)):= by
      rw [<-wsum_fi] at Hi3'
      apply bddAbove_def.2 ⟨wsum (pure i) f, by
        intro y hy
        obtain ⟨j, hj⟩ := Set.mem_range.1 hy
        simp only [<-hj,Hi3']⟩
    apply le_ciSup H
  · exact ciSup_le Hi3'

end S
