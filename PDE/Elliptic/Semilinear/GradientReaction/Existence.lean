/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.GradientReaction.Load
public import PDE.Analysis.Operator.StrongMonotonicity

/-!
# Solvability of a Lipschitz gradient reaction

The weak operator of `-Δu + b(Du) + μu` is strongly monotone once
`μ ≥ 1 + K²`. The negative part of the reaction pairing is bounded by
`K ‖D(u-v)‖ ‖u-v‖`. Young's inequality absorbs this cross term into the
Dirichlet and mass energies, leaving half the full `H¹` norm squared.

The Hilbert-space bijectivity theorem uses Riesz representation and a contraction
argument. Thus every dual load has a unique weak solution, with no boundary
regularity or compactness hypothesis.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory
open scoped NNReal InnerProductSpace

namespace SobolevSpace.GraphSpace.GradientReaction

variable {n : ℕ} {Ω : Set (ℝ^n)} {K : ℝ≥0} {b : ℝ^n → ℝ}

/-- The zero-boundary weak equation with the original pointwise gradient reaction.
Under boundedness and global Lipschitz continuity its integral is absolutely integrable. -/
def IsWeakSolution (b : ℝ^n → ℝ) (μ : ℝ) (u : H¹₀(Ω)) : Prop :=
  ∀ v : H¹₀(Ω),
    dirichletForm u v + μ * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ +
      (∫ x, b (∇ (u : H¹(Ω)) x) * baseCoordCLM v x ∂domainMeasure n Ω) = 0

/-- The dual operator associated with `-Δu + μu + b(Du)`. -/
def weakOperator (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (μ : ℝ) (u : H¹₀(Ω)) : StrongDual ℝ (H¹₀(Ω)) :=
  dirichletForm u + μ • massFormCLM u + load hbounded hb u

/-- Evaluation exposes the Dirichlet, mass, and nonlinear reaction pairings. -/
theorem weakOperator_apply (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (μ : ℝ) (u v : H¹₀(Ω)) :
    weakOperator hbounded hb μ u v =
      dirichletForm u v + μ * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ +
        ⟪reaction hbounded hb u, baseCoordCLM v⟫_ℝ :=
  rfl

/-- Vanishing of the dual operator is exactly the weak integral equation. -/
theorem weakOperator_eq_zero_iff (hbounded : Bornology.IsBounded Ω)
    (hb : LipschitzWith K b) (μ : ℝ) (u : H¹₀(Ω)) :
    weakOperator hbounded hb μ u = 0 ↔ IsWeakSolution b μ u := by
  have happ (v : H¹₀(Ω)) :
      weakOperator hbounded hb μ u v =
        dirichletForm u v + μ * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ +
          ∫ x, b (∇ (u : H¹(Ω)) x) * baseCoordCLM v x ∂domainMeasure n Ω := by
    change dirichletForm u v + μ * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ +
      load hbounded hb u v = _
    rw [load_eq_integral]
  constructor
  · intro h v
    rw [← happ, h, zero_apply]
  · intro h
    ext v
    exact (happ v).trans (h v)

/-- The full weak operator is globally Lipschitz as a map to the dual. -/
theorem lipschitzWith_weakOperator (hbounded : Bornology.IsBounded Ω)
    (hb : LipschitzWith K b) (μ : ℝ) :
    LipschitzWith
      (‖dirichletForm (n := n) (Ω := Ω) + μ • massFormCLM‖₊ + K)
      (weakOperator hbounded hb μ) :=
  (dirichletForm (n := n) (Ω := Ω) + μ • massFormCLM).lipschitzWith.add
    (lipschitzWith_load hbounded hb)

/-- The monotonicity pairing controls half the full `H¹` norm squared.
The threshold is independent of the reaction's value at zero. -/
theorem pairing_lower_bound (μ : ℝ) (hμ : 1 + (K : ℝ) ^ 2 ≤ μ)
    (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (u v : H¹₀(Ω)) :
    (1 / 2 : ℝ) * ‖u - v‖ * ‖u - v‖ ≤
      (weakOperator hbounded hb μ u - weakOperator hbounded hb μ v) (u - v) := by
  have hpair :
      (weakOperator hbounded hb μ u - weakOperator hbounded hb μ v) (u - v) =
        ‖∇ ((u - v : H¹₀(Ω)) : H¹(Ω))‖ ^ 2 + μ * ‖baseCoordCLM (u - v)‖ ^ 2 +
          (load hbounded hb u - load hbounded hb v) (u - v) := by
    have hlin :
        weakOperator hbounded hb μ u - weakOperator hbounded hb μ v =
          dirichletForm (u - v) + μ • massFormCLM (u - v) +
            (load hbounded hb u - load hbounded hb v) := by
      simp only [weakOperator, map_sub, smul_sub]
      abel
    rw [hlin]
    simp only [add_apply, smul_apply,
      dirichletForm_eq_inner_gradient, massFormCLM_apply, real_inner_self_eq_norm_sq,
      smul_eq_mul]
  have hnorm :
      ‖u - v‖ ^ 2 = ‖baseCoordCLM (u - v)‖ ^ 2 + ‖∇ ((u - v : H¹₀(Ω)) : H¹(Ω))‖ ^ 2 := by
    rw [norm_sq_eq_base_sq_add_sum_deriv_sq]
    exact congrArg (‖baseCoordCLM (u - v)‖ ^ 2 + ·)
      (norm_gradientCLM_sq_eq_sum_deriv_sq (u - v)).symm
  have hcross := (abs_le.mp (abs_load_sub_apply_le hbounded hb u v)).1
  have hmass := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖baseCoordCLM (u - v)‖)
  have hyoung :=
    sq_nonneg (‖∇ ((u - v : H¹₀(Ω)) : H¹(Ω))‖ - (K : ℝ) * ‖baseCoordCLM (u - v)‖)
  rw [hpair]
  nlinarith [sq_nonneg ‖baseCoordCLM (u - v)‖]

/-- For the stated threshold, every dual load has exactly one weak solution. -/
theorem bijective_weakOperator (μ : ℝ) (hμ : 1 + (K : ℝ) ^ 2 ≤ μ)
    (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b) :
    Function.Bijective (weakOperator hbounded hb μ) :=
  PDE.Analysis.Operator.bijective_dual_of_pairing_lower_bound_of_lipschitzWith
    (V := H¹₀(Ω)) (weakOperator hbounded hb μ) (1 / 2) (by norm_num)
    (pairing_lower_bound μ hμ hbounded hb) (lipschitzWith_weakOperator hbounded hb μ)

/-- In particular, the homogeneous gradient-reaction equation has a unique weak solution. -/
theorem existsUnique_weakSolution (μ : ℝ) (hμ : 1 + (K : ℝ) ^ 2 ≤ μ)
    (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b) :
    ∃! u : H¹₀(Ω), weakOperator hbounded hb μ u = 0 := by
  obtain ⟨u, hu⟩ := (bijective_weakOperator μ hμ hbounded hb).surjective 0
  exact ⟨u, hu, fun v hv ↦ (bijective_weakOperator μ hμ hbounded hb).injective (hv.trans hu.symm)⟩

/-- Moving the reaction and mass to the right gives the Poisson `L²` load. -/
theorem dirichletForm_eq_load_of_weakOperator_eq_zero
    (hbounded : Bornology.IsBounded Ω) (hb : LipschitzWith K b)
    (μ : ℝ) (u : H¹₀(Ω)) (hu : weakOperator hbounded hb μ u = 0) :
    dirichletForm u =
      loadFunctional (-reaction hbounded hb u - μ • baseCoordCLM u) := by
  ext v
  have h := congrArg (fun f : StrongDual ℝ (H¹₀(Ω)) ↦ f v) hu
  simp only [weakOperator_apply, zero_apply] at h
  simp only [loadFunctional_sub, loadFunctional_neg, loadFunctional_smul,
    sub_apply, neg_apply, smul_apply, loadFunctional_apply, smul_eq_mul]
  linarith

end SobolevSpace.GraphSpace.GradientReaction
