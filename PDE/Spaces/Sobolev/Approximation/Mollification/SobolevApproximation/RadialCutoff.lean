/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Common.Euclidean.CoordinateReflection
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Cutoff
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions

/-!
# Radial cutoffs and their derivatives

Rescaling Mathlib's explicit inner-product bump gives a cutoff invariant under every
coordinate reflection. It is one on the inner ball, vanishes outside twice that radius,
and each derivative of order `j` is bounded by a radius-independent constant times `R⁻ʲ`.
The explicit radial base is needed to retain reflection symmetry.
-/

@[expose] public noncomputable section

open PDE (partialDeriv iteratedPartialDeriv iteratedPartialDeriv_comp_const_smul)

open Filter Metric Set SobolevSpace PDE.Common
open scoped Topology

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- A radial smooth cutoff with inner radius `R` and outer radius `2R`. -/
def radialCutoff (R : ℝ) : ℝ^n → ℝ :=
  fun x ↦ (ContDiffBumpBase.ofInnerProductSpace (ℝ^n)).toFun 2 (R⁻¹ • x)

private theorem radialCutoff_base_smooth :
    ContDiff ℝ (⊤ : ℕ∞)
      ((ContDiffBumpBase.ofInnerProductSpace (ℝ^n)).toFun 2) :=
  (ContDiffBumpBase.ofInnerProductSpace (ℝ^n)).smooth.comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun _ ↦ ⟨one_lt_two, mem_univ _⟩)

/-- The radial cutoff is smooth at every scale. -/
theorem radialCutoff_contDiff (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialCutoff (n := n) R) :=
  radialCutoff_base_smooth.comp (contDiff_id.const_smul R⁻¹)

/-- The radial cutoff is unchanged by reflection in any coordinate. -/
theorem radialCutoff_even (R : ℝ) (i : Fin n) :
    IsEvenUnderCoordinateReflection i (radialCutoff R) := by
  intro x
  simp only [radialCutoff, ContDiffBumpBase.ofInnerProductSpace, norm_smul,
    norm_coordinateReflection]

/-- The cutoff equals one throughout the inner closed ball. -/
theorem radialCutoff_eq_one {R : ℝ} (hR : 0 < R) {x : ℝ^n}
    (hx : ‖x‖ ≤ R) : radialCutoff R x = 1 := by
  apply (ContDiffBumpBase.ofInnerProductSpace (ℝ^n)).eq_one 2 one_lt_two
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  exact (inv_mul_le_iff₀ hR).mpr (by simpa using hx)

/-- The support is contained in the outer closed ball. -/
theorem tsupport_radialCutoff_subset {R : ℝ} (hR : 0 < R) :
    tsupport (radialCutoff (n := n) R) ⊆ closedBall 0 (2 * R) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hmem : R⁻¹ • x ∈ Function.support
      ((ContDiffBumpBase.ofInnerProductSpace (ℝ^n)).toFun 2) := hx
  rw [(ContDiffBumpBase.ofInnerProductSpace (ℝ^n)).support 2 one_lt_two] at hmem
  have hh : ‖x‖ < 2 * R := by
    have hh : R⁻¹ * ‖x‖ < 2 := by
      simpa [mem_ball, dist_zero_right, norm_smul, abs_of_pos hR] using hmem
    simpa only [mul_comm R 2] using (inv_mul_lt_iff₀ hR).mp hh
  simpa using hh.le

/-- The radial cutoff has compact support at every positive scale. -/
theorem radialCutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (radialCutoff (n := n) R) :=
  (isCompact_closedBall (0 : ℝ^n) (2 * R)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_radialCutoff_subset hR)

private theorem derivative_const_eq_zero (α : List (Fin n)) (hα : α ≠ [])
    (c : ℝ) (x : ℝ^n) : iteratedPartialDeriv α (fun _ ↦ c) x = 0 := by
  induction α generalizing x with
  | nil => exact (hα rfl).elim
  | cons i α ih =>
    cases α with
    | nil => simp [iteratedPartialDeriv, partialDeriv]
    | cons j α =>
      have hz : iteratedPartialDeriv (j :: α) (fun _ : ℝ^n ↦ c) = fun _ ↦ 0 :=
        funext fun y ↦ ih (by simp) y
      simp only [iteratedPartialDeriv] at hz ⊢
      rw [hz]
      simp [partialDeriv]

/-- Nonempty cutoff derivatives vanish on the inner open ball. -/
theorem radialCutoff_derivative_zero_inside
    (α : List (Fin n)) (hα : α ≠ []) {R : ℝ} (hR : 0 < R)
    {x : ℝ^n} (hx : ‖x‖ < R) :
    iteratedPartialDeriv α (radialCutoff R) x = 0 := by
  have heq : radialCutoff R =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
    have hxball : x ∈ ball (0 : ℝ^n) R := by simpa using hx
    filter_upwards [isOpen_ball.mem_nhds hxball] with y hy
    exact radialCutoff_eq_one hR (by simpa using (ball_subset_closedBall hy))
  exact (heq.iteratedPartialDeriv α).eq_of_nhds.trans
    (derivative_const_eq_zero α hα 1 x)

/-- All derivatives vanish outside the outer closed ball. -/
theorem radialCutoff_derivative_zero_outside
    (α : List (Fin n)) {R : ℝ} (hR : 0 < R) {x : ℝ^n} (hx : 2 * R < ‖x‖) :
    iteratedPartialDeriv α (radialCutoff R) x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hball := tsupport_radialCutoff_subset hR
    ((tsupport_iteratedPartialDeriv_subset_tsupport α _) hmem)
  have hnorm : ‖x‖ ≤ 2 * R := by simpa using hball
  exact (hx.trans_le hnorm).false

/-- Each derivative is bounded by a constant times `R` to minus its order.
The constant is independent of the radius. -/
theorem exists_radialCutoff_derivative_bound (α : List (Fin n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 < R → ∀ x : ℝ^n,
      |iteratedPartialDeriv α (radialCutoff R) x| ≤ B * R⁻¹ ^ α.length := by
  let b := (ContDiffBumpBase.ofInnerProductSpace (ℝ^n)).toFun 2
  have hb : HasCompactSupport b := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ^n) 2)
    rw [show Function.support b = ball 0 2 from
      (ContDiffBumpBase.ofInnerProductSpace (ℝ^n)).support 2 one_lt_two]
    exact ball_subset_closedBall
  obtain ⟨B, hB, hbound⟩ := exists_abs_le_iteratedPartialDeriv_of_hasCompactSupport
    hb radialCutoff_base_smooth α
  refine ⟨B, hB, ?_⟩
  intro R hR x
  change |iteratedPartialDeriv α (fun y ↦ b (R⁻¹ • y)) x| ≤ _
  rw [iteratedPartialDeriv_comp_const_smul α radialCutoff_base_smooth,
    abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) _)]
  exact (mul_le_mul_of_nonneg_left (hbound _) (by positivity)).trans_eq (mul_comm _ _)

/-- The radial cutoff takes values in the unit interval. -/
theorem radialCutoff_mem_Icc (R : ℝ) (x : ℝ^n) :
    radialCutoff R x ∈ Icc (0 : ℝ) 1 :=
  (ContDiffBumpBase.ofInnerProductSpace (ℝ^n)).mem_Icc 2 (R⁻¹ • x)

attribute [inherit_doc radialCutoff] radialCutoff.eq_1

/-- The inner-product bump depends only on the norm through a smooth transition. -/
add_decl_doc ContDiffBumpBase.ofInnerProductSpace.eq_1

end SobolevSpace.Approximation
