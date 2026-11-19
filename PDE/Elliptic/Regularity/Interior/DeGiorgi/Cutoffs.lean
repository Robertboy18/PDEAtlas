/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.Analysis.Calculus.SmoothTransitionDerivatives

/-!
# Quantitative smooth cutoffs between concentric balls

A single Lipschitz constant for Mathlib's smooth transition function gives
smooth cutoffs with derivative bounded by a constant times `(R-r)⁻¹`.
The cutoff equals one on the smaller closed ball and has compact support
strictly inside the larger open ball. The constant is uniform in the centre
and both radii.
-/

@[expose] public noncomputable section

open Set Metric Function TopologicalSpace
open scoped Distributions Topology NNReal ContDiff

namespace PDE.Elliptic.Regularity.DeGiorgi

private theorem radial_transition_contDiff {n : ℕ} (z : ℝ^n)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    ContDiff ℝ ∞ (fun x : ℝ^n ↦
      Real.smoothTransition ((s - ‖x - z‖) / (s - r))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = z
  · subst x
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with x hx
    apply Real.smoothTransition.one_of_one_le
    apply (one_le_div (sub_pos.mpr hrs)).mpr
    have hd : ‖x - z‖ < r := mem_ball_iff_norm.mp hx
    linarith
  · exact Real.smoothTransition.contDiffAt.comp x
      ((contDiffAt_const.sub
        ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hx))).div_const _)

/-- Smooth cutoffs with a derivative bound uniform in the centre and radii.
Their support is compactly contained in the larger open ball, so they are
admissible tests for every weak equation on that ball. -/
theorem exists_ball_cutoffs_with_derivative_bound {n : ℕ} :
    ∃ D : ℝ, 0 < D ∧ ∀ (z : ℝ^n) (r R : ℝ), 0 < r → r < R →
      ∃ η : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
        tsupport η.toFun ⊆ ball z R ∧
          (∀ x ∈ closedBall z r, η.toFun x = 1) ∧
          (∀ x, 0 ≤ η.toFun x ∧ η.toFun x ≤ 1) ∧
          ∀ x, ‖fderiv ℝ η.toFun x‖ ≤ D / (R - r) := by
  obtain ⟨K, hK⟩ := Analysis.exists_lipschitzWith_smoothTransition
  refine ⟨2 * ((K : ℝ) + 1), by positivity, ?_⟩
  intro z r R hr hrR
  let s := (r + R) / 2
  have hrs : r < s := by dsimp only [s]; linarith
  have hsR : s < R := by dsimp only [s]; linarith
  have hgap : 0 < s - r := sub_pos.mpr hrs
  let g : ℝ^n → ℝ := fun x ↦ Real.smoothTransition ((s - ‖x - z‖) / (s - r))
  have hg : ContDiff ℝ ∞ g := radial_transition_contDiff z hr hrs
  have hsupp : tsupport g ⊆ closedBall z s := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra h
    have hd : s < ‖x - z‖ := lt_of_not_ge (fun hle ↦ h (mem_closedBall_iff_norm.mpr hle))
    exact hx (Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hgap.le))
  have hcompact : HasCompactSupport g :=
    (isCompact_closedBall z s).of_isClosed_subset isClosed_closure hsupp
  let η : 𝓓((⊤ : Opens (ℝ^n)), ℝ) := ⟨g, hg, hcompact, subset_univ _⟩
  refine ⟨η, hsupp.trans (closedBall_subset_ball hsR), ?_, ?_, ?_⟩
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    apply (one_le_div hgap).mpr
    have hd : ‖x - z‖ ≤ r := mem_closedBall_iff_norm.mp hx
    linarith
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · have hLip : LipschitzWith ⟨(K : ℝ) / (s - r), by positivity⟩ g := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have hn : |‖x - z‖ - ‖y - z‖| ≤ dist x y := by
        simpa only [sub_sub_sub_cancel_right, dist_eq_norm] using
          abs_norm_sub_norm_le (x - z) (y - z)
      calc
        dist (g x) (g y) ≤ (K : ℝ) *
            dist ((s - ‖x - z‖) / (s - r)) ((s - ‖y - z‖) / (s - r)) :=
          hK.dist_le_mul _ _
        _ = (K : ℝ) * (|‖x - z‖ - ‖y - z‖| / (s - r)) := by
          rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hgap,
            sub_sub_sub_cancel_left, abs_sub_comm]
        _ ≤ (K : ℝ) * (dist x y / (s - r)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn hgap.le) K.coe_nonneg
        _ = _ := by
          change (K : ℝ) * (dist x y / (s - r)) = ((K : ℝ) / (s - r)) * dist x y
          ring
    intro x
    have hder : ‖fderiv ℝ g x‖ ≤ (K : ℝ) / (s - r) :=
      norm_fderiv_le_of_lipschitz ℝ hLip
    refine hder.trans ?_
    apply (div_le_div_iff₀ hgap (sub_pos.mpr hrR)).mpr
    dsimp only [s]
    nlinarith [K.coe_nonneg]

end PDE.Elliptic.Regularity.DeGiorgi

namespace SobolevSpace.GraphSpace

open MeasureTheory

/-- A uniform bound on the Fréchet derivative bounds every represented
coordinate derivative in L∞ on a domain of finite measure. -/
theorem norm_partialTestFunctionLpTop_le_of_fderiv_bound {n : ℕ} {V : Set ℝ^n}
    [IsFiniteMeasure (domainMeasure n V)]
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ x, ‖fderiv ℝ η.toFun x‖ ≤ D) (i : Fin n) :
    ‖partialTestFunctionLpTop (Ω := V) η i‖ ≤ D := by
  have hb : ∀ᵐ x ∂domainMeasure n V,
      ‖partialTestFunctionLpTop (Ω := V) η i x‖ ≤ D := by
    filter_upwards [partialTestFunctionLpTop_apply_ae (Ω := V) η i] with x hx
    rw [hx]
    change ‖fderiv ℝ η.toFun x (EuclideanSpace.single i 1)‖ ≤ D
    exact ((fderiv ℝ η.toFun x).le_opNorm _).trans
      (by simpa only [PiLp.norm_single, norm_one, mul_one] using hd x)
  simpa only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, one_mul]
    using Lp.norm_le_of_ae_bound hD hb

end SobolevSpace.GraphSpace
