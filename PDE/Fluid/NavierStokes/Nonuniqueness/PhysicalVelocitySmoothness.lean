/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalCoefficients
public import PDE.Fluid.Incompressible.Domain
public import PDE.Parabolic.Heat.ConvolutionSpace.JointSmoothness
import PDE.Analysis.Calculus.Homogeneous

/-!
# Smoothness of the physical velocity

At positive times the physical velocity is the sum of three parts
(`physicalVelocity_timeSpaceCons_eq`): the self-similar profile velocity `t^{-1/2} Ũ(x / √t)`,
smooth as a composition; the cutoff part `-e^{tΔ} w`, the heat flow of the bounded smooth
localization remainder, jointly smooth at positive times
(`contDiffOn_gaussianFlow_localizationRemainder`); and the correction part
`t^{-1/2} U_cor(log t, x / √t)`. The correction part is jointly smooth on `(0, 1) × ℝ³` once
the cutoff forcing and linear coefficient paths in physical variables are smooth in time
(`contDiffOn_physicalCorrectionField_of_coefficients`), so under that hypothesis the physical
velocity is smooth at every point of `(0, 1) × ℝ³`
(`contDiffAt_physicalVelocity_of_coefficients`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace PDE.Common
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable (D : UnstableProfile) {R : ℝ}

/-- The localization remainder of the far field is bounded, for every radius: the remainder
depends on `R` only through `R²`, and it vanishes at `R = 0`. -/
theorem exists_norm_localizationRemainder_le :
    ∃ M, ∀ x, ‖localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R x‖ ≤ M := by
  rcases eq_or_ne R 0 with rfl | hR0
  · exact ⟨0, fun x ↦ by simp [localizationRemainder_radius_zero]⟩
  rw [← localizationRemainder_abs]
  have hR : 0 < |R| := abs_pos.mpr hR0
  generalize |R| = R at hR ⊢
  obtain ⟨C, hC0, hC⟩ := PDE.exists_norm_le_mul_inv_norm_of_homogeneous
    (fun x c hc ↦ D.farField_smul x hc) (fun x hx ↦ (D.contDiffAt_farField hx).continuousAt)
  have hcont : Continuous (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) :=
    (contDiff_localizationRemainder hR fun x hx ↦ D.contDiffAt_farField hx).continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ^3) (2 * R + 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M (C * (2 * R)⁻¹), fun x ↦ ?_⟩
  by_cases hx : ‖x‖ ≤ 2 * R + 1
  · exact (hM x (by simpa using hx)).trans (le_max_left _ _)
  · have hx' := not_le.mp hx
    rw [localizationRemainder_of_two_mul_lt hR (by linarith)]
    refine (hC x).trans (le_trans ?_ (le_max_right _ _))
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith)) hC0

/-- The cutoff part `e^{tΔ} w` of the physical velocity is jointly smooth at positive times. -/
theorem contDiffOn_gaussianFlow_localizationRemainder (hR : 0 < R) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ^3 ↦
      gaussianFlow p.1 (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) p.2) {p | 0 < p.1} := by
  have hcont : Continuous (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) :=
    (contDiff_localizationRemainder hR fun x hx ↦ D.contDiffAt_farField hx).continuous
  obtain ⟨M, hM⟩ := exists_norm_localizationRemainder_le D (R := R)
  refine contDiffOn_piLp' 2 fun j ↦ ?_
  have hj : (fun p : ℝ × ℝ^3 ↦
      gaussianFlow p.1 (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) p.2 j) =
      fun p ↦ HeatEquation.initialValueSolution
        (fun y ↦ localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R y j) p.2 p.1 := by
    funext p
    rw [gaussianFlow_component p.1 (by norm_num : (1 : ℝ≥0∞) ≤ 4)
      (D.memLp_four_localizationRemainder R), initialValueSolution_eq_gaussianFlow]
  rw [hj]
  exact HeatEquation.contDiffOn_initialValueSolution_timeSpace _
    ((PiLp.continuous_apply 2 _ j).comp hcont)
    ⟨M, fun y ↦ by
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le _ j).trans (hM y)⟩

/-- The profile part `t^{-1/2} Ũ(x / √t)` of the physical velocity is jointly smooth at positive
times. -/
theorem contDiffOn_profileField :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ^3 ↦
      (Real.sqrt p.1)⁻¹ • D.U ((Real.sqrt p.1)⁻¹ • p.2)) {p | 0 < p.1} := by
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ^3 ↦ (Real.sqrt p.1)⁻¹) {p | 0 < p.1} :=
    fun p hp ↦ ((((Real.contDiffAt_sqrt (ne_of_gt hp)).comp p contDiffAt_fst).inv
      (Real.sqrt_pos.mpr hp).ne').contDiffWithinAt)
  exact hs.smul (D.contDiff_U.comp_contDiffOn (hs.smul contDiffOn_snd))

variable {D} {s : ℝ}

/-- **Smoothness of the physical velocity from smooth coefficient paths.** Above the threshold
radius and for `s ∈ [0, 1]`, if the cutoff forcing path and the linear coefficient path in
physical variables are smooth on `(0, 1)` at every order, then the physical velocity is smooth
at every point of `(0, 1) × ℝ³`. -/
theorem contDiffAt_physicalVelocity_of_coefficients (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hf : ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCutoffForcing D R m) (Ioo 0 1))
    (hA : ∀ m : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (physicalCoefficient D R m) (Ioo 0 1))
    {z : ℝ^(3 + 1)} (hz : z ∈ IncompressibleFlow.finiteTimeDomain 3 1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalVelocity D R s) z := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  let Φ : ℝ × ℝ^3 → ℝ^3 := fun p ↦
    (Real.sqrt p.1)⁻¹ • D.U ((Real.sqrt p.1)⁻¹ • p.2) -
      gaussianFlow p.1 (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) p.2 +
      (Real.sqrt p.1)⁻¹ • correctionField D R s (Real.log p.1) ((Real.sqrt p.1)⁻¹ • p.2)
  have hsub : Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ^3)) ⊆ {p | 0 < p.1} := fun p hp ↦ hp.1.1
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (Ioo 0 1 ×ˢ univ) :=
    (((contDiffOn_profileField D).mono hsub).sub
      ((contDiffOn_gaussianFlow_localizationRemainder D hR0).mono hsub)).add
      (contDiffOn_physicalCorrectionField_of_coefficients hR hs hf hA)
  have hopen : IsOpen (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ^3))) := isOpen_Ioo.prod isOpen_univ
  have hπ : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ^(3 + 1) ↦ (z 0, spatialPart z)) := by
    refine (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (3 + 1))).contDiff.prodMk ?_
    have he : (spatialPart : ℝ^(3 + 1) → ℝ^3) = ⇑(spatialPartCLM 3) :=
      funext fun z ↦ PiLp.ext fun i ↦ by rw [spatialPartCLM_apply, spatialPart_apply]
    rw [he]
    exact (spatialPartCLM 3).contDiff
  have hπz : (z 0, spatialPart z) ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set (ℝ^3)) :=
    ⟨⟨hz.1, hz.2⟩, mem_univ _⟩
  have h₁ : ContDiffAt ℝ (⊤ : ℕ∞) (Φ ∘ fun z : ℝ^(3 + 1) ↦ (z 0, spatialPart z)) z :=
    ContDiffAt.comp z (hΦ.contDiffAt (hopen.mem_nhds hπz)) hπ.contDiffAt
  refine h₁.congr_of_eventuallyEq ?_
  have hpos : {z' : ℝ^(3 + 1) | 0 < z' 0} ∈ 𝓝 z :=
    (isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (3 + 1))).continuous).mem_nhds
      hz.1
  filter_upwards [hpos] with z' hz'
  have h := physicalVelocity_timeSpaceCons_eq D R s hz' (spatialPart z')
  rw [timeSpaceCons_spatialPart] at h
  exact h

end NavierStokes.Nonuniqueness
