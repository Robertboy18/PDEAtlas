/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IntegrationByParts.Lipschitz.Potential
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.Coordinates.Measure
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.SmoothTesting

/-!
# From a Lipschitz potential to the initial conservation law

The scalar spatial derivative of a globally Lipschitz potential is bounded and
measurable. Its Hamilton–Jacobi equation, together with the derivative of the
initial trace, implies the conservation-law identity. Smooth
testing uses the initial-face integration formula; compact approximation then
supplies every C¹ test.
-/

@[expose] public noncomputable section

open PDE (partialDeriv)

open MeasureTheory Set PDE.Common PDE.Analysis PDE.Hyperbolic.ConservationLaw
open scoped Distributions ENNReal NNReal Topology

namespace HamiltonJacobi1D

private theorem norm_spatial_fderiv_le {W : ℝ × ℝ → ℝ} {K : ℝ≥0}
    (hW : LipschitzWith K W) (p : ℝ × ℝ) :
    ‖fderiv ℝ W p (1, 0)‖ ≤ K := by
  have h := (fderiv ℝ W p).le_opNorm (1, 0) |>.trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hW) (norm_nonneg (1, (0 : ℝ))))
  simpa using h

/-- The spatial derivative of a Lipschitz potential is globally `L∞`
in the Euclidean spacetime coordinates. -/
theorem memLp_top_spatial_fderiv_of_lipschitz {W : ℝ × ℝ → ℝ} {K : ℝ≥0} (hW : LipschitzWith K W) :
    MemLp (fun p : ℝ^2 ↦ fderiv ℝ W (scalarSpaceTimeEquiv p) (1, 0)) ∞ volume := by
  apply memLp_top_of_bound ((measurable_fderiv_apply_const ℝ W (1, 0)).comp
      scalarSpaceTimeEquiv.continuous.measurable).aestronglyMeasurable (K : ℝ)
  exact Filter.Eventually.of_forall fun p ↦ norm_spatial_fderiv_le hW _

/-- A Lipschitz Hamilton–Jacobi potential with the initial primitive
gives the weak initial-value solution, with all C¹ compact tests. -/
theorem isWeakInitialValueSolution_of_lipschitz_potential {W : ℝ × ℝ → ℝ} {F g : ℝ → ℝ} {K : ℝ≥0}
    (hW : LipschitzWith K W) (hF : Continuous F) (hg : LocallyIntegrable g volume)
    (htrace : ∀ᵐ x : ℝ, deriv (fun y ↦ W (y, 0)) x = g x)
    (hHJ : ∀ᵐ p ∂volume.restrict (univ ×ˢ Ioi (0 : ℝ)),
      fderiv ℝ W p (0, 1) + F (fderiv ℝ W p (1, 0)) = 0) :
    IsWeakInitialValueSolution F g (fun p : ℝ^2 ↦ fderiv ℝ W (scalarSpaceTimeEquiv p) (1, 0)) := by
  let u : ℝ^2 → ℝ := fun p ↦ fderiv ℝ W (scalarSpaceTimeEquiv p) (1, 0)
  have huM : Measurable u := (measurable_fderiv_apply_const ℝ W (1, 0)).comp
    scalarSpaceTimeEquiv.continuous.measurable
  have hu := (memLp_top_spatial_fderiv_of_lipschitz hW).locallyIntegrable (by simp)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : ℝ) (K : ℝ)).image hF ).isBounded.exists_norm_le
  have hqBound (p : ℝ^2) : ‖F (u p)‖ ≤ B := by
    apply hB _ ⟨u p, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_spatial_fderiv_le hW (scalarSpaceTimeEquiv p)
  have hq : LocallyIntegrable (fun p : ℝ^2 ↦ F (u p)) volume :=
    (memLp_top_of_bound (hF.measurable.comp huM).aestronglyMeasurable
    B (Filter.Eventually.of_forall hqBound)).locallyIntegrable (by simp)
  have huR : LocallyIntegrable u (volume.restrict forwardHalfSpace) :=
    hu.mono_measure Measure.restrict_le_self
  have hqR : LocallyIntegrable (fun p ↦ F (u p)) (volume.restrict forwardHalfSpace) :=
    hq.mono_measure Measure.restrict_le_self
  have hI (φ : InitialValueTestFunction) :
      IntegrableOn (InteriorWeakForm.integrand u (fun p ↦ F (u p)) φ)
        forwardHalfSpace := (huR.integrable_smul_left_of_hasCompactSupport
      (φ.continuous_partialDeriv 0) (φ.hasCompactSupport_partialDeriv 0)).add
      (hqR.integrable_smul_left_of_hasCompactSupport
        (φ.continuous_partialDeriv 1) (φ.hasCompactSupport_partialDeriv 1))
  refine ⟨hu.locallyIntegrableOn _, hq.locallyIntegrableOn _, hg, hI, ?_⟩
  refine initialWeak_eq_zero_of_smooth huR hqR hg fun a ↦ ?_
  let φ : ℝ × ℝ → ℝ := a ∘ scalarSpaceTimeEquiv.symm
  have hφ : ContDiff ℝ 2 φ :=
    (a.contDiff.of_le (by simp)).comp scalarSpaceTimeEquiv.symm.contDiff
  have hc : HasCompactSupport φ :=
    a.hasCompactSupport.comp_homeomorph scalarSpaceTimeEquiv.symm.toHomeomorph
  have hφderiv (p v : ℝ × ℝ) : fderiv ℝ φ p v = fderiv ℝ (a : ℝ^2 → ℝ) (scalarSpaceTimeEquiv.symm p)
        (scalarSpaceTimeEquiv.symm v) := congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ ↦ A v)
      (((a.contDiff.differentiable (by simp) _).hasFDerivAt.comp p
        scalarSpaceTimeEquiv.symm.toContinuousLinearMap.hasFDerivAt).fderiv)
  have hpartial (p : ℝ × ℝ) :
      fderiv ℝ φ p (0, 1) = (∂[0] (a : ℝ^2 → ℝ)) (scalarSpaceTimeEquiv.symm p) ∧
        fderiv ℝ φ p (1, 0) = (∂[1] (a : ℝ^2 → ℝ)) (scalarSpaceTimeEquiv.symm p) := by
    simp only [hφderiv, partialDeriv]
    constructor <;> congr 1 <;> ext i <;> fin_cases i <;> simp
  have hemb := scalarSpaceTimeEquiv.symm.toHomeomorph.measurableEmbedding
  have hset : scalarSpaceTimeEquiv.symm ⁻¹' (forwardHalfSpace : Set ℝ^2) =
      univ ×ˢ Ioi (0 : ℝ) := by
    ext p
    simp [forwardHalfSpace]
  have heq := measurePreserving_scalarSpaceTimeEquiv_symm.setIntegral_preimage_emb
    hemb (g := fun p ↦ (∂[0] (a : ℝ^2 → ℝ)) p * u p + (∂[1] (a : ℝ^2 → ℝ)) p * F (u p))
    (s := (forwardHalfSpace : Set ℝ^2))
  rw [hset] at heq
  simp only [smul_eq_mul]
  rw [← heq]
  have hident : (fun p ↦ (∂[0] (a : ℝ^2 → ℝ)) (scalarSpaceTimeEquiv.symm p) *
          u (scalarSpaceTimeEquiv.symm p) + (∂[1] (a : ℝ^2 → ℝ)) (scalarSpaceTimeEquiv.symm p) *
          F (u (scalarSpaceTimeEquiv.symm p))) =ᵐ[ volume.restrict (univ ×ˢ Ioi (0 : ℝ))]
      (fun p ↦ fderiv ℝ W p (1, 0) * fderiv ℝ φ p (0, 1) -
        fderiv ℝ W p (0, 1) * fderiv ℝ φ p (1, 0)) := by
    filter_upwards [hHJ] with p hp
    simp only [u, ContinuousLinearEquiv.apply_symm_apply, hpartial]
    rw [show F (fderiv ℝ W p (1, 0)) = -fderiv ℝ W p (0, 1) by linarith only [hp]]
    ring
  rw [integral_congr_ae hident]
  have hboundary : (∫ x : ℝ, a !₂[0, x] * g x) = ∫ x : ℝ, g x * φ (x, 0) := by
    simp only [φ, Function.comp_apply, scalarSpaceTimeEquiv_symm_apply, mul_comm]
  rw [hboundary]
  exact integral_halfSpace_rotated_fderiv_add_initial_eq_zero hW hφ hc htrace

end HamiltonJacobi1D
