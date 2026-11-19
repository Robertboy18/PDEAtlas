/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.FirstOrder.Viscosity.PolynomialFamily.Forcing
import PDE.Analysis.MeasureTheory.Lp.FiniteCoordinates.Hilbert
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Forcing norms and the time horizon

Sobolev slicing identifies the squared joint H¹ norm with the sum of the squared
spatial H¹ and time-derivative L² Bochner norms. For `ε = T⁻²`, the forcing grows at most
like `√T`, while the terminal state grows like `T`. Thus a bound valid for all
these solutions cannot use one constant independent of the time horizon.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily

open Filter MeasureTheory Set TopologicalSpace PDE.Common
open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Slices
open scoped ENNReal Distributions Sobolev

attribute [local instance] profileNormedAddCommGroup profileNormedSpace

/-- The polynomial state is a strong solution with the forcing `jointForcing`. -/
theorem isStrongTransportDiffusionSolution_vectorState_jointForcing
    {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution ε 0 T
      (fun _ _ _ _ ↦ 0)
      (fun p y ↦ wkpBaseCoordinateCLM (jointForcing hT ε p) (timeSpaceCons y.1 y.2))
      0 (strongState T) (strongVelocity T) (vectorState 1) := by
  refine { isStrongTransportDiffusionSolution_vectorState T ε with equation := ?_ }
  filter_upwards [(isStrongTransportDiffusionSolution_vectorState T ε).equation,
    jointForcing_base_sections hT ε]
    with t ht hf
  filter_upwards [ht, hf] with x hx hfx
  intro p
  exact (hx p).trans (hfx p).symm

/-- `forcingCurve ε t` is represented by `forcing ε t`. -/
theorem forcingCurve_base_ae (ε t : ℝ) :
    (wkpBaseCoordinateCLM (forcingCurve ε t) : ℝ^1 → ℝ) =ᵐ[volume]
      forcing ε t := by
  have hb := globalTestFunctionToWkpOn_coordinate_ae (k := 1) (p := 2) (Ω := univ)
    spatialTest (baseIndex 1 1)
  have hlap := globalTestFunctionToWkpOn_coordinate_ae (k := 1) (p := 2) (Ω := univ)
    laplaceTest (baseIndex 1 1)
  simp only [domainMeasure, Measure.restrict_univ, TestFunction.toFun_eq_coe,
    ← wkpCoordinateCLM_apply] at hb
  rw [← profile] at hb
  simp only [domainMeasure, Measure.restrict_univ, baseIndex_toList, iteratedPartialDeriv,
    TestFunction.toFun_eq_coe, ← wkpBaseCoordinateCLM_apply] at hlap
  rw [← laplaceProfile] at hlap
  have hs := Lp.coeFn_smul (ε * t) (wkpBaseCoordinateCLM (laplaceProfile 1))
  have hd := Lp.coeFn_sub (wkpBaseCoordinateCLM (profile 1))
    ((ε * t) • wkpBaseCoordinateCLM (laplaceProfile 1))
  simp only [domainMeasure, Measure.restrict_univ] at hs hd
  filter_upwards [hb, hlap, hs, hd] with x hx hl hsm hsub
  simp only [forcingCurve, map_sub, map_smul]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsm]
  change wkpBaseCoordinateCLM (profile 1) x -
    (ε * t) * wkpBaseCoordinateCLM (laplaceProfile 1) x = _
  rw [hl]
  have hbase : wkpBaseCoordinateCLM (profile 1) x = spatialTest x := by
    simpa only [wkpBaseCoordinateCLM, baseIndex_toList, iteratedPartialDeriv] using hx
  rw [hbase]
  rfl

/-- `forcingVelocityLp T ε` is represented by `-ε Δq`. -/
theorem forcingVelocity_sections (T ε : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume,
      forcingVelocityLp T ε t x = -ε * laplaceTest x := by
  have hG := (memLp_const (μ := volume.restrict (Ioc 0 T))
    (p := (2 : ℝ≥0∞)) (-ε • wkpBaseCoordinateCLM (laplaceProfile 1))).coeFn_toLp
  have hs := Lp.coeFn_smul (-ε) (wkpBaseCoordinateCLM (laplaceProfile 1))
  simp only [domainMeasure, Measure.restrict_univ] at hs
  have hlap := globalTestFunctionToWkpOn_coordinate_ae (k := 1) (p := 2) (Ω := univ)
    laplaceTest (baseIndex 1 1)
  simp only [domainMeasure, Measure.restrict_univ, baseIndex_toList, iteratedPartialDeriv,
    TestFunction.toFun_eq_coe, ← wkpBaseCoordinateCLM_apply] at hlap
  rw [← laplaceProfile] at hlap
  filter_upwards [hG] with t ht
  filter_upwards [hs, hlap] with x hx hl
  rw [show forcingVelocityLp T ε t = -ε • wkpBaseCoordinateCLM (laplaceProfile 1)
    from ht, hx]
  change -ε * wkpBaseCoordinateCLM (laplaceProfile 1) x = _
  rw [hl]

/-- The squared joint `H¹` norm of the forcing is the sum of the squared norms of
`forcingLp` and `forcingVelocityLp`. -/
theorem norm_jointForcing_sq {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    ‖jointForcing hT ε‖ ^ 2 =
      ‖forcingLp T ε‖ ^ 2 + ‖forcingVelocityLp T ε‖ ^ 2 := by
  obtain ⟨F, G, _hw, hb, hd, ht⟩ :=
    exists_vector_timeSlices_of_wkpSpaceOn (jointForcing hT ε)
  have hFraw : (forcingLp T ε : ℝ → W^{1,2}(ℝ^1))
      =ᵐ[volume.restrict (Ioc 0 T)] forcingCurve ε := by
    exact MemLp.coeFn_toLp _
  have hF : ∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ p, F t p = forcingLp T ε t := by
    filter_upwards [hb, jointForcing_base_sections hT ε, hFraw] with t hbt hft hraw
    intro p
    apply wkpBaseCoordinateCLM_injective isOpen_univ
    apply Lp.ext
    simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [hbt, hft, forcingCurve_base_ae ε t] with x hbx hfx hcurve
    rw [hbx p, hfx p, hraw, hcurve]
  have hG : ∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ p,
      G t p = forcingVelocityLp T ε t := by
    filter_upwards [ht, jointForcing_time_sections hT ε, forcingVelocity_sections T ε]
      with t htt hft hraw
    intro p
    apply Lp.ext
    simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [htt, hft, hraw] with x htx hfx hx
    rw [htx p, hfx p, hx]
  have hFnorm := Lp.norm_sq_piLp_of_ae_coordinates F (fun _ ↦ forcingLp T ε) hF
  have hGnorm := Lp.norm_sq_piLp_of_ae_coordinates G (fun _ ↦ forcingVelocityLp T ε) hG
  have hnorm := norm_sq_vector_timeSlices_add_timeDerivative_eq (jointForcing hT ε)
  rw [restrict_Ioo_eq_restrict_Ioc] at hnorm
  simpa only [hFnorm, hGnorm, Fin.sum_univ_one] using (hnorm F G hb hd ht).symm

/-- `‖jointForcing‖ ≤ ‖forcingLp‖ + ‖forcingVelocityLp‖`. -/
theorem norm_jointForcing_le {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    ‖jointForcing hT ε‖ ≤ ‖forcingLp T ε‖ + ‖forcingVelocityLp T ε‖ := by
  have h := norm_jointForcing_sq hT ε
  nlinarith [norm_nonneg (jointForcing hT ε), norm_nonneg (forcingLp T ε),
    norm_nonneg (forcingVelocityLp T ε),
    mul_nonneg (norm_nonneg (forcingLp T ε)) (norm_nonneg (forcingVelocityLp T ε))]

/-- `vectorState 1 t` has the norm of `state 1 t`. -/
theorem norm_vectorState (t : ℝ) : ‖vectorState 1 t‖ = ‖state 1 t‖ := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 1 ↦ W^{1,2}(ℝ^1)) (vectorState 1 t)
  simp only [Fin.sum_univ_one] at h
  change ‖vectorState 1 t‖ ^ 2 = ‖state 1 t‖ ^ 2 at h
  nlinarith [norm_nonneg (vectorState 1 t), norm_nonneg (state 1 t)]

/-- No constant `C` gives `‖u(T)‖ ≤ C ‖F‖` for all `T ≥ 1` with `ε = T⁻²`. -/
theorem not_exists_time_uniform_joint_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (hT : 1 ≤ T),
      ‖vectorState 1 T‖ ≤
        C * ‖jointForcing (lt_of_lt_of_le zero_lt_one hT) (T ^ 2)⁻¹‖ := by
  rintro ⟨C, hC, h⟩
  apply not_exists_time_uniform_bound
  refine ⟨C, fun T hT ↦ ?_⟩
  rw [← norm_vectorState]
  exact (h T hT).trans (mul_le_mul_of_nonneg_left
    (norm_jointForcing_le (lt_of_lt_of_le zero_lt_one hT) (T ^ 2)⁻¹) hC)

end PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily
