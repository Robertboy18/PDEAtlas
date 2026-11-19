/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalLerayForm
public import PDE.Fluid.NavierStokes.Nonuniqueness.Statement

/-!
# The momentum equation of the physical solutions

The physical velocity `u` of an unstable profile and its Riesz pressure `p` (`physicalPressure`)
solve the unforced Navier–Stokes equations with unit viscosity at every point of `(0, 1) × ℝ³`, and
`u` is divergence free there.

## Main results

* `hasDerivAt_physicalVelocity_time`: for `t ∈ (0, 1)` each component of `u` is differentiable in
  time, with derivative the sum of the derivatives of the profile, cutoff and correction parts.
* `momentumEquationAt_physical`: the momentum equation at every point of `(0, 1) × ℝ³`.
* `divergenceFreeAt_physical`: `u` is divergence free at every point of `(0, 1) × ℝ³`.

## How it works

We compute the time derivative of the slice part by part. The dilated profile `ũ(t) = a Ũ(a ·)`,
with `Ũ = D.U` and `a = t^{-1/2}`, has `∂ₜũ = -½ a³ (Ũ + ξ·∇Ũ)(a ·)`
(`hasDerivAt_physicalProfileField`). The cutoff part, the negative of the heat flow of the
localization remainder, solves the heat equation (`hasDerivAt_physicalCutoffField`), and the
correction solves `∂ₜu_cor = Δu_cor + Π g` with `Π` the Leray projection and `g` the forcing of the
correction (`physicalForcing`, `hasDerivAt_physicalCorrectionField`). With `Δũ = a³ ΔŨ(a ·)` the
momentum equation becomes the Leray form of the slices (`physical_lerayForm`). The divergence of `u`
at `(t, x)` is that of the slice at time `t`, which vanishes
(`divergence_velocitySlice_physicalVelocity`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Common
open scoped NNReal ENNReal Sobolev Laplacian

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable {D : UnstableProfile} {R s : ℝ}

/-- The square of the physical factor at `log t` is `t⁻¹`. -/
theorem physicalFactor_log_sq {t : ℝ} (ht : 0 < t) : physicalFactor (Real.log t) ^ 2 = t⁻¹ := by
  rw [physicalFactor_log ht, inv_pow, Real.sq_sqrt ht.le]

/-- **The time derivative of the profile part.** `∂ₜ (a Ũ(a x)) = -½ a³ (Ũ + ξ·∇Ũ)(a x)` with
`a = t^{-1/2}`. -/
theorem hasDerivAt_physicalProfileField {t : ℝ} (ht : 0 < t) (x : ℝ^3) :
    HasDerivAt (fun t' ↦ physicalProfileField D t' x)
      ((-(1 / 2) * physicalFactor (Real.log t) ^ 3) •
        SpectralProfile.velocityDrift D.U (physicalFactor (Real.log t) • x)) t := by
  have h₁ : HasDerivAt (fun t' ↦ -(Real.log t' / 2)) (-(t⁻¹ / 2)) t :=
    ((Real.hasDerivAt_log ht.ne').div_const 2).neg
  have hb : HasDerivAt (fun t' ↦ physicalFactor (Real.log t'))
      (-(1 / 2) * physicalFactor (Real.log t) ^ 3) t := by
    have h₂ := (Real.hasDerivAt_exp _).comp t h₁
    have hf : (fun t' ↦ physicalFactor (Real.log t')) = Real.exp ∘ fun t' ↦ -(Real.log t' / 2) :=
      rfl
    rw [hf]
    convert h₂ using 1
    rw [pow_succ, physicalFactor_log_sq ht, physicalFactor]
    ring_nf
  exact (hasDerivAt_dilateField_apply D.contDiff_U _ x).scomp t hb

/-- **The cutoff part solves the heat equation** at positive times. -/
theorem hasDerivAt_physicalCutoffField (hR : 0 < R) {t : ℝ} (ht : 0 < t) (x : ℝ^3) (j : Fin 3) :
    HasDerivAt (fun t' ↦ physicalCutoffField D R t' x j)
      (PDE.laplacian (fun y ↦ physicalCutoffField D R t y j) x) t := by
  set W := localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R with hWdef
  have hW := D.contDiff_remainder hR
  have hW4 := D.memLp_four_localizationRemainder R
  have hWj : Continuous (fun y ↦ W y j) := (PiLp.continuous_apply 2 _ j).comp hW.continuous
  obtain ⟨M, hM⟩ := D.exists_bound_iteratedFDeriv_remainder hR 0
  have hbdd : ∃ M, ∀ y, |W y j| ≤ M := ⟨M, fun y ↦ by
    rw [← Real.norm_eq_abs]
    refine (PiLp.norm_apply_le _ j).trans ?_
    simpa [norm_iteratedFDeriv_zero] using hM y⟩
  have hslice (t' : ℝ) (ht' : 0 < t') : (fun y ↦ physicalCutoffField D R t' y j) =
      fun y ↦ -HeatEquation.initialValueSolution (fun y ↦ W y j) y t' := by
    funext y
    rw [physicalCutoffField_eq ht', Pi.neg_apply, PiLp.neg_apply,
      gaussianFlow_component t' (by norm_num) hW4 y j, initialValueSolution_eq_gaussianFlow]
  have hev : (fun t' ↦ physicalCutoffField D R t' x j) =ᶠ[𝓝 t]
      fun t' ↦ -HeatEquation.initialValueSolution (fun y ↦ W y j) x t' := by
    filter_upwards [Ioi_mem_nhds ht] with t' ht'
    exact congrFun (hslice t' ht') x
  have hd := HeatEquation.hasDerivAt_initialValueSolution_time (fun y ↦ W y j) x t ht hWj hbdd
  have hderiv := HeatEquation.deriv_initialValueSolution_time_eq_laplacian (fun y ↦ W y j) x t ht
    hWj hbdd
  have hd' : HasDerivAt (fun s ↦ HeatEquation.initialValueSolution (fun y ↦ W y j) x s)
      (PDE.laplacian (fun x' ↦ HeatEquation.initialValueSolution (fun y ↦ W y j) x' t) x) t := by
    rw [← hderiv]
    exact hd.differentiableAt.hasDerivAt
  refine (hd'.neg.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hslice t ht]
  exact (PDE.laplacian_neg _ x).symm

/-- **The time derivative of the physical velocity.** For `t ∈ (0, 1)` each component of the
physical velocity is differentiable in time, with derivative the sum of the derivatives of the
profile, cutoff and correction parts. -/
theorem hasDerivAt_physicalVelocity_time (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : ℝ^3) (j : Fin 3) :
    HasDerivAt (fun t' ↦ physicalVelocity D R s (timeSpaceCons t' x) j)
      ((-(1 / 2) * physicalFactor (Real.log t) ^ 3) *
          SpectralProfile.velocityDrift D.U (physicalFactor (Real.log t) • x) j +
        PDE.laplacian (fun y ↦ physicalCutoffField D R t y j) x +
        (Δ (fun y ↦ physicalCorrectionField D R s t y j) x +
          classicalRepresentativeCLM (three_lt_two_mul_succ_sub_one (by norm_num : (3 : ℝ) <
            2 * ((3 : ℕ) : ℝ))) (leraySobolev 3 (3 + 1) (physicalForcing D R s 3
              (by norm_num) t) j) x)) t := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  have hP := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_physicalProfileField (D := D) ht.1 x)
  have hC := hasDerivAt_physicalCutoffField (D := D) hR0 ht.1 x j
  have hK := hasDerivAt_physicalCorrectionField hR hs ht x j
  have hev : (fun t' ↦ physicalVelocity D R s (timeSpaceCons t' x) j) =ᶠ[𝓝 t]
      fun t' ↦ physicalProfileField D t' x j + physicalCutoffField D R t' x j +
        physicalCorrectionField D R s t' x j := by
    filter_upwards [Ioi_mem_nhds ht.1] with t' ht'
    have h := congrFun (velocitySlice_physicalVelocity_eq_add (D := D) (R := R) (s := s) ht') x
    rw [velocitySlice] at h
    rw [h]
    rfl
  refine ((hP.add hC).add hK).congr_of_eventuallyEq hev |>.congr_deriv ?_
  change (-(1 / 2) * physicalFactor (Real.log t) ^ 3) •
      SpectralProfile.velocityDrift D.U (physicalFactor (Real.log t) • x) j + _ + _ = _
  rw [smul_eq_mul]
  rfl

/-- **The momentum equation.** Above the threshold radius and for `s ∈ [0, 1]`, the physical
velocity and pressure satisfy the unforced Navier–Stokes momentum equation with unit viscosity at
every point of `(0, 1) × ℝ³`. -/
theorem momentumEquationAt_physical (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (hu₀ : DistributionallyDivergenceFree (localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R))
    {z : ℝ^(3 + 1)} (hz : z ∈ finiteTimeDomain 3 1) :
    MomentumEquationAt (unforcedProblem (localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R) hu₀)
      (physicalVelocity D R s) (physicalPressure D R s) z := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  have ht : z 0 ∈ Ioo (0 : ℝ) 1 := ⟨hz.1, hz.2⟩
  have hu := (physical_time_regularity D R s hR hs).2 z hz
  have hp := contDiffAt_physicalPressure hR hs hz
  rw [← timeSpaceCons_spatialPart z] at hu hp ⊢
  set t := z 0
  set x := spatialPart z
  set v := velocitySlice (physicalVelocity D R s) t with hvdef
  set a := physicalFactor (Real.log t) with hadef
  have huj (j : Fin 3) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ physicalVelocity D R s y j)
      (timeSpaceCons t x) := (contDiffAt_piLp 2).mp hu j
  have hdu (j : Fin 3) : DifferentiableAt ℝ (fun y ↦ physicalVelocity D R s y j)
      (timeSpaceCons t x) := (huj j).differentiableAt (by simp)
  have hvs := contDiff_velocitySlice_physicalVelocity hR hs ht.1 ht.2.le
  have hvd : Differentiable ℝ v := hvs.differentiable (by simp)
  refine PiLp.ext fun j ↦ ?_
  simp only [PiLp.add_apply, materialDerivative_apply, PDE.spatialGradient_apply, viscousTerm_apply,
    spatialVectorLaplacian_apply, unforcedProblem_forcing, unforcedProblem_kinematicViscosity,
    add_zero, one_mul]
  -- the time derivative
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ x t (hdu j),
    (hasDerivAt_physicalVelocity_time hR hs ht x j).deriv]
  -- the spatial derivatives
  have hsp (i : Fin 3) : (∂[i.succ] (fun y ↦ physicalVelocity D R s y j)) (timeSpaceCons t x) =
      ∂[i] (fun y ↦ v y j) x := (PDE.partialDeriv_timeSpaceCons_spatial i _ t x (hdu j)).symm
  have hval (i : Fin 3) : physicalVelocity D R s (timeSpaceCons t x) i = v x i := rfl
  simp_rw [hsp, hval]
  -- the pressure gradient
  have hpz : (∂[j.succ] (physicalPressure D R s)) (timeSpaceCons t x) =
      ∂[j] (rieszPressure v) x := by
    rw [← PDE.partialDeriv_timeSpaceCons_spatial j _ t x (hp.differentiableAt (by simp))]
    congr 1
    funext y
    exact physicalPressure_timeSpaceCons D R s ht.1 y
  rw [hpz]
  -- the Laplacian
  rw [spatialLaplacian_timeSpaceCons_of_contDiffAt ((huj j).of_le (by simp))]
  have hvP := (contDiff_physicalProfileField (D := D) t)
  have hvC := (contDiff_physicalCutoffField (D := D) (R := R) t)
  have hvK : ContDiff ℝ (⊤ : ℕ∞) (physicalCorrectionField D R s t) :=
    contDiff_physicalCorrectionField hR hs ht.1 ht.2.le
  have hcomp {F : ℝ^3 → ℝ^3} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
      ContDiffAt ℝ 2 (fun y ↦ F y j) x :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hF).contDiffAt.of_le (by simp)
  have hlap : PDE.laplacian (fun y ↦ physicalVelocity D R s (timeSpaceCons t y) j) x =
      a ^ 3 * PDE.laplacian D.U (a • x) j +
        PDE.laplacian (fun y ↦ physicalCutoffField D R t y j) x +
        Δ (fun y ↦ physicalCorrectionField D R s t y j) x := by
    have hsl : (fun y ↦ physicalVelocity D R s (timeSpaceCons t y) j) = fun y ↦
        (physicalProfileField D t y j + physicalCutoffField D R t y j) +
          physicalCorrectionField D R s t y j := by
      funext y
      have h := congrFun (velocitySlice_physicalVelocity_eq_add (D := D) (R := R) (s := s) ht.1) y
      rw [velocitySlice] at h
      rw [h]
      rfl
    rw [hsl, PDE.laplacian_add _ _ x ((hcomp hvP).add (hcomp hvC)) (hcomp hvK),
      PDE.laplacian_add _ _ x (hcomp hvP) (hcomp hvC),
      (hcomp hvK).coordinate_laplacian_eq_laplacian,
      ← PDE.laplacian_apply_of_contDiff (hvP.of_le (by simp)) x j, physicalProfileField,
      laplacian_dilateField D.contDiff_U, PiLp.smul_apply, smul_eq_mul]
  rw [hlap]
  -- the convection
  have hadv : PDE.advectiveDerivative v v x j = ∑ i : Fin 3, v x i * ∂[i] (fun y ↦ v y j) x := by
    rw [PDE.advectiveDerivative, ContinuousLinearMap.apply_eq_sum_mul_apply_single]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← PDE.partialDeriv_apply i j (hvd x)]
    rfl
  have hLF := physical_lerayForm hR hs ht.1 ht.2.le x j
  rw [hadv] at hLF
  linarith

/-- **Incompressibility.** Above the threshold radius and for `s ∈ [0, 1]`, the physical
velocity is divergence free at every point of `(0, 1) × ℝ³`. -/
theorem divergenceFreeAt_physical (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    {z : ℝ^(3 + 1)} (hz : z ∈ finiteTimeDomain 3 1) :
    DivergenceFreeAt (physicalVelocity D R s) z := by
  have hu := (physical_time_regularity D R s hR hs).2 z hz
  rw [← timeSpaceCons_spatialPart z] at hu ⊢
  rw [DivergenceFreeAt, ← spatialFieldDivergence_velocitySlice _ _ (hu.differentiableAt (by simp))]
  exact divergence_velocitySlice_physicalVelocity hR hs hz.1 hz.2.le _

end NavierStokes.Nonuniqueness
