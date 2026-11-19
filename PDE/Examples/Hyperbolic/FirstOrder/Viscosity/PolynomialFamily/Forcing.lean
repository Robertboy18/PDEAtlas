/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.FirstOrder.Viscosity.PolynomialFamily.Solution
public import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.Norms
import CAS.ExactTactic

/-!
# The polynomial solution's spacetime forcing

A smooth time cutoff extends `q - ε*t*Δq` off the closed time interval. Its joint
spacetime H¹ class has the forcing and its time derivative as its base and
time coordinates. These identifications are the hypotheses of the viscous velocity
estimate.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily

open Filter MeasureTheory Set TopologicalSpace PDE.Common
open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Slices
open scoped ENNReal Distributions Sobolev

attribute [local instance] profileNormedAddCommGroup profileNormedSpace

/-- The time cutoff `timeCutoff` as a test function. -/
def constantTimeTest {T : ℝ} (hT : 0 < T) : 𝓓((⊤ : Opens ℝ), ℝ) :=
  ⟨timeCutoff hT, (timeCutoff hT).contDiff, (timeCutoff hT).hasCompactSupport,
    subset_univ _⟩

/-- The cutoff equals one on a neighborhood of every point of the closed slab. -/
theorem constantTimeTest_eventuallyEq {T : ℝ} (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    (constantTimeTest hT : ℝ → ℝ) =ᶠ[nhds t] fun _ ↦ 1 := by
  apply (timeCutoff hT).eventuallyEq_one_of_mem_ball
  change dist t 0 < T + 1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  linarith [ht.2]

/-- A compactly supported smooth extension of the forcing `q - ε t Δq` to spacetime. -/
def jointForcingTest {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    𝓓((⊤ : Opens (SpaceTime 1)), ℝ) :=
  TestFunction.timeSpaceTensor (constantTimeTest hT) (spatialTest + ε • laplaceTest) -
    ε • TestFunction.timeSpaceTensor (timeTest hT) laplaceTest

/-- On the closed slab the extension equals `forcing ε t x`. -/
theorem jointForcingTest_eq {T : ℝ} (hT : 0 < T) (ε : ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : ℝ^1) :
    jointForcingTest hT ε (timeSpaceCons t x) = forcing ε t x := by
  change TestFunction.timeSpaceTensor _ _ (timeSpaceCons t x) -
    ε * TestFunction.timeSpaceTensor _ _ (timeSpaceCons t x) = _
  rw [TestFunction.timeSpaceTensor_timeSpaceCons,
    TestFunction.timeSpaceTensor_timeSpaceCons,
    (constantTimeTest_eventuallyEq hT ht).eq_of_nhds, timeTest_eq hT ht]
  change 1 * (spatialTest x + ε * laplaceTest x) -
    ε * ((1 + t) * laplaceTest x) = spatialTest x - ε * t * laplaceTest x
  cas

/-- On the closed slab the time derivative of the extension is `-ε Δq`. -/
theorem jointForcingTest_time {T : ℝ} (hT : 0 < T) (ε : ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : ℝ^1) :
    (∂[0] (jointForcingTest hT ε : SpaceTime 1 → ℝ)) (timeSpaceCons t x) =
      -ε * laplaceTest x := by
  let A := TestFunction.timeSpaceTensor (constantTimeTest hT) (spatialTest + ε • laplaceTest)
  let B := TestFunction.timeSpaceTensor (timeTest hT) laplaceTest
  change (∂[0] ((A : SpaceTime 1 → ℝ) - ε • (B : SpaceTime 1 → ℝ))) _ = _
  rw [(A.contDiff.differentiable (by simp)).partialDeriv_sub
    ((B.contDiff.differentiable (by simp)).const_smul ε) 0]
  change (∂[0] (A : SpaceTime 1 → ℝ)) _ -
    (∂[0] (fun y ↦ ε • B y)) _ = _
  rw [partialDeriv_const_smul]
  dsimp only [A, B]
  rw [TestFunction.partialDeriv_timeSpaceTensor_zero,
    TestFunction.partialDeriv_timeSpaceTensor_zero, timeTest_deriv hT ht,
    (constantTimeTest_eventuallyEq hT ht).deriv_eq, deriv_const]
  simp

/-- The extension as a one-component element of `W^{1,2}` on the slab `0 < t < T`. -/
def jointForcing {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    PiLp 2 (fun _ : Fin 1 ↦ W^{1,2}({y : ℝ^2 | y 0 ∈ Ioo 0 T})) :=
  WithLp.toLp 2 fun _ ↦ globalTestFunctionToWkpOn (jointForcingTest hT ε)

/-- The weak derivatives of order at most one of `jointForcing` are the classical
derivatives of the extension. -/
theorem jointForcing_coordinate_ae {T : ℝ} (hT : 0 < T) (ε : ℝ)
    (a : DerivIndex 2 1) (p : Fin 1) :
    (wkpCoordinateCLM a (jointForcing hT ε p) : ℝ^2 → ℝ)
      =ᵐ[volume.restrict {y | y 0 ∈ Ioo 0 T}]
        iteratedPartialDeriv a.toList (jointForcingTest hT ε : ℝ^2 → ℝ) := by
  simpa only [jointForcing, PiLp.toLp_apply, wkpCoordinateCLM_apply,
    domainMeasure, TestFunction.toFun_eq_coe] using
    globalTestFunctionToWkpOn_coordinate_ae (k := 1) (p := 2)
      (Ω := {y | y 0 ∈ Ioo 0 T}) (jointForcingTest hT ε) a

/-- For a.e. `t ∈ (0, T]` and a.e. `x`, the joint forcing equals `forcing ε t x`. -/
theorem jointForcing_base_sections {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (jointForcing hT ε p) (timeSpaceCons t x) = forcing ε t x := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  have h := Measure.ae_ae_of_ae_prod
    ((measurePreserving_timeSpaceCons_restrict (Ioo 0 T)).quasiMeasurePreserving.ae
      (ae_all_iff.mpr (jointForcing_coordinate_ae hT ε (baseIndex 2 1))))
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  filter_upwards [ht] with x hx
  intro p
  have hp := hx p
  simpa only [wkpBaseCoordinateCLM, baseIndex_toList, iteratedPartialDeriv,
    timeSpaceContinuousLinearEquiv_symm_apply,
    jointForcingTest_eq hT ε ⟨hmem.1.le, hmem.2.le⟩] using hp

/-- For a.e. `t ∈ (0, T]` and a.e. `x`, its time derivative is `-ε Δq(x)`. -/
theorem jointForcing_time_sections {T : ℝ} (hT : 0 < T) (ε : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ p,
      wkpCoordinateCLM (singleDerivIndex 2 0) (jointForcing hT ε p)
        (timeSpaceCons t x) = -ε * laplaceTest x := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  have h := Measure.ae_ae_of_ae_prod
    ((measurePreserving_timeSpaceCons_restrict (Ioo 0 T)).quasiMeasurePreserving.ae
      (ae_all_iff.mpr (jointForcing_coordinate_ae hT ε (singleDerivIndex 2 0))))
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  filter_upwards [ht] with x hx
  intro p
  have hp := hx p
  simpa only [singleDerivIndex_toList, iteratedPartialDeriv,
    timeSpaceContinuousLinearEquiv_symm_apply,
    jointForcingTest_time hT ε ⟨hmem.1.le, hmem.2.le⟩] using hp

end PDE.Examples.Hyperbolic.Viscosity.PolynomialFamily
