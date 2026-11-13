/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.SpaceTime.TensorProduct
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import CAS.ExactTactic

/-!
# Concrete nonzero data for a coupled viscous system

The canonical mollifier kernel supplies a nonzero compact smooth spatial
profile. The initial datum is `(ρ, 2ρ)` and the forcing on the given slab
is `(1+t)(ρ, -ρ)`. The forcing is extended past the slab by a smooth time cutoff equal
to one near `[0, T]`, so it is a test function.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Viscosity

open MeasureTheory Set TopologicalSpace PDE.Common
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal Distributions Sobolev

/-- The normalized standard spatial kernel, regarded as a compact smooth test. -/
def spatialTest : 𝓓((⊤ : Opens (ℝ^1)), ℝ) :=
  ⟨(standardMollifier 1).ρ, (standardMollifier 1).smooth,
    (standardMollifier 1).compactSupport, subset_univ _⟩

/-- The initial profiles `ρ` and `2ρ`. -/
def initialTest (p : Fin 2) : 𝓓((⊤ : Opens (ℝ^1)), ℝ) :=
  if p = 0 then spatialTest else 2 • spatialTest

/-- The initial datum `(ρ, 2ρ)` in `W^{1,2}(ℝ)²`. -/
def initialData : PiLp 2 (fun _ : Fin 2 ↦ W^{1,2}(ℝ^1)) :=
  WithLp.toLp 2 fun p ↦ globalTestFunctionToWkpOn (initialTest p)

/-- A compact smooth cutoff which is identically one near the closed time slab. -/
def timeCutoff {T : ℝ} (hT : 0 < T) : ContDiffBump (0 : ℝ) where
  rIn := T + 1
  rOut := T + 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- A compact smooth extension of `1+t` from the closed time slab. -/
def timeTest {T : ℝ} (hT : 0 < T) : 𝓓((⊤ : Opens ℝ), ℝ) :=
  ⟨fun t ↦ (1 + t) * timeCutoff hT t,
    (contDiff_const.add contDiff_id).mul (timeCutoff hT).contDiff,
    (timeCutoff hT).hasCompactSupport.mul_left, subset_univ _⟩

/-- On `[0, T]` the time factor is `1 + t`. -/
theorem timeTest_eq {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    timeTest hT t = 1 + t := by
  change (1 + t) * timeCutoff hT t = _
  rw [(timeCutoff hT).one_of_mem_closedBall, mul_one]
  change dist t 0 ≤ T + 1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  linarith [ht.2]

/-- On `[0, T]` the time factor has derivative `1`. -/
theorem timeTest_deriv {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    deriv (timeTest hT : ℝ → ℝ) t = 1 := by
  have hball : t ∈ Metric.ball 0 (timeCutoff hT).rIn := by
    change dist t 0 < T + 1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  have heq : (timeTest hT : ℝ → ℝ) =ᶠ[nhds t] fun s ↦ 1 + s := by
    filter_upwards [(timeCutoff hT).eventuallyEq_one_of_mem_ball hball] with s hs
    change (1 + s) * timeCutoff hT s = 1 + s
    rw [hs, Pi.one_apply, mul_one]
  rw [heq.deriv_eq]
  cas

/-- The two compact spacetime extensions of the forcing profiles. -/
def forcingTest {T : ℝ} (hT : 0 < T) (p : Fin 2) :
    𝓓((⊤ : Opens (SpaceTime 1)), ℝ) :=
  TestFunction.timeSpaceTensor (timeTest hT)
    (if p = 0 then spatialTest else -spatialTest)

/-- The forcing as an element of `W^{1,2}` on the open slab `0 < t < T`. -/
def forcingData {T : ℝ} (hT : 0 < T) :
    PiLp 2 (fun _ : Fin 2 ↦ W^{1,2}({y : ℝ^2 | y 0 ∈ Ioo 0 T})) :=
  WithLp.toLp 2 fun p ↦ globalTestFunctionToWkpOn (forcingTest hT p)

/-- The initial graph represents the chosen initial profiles. -/
theorem initialData_base_ae (p : Fin 2) :
    (wkpBaseCoordinateCLM (initialData p) : ℝ^1 → ℝ) =ᵐ[volume] initialTest p := by
  simpa only [initialData, PiLp.toLp_apply, wkpBaseCoordinateCLM_apply,
    domainMeasure, Measure.restrict_univ, baseIndex_toList, iteratedPartialDeriv,
    TestFunction.toFun_eq_coe] using
    globalTestFunctionToWkpOn_coordinate_ae (k := 1) (p := 2) (Ω := univ)
      (initialTest p) (baseIndex 1 1)

/-- The forcing graph represents the compact smooth extension on its slab. -/
theorem forcingData_base_ae {T : ℝ} (hT : 0 < T) (p : Fin 2) :
    (wkpBaseCoordinateCLM (forcingData hT p) : SpaceTime 1 → ℝ)
      =ᵐ[volume.restrict {y | y 0 ∈ Ioo 0 T}] forcingTest hT p := by
  simpa only [forcingData, PiLp.toLp_apply, wkpBaseCoordinateCLM_apply,
    domainMeasure, baseIndex_toList, iteratedPartialDeriv, TestFunction.toFun_eq_coe] using
    globalTestFunctionToWkpOn_coordinate_ae (k := 1) (p := 2)
      (Ω := {y | y 0 ∈ Ioo 0 T}) (forcingTest hT p) (baseIndex 2 1)

/-- On the closed slab the forcing is exactly the prescribed affine-time spatial bump. -/
theorem forcingTest_timeSpaceCons {T : ℝ} (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : ℝ^1) (p : Fin 2) :
    forcingTest hT p (timeSpaceCons t x) =
      (1 + t) * (if p = 0 then spatialTest x else -spatialTest x) := by
  simp only [forcingTest, TestFunction.timeSpaceTensor_timeSpaceCons, timeTest_eq hT ht]
  split_ifs <;> rfl

/-- The prescribed spatial profile is nonzero: its integral is one. -/
theorem spatialTest_ne_zero : (spatialTest : ℝ^1 → ℝ) ≠ 0 := by
  intro h
  have hi := (standardMollifier 1).integral_one
  change (∫ x, spatialTest x) = 1 at hi
  rw [h] at hi
  norm_num at hi

/-- The initial datum is nonzero. -/
theorem initialData_ne_zero : initialData ≠ 0 := by
  intro h
  have ha := initialData_base_ae 0
  rw [h] at ha
  have hz : (0 : ℝ^1 → ℝ) =ᵐ[volume] spatialTest := by
    have hz0 := Lp.coeFn_zero ℝ 2 (domainMeasure 1 univ)
    simp only [domainMeasure, Measure.restrict_univ] at hz0
    exact hz0.symm.trans (by simpa [initialTest] using ha)
  exact spatialTest_ne_zero
    (Measure.eq_of_ae_eq hz.symm spatialTest.continuous continuous_const)

/-- The prescribed forcing is nonzero on every positive time slab. -/
theorem forcingData_ne_zero {T : ℝ} (hT : 0 < T) : forcingData hT ≠ 0 := by
  intro h
  have ha := forcingData_base_ae hT 0
  rw [h] at ha
  have hz0 := Lp.coeFn_zero ℝ 2 (domainMeasure 2 {y | y 0 ∈ Ioo 0 T})
  have hz : (forcingTest hT 0 : SpaceTime 1 → ℝ)
      =ᵐ[volume.restrict {y | y 0 ∈ Ioo 0 T}] 0 :=
    (by simpa using ha.symm : (forcingTest hT 0 : SpaceTime 1 → ℝ)
      =ᵐ[volume.restrict {y | y 0 ∈ Ioo 0 T}] (0 : DerivLp 2 2 {y | y 0 ∈ Ioo 0 T})).trans
        hz0
  have heq := Measure.eqOn_open_of_ae_eq hz
    (isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous)
    (forcingTest hT 0).continuous.continuousOn continuous_const.continuousOn
  obtain ⟨x, hx⟩ : ∃ x : ℝ^1, spatialTest x ≠ 0 := by
    by_contra! hzero
    exact spatialTest_ne_zero (funext hzero)
  have hmid : T / 2 ∈ Ioo 0 T := ⟨by linarith, by linarith⟩
  have hzero := heq (show timeSpaceCons (T / 2) x ∈ {y | y 0 ∈ Ioo 0 T} by
    simpa using hmid)
  rw [forcingTest_timeSpaceCons hT (Ioo_subset_Icc_self hmid)] at hzero
  simp only [ite_true, Pi.zero_apply] at hzero
  exact mul_ne_zero (by linarith : 1 + T / 2 ≠ 0) hx hzero

end PDE.Examples.Hyperbolic.Viscosity
