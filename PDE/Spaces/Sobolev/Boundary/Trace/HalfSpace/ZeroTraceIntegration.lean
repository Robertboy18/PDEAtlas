/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponentCompletion
import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts for the half-space trace

The boundary term in normal integration by parts is the completed geometric trace.
The identity is proved first for smooth functions by the fundamental theorem of calculus
on normal slices, and then extended by density and Hölder duality. This gives the analytic
identity needed to extend a zero-trace Sobolev function by zero across the boundary.

The trace here is the boundary `Lᵖ` operator, independently constructed from smooth
restriction; no identification with the closure of interior test functions is used.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set
open scoped ENNReal Topology Sobolev

variable {n : ℕ}

/-- The integral of a compactly supported normal derivative is minus its boundary integral. -/
theorem integral_upper_partialDeriv_last {f : ℝ^(n + 1) → ℝ}
    (hf : ContDiff ℝ 1 f) (hcs : HasCompactSupport f) :
    (∫ x in HalfSpace.upper (n + 1), (∂[Fin.last n] f) x) =
      -(∫ y : ℝ^n, smoothBoundaryValue f y) := by
  rw [← integral_joinTangentialNormal_eq_integral_upper]
  have hint : Integrable (normalDerivativeInSplit f)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
    (normalDerivativeInSplit_continuous hf).integrable_of_hasCompactSupport
      (normalDerivativeInSplit_hasCompactSupport hcs)
  rw [show (fun z ↦ (∂[Fin.last n] f) (joinTangentialNormal z)) =
      normalDerivativeInSplit f by rfl, integral_prod _ hint]
  simp_rw [← deriv_normalSlice hf]
  have hslice (y : ℝ^n) :
      (∫ t, deriv (normalSlice f y) t ∂positiveNormalMeasure) =
        -smoothBoundaryValue f y :=
    HasCompactSupport.integral_Ioi_deriv_eq
      (normalSlice_contDiff hf y) (normalSlice_hasCompactSupport hcs y) 0
  simp_rw [hslice]
  exact integral_neg _

/-- Normal integration by parts for smooth compactly supported functions on the half-space. -/
theorem integral_upper_mul_partialDeriv_add
    {f g : ℝ^(n + 1) → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ x in HalfSpace.upper (n + 1), f x * (∂[Fin.last n] g) x) +
        (∫ x in HalfSpace.upper (n + 1), (∂[Fin.last n] f) x * g x) =
      -(∫ y : ℝ^n, smoothBoundaryValue f y * smoothBoundaryValue g y) := by
  have hdf : Continuous (∂[Fin.last n] f) := by
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdg : Continuous (∂[Fin.last n] g) := by
    exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint₁ := (hf.continuous.mul hdg).integrable_of_hasCompactSupport (μ := volume)
    hfc.mul_right
  have hint₂ := (hdf.mul hg.continuous).integrable_of_hasCompactSupport (μ := volume)
    hgc.mul_left
  rw [← integral_add (μ := volume.restrict (HalfSpace.upper (n + 1)))
    (f := fun x ↦ f x * (∂[Fin.last n] g) x)
    (g := fun x ↦ (∂[Fin.last n] f) x * g x)
    hint₁.integrableOn hint₂.integrableOn]
  have hprod : (fun x ↦ f x * (∂[Fin.last n] g) x +
      (∂[Fin.last n] f) x * g x) =
        ∂[Fin.last n] (fun x ↦ f x * g x) := by
    funext x
    rw [PDE.partialDeriv_mul (hf.differentiable one_ne_zero x)
      (hg.differentiable one_ne_zero x)]
    exact add_comm _ _
  rw [hprod, integral_upper_partialDeriv_last (hf.mul hg) hfc.mul_right]
  rfl

private theorem continuous_integral_mul_lp {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {μ : Measure (ℝ^d)} [IsFiniteMeasureOnCompacts μ]
    {f : ℝ^d → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (fun u : Lp ℝ p μ ↦ ∫ x, u x * f x ∂μ) := by
  let q := ENNReal.conjExponent p
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let v : Lp ℝ q μ := (hf.memLp_of_hasCompactSupport hcs).toLp f
  have heq (u : Lp ℝ p μ) :
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q u v = ∫ x, u x * f x ∂μ := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [(hf.memLp_of_hasCompactSupport (p := q) hcs).coeFn_toLp] with x hx
    change u x * v x = u x * f x
    rw [show v x = f x from hx]
  have hc := ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q).flip v |>.continuous
  change Continuous (fun u ↦ (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q u v) at hc
  simpa only [heq] using hc

/-- The normal Green identity for the completed finite-exponent half-space trace. -/
theorem integral_upper_normal_green (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 ≤ p)
    (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)))
    (φ : GlobalTestFunction n) :
    (∫ x in HalfSpace.upper (n + 1), GraphSpace.baseRepresentative u x *
        (∂[Fin.last n] φ.1.toFun) x) +
      (∫ x in HalfSpace.upper (n + 1),
        GraphSpace.wkpCoordinateCLM (GraphSpace.singleDerivIndex (n + 1) (Fin.last n)) u x *
          φ.1.toFun x) =
      -(∫ y : ℝ^n, traceLp n p hp u y * smoothBoundaryValue φ.1.toFun y) := by
  let L := fun v : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) ↦
    (∫ x in HalfSpace.upper (n + 1), GraphSpace.baseRepresentative v x *
        (∂[Fin.last n] φ.1.toFun) x) +
      (∫ x in HalfSpace.upper (n + 1),
        GraphSpace.wkpCoordinateCLM (GraphSpace.singleDerivIndex (n + 1) (Fin.last n)) v x *
          φ.1.toFun x)
  let R := fun v : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) ↦
    -(∫ y : ℝ^n, traceLp n p hp v y * smoothBoundaryValue φ.1.toFun y)
  have hL : Continuous L := by
    apply Continuous.add
    · exact (continuous_integral_mul_lp
        ((φ.1.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const)
        (φ.1.hasCompactSupport.fderiv_apply (𝕜 := ℝ)
          (v := EuclideanSpace.single (Fin.last n) 1))).comp
          GraphSpace.wkpBaseCoordinateCLM.continuous
    · exact (continuous_integral_mul_lp φ.1.contDiff.continuous φ.1.hasCompactSupport).comp
        (GraphSpace.wkpCoordinateCLM _).continuous
  have hR : Continuous R :=
    ((continuous_integral_mul_lp (smoothBoundaryValue_continuous φ.1.contDiff.continuous)
      (smoothBoundaryValue_hasCompactSupport φ.1.hasCompactSupport)).comp
      (traceLp n p hp).continuous).neg
  suffices heq : L = R from congrFun heq u
  apply (denseRange_globalTestFunctionToUpperW1pLinear n p).equalizer hL hR
  funext ψ
  have hbase := GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := HalfSpace.upper (n + 1))
    ψ.1.toFun ψ.1.contDiff ψ.1.hasCompactSupport (GraphSpace.baseIndex (n + 1) 1)
  have hderiv := GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
    (n := n + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := HalfSpace.upper (n + 1))
    ψ.1.toFun ψ.1.contDiff ψ.1.hasCompactSupport
    (GraphSpace.singleDerivIndex (n + 1) (Fin.last n))
  have hbdy := (smoothBoundaryValue_memLp_ofReal n p ψ).coeFn_toLp
  change L (globalTestFunctionToUpperW1pLinear n p ψ) =
    R (globalTestFunctionToUpperW1pLinear n p ψ)
  dsimp only [L, R]
  rw [traceLp_smooth, globalTestFunctionToUpperW1pLinear_eq_mk]
  have h₁ : (∫ x in HalfSpace.upper (n + 1),
      GraphSpace.baseRepresentative
        (GraphSpace.mkWkpSpaceOnOfContDiff (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper (n + 1))
          ψ.1.toFun ψ.1.contDiff ψ.1.hasCompactSupport) x *
          (∂[Fin.last n] φ.1.toFun) x) =
      ∫ x in HalfSpace.upper (n + 1), ψ.1.toFun x * (∂[Fin.last n] φ.1.toFun) x := by
    apply integral_congr_ae
    filter_upwards [hbase] with x hx
    simpa [GraphSpace.baseRepresentative, iteratedPartialDeriv] using
      congrArg (fun a ↦ a * (∂[Fin.last n] φ.1.toFun) x) hx
  have h₂ : (∫ x in HalfSpace.upper (n + 1),
      GraphSpace.wkpCoordinateCLM (GraphSpace.singleDerivIndex (n + 1) (Fin.last n))
        (GraphSpace.mkWkpSpaceOnOfContDiff (k := 1) (p := ENNReal.ofReal p)
          (Ω := HalfSpace.upper (n + 1))
          ψ.1.toFun ψ.1.contDiff ψ.1.hasCompactSupport) x *
          φ.1.toFun x) =
      ∫ x in HalfSpace.upper (n + 1), (∂[Fin.last n] ψ.1.toFun) x * φ.1.toFun x := by
    apply integral_congr_ae
    filter_upwards [hderiv] with x hx
    simpa [GraphSpace.wkpCoordinateCLM, iteratedPartialDeriv] using
      congrArg (fun a ↦ a * φ.1.toFun x) hx
  have h₃ : (∫ y : ℝ^n, globalTestFunctionBoundaryLpLinear n p ψ y *
      smoothBoundaryValue φ.1.toFun y) =
      ∫ y : ℝ^n, smoothBoundaryValue ψ.1.toFun y * smoothBoundaryValue φ.1.toFun y := by
    apply integral_congr_ae
    filter_upwards [hbdy] with y hy
    exact congrArg (fun a ↦ a * smoothBoundaryValue φ.1.toFun y) hy
  rw [h₁, h₂, h₃]
  exact integral_upper_mul_partialDeriv_add
    (ψ.1.contDiff.of_le (by simp)) (φ.1.contDiff.of_le (by simp))
    ψ.1.hasCompactSupport φ.1.hasCompactSupport

end SobolevSpace.Trace.HalfSpace
