/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Passing Poincaré estimates to the supported-core Sobolev closure

A uniform estimate for smooth test functions passes to `W^{1,p}_0` through the
continuous coordinate projections. All derivative norms use the original exponent.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function
open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

omit [Fact (1 ≤ p)] in
private theorem norm_testFunction_base_le_of_eLpNorm
    (C : NNReal) (φ : TestFunctionOn n Ω)
    (hest : eLpNorm φ.1.toFun p volume ≤ C *
      ∑ i : Fin n, eLpNorm (∂[i] φ.1.toFun) p volume) :
    ‖((testFunctionToWkp (k := 1) (p := p) φ : WkpAmbientOn n 1 p Ω) (baseIndex n 1))‖ ≤
      (C : ℝ) * ∑ i : Fin n,
        ‖((testFunctionToWkp (k := 1) (p := p) φ : WkpAmbientOn n 1 p Ω)
          (singleDerivIndex n i))‖ := by
  classical
  let U : WkpAmbientOn n 1 p Ω := (testFunctionToWkp (k := 1) (p := p) φ :
    W^{1,p}(Ω))
  have hcoord (a : DerivIndex n 1) :
      eLpNorm (iteratedPartialDeriv a.toList φ.1.toFun) p volume =
        eLpNorm (U a) p (domainMeasure n Ω) := by
    have hs : support (iteratedPartialDeriv a.toList φ.1.toFun) ⊆ Ω :=
      (subset_tsupport _).trans
        ((tsupport_iteratedPartialDeriv_subset_tsupport a.toList φ.1.toFun).trans φ.2)
    rw [← eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := p)
      (f := iteratedPartialDeriv a.toList φ.1.toFun)
      (PDE.contDiff_top_iteratedPartialDeriv φ.1.contDiff a.toList).continuous.aestronglyMeasurable
        hs]
    exact (eLpNorm_congr_ae (testFunctionToWkp_coordinate_ae (p := p) φ a)).symm
  have hbase : eLpNorm φ.1.toFun p volume =
      eLpNorm (U (baseIndex n 1)) p (domainMeasure n Ω) := by
    simpa only [baseIndex_toList, iteratedPartialDeriv] using hcoord (baseIndex n 1)
  have hderiv (i : Fin n) : eLpNorm (∂[i] φ.1.toFun) p volume =
      eLpNorm (U (singleDerivIndex n i)) p (domainMeasure n Ω) := by
    simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using
      hcoord (singleDerivIndex n i)
  simp_rw [hbase, hderiv] at hest
  have hfinite : (∑ i : Fin n,
      eLpNorm (U (singleDerivIndex n i)) p (domainMeasure n Ω)) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun i _ ↦ Lp.eLpNorm_ne_top _
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfinite) hest
  simpa only [U, Lp.norm_def, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_sum (fun i _ ↦ Lp.eLpNorm_ne_top (U (singleDerivIndex n i)))] using hreal

/-- A uniform Poincaré estimate for test functions holds throughout `W^{1,p}_0`.
The completed-space conclusion uses weak derivative coordinates at the same exponent;
no smooth representative or boundary trace theorem is assumed. -/
theorem poincare_Wkp0_of_testFunctions
    (C : NNReal)
    (hest : ∀ φ : TestFunctionOn n Ω,
      eLpNorm φ.1.toFun p volume ≤ C *
        ∑ i : Fin n, eLpNorm (∂[i] φ.1.toFun) p volume)
    (u : W₀^{1,p}(Ω)) :
    ‖(((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω) (baseIndex n 1))‖ ≤
      (C : ℝ) * ∑ i : Fin n,
        ‖(((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
          (singleDerivIndex n i))‖ := by
  classical
  apply Wkp0SpaceOn.closed_property_of_testFunctions (S := {v |
    ‖(v : WkpAmbientOn n 1 p Ω) (baseIndex n 1)‖ ≤
      (C : ℝ) * ∑ i : Fin n,
        ‖(v : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)‖}) ?_ ?_ u
  · exact isClosed_le (wkpCoordinateCLM (baseIndex n 1)).continuous.norm
      (continuous_const.mul (continuous_finsetSum _ fun i _ ↦
        (wkpCoordinateCLM (singleDerivIndex n i)).continuous.norm))
  · intro φ
    exact norm_testFunction_base_le_of_eLpNorm C φ (hest φ)

end SobolevSpace.GraphSpace
