/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.WkpExtensionByZero
public import PDE.Spaces.Sobolev.Calculus.Composition.AbsoluteValue.Approximation
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Extending positivity from smooth tests

A continuous Sobolev functional which is nonnegative on nonnegative smooth compactly
supported functions is nonnegative on every nonnegative element of the supported closure.
Ordinary density alone does not give this: its approximants need not preserve sign.
We first smooth their absolute values by `sqrt(s² + ε²) - ε`, which preserves both
nonnegativity and compact support, and then use strong continuity of absolute value.
No boundary regularity or finite measure is required.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open Filter Function MeasureTheory Set
open scoped ENNReal Topology Sobolev
open ZeroTrace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}

/-- Positivity on nonnegative smooth compact tests extends to the zero-boundary
Sobolev space at every finite exponent. -/
theorem nonneg_on_wkp0_of_nonneg_testFunctions
    (hΩ : IsOpen Ω) (hp : p ≠ ∞) (ℓ : W^{1,p}(Ω) →L[ℝ] ℝ)
    (hℓ : ∀ φ : TestFunctionOn n Ω, (∀ x, 0 ≤ φ.1.toFun x) →
      0 ≤ ℓ (testFunctionToWkp (k := 1) (p := p) φ))
    (u : W₀^{1,p}(Ω))
    (hu : ∀ᵐ x ∂domainMeasure n Ω,
      0 ≤ wkpCoordinateCLM (baseIndex n 1) (u : W^{1,p}(Ω)) x) :
    0 ≤ ℓ (u : W^{1,p}(Ω)) := by
  let R : W^{1,p}(ℝ^n) →L[ℝ] W^{1,p}(Ω) :=
    restrictCLM hΩ.measurableSet (subset_univ Ω)
  let A : W₀^{1,p}(Ω) → ℝ :=
    fun v ↦ ℓ (R (absoluteValue (zeroExtendWkp0 hΩ.measurableSet v)))
  have hAcont : Continuous A :=
    ℓ.continuous.comp (R.continuous.comp
      ((continuous_absoluteValue hp).comp (zeroExtendWkp0 hΩ.measurableSet).continuous))
  have hA : 0 ≤ A u := by
    refine (denseRange_testFunctionToWkp0Linear (n := n) (k := 1) (p := p)
      (Ω := Ω)).induction_on (p := fun v ↦ 0 ≤ A v) u
        (isClosed_le continuous_const hAcont) ?_
    intro φ
    let U := zeroExtendWkp0 hΩ.measurableSet (testFunctionToWkp0 (k := 1) (p := p) φ)
    let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
    have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
    have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hconv := tendsto_smoothAbsComposition hp U ε hε hε0
    apply isClosed_Ici.mem_of_tendsto
      (((ℓ.comp R).continuous.tendsto _).comp hconv)
    apply Eventually.of_forall
    intro j
    let F := PDE.Analysis.Calculus.smoothAbs (ε j)
    let ψ : TestFunctionOn n Ω :=
      ⟨_root_.TestFunction.mk (F ∘ φ.1.toFun)
        ((PDE.Analysis.Calculus.contDiff_smoothAbs (hε j)).comp φ.1.contDiff)
        (φ.1.hasCompactSupport.comp_left
          (PDE.Analysis.Calculus.smoothAbs_zero _ (hε j).le)) (subset_univ _),
        (tsupport_comp_subset
          (PDE.Analysis.Calculus.smoothAbs_zero _ (hε j).le) φ.1.toFun).trans φ.2⟩
    let V := smoothComposition
      ((PDE.Analysis.Calculus.contDiff_smoothAbs (hε j)).of_le (by simp))
      (PDE.Analysis.Calculus.hasDerivAt_smoothAbs (hε j))
      (PDE.Analysis.Calculus.smoothAbs_zero _ (hε j).le)
      (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j)) U
    have heq : R V = testFunctionToWkp (k := 1) (p := p) ψ := by
      apply wkpBaseCoordinateCLM_injective hΩ
      apply Lp.ext
      have hglobal := ae_mono (domainMeasure_le (subset_univ Ω))
        (smoothComposition_base_ae
          ((PDE.Analysis.Calculus.contDiff_smoothAbs (hε j)).of_le (by simp))
          (PDE.Analysis.Calculus.hasDerivAt_smoothAbs (hε j))
          (PDE.Analysis.Calculus.smoothAbs_zero _ (hε j).le)
          (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j)) U)
      filter_upwards
        [restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω) V (baseIndex n 1),
         hglobal, zeroExtendWkp0_coordinate_ae_on hΩ.measurableSet
           (testFunctionToWkp0 (k := 1) (p := p) φ) (baseIndex n 1),
         testFunctionToWkp_coordinate_ae (k := 1) (p := p) φ (baseIndex n 1),
         testFunctionToWkp_coordinate_ae (k := 1) (p := p) ψ (baseIndex n 1)]
        with x hr hv he hφ hψ
      simp only [baseIndex_toList, iteratedPartialDeriv] at hφ hψ
      exact hr.trans ((hv.trans (congrArg F (he.trans hφ))).trans hψ.symm)
    change 0 ≤ ℓ (R V)
    rw [heq]
    exact hℓ ψ (fun x ↦ PDE.Analysis.Calculus.smoothAbs_nonneg (hε j).le _)
  have heq : R (absoluteValue (zeroExtendWkp0 hΩ.measurableSet u)) =
      (u : W^{1,p}(Ω)) := by
    apply wkpBaseCoordinateCLM_injective hΩ
    apply Lp.ext
    have habs := ae_mono (domainMeasure_le (subset_univ Ω))
      (absoluteValue_base_ae (zeroExtendWkp0 hΩ.measurableSet u))
    filter_upwards
      [restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω)
        (absoluteValue (zeroExtendWkp0 hΩ.measurableSet u)) (baseIndex n 1),
       habs, zeroExtendWkp0_coordinate_ae_on hΩ.measurableSet u (baseIndex n 1), hu]
      with x hr ha he hx
    exact hr.trans ((ha.trans (congrArg abs he)).trans (abs_of_nonneg hx))
  change 0 ≤ ℓ (R (absoluteValue (zeroExtendWkp0 hΩ.measurableSet u))) at hA
  rwa [heq] at hA

end SobolevSpace.GraphSpace
