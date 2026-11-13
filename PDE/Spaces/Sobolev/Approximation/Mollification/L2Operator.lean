/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ConvolutionL2
public import PDE.FDeriv.PartialDeriv
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core

/-!
# Mollifier kernels as bounded L² operators

For a positive scale `ε`, `mollifierL2CLM` is convolution by `ρ_ε` and has norm at most one.
`mollifierDerivativeL2CLM` is convolution by the coordinate derivative of `ρ_ε`, with
operator norm bounded by the `L¹` norm of that derivative. Both operators are constructed
from their integrable kernels using the generic `L²` convolution map. As the positive scale
tends to zero, `mollifierL2CLM` converges strongly to the identity on L².

The standard kernel is even, and positive rescaling preserves evenness. Its L² convolution
operator is therefore self-adjoint.

This is the bounded-operator layer of Sobolev mollification (Evans, App. C.5 and §5.3).
Identifying the derivative-kernel operator with the weak derivative of mollification is a
separate result; no bounded spatial derivative on arbitrary `L²` inputs is assumed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.5, pp. 713-715, for mollifiers and Theorem 7 on their
  properties, and §5.3, pp. 264-268, for their use in approximation by smooth functions.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Convolution ENNReal Topology

namespace SobolevSpace.Approximation

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

open Filter PDE.Analysis

/-- Every positive-scale mollifier kernel is integrable. -/
theorem integrable_scaled (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    Integrable (scaled μ ε) volume :=
  (scaled_contDiff μ).continuous.integrable_of_hasCompactSupport
    (scaled_hasCompactSupport μ hε)

/-- Every coordinate derivative of a positive-scale mollifier kernel is integrable. -/
theorem integrable_fderiv_scaled_apply (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (j : Fin n) :
    Integrable (∂[j] (scaled μ ε)) volume := by
  have hcont : Continuous
      (fun x ↦ fderiv ℝ (scaled μ ε) x (EuclideanSpace.single j 1)) :=
    ((scaled_contDiff μ).continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  exact hcont.integrable_of_hasCompactSupport
    ((scaled_hasCompactSupport μ hε).fderiv_apply
      (𝕜 := ℝ) (EuclideanSpace.single j 1))

/-- Convolution by the normalized mollifier, as an operator on `L²`. -/
def mollifierL2CLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    Lp E 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp E 2 (volume : Measure (ℝ^n)) :=
  convolutionL2CLM (scaled μ ε) (integrable_scaled μ hε)

omit [CompleteSpace E] in
/-- Mollification is a contraction on `L²`. -/
theorem norm_mollifierL2CLM_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    ‖mollifierL2CLM (E := E) μ hε‖ ≤ 1 := by
  calc
    ‖mollifierL2CLM (E := E) μ hε‖ ≤ ∫ y, ‖scaled μ ε y‖ :=
      norm_convolutionL2CLM_le _ _
    _ = 1 := by
      simp_rw [Real.norm_of_nonneg (scaled_nonneg μ hε _)]
      exact scaled_integral_one μ hε

/-- The constructed mollifier operators converge strongly to the identity on L2 along
any sequence of positive scales tending to zero. No regularity of the input is assumed. -/
theorem tendsto_mollifierL2CLM (μ : Mollifier n) (ε : ℕ → ℝ)
    (hεpos : ∀ m, 0 < ε m) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : Lp E 2 (volume : Measure (ℝ^n))) :
    Tendsto (fun m ↦ mollifierL2CLM μ (hεpos m) u) atTop (𝓝 u) := by
  let orbit : ℝ^n → Lp E 2 (volume : Measure (ℝ^n)) := fun y ↦ translateL2 ℝ (-y) u
  have hcont : Continuous orbit := (continuous_translateL2 ℝ u).comp continuous_neg
  have hzero : orbit 0 = u := by
    simp only [orbit, neg_zero, translateL2_zero]
  have heq (m : ℕ) :
      mollifierL2CLM μ (hεpos m) u = mollifyVector μ (ε m) orbit 0 :=
    convolutionL2CLM_eq_convolution_orbit _ _ u
  simpa only [← heq, hzero] using
    mollifyVector_tendsto_of_continuous μ hcont ε hεpos hε0 (0 : ℝ^n)

/-- Convolution by a coordinate derivative of the mollifier kernel.

This definition uses the derivative of `ρ_ε`; it does not assume a bounded spatial
derivative on `L²`. Identification with the weak derivative of mollification is separate. -/
def mollifierDerivativeL2CLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (j : Fin n) :
    Lp E 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp E 2 (volume : Measure (ℝ^n)) :=
  convolutionL2CLM
    (∂[j] (scaled μ ε))
    (integrable_fderiv_scaled_apply μ hε j)

omit [CompleteSpace E] in
/-- The derivative-kernel operator is bounded by the integral of the derivative's norm. -/
theorem norm_mollifierDerivativeL2CLM_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (j : Fin n) :
    ‖mollifierDerivativeL2CLM (E := E) μ hε j‖ ≤
      ∫ y, ‖(∂[j] (scaled μ ε)) y‖ :=
  norm_convolutionL2CLM_le _ _

end SobolevSpace.Approximation

namespace SobolevSpace.Approximation

open PDE.Analysis

variable {n : ℕ}

/-- The normalized bump at the origin defining the standard mollifier is even. -/
theorem standardMollifier_even : Function.Even (standardMollifier n).ρ := by
  intro x
  rw [standardMollifier_eq_norm, standardMollifier_eq_norm, norm_neg]

/-- Positive rescaling preserves the evenness of a mollifier kernel. -/
theorem scaled_even (μ : Mollifier n) (hμ : Function.Even μ.ρ)
    {ε : ℝ} (hε : 0 < ε) : Function.Even (scaled μ ε) := by
  intro x
  simp only [scaled_of_pos μ hε, smul_neg]
  exact congrArg (fun r ↦ ε⁻¹ ^ n * r) (hμ (ε⁻¹ • x))

/-- Standard mollification is self-adjoint on real Hilbert-valued L2.
Evenness is proved from the standard kernel, not supplied as an operator hypothesis. -/
theorem inner_standardMollifierL2CLM_left {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ε : ℝ} (hε : 0 < ε) (u v : Lp E 2 (volume : Measure (ℝ^n))) :
    inner ℝ (mollifierL2CLM (standardMollifier n) hε u) v =
      inner ℝ u (mollifierL2CLM (standardMollifier n) hε v) :=
  inner_convolutionL2CLM_eq_of_even _ _
    (scaled_even _ standardMollifier_even hε) u v

end SobolevSpace.Approximation
