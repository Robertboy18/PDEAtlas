/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import PDE.FDeriv.PartialDeriv.Support

/-!
# Integration by parts for compact bilinear pairings

One compactly supported factor is enough to remove the boundary term. The core
statement allows the other factor to be `C¹` only near that support, on any
finite-dimensional real normed domain with additive Haar measure. The global
`C¹` interfaces cover arbitrary directions and coordinate derivatives, for
scalar–vector multiplication, real or complex products, and continuous bilinear
pairings. Compact support supplies all integrability conditions.

The mixed second-derivative formula assumes only that the compact factor is `C²`.
All vector-valued integrals are Bochner integrals, and as in Mathlib the identities
need no completeness assumption.

On `ℝ^n` these identities are the integration by parts formula (3) of Evans, Appendix C.2,
Theorem 2, with the boundary integral removed by compact support. The identity itself is
Mathlib's `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`; we derive its
integrability hypotheses from compact support.

## Main results

* `integral_bilinear_fderiv_eq_neg_of_contDiffAt`, `integral_bilinear_fderiv_eq_neg`:
  `∫ B(f, ∂_v g) = -∫ B(∂_v f, g)` when `f` is `C¹` with compact support.
* `integral_smul_fderiv_eq_neg`, `integral_mul_fderiv_eq_neg`: the scalar–vector and product
  cases.
* `integral_bilinear_partialDeriv_eq_neg`, `integral_smul_partialDeriv_eq_neg`,
  `integral_mul_partialDeriv_eq_neg`, with their `_of_contDiffAt` versions: coordinate
  derivatives on `ℝ^n`.
* `integral_bilinear_partialDeriv_partialDeriv_eq_neg`: a derivative moved onto a first
  derivative of a compactly supported `C²` factor.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix C.2, Theorem 2 (Integration by parts formula),
  p. 712. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Measure Set

namespace PDE.Analysis

variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  {μ : Measure D} [IsAddHaarMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedSpace ℝ E] [NormedSpace ℝ G] in
/-- A function that is continuous on the topological support of a compactly supported
function and vanishes off that support is integrable. -/
theorem _root_.HasCompactSupport.integrable_of_continuousOn_tsupport {f : D → E} {h : D → G}
    (hf : HasCompactSupport f) (hh : ContinuousOn h (tsupport f))
    (hzero : ∀ x, x ∉ tsupport f → h x = 0) : Integrable h μ :=
  (hh.integrableOn_compact hf).integrable_of_forall_notMem_eq_zero hzero

/-- Move a derivative in any fixed direction across a continuous bilinear pairing.
Compact support of the first factor supplies integrability; the second factor
only needs to be `C¹` at points of that support. -/
theorem integral_bilinear_fderiv_eq_neg_of_contDiffAt
    (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} (v : D)
    (hf : ContDiff ℝ 1 f) (hg : ∀ x ∈ tsupport f, ContDiffAt ℝ 1 g x)
    (hcompact : HasCompactSupport f) :
    (∫ x, B (f x) (fderiv ℝ g x v) ∂μ) =
      -∫ x, B (fderiv ℝ f x v) (g x) ∂μ := by
  have hgContinuous : ContinuousOn g (tsupport f) :=
    fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt
  have hgDerivContinuous :
      ContinuousOn (fun x ↦ fderiv ℝ g x v) (tsupport f) := by
    intro x hx
    exact ((hg x hx).continuousAt_fderiv one_ne_zero).clm_apply
      continuousAt_const |>.continuousWithinAt
  have hfDerivContinuous : Continuous (fun x ↦ fderiv ℝ f x v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hfg : Integrable (fun x ↦ B (f x) (g x)) μ := by
    apply hcompact.integrable_of_continuousOn_tsupport
      ((B.continuous.comp hf.continuous).continuousOn.clm_apply hgContinuous)
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hfg' : Integrable (fun x ↦ B (f x) (fderiv ℝ g x v)) μ := by
    apply hcompact.integrable_of_continuousOn_tsupport
      ((B.continuous.comp hf.continuous).continuousOn.clm_apply hgDerivContinuous)
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hf'g : Integrable (fun x ↦ B (fderiv ℝ f x v) (g x)) μ := by
    apply hcompact.integrable_of_continuousOn_tsupport
      ((B.continuous.comp hfDerivContinuous).continuousOn.clm_apply hgContinuous)
    intro x hx
    simp [fderiv_of_notMem_tsupport ℝ hx]
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := B) hf'g hfg' hfg
    (fun _ _ ↦ hf.differentiable_one.differentiableAt)
    (fun x hx ↦ (hg x hx).differentiableAt_one)

/-- Global `C¹` factors satisfy integration by parts in every direction when the
first factor has compact support. No separate integrability assumptions are needed. -/
theorem integral_bilinear_fderiv_eq_neg
    (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} (v : D)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hcompact : HasCompactSupport f) :
    (∫ x, B (f x) (fderiv ℝ g x v) ∂μ) =
      -∫ x, B (fderiv ℝ f x v) (g x) ∂μ :=
  integral_bilinear_fderiv_eq_neg_of_contDiffAt B v hf (fun _ _ ↦ hg.contDiffAt) hcompact

section Scalar

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]

/-- Scalar–vector integration by parts in a fixed direction, with global `C¹`
regularity. The scalar field may be real or complex. -/
theorem integral_smul_fderiv_eq_neg [NormedSpace 𝕜 F]
    {f : D → 𝕜} {g : D → F} (v : D)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hcompact : HasCompactSupport f) :
    (∫ x, f x • fderiv ℝ g x v ∂μ) = -∫ x, fderiv ℝ f x v • g x ∂μ :=
  integral_bilinear_fderiv_eq_neg (ContinuousLinearMap.lsmul ℝ 𝕜) v hf hg hcompact

/-- Integration by parts for real or complex multiplication in any fixed direction. -/
theorem integral_mul_fderiv_eq_neg {f g : D → 𝕜} (v : D)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hcompact : HasCompactSupport f) :
    (∫ x, f x * fderiv ℝ g x v ∂μ) = -∫ x, fderiv ℝ f x v * g x ∂μ :=
  integral_bilinear_fderiv_eq_neg (ContinuousLinearMap.mul ℝ 𝕜) v hf hg hcompact

end Scalar

variable {n : ℕ}

/-- Coordinate integration by parts for a continuous bilinear pairing, with
regularity of the second factor only on the compact first factor's support. -/
theorem integral_bilinear_partialDeriv_eq_neg_of_contDiffAt
    (B : E →L[ℝ] F →L[ℝ] G) {f : ℝ^n → E} {g : ℝ^n → F} (i : Fin n)
    (hf : ContDiff ℝ 1 f) (hg : ∀ x ∈ tsupport f, ContDiffAt ℝ 1 g x)
    (hcompact : HasCompactSupport f) :
    (∫ x, B (f x) (∂[i] g x)) = -∫ x, B (∂[i] f x) (g x) :=
  integral_bilinear_fderiv_eq_neg_of_contDiffAt B (EuclideanSpace.single i 1) hf hg hcompact

/-- Coordinate integration by parts from global `C¹` regularity and compact
support of the first factor. -/
theorem integral_bilinear_partialDeriv_eq_neg
    (B : E →L[ℝ] F →L[ℝ] G) {f : ℝ^n → E} {g : ℝ^n → F} (i : Fin n)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hcompact : HasCompactSupport f) :
    (∫ x, B (f x) (∂[i] g x)) = -∫ x, B (∂[i] f x) (g x) :=
  integral_bilinear_fderiv_eq_neg B (EuclideanSpace.single i 1) hf hg hcompact

/-- Move a derivative onto a first derivative of a compactly supported `C²` factor.
Both the regularity and compact support of that first derivative follow from
the original data. This applies to mixed derivatives, including distinct coordinates. -/
theorem integral_bilinear_partialDeriv_partialDeriv_eq_neg
    (B : E →L[ℝ] F →L[ℝ] G) {f : ℝ^n → E} {g : ℝ^n → F} (i j : Fin n)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g) (hcompact : HasCompactSupport f) :
    (∫ x, B (∂[i] f x) (∂[j] g x)) = -∫ x, B (∂[j] ∂[i] f x) (g x) :=
  integral_bilinear_partialDeriv_eq_neg B j (hf.partialDeriv i (by norm_num)) hg
    (hcompact.partialDeriv i)

section Scalar

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]

/-- Scalar–vector coordinate integration by parts with coefficient regularity
only at points of the compact scalar factor's support. -/
theorem integral_smul_partialDeriv_eq_neg_of_contDiffAt
    [NormedSpace 𝕜 F]
    {f : ℝ^n → 𝕜} {g : ℝ^n → F} (i : Fin n)
    (hf : ContDiff ℝ 1 f) (hg : ∀ x ∈ tsupport f, ContDiffAt ℝ 1 g x)
    (hcompact : HasCompactSupport f) :
    (∫ x, f x • ∂[i] g x) = -∫ x, ∂[i] f x • g x :=
  integral_bilinear_partialDeriv_eq_neg_of_contDiffAt
    (ContinuousLinearMap.lsmul ℝ 𝕜) i hf hg hcompact

/-- Scalar–vector coordinate integration by parts from global `C¹` data.
Compact support of the scalar factor supplies all integrability conditions. -/
theorem integral_smul_partialDeriv_eq_neg [NormedSpace 𝕜 F]
    {f : ℝ^n → 𝕜} {g : ℝ^n → F} (i : Fin n)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hcompact : HasCompactSupport f) :
    (∫ x, f x • ∂[i] g x) = -∫ x, ∂[i] f x • g x :=
  integral_smul_fderiv_eq_neg (EuclideanSpace.single i 1) hf hg hcompact

/-- Coordinate integration by parts for multiplication, with `C¹` regularity
of the second factor only on the compact first factor's support. -/
theorem integral_mul_partialDeriv_eq_neg_of_contDiffAt
    {f g : ℝ^n → 𝕜} (i : Fin n)
    (hf : ContDiff ℝ 1 f) (hg : ∀ x ∈ tsupport f, ContDiffAt ℝ 1 g x)
    (hcompact : HasCompactSupport f) :
    (∫ x, f x * ∂[i] g x) = -∫ x, ∂[i] f x * g x :=
  integral_bilinear_partialDeriv_eq_neg_of_contDiffAt
    (ContinuousLinearMap.mul ℝ 𝕜) i hf hg hcompact

/-- Real or complex coordinate integration by parts under global `C¹` hypotheses. -/
theorem integral_mul_partialDeriv_eq_neg {f g : ℝ^n → 𝕜} (i : Fin n)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hcompact : HasCompactSupport f) :
    (∫ x, f x * ∂[i] g x) = -∫ x, ∂[i] f x * g x :=
  integral_mul_fderiv_eq_neg (EuclideanSpace.single i 1) hf hg hcompact

end Scalar

end PDE.Analysis
