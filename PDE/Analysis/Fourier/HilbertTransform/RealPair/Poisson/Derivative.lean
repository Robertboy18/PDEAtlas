/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Poisson
public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue
import PDE.Analysis.Fourier.HilbertTransform.RealPair.Derivative
import PDE.Analysis.Fourier.HilbertTransform.RealPair.PrincipalValue.LocallyLipschitz
import CAS.ExactTactic

/-!
# The differentiated Poisson kernels as a Hilbert pair

For `ε > 0` the derivative `(ε² - x²) / (ε² + x²)²` of the conjugate Poisson kernel
`x / (ε² + x²)` is the Hilbert transform of the derivative `-2 ε x / (ε² + x²)²` of the Poisson
kernel `ε / (ε² + x²)`. These are the real and imaginary parts of `-i / (x + i ε)²`, the
derivative of `i / (x + i ε)`, whose real and imaginary parts are the Poisson kernel and its
conjugate. The relation is proved in two forms: almost everywhere, as an `IsHilbertPair`, and
pointwise, as a principal value at every real `x`.

## Main results

* `PDE.Analysis.isHilbertPair_deriv_poisson`: for every `ε > 0`, `(ε² - x²) / (ε² + x²)²` is the
  Hilbert transform of `-2 ε x / (ε² + x²)²`.
* `PDE.Analysis.integrable_deriv_poisson`: for every `ε > 0`, `-2 ε x / (ε² + x²)²` is
  integrable.
* `PDE.Analysis.hasHilbertPV_deriv_poisson`: for every `ε > 0` and every real `x`, the Hilbert
  principal value of `-2 ε y / (ε² + y²)²` at `x` exists and equals `(ε² - x²) / (ε² + x²)²`.

## How it works

The Hilbert transform commutes with differentiation (`IsHilbertPair.deriv`), and the Poisson
kernel and its conjugate are a Hilbert pair (`isHilbertPair_poisson`). The derivative of the
Poisson kernel is `-2` times the product of the Poisson kernel and its conjugate, both square
integrable, so it is integrable. It is continuously differentiable, and the derivative of the
conjugate kernel is continuous, so the pair is a principal value at every point by
`IsHilbertPair.hasHilbertPV`.

## References

The pair is obtained here from `isHilbertPair_poisson`. It is the profile of explicit
self-similar solutions of the generalized Constantin–Lax–Majda equation:

* J. Chen, "Singularity formation and global well-posedness for the generalized
  Constantin–Lax–Majda equation with dissipation", *Nonlinearity* 33 (2020), no. 5, 2502-2532;
  numbering of arXiv:1908.09385v1, (2.2), p. 4, where `Ω = -2 b x / (x² + b²)²` and
  `U_x = (b² - x²) / (b² + x²)² = HΩ` are this pair at `ε = b`.
  <https://doi.org/10.1088/1361-6544/ab74b0> <https://arxiv.org/abs/1908.09385v1>
* P. M. Lushnikov, D. A. Silantyev, and M. Siegel, "Collapse versus blow-up and global existence
  in the generalized Constantin–Lax–Majda equation", *J. Nonlinear Sci.* 31 (2021), no. 5,
  article 82; numbering of arXiv:2010.01201v2, (33) and (34), p. 10, the same pair with the pole
  at height `v_c`. <https://doi.org/10.1007/s00332-021-09737-x>
  <https://arxiv.org/abs/2010.01201v2>
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PDE.Analysis

/-- **The Hilbert transform of the differentiated Poisson kernel.** For `ε > 0` the derivative
`(ε² - x²) / (ε² + x²)²` of the conjugate Poisson kernel is the Hilbert transform of the
derivative `-2 ε x / (ε² + x²)²` of the Poisson kernel. -/
theorem isHilbertPair_deriv_poisson {ε : ℝ} (hε : 0 < ε) :
    IsHilbertPair (fun x ↦ -(2 * ε * x) / (ε ^ 2 + x ^ 2) ^ 2)
      (fun x ↦ (ε ^ 2 - x ^ 2) / (ε ^ 2 + x ^ 2) ^ 2) := by
  have hd (x : ℝ) : ε ^ 2 + x ^ 2 ≠ 0 := by positivity
  have hP : deriv (fun x : ℝ ↦ ε / (ε ^ 2 + x ^ 2)) =
      fun x ↦ -(2 * ε * x) / (ε ^ 2 + x ^ 2) ^ 2 := funext fun x ↦ by cas using [hd x]
  have hQ : deriv (fun x : ℝ ↦ x / (ε ^ 2 + x ^ 2)) =
      fun x ↦ (ε ^ 2 - x ^ 2) / (ε ^ 2 + x ^ 2) ^ 2 := funext fun x ↦ by cas using [hd x]
  have hpair := isHilbertPair_poisson hε
  rw [← hP, ← hQ]
  refine hpair.deriv (by cas) ?_ (by cas)
  refine hpair.memLp_left.of_le_mul (c := ε⁻¹) (aestronglyMeasurable_deriv _ _)
    (.of_forall fun x ↦ ?_)
  have hx : 2 * ε * |x| ≤ ε ^ 2 + x ^ 2 := by cas using [sq_nonneg (ε - |x|), sq_abs x]
  have h₁ : |-(2 * ε * x) / (ε ^ 2 + x ^ 2) ^ 2| = 2 * ε * |x| / (ε ^ 2 + x ^ 2) ^ 2 := by
    cas using [hε]
  have h₂ : ε⁻¹ * |ε / (ε ^ 2 + x ^ 2)| = (ε ^ 2 + x ^ 2) / (ε ^ 2 + x ^ 2) ^ 2 := by
    cas using [hε]
  rw [hP, Real.norm_eq_abs, Real.norm_eq_abs, h₁, h₂]
  gcongr

/-- For `ε > 0` the derivative `-2 ε x / (ε² + x²)²` of the Poisson kernel is integrable: it is
`-2` times the product of the Poisson kernel and its conjugate, which are square integrable. -/
theorem integrable_deriv_poisson {ε : ℝ} (hε : 0 < ε) :
    Integrable fun x : ℝ ↦ -(2 * ε * x) / (ε ^ 2 + x ^ 2) ^ 2 := by
  have hpair := isHilbertPair_poisson hε
  refine ((hpair.memLp_left.integrable_mul hpair.memLp_right).const_mul (-2)).congr
    (.of_forall fun x ↦ ?_)
  have hd : ε ^ 2 + x ^ 2 ≠ 0 := by positivity
  change -2 * (ε / (ε ^ 2 + x ^ 2) * (x / (ε ^ 2 + x ^ 2))) = -(2 * ε * x) / (ε ^ 2 + x ^ 2) ^ 2
  cas using [hd]

/-- **The principal value of the differentiated Poisson kernel.** For `ε > 0` and every real `x`
the Hilbert principal value `(1 / π) p.v. ∫ f (y) / (x - y) dy` of the derivative
`f (y) = -2 ε y / (ε² + y²)²` of the Poisson kernel exists and equals the derivative
`(ε² - x²) / (ε² + x²)²` of the conjugate Poisson kernel at `x`. This is the pointwise form of
`isHilbertPair_deriv_poisson`. -/
theorem hasHilbertPV_deriv_poisson {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasHilbertPV (fun y ↦ -(2 * ε * y) / (ε ^ 2 + y ^ 2) ^ 2) x
      ((ε ^ 2 - x ^ 2) / (ε ^ 2 + x ^ 2) ^ 2) :=
  (isHilbertPair_deriv_poisson hε).hasHilbertPV (by cas) (integrable_deriv_poisson hε)
    (ContDiff.locallyLipschitz (𝕂 := ℝ) (by cas)) x

end PDE.Analysis
