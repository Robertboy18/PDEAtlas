/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.PlanarEndpoint.Holder
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Planar order-two embedding for smooth compact data

For smooth compactly supported real functions on `ℝ²`, the bundled
`W^{2,2}` norm equals the sum of the six squared `L²` derivative norms through
order two. Fourier inversion and Plancherel give the pointwise estimate with
constant `3 / (2√π)` and the Hölder estimate for every `0 < γ < 1`.

The pointwise constant is the Bessel-norm constant `1 / (2√π)` multiplied by
`3` from the nonsharp six-row symbol comparison in
`PDE.Analysis.Fourier.PlanarEndpoint`. The Hölder constant has the same factor
`3`, together with the normalized Fourier phase bound `1 / π` and the kernel norm.

The representative theorem for arbitrary Sobolev classes is in
`PDE.Spaces.Sobolev.Inequalities.PlanarEmbedding.Representative`.

## Main results

* `SobolevSpace.smoothCompact_orderTwo_norm_sq`: the squared bundled `W^{2,2}(ℝ²)` norm is the
  sum of the six squared `L²` norms of the derivatives through order two.
* `SobolevSpace.smoothCompact_orderTwo_pointwise`: `|f x| ≤ (3 / (2√π)) ‖f‖_{W^{2,2}}`.
* `SobolevSpace.smoothCompact_orderTwo_holder`: the Hölder estimate of exponent `γ` for
  `0 < γ < 1`, with constant `(3 / π) ‖orderTwoHolderKernel γ‖_{L²}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3, Theorem 6, pp. 284-285, for the embedding of
  `W^{2,2}` into `C^{0,γ}` for `0 < γ < 1` in two dimensions, and §5.10, Problem 20, p. 309, which
  asks for the Fourier transform proof of `‖u‖_{L^∞(ℝⁿ)} ≤ C ‖u‖_{H^s(ℝⁿ)}` for `s > n/2`.
  <https://doi.org/10.1090/gsm/019>
* C. Morosi and L. Pizzocchero, "On the constants for some Sobolev imbeddings", *J. Inequal. Appl.*
  6 (2001), no. 6, 665-679, numbering of arXiv:math/0011141v1, Propositions 2.1 and 3.1, for the
  sharp constant `1 / (2√π)` of the embedding of `H²(ℝ²)` into `L^∞(ℝ²)` in the Bessel norm.
  <https://arxiv.org/abs/math/0011141v1>
* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.1, Proposition 6, for
  the comparison of the derivative norm with the Bessel norm, and Appendix B.4, Proposition 9, for
  the constant `1 / (2√(π(s - 1)))`.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter
open PDE.FDeriv
open PDE.Analysis.Fourier
open LineDeriv
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap Topology

namespace SobolevSpace

/-- The bundled `W^{2,2}(ℝ²)` norm of a smooth compactly supported function
expands into the six symmetric derivative coordinates through order two.
-/
theorem smoothCompact_orderTwo_norm_sq
    (f : (ℝ^2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) :
    ‖GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
        (Ω := Set.univ) f hf hcs‖ ^ 2 =
      (∫ x, f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [0] f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [1] f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [0, 0] f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [0, 1] f x ^ 2) +
      (∫ x, iteratedPartialDeriv (n := 2) [1, 1] f x ^ 2) := by
  let U := GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
    (Ω := Set.univ) f hf hcs
  have hcoord (a : GraphSpace.DerivIndex 2 2) :
      ‖((U : GraphSpace.WkpAmbientOn 2 2 2 Set.univ) a)‖ ^ 2 =
        ∫ x, iteratedPartialDeriv (n := 2) a.toList f x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    simp only [domainMeasure, Measure.restrict_univ]
    apply integral_congr_ae
    have hae := GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
      (n := 2) (k := 2) (p := 2) (Ω := Set.univ) f hf hcs a
    have hae' :
        (((U : GraphSpace.WkpAmbientOn 2 2 2 Set.univ) a : (ℝ^2) → ℝ)) =ᵐ[volume]
          fun x ↦ iteratedPartialDeriv (n := 2) a.toList f x := by
      simpa [U, domainMeasure] using hae
    filter_upwards [hae'] with x hx
    rw [hx]
    simp [pow_two]
  have hidx (α : List (Fin 2)) (hα : α.length ≤ 2) :
      (fun x ↦ iteratedPartialDeriv (n := 2)
        (GraphSpace.derivIndexOfList α hα).toList f x) =
      fun x ↦ iteratedPartialDeriv (n := 2) α f x :=
    iteratedPartialDeriv_congr_perm_smooth hf
      (GraphSpace.derivIndexOfList_toList_perm α hα)
  have hidxInt (α : List (Fin 2)) (hα : α.length ≤ 2) :
      (∫ x, iteratedPartialDeriv (n := 2)
          (GraphSpace.derivIndexOfList α hα).toList f x ^ 2) =
        ∫ x, iteratedPartialDeriv (n := 2) α f x ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [congrFun (hidx α hα) x]
  change ‖(U : GraphSpace.WkpAmbientOn 2 2 2 Set.univ)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  rw [GraphSpace.sum_derivIndex_two_two]
  rw [hcoord, hcoord, hcoord, hcoord, hcoord, hcoord]
  rw [hidxInt [0] (by simp), hidxInt [1] (by simp),
    hidxInt [0, 0] (by simp), hidxInt [0, 1] (by simp),
    hidxInt [1, 1] (by simp)]
  simp [GraphSpace.baseIndex_toList, iteratedPartialDeriv]

/-- For a smooth compactly supported real function `f` on `ℝ²` and every point `x`,
`|f x| ≤ (3 / (2√π)) ‖f‖`, where the norm is the bundled `W^{2,2}` norm of
`mkWkpSpaceOnOfContDiff`. We transfer the estimate from complex Schwartz functions. The constant
is the sharp Bessel-norm constant `1 / (2√π)` times the factor `3` from a nonsharp comparison
of the six-row derivative norm with the Bessel norm; the sharpness of the Bessel constant does
not transfer to this larger constant.
-/
theorem smoothCompact_orderTwo_pointwise
    (f : (ℝ^2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (x : (ℝ^2)) :
    |f x| ≤ (3 / (2 * √Real.pi)) *
      ‖GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
        (Ω := Set.univ) f hf hcs‖ := by
  have hcsC : HasCompactSupport (fun x ↦ (f x : ℂ)) := by
    simpa [Function.comp_def] using hcs.comp_left (g := Complex.ofReal) (by simp)
  have hfC : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  let sf : 𝓢((ℝ^2), ℂ) := hcsC.toSchwartzMap hfC
  have hfderivC (y : (ℝ^2)) :
      fderiv ℝ (fun x ↦ (f x : ℂ)) y =
        Complex.ofRealCLM.comp (fderiv ℝ f y) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ f) y = _
    rw [fderiv_comp y (Complex.ofRealCLM.differentiableAt)
      (hf.differentiable (by simp) y)]
    simp [ContinuousLinearMap.fderiv]
  have hline (m y : (ℝ^2)) :
      ‖(∂_{m} sf) y‖ = |lineDeriv ℝ f y m| := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change ‖(fderiv ℝ (fun x ↦ (f x : ℂ)) y) m‖ = _
    rw [hfderivC]
    rw [(hf.differentiable (by simp) y).lineDeriv_eq_fderiv]
    simp
  have hlineCoord (i : Fin 2) (y : (ℝ^2)) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} sf) y =
        (((∂[i] f) y : ℝ) : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change (fderiv ℝ (fun x ↦ (f x : ℂ)) y) (EuclideanSpace.single i 1) = _
    rw [hfderivC]
    simp [partialDeriv]
  have hsecondCoord (i j : Fin 2) (y : (ℝ^2)) :
      (∂_{EuclideanSpace.single i (1 : ℝ)}
        (∂_{EuclideanSpace.single j (1 : ℝ)} sf)) y =
        (((∂[i]
          (fun z ↦ ((∂[j] f) z : ℝ))) y : ℝ) : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hfun :
        ((∂_{EuclideanSpace.single j (1 : ℝ)} sf : 𝓢((ℝ^2), ℂ)) : (ℝ^2) → ℂ) =
          fun z ↦ (((∂[j] f) z : ℝ) : ℂ) := by
      funext z
      exact hlineCoord j z
    rw [hfun]
    let g : (ℝ^2) → ℝ := fun z ↦ (∂[j] f) z
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
      simpa [g, iteratedPartialDeriv] using
        PDE.contDiff_top_iteratedPartialDeriv (n := 2) (f := f) hf [j]
    have hgderivC :
        fderiv ℝ (fun z ↦ (g z : ℂ)) y =
          Complex.ofRealCLM.comp (fderiv ℝ g y) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ g) y = _
      rw [fderiv_comp y Complex.ofRealCLM.differentiableAt
        (hg.differentiable (by simp) y)]
      simp [ContinuousLinearMap.fderiv]
    change (fderiv ℝ (fun z ↦ (g z : ℂ)) y) (EuclideanSpace.single i 1) = _
    rw [hgderivC]
    simp [g, partialDeriv]
  have hend := PDE.Analysis.Fourier.morosi_pizzocchero_endpoint_orderTwo_schwartz sf x
  have hnorm := smoothCompact_orderTwo_norm_sq f hf hcs
  rw [← Real.sqrt_sq (norm_nonneg _), hnorm]
  simpa [sf, hlineCoord, hsecondCoord, iteratedPartialDeriv, pow_two] using hend

/-- For real smooth compactly supported data, the Fourier derivative energy
with factor `(2π)⁻²` is exactly the bundled `W^{2,2}` norm squared.
-/
theorem smoothCompact_orderTwo_fourierEnergy_eq_norm_sq
    (f : (ℝ^2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) :
    ((2 * Real.pi) ^ 2)⁻¹ *
        ∫ ξ : (ℝ^2),
          (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 0 ^ 4 +
              ξ 0 ^ 2 * ξ 1 ^ 2 + ξ 1 ^ 4) *
            ‖PDE.Analysis.Fourier.angularFourierTransform2D (fun x ↦ (f x : ℂ)) ξ‖ ^ 2 =
      ‖GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
        (Ω := Set.univ) f hf hcs‖ ^ 2 := by
  have hcsC : HasCompactSupport (fun x ↦ (f x : ℂ)) := by
    simpa [Function.comp_def] using hcs.comp_left
      (g := Complex.ofReal) (by simp)
  have hfC : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  let sf : 𝓢((ℝ^2), ℂ) := hcsC.toSchwartzMap hfC
  have hfderivC (y : (ℝ^2)) :
      fderiv ℝ (fun x ↦ (f x : ℂ)) y =
        Complex.ofRealCLM.comp (fderiv ℝ f y) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ f) y = _
    rw [fderiv_comp y Complex.ofRealCLM.differentiableAt
      (hf.differentiable (by simp) y)]
    simp [ContinuousLinearMap.fderiv]
  have hlineCoord (i : Fin 2) (y : (ℝ^2)) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} sf) y =
        (((∂[i] f) y : ℝ) : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change (fderiv ℝ (fun x ↦ (f x : ℂ)) y)
      (EuclideanSpace.single i 1) = _
    rw [hfderivC]
    simp [partialDeriv]
  have hsecondCoord (i j : Fin 2) (y : (ℝ^2)) :
      (∂_{EuclideanSpace.single i (1 : ℝ)}
        (∂_{EuclideanSpace.single j (1 : ℝ)} sf)) y =
        (((∂[i]
          (fun z ↦ ((∂[j] f) z : ℝ))) y : ℝ) : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hfun :
        ((∂_{EuclideanSpace.single j (1 : ℝ)} sf : 𝓢((ℝ^2), ℂ)) :
            (ℝ^2) → ℂ) =
          fun z ↦ (((∂[j] f) z : ℝ) : ℂ) := by
      funext z
      exact hlineCoord j z
    rw [hfun]
    let g : (ℝ^2) → ℝ := fun z ↦ (∂[j] f) z
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
      simpa [g, iteratedPartialDeriv] using
        PDE.contDiff_top_iteratedPartialDeriv (n := 2) (f := f) hf [j]
    have hgderivC :
        fderiv ℝ (fun z ↦ (g z : ℂ)) y =
          Complex.ofRealCLM.comp (fderiv ℝ g y) := by
      change fderiv ℝ (Complex.ofRealCLM ∘ g) y = _
      rw [fderiv_comp y Complex.ofRealCLM.differentiableAt
        (hg.differentiable (by simp) y)]
      simp [ContinuousLinearMap.fderiv]
    change (fderiv ℝ (fun z ↦ (g z : ℂ)) y)
      (EuclideanSpace.single i 1) = _
    rw [hgderivC]
    simp [g, partialDeriv]
  have hFourier := PDE.Analysis.Fourier.angularFourier_orderTwo_derivativeEnergy_eq_schwartz sf
  have hnorm := smoothCompact_orderTwo_norm_sq f hf hcs
  rw [hnorm]
  simpa [sf, hlineCoord, hsecondCoord, iteratedPartialDeriv, pow_two] using hFourier

/-- For `0 < γ < 1`, a smooth compactly supported real function `f` on `ℝ²` satisfies
`|f x - f y| ≤ (3 / π) ‖K_γ‖_{L²} ‖f‖ ‖x - y‖ ^ γ` for all `x` and `y`, where `K_γ` is
`orderTwoHolderKernel γ` and the norm of `f` is the bundled `W^{2,2}` norm.
-/
theorem smoothCompact_orderTwo_holder
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (f : (ℝ^2) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (x y : (ℝ^2)) :
    |f x - f y| ≤
      (3 / Real.pi) * √(∫ ξ : (ℝ^2), orderTwoHolderKernel γ ξ ^ 2) *
        ‖GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
          (Ω := Set.univ) f hf hcs‖ *
        ‖x - y‖ ^ γ := by
  have hcsC : HasCompactSupport (fun z ↦ (f z : ℂ)) := by
    simpa [Function.comp_def] using hcs.comp_left
      (g := Complex.ofReal) (by simp)
  have hfC : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ (f z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  let sf : 𝓢((ℝ^2), ℂ) := hcsC.toSchwartzMap hfC
  have hfInt : Integrable (fun z : (ℝ^2) ↦ (f z : ℂ)) := by
    exact hfC.continuous.integrable_of_hasCompactSupport hcsC
  have hFourier : Integrable (𝓕 (fun z : (ℝ^2) ↦ (f z : ℂ))) := by
    simpa [sf, SchwartzMap.fourier_coe] using (𝓕 sf).integrable
  have hEnergy : Integrable (fun ξ : (ℝ^2) ↦
      (1 + ‖ξ‖ ^ 2) ^ 2 *
        ‖PDE.Analysis.Fourier.angularFourierTransform2D (fun z ↦ (f z : ℂ)) ξ‖ ^ 2) := by
    simpa [sf, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using
      PDE.Analysis.Fourier.integrable_angularFourier_orderTwo_besselEnergy_schwartz sf
  have hHolder := angularFourier_orderTwo_holder γ hγ0 hγ1
    (fun z : (ℝ^2) ↦ (f z : ℂ)) hfC.continuous hfInt hFourier hEnergy x y
  have hcomparison :=
    PDE.Analysis.Fourier.sqrt_normalized_point_orderTwo_bessel_le_three_derivative
      (fun ξ : (ℝ^2) ↦
        ‖PDE.Analysis.Fourier.angularFourierTransform2D (fun z ↦ (f z : ℂ)) ξ‖)
      (by simpa [sf] using
        PDE.Analysis.Fourier.integrable_angularFourier_orderTwo_derivativeEnergy_schwartz sf)
      (by simpa [sf] using
        PDE.Analysis.Fourier.integrable_angularFourier_orderTwo_besselEnergy_schwartz sf)
  rw [smoothCompact_orderTwo_fourierEnergy_eq_norm_sq f hf hcs,
    Real.sqrt_sq (norm_nonneg _)] at hcomparison
  have hcomparison' :
      √(((2 * Real.pi) ^ 2)⁻¹ *
        ∫ ξ : (ℝ^2), (1 + ‖ξ‖ ^ 2) ^ 2 *
          ‖PDE.Analysis.Fourier.angularFourierTransform2D (fun z ↦ (f z : ℂ)) ξ‖ ^ 2) ≤
        3 * ‖GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
          (Ω := Set.univ) f hf hcs‖ := by
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using hcomparison
  have hK : 0 ≤ √(∫ ξ : (ℝ^2), orderTwoHolderKernel γ ξ ^ 2) := Real.sqrt_nonneg _
  have hD : 0 ≤ ‖x - y‖ ^ γ := Real.rpow_nonneg (norm_nonneg _) _
  calc
    |f x - f y| = ‖(f x : ℂ) - (f y : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (1 / Real.pi) * √(∫ ξ : (ℝ^2), orderTwoHolderKernel γ ξ ^ 2) *
        √(((2 * Real.pi) ^ 2)⁻¹ *
          ∫ ξ : (ℝ^2), (1 + ‖ξ‖ ^ 2) ^ 2 *
            ‖PDE.Analysis.Fourier.angularFourierTransform2D (fun z ↦ (f z : ℂ)) ξ‖ ^ 2) *
        ‖x - y‖ ^ γ := hHolder
    _ ≤ (1 / Real.pi) * √(∫ ξ : (ℝ^2), orderTwoHolderKernel γ ξ ^ 2) *
        (3 * ‖GraphSpace.mkWkpSpaceOnOfContDiff (n := 2) (k := 2) (p := 2)
          (Ω := Set.univ) f hf hcs‖) *
        ‖x - y‖ ^ γ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcomparison' (by positivity)) hD
    _ = _ := by ring

end SobolevSpace
