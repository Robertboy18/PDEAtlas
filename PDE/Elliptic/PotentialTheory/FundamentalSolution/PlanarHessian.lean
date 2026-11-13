/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarGradient
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The planar Hessian kernels

Off the pole, the second derivatives of the planar fundamental solution
`Φ(z) = -(2π)⁻¹ log |z|` are `∂ᵢ∂ⱼΦ = π⁻¹ kᵢⱼ` with the homogeneous kernels

`kᵢⱼ(z) = (2 zᵢ zⱼ - δᵢⱼ |z|²) / (2 |z|⁴)`.

They are the kernels of Chen and Hou I, Section 3, (3.1), the second derivatives of
`G(y) = -(1/2) log |y| = π Φ(y)`: `K₁(y) = y₁ y₂ / |y|⁴ = k₀₁(y)` and
`K₂(y) = (y₁² - y₂²) / (2 |y|⁴) = k₀₀(y)`, with `k₁₁ = -K₂`. Coordinate `0` of `ℝ^2` is `y₁`.
In complex notation `w = z₀ + i z₁`, `K₂ - i K₁ = 1 / (2 w²)`; this identity reduces every
derivative bound of the kernels to derivatives of `w⁻²`.

## Main results

* `hessianKernel`: the kernel `kᵢⱼ`, set to `0` at the pole.
* `hessianKernel_zero_one`, `hessianKernel_zero_zero`, `hessianKernel_one_one`: the explicit
  forms of `K₁`, `K₂` and `k₁₁ = -K₂`.
* `hessianKernel_zero_zero_eq_re`, `hessianKernel_zero_one_eq_neg_im`: the complex form.
* `abs_hessianKernel_le`: `|kᵢⱼ(z)| ≤ 1 / (2 |z|²)`.
* `hessianKernel_smul`: homogeneity of degree `-2`.
* reflection and swap symmetries: `K₁` is odd under each coordinate reflection and invariant
  under the coordinate swap; `K₂` is even under each reflection and odd under the swap.
* `partialDeriv_gradientKernel`: `∂ᵢ (∂ⱼ Φ) = π⁻¹ kᵢⱼ` away from the pole.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3, (3.1).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Complex
open scoped ComplexConjugate

namespace PotentialTheory.Planar

open PDE (partialDeriv)

/-- The planar Hessian kernel `kᵢⱼ(z) = (2 zᵢ zⱼ - δᵢⱼ |z|²) / (2 |z|⁴)`, so that
`∂ᵢ ∂ⱼ Φ = π⁻¹ kᵢⱼ` away from the pole. Its value at the pole is `0`. -/
def hessianKernel (i j : Fin 2) (z : ℝ^2) : ℝ :=
  (2 * z i * z j - if i = j then ‖z‖ ^ 2 else 0) / (2 * ‖z‖ ^ 4)

/-- The squared norm of the point `(s, h)` of the plane is `s² + h²`. -/
theorem norm_sq_vec (s h : ℝ) : ‖(!₂[s, h] : ℝ^2)‖ ^ 2 = s ^ 2 + h ^ 2 := by
  rw [EuclideanSpace.norm_sq_fin_two]
  simp

/-- The Hessian kernel is symmetric in its two indices. -/
theorem hessianKernel_comm (i j : Fin 2) (z : ℝ^2) :
    hessianKernel i j z = hessianKernel j i z := by
  unfold hessianKernel
  rw [mul_assoc, mul_comm (z i), ← mul_assoc]
  simp only [eq_comm (a := i)]

/-- `K₁(z) = z₀ z₁ / |z|⁴`. -/
theorem hessianKernel_zero_one (z : ℝ^2) : hessianKernel 0 1 z = z 0 * z 1 / ‖z‖ ^ 4 := by
  simp only [hessianKernel, Fin.isValue, zero_ne_one, ↓reduceIte, sub_zero]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · field_simp

/-- `K₂(z) = (z₀² - z₁²) / (2 |z|⁴)`. -/
theorem hessianKernel_zero_zero (z : ℝ^2) :
    hessianKernel 0 0 z = (z 0 ^ 2 - z 1 ^ 2) / (2 * ‖z‖ ^ 4) := by
  simp only [hessianKernel, ↓reduceIte, EuclideanSpace.norm_sq_fin_two]
  ring_nf

/-- `K₁(p, q) = p q / (p² + q²)²` at the point `(p, q)`. -/
theorem hessianKernel_zero_one_toLp (p q : ℝ) :
    hessianKernel 0 1 !₂[p, q] = p * q / (p ^ 2 + q ^ 2) ^ 2 := by
  rw [hessianKernel_zero_one, show ‖(!₂[p, q] : ℝ^2)‖ ^ 4 = (‖(!₂[p, q] : ℝ^2)‖ ^ 2) ^ 2 by ring,
    norm_sq_vec]
  simp

/-- For `p ≠ 0` the vertical slice `q ↦ K₁(p, q)` is continuous. -/
theorem continuous_hessianKernel_zero_one_slice {p : ℝ} (hp : p ≠ 0) :
    Continuous fun q : ℝ ↦ hessianKernel 0 1 !₂[p, q] := by
  simp only [hessianKernel_zero_one_toLp]
  exact (continuous_const.mul continuous_id).div (by fun_prop) fun q ↦ by positivity

/-- The difference of a point and a point given in coordinates. -/
theorem sub_vec (x : ℝ^2) (s t : ℝ) : x - !₂[s, t] = !₂[x 0 - s, x 1 - t] := by
  ext i
  fin_cases i <;> simp

/-- `K₂(p, q) = (p² - q²) / (2 (p² + q²)²)` at the point `(p, q)`. -/
theorem hessianKernel_zero_zero_toLp (p q : ℝ) :
    hessianKernel 0 0 !₂[p, q] = (p ^ 2 - q ^ 2) / (2 * (p ^ 2 + q ^ 2) ^ 2) := by
  rw [hessianKernel_zero_zero, show ‖(!₂[p, q] : ℝ^2)‖ ^ 4 = (‖(!₂[p, q] : ℝ^2)‖ ^ 2) ^ 2 by ring,
    norm_sq_vec]
  simp

/-- `k₁₁ = -K₂`. -/
theorem hessianKernel_one_one (z : ℝ^2) : hessianKernel 1 1 z = -hessianKernel 0 0 z := by
  simp only [hessianKernel, ↓reduceIte, EuclideanSpace.norm_sq_fin_two]
  ring

/-- `k₁₀ = K₁`. -/
theorem hessianKernel_one_zero (z : ℝ^2) : hessianKernel 1 0 z = hessianKernel 0 1 z :=
  hessianKernel_comm 1 0 z

/-- The real part of the complex coordinate `z₀ + i z₁` of a planar point is `z₀`. -/
theorem orthonormalBasisOneI_repr_symm_re (z : ℝ^2) :
    (Complex.orthonormalBasisOneI.repr.symm z).re = z 0 := by
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  simp

/-- The imaginary part of the complex coordinate `z₀ + i z₁` of a planar point is `z₁`. -/
theorem orthonormalBasisOneI_repr_symm_im (z : ℝ^2) :
    (Complex.orthonormalBasisOneI.repr.symm z).im = z 1 := by
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  simp

/-- In the complex coordinate the reflection `R₀ : z₀ ↦ -z₀` is `w ↦ -conj w`. -/
theorem orthonormalBasisOneI_repr_symm_coordinateReflection_zero (z : ℝ^2) :
    Complex.orthonormalBasisOneI.repr.symm (PDE.Common.coordinateReflection 0 z) =
      -conj (Complex.orthonormalBasisOneI.repr.symm z) := by
  apply Complex.ext
  · rw [orthonormalBasisOneI_repr_symm_re, neg_re, conj_re, orthonormalBasisOneI_repr_symm_re,
      PDE.Common.coordinateReflection_apply_same]
  · rw [orthonormalBasisOneI_repr_symm_im, neg_im, conj_im, orthonormalBasisOneI_repr_symm_im,
      neg_neg, PDE.Common.coordinateReflection_apply_of_ne 0 1 (by decide)]

/-- In the complex coordinate the reflection `R₁ : z₁ ↦ -z₁` is `w ↦ conj w`. -/
theorem orthonormalBasisOneI_repr_symm_coordinateReflection_one (z : ℝ^2) :
    Complex.orthonormalBasisOneI.repr.symm (PDE.Common.coordinateReflection 1 z) =
      conj (Complex.orthonormalBasisOneI.repr.symm z) := by
  apply Complex.ext
  · rw [orthonormalBasisOneI_repr_symm_re, conj_re, orthonormalBasisOneI_repr_symm_re,
      PDE.Common.coordinateReflection_apply_of_ne 1 0 (by decide)]
  · rw [orthonormalBasisOneI_repr_symm_im, conj_im, orthonormalBasisOneI_repr_symm_im,
      PDE.Common.coordinateReflection_apply_same]

/-- `K₂(z) = Re (1 / (2 w²))` with `w = z₀ + i z₁`. -/
theorem hessianKernel_zero_zero_eq_re (z : ℝ^2) :
    hessianKernel 0 0 z = (1 / (2 * (Complex.orthonormalBasisOneI.repr.symm z) ^ 2)).re := by
  have hre := orthonormalBasisOneI_repr_symm_re z
  have him := orthonormalBasisOneI_repr_symm_im z
  set w := Complex.orthonormalBasisOneI.repr.symm z
  rw [hessianKernel_zero_zero, one_div, Complex.inv_re, Complex.normSq_apply]
  have h2 : (2 * w ^ 2).re = 2 * (z 0 ^ 2 - z 1 ^ 2) := by
    simp [sq, hre, him]
  have h2' : (2 * w ^ 2).im = 4 * (z 0 * z 1) := by
    simp [sq, hre, him]; ring
  have hden : 2 * (z 0 ^ 2 - z 1 ^ 2) * (2 * (z 0 ^ 2 - z 1 ^ 2)) +
      4 * (z 0 * z 1) * (4 * (z 0 * z 1)) = 4 * (z 0 ^ 2 + z 1 ^ 2) ^ 2 := by ring
  rw [h2, h2', hden, show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring, EuclideanSpace.norm_sq_fin_two]
  by_cases h0 : z 0 ^ 2 + z 1 ^ 2 = 0
  · have ha : z 0 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    have hb : z 1 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    simp [ha, hb]
  · field_simp
    ring

/-- `K₁(z) = -Im (1 / (2 w²))` with `w = z₀ + i z₁`. -/
theorem hessianKernel_zero_one_eq_neg_im (z : ℝ^2) :
    hessianKernel 0 1 z = -(1 / (2 * (Complex.orthonormalBasisOneI.repr.symm z) ^ 2)).im := by
  have hre := orthonormalBasisOneI_repr_symm_re z
  have him := orthonormalBasisOneI_repr_symm_im z
  set w := Complex.orthonormalBasisOneI.repr.symm z
  rw [hessianKernel_zero_one, one_div, Complex.inv_im, Complex.normSq_apply]
  have h2 : (2 * w ^ 2).re = 2 * (z 0 ^ 2 - z 1 ^ 2) := by
    simp [sq, hre, him]
  have h2' : (2 * w ^ 2).im = 4 * (z 0 * z 1) := by
    simp [sq, hre, him]; ring
  have hden : 2 * (z 0 ^ 2 - z 1 ^ 2) * (2 * (z 0 ^ 2 - z 1 ^ 2)) +
      4 * (z 0 * z 1) * (4 * (z 0 * z 1)) = 4 * (z 0 ^ 2 + z 1 ^ 2) ^ 2 := by ring
  rw [h2, h2', hden, show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring, EuclideanSpace.norm_sq_fin_two]
  by_cases h0 : z 0 ^ 2 + z 1 ^ 2 = 0
  · have ha : z 0 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    have hb : z 1 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    simp [ha, hb]
  · field_simp

/-- The Hessian kernels are bounded by `1 / (2 |z|²)`. -/
theorem abs_hessianKernel_le (i j : Fin 2) (z : ℝ^2) :
    |hessianKernel i j z| ≤ 1 / (2 * ‖z‖ ^ 2) := by
  by_cases hz : z = 0
  · subst hz; simp [hessianKernel]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h4 : ‖z‖ ^ 4 = ‖z‖ ^ 2 * ‖z‖ ^ 2 := by ring
  have hoff : |hessianKernel 0 1 z| ≤ 1 / (2 * ‖z‖ ^ 2) := by
    rw [hessianKernel_zero_one, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖z‖ ^ 4), h4,
      div_le_div_iff₀ (by positivity) (by positivity), abs_mul]
    have : 2 * (|z 0| * |z 1|) ≤ ‖z‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_fin_two, ← sq_abs (z 0), ← sq_abs (z 1)]
      nlinarith [sq_nonneg (|z 0| - |z 1|)]
    nlinarith [sq_nonneg ‖z‖]
  have hdiag : |hessianKernel 0 0 z| ≤ 1 / (2 * ‖z‖ ^ 2) := by
    rw [hessianKernel_zero_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ‖z‖ ^ 4),
      h4, div_le_div_iff₀ (by positivity) (by positivity)]
    have : |z 0 ^ 2 - z 1 ^ 2| ≤ ‖z‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_fin_two, abs_le]
      constructor <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    nlinarith [sq_nonneg ‖z‖]
  fin_cases i <;> fin_cases j
  · exact hdiag
  · exact hoff
  · simpa [hessianKernel_one_zero] using hoff
  · simpa [hessianKernel_one_one, abs_neg] using hdiag

/-- The Hessian kernels are homogeneous of degree `-2`. -/
theorem hessianKernel_smul (i j : Fin 2) (c : ℝ) (z : ℝ^2) :
    hessianKernel i j (c • z) = (c ^ 2)⁻¹ * hessianKernel i j z := by
  by_cases hc : c = 0
  · subst hc; simp [hessianKernel]
  unfold hessianKernel
  simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hc4 : |c| ^ 4 = (c ^ 2) ^ 2 := by rw [← sq_abs c]; ring
  rw [hc4]
  split_ifs
  · field_simp
  · simp only [sub_zero]; field_simp

/-- The Hessian kernels are even. -/
theorem hessianKernel_neg (i j : Fin 2) (z : ℝ^2) :
    hessianKernel i j (-z) = hessianKernel i j z := by
  simp [hessianKernel]

/-- `K₁` is odd under each coordinate reflection. -/
theorem hessianKernel_zero_one_coordinateReflection (k : Fin 2) (z : ℝ^2) :
    hessianKernel 0 1 (PDE.Common.coordinateReflection k z) = -hessianKernel 0 1 z := by
  rw [hessianKernel_zero_one, hessianKernel_zero_one, PDE.Common.norm_coordinateReflection]
  fin_cases k <;>
    simp [PDE.Common.coordinateReflection_apply_same, PDE.Common.coordinateReflection_apply_of_ne]
      <;> ring

/-- `K₂` is even under each coordinate reflection. -/
theorem hessianKernel_zero_zero_coordinateReflection (k : Fin 2) (z : ℝ^2) :
    hessianKernel 0 0 (PDE.Common.coordinateReflection k z) = hessianKernel 0 0 z := by
  rw [hessianKernel_zero_zero, hessianKernel_zero_zero, PDE.Common.norm_coordinateReflection]
  fin_cases k <;>
    simp [PDE.Common.coordinateReflection_apply_same, PDE.Common.coordinateReflection_apply_of_ne]

/-- The isometry exchanging the two planar coordinates. -/
theorem coordinateSwap_apply (z : ℝ^2) :
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) z) 0 = z 1 ∧
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) z) 1 = z 0 := by
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

/-- `K₁` is invariant under the coordinate swap. -/
theorem hessianKernel_zero_one_swap (z : ℝ^2) :
    hessianKernel 0 1 (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) z) =
      hessianKernel 0 1 z := by
  obtain ⟨h0, h1⟩ := coordinateSwap_apply z
  rw [hessianKernel_zero_one, hessianKernel_zero_one, LinearIsometryEquiv.norm_map, h0, h1,
    mul_comm]

/-- `K₂` is odd under the coordinate swap. -/
theorem hessianKernel_zero_zero_swap (z : ℝ^2) :
    hessianKernel 0 0 (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) z) =
      -hessianKernel 0 0 z := by
  obtain ⟨h0, h1⟩ := coordinateSwap_apply z
  rw [hessianKernel_zero_zero, hessianKernel_zero_zero, LinearIsometryEquiv.norm_map, h0, h1]
  ring

/-- The Hessian kernels are measurable. -/
theorem measurable_hessianKernel (i j : Fin 2) : Measurable (hessianKernel i j) := by
  unfold hessianKernel
  have hi : Measurable fun z : ℝ^2 ↦ z i := (EuclideanSpace.proj i).continuous.measurable
  have hj : Measurable fun z : ℝ^2 ↦ z j := (EuclideanSpace.proj j).continuous.measurable
  split_ifs <;> fun_prop

/-- The gradient kernel is homogeneous of degree `-1`. -/
theorem gradientKernel_smul (j : Fin 2) {c : ℝ} (hc : 0 < c) (z : ℝ^2) :
    gradientKernel j (c • z) = c⁻¹ * gradientKernel j z := by
  rw [gradientKernel_eq_div, gradientKernel_eq_div]
  simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · field_simp

/-- The gradient kernel is even up to sign: `gⱼ(-z) = -gⱼ(z)`. -/
theorem gradientKernel_neg (j : Fin 2) (z : ℝ^2) : gradientKernel j (-z) = -gradientKernel j z := by
  rw [gradientKernel_eq_div, gradientKernel_eq_div]
  simp only [PiLp.neg_apply, norm_neg]
  ring

/-- The gradient kernel as an explicit quotient. -/
private theorem gradientKernel_eq_mul_inv (j : Fin 2) :
    gradientKernel j = fun y : ℝ^2 ↦ -(1 / (2 * Real.pi)) * (y j * (‖y‖ ^ 2)⁻¹) := by
  funext y; rw [gradientKernel_eq_div]; ring

/-- **The second derivatives of the planar fundamental solution**: away from the pole,
`∂ᵢ (∂ⱼ Φ) = π⁻¹ kᵢⱼ`. -/
theorem partialDeriv_gradientKernel (i j : Fin 2) {z : ℝ^2} (hz : z ≠ 0) :
    (∂[i] (gradientKernel j)) z = hessianKernel i j z / Real.pi := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have h1 : HasFDerivAt (fun y : ℝ^2 ↦ y j) (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ) z :=
    (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun y : ℝ^2 ↦ (‖y‖ ^ 2)⁻¹) _ z :=
    (hasFDerivAt_inv hn).comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h : HasFDerivAt (fun y : ℝ^2 ↦ -(1 / (2 * Real.pi)) * (y j * (‖y‖ ^ 2)⁻¹)) _ z :=
    (h1.fun_mul h2).const_mul _
  unfold partialDeriv
  rw [gradientKernel_eq_mul_inv, h.fderiv]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  by_cases hij : j = i
  · subst hij
    simp [hessianKernel, EuclideanSpace.inner_single_right]
    field_simp
    ring
  · have hji : i ≠ j := Ne.symm hij
    simp [hessianKernel, EuclideanSpace.inner_single_right, hij, hji]
    field_simp

/-- Away from the pole the gradient kernel is smooth. -/
theorem contDiffAt_gradientKernel (j : Fin 2) {z : ℝ^2} (hz : z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (gradientKernel j) z := by
  rw [gradientKernel_eq_mul_inv]
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hj : ContDiffAt ℝ n (fun y : ℝ^2 ↦ y j) z :=
    (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ).contDiff.contDiffAt
  exact contDiffAt_const.mul (hj.mul ((contDiff_norm_sq ℝ).contDiffAt.inv hn))

/-- Away from the pole the Hessian kernels are smooth. -/
theorem contDiffAt_hessianKernel (i j : Fin 2) {z : ℝ^2} (hz : z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (hessianKernel i j) z := by
  have hn : 2 * ‖z‖ ^ 4 ≠ 0 := by
    have := norm_ne_zero_iff.mpr hz
    positivity
  have hi : ContDiff ℝ n (fun y : ℝ^2 ↦ y i) := (EuclideanSpace.proj i : ℝ^2 →L[ℝ] ℝ).contDiff
  have hj : ContDiff ℝ n (fun y : ℝ^2 ↦ y j) := (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ).contDiff
  have hsq : ContDiff ℝ n (fun y : ℝ^2 ↦ ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have h4 : ContDiff ℝ n (fun y : ℝ^2 ↦ 2 * ‖y‖ ^ 4) := by
    have : (fun y : ℝ^2 ↦ 2 * ‖y‖ ^ 4) = fun y ↦ 2 * (‖y‖ ^ 2) ^ 2 := by
      funext y; ring
    rw [this]; exact contDiff_const.mul (hsq.pow 2)
  unfold hessianKernel
  split_ifs
  · exact ((contDiff_const.mul hi).mul hj |>.sub hsq).contDiffAt.div h4.contDiffAt hn
  · exact ((contDiff_const.mul hi).mul hj |>.sub contDiff_const).contDiffAt.div h4.contDiffAt hn

end PotentialTheory.Planar
