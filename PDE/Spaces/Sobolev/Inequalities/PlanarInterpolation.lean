/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.WeightedRay
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PDE.Spaces.Sobolev.Weighted.HomogeneousInterpolation
public import PDE.Spaces.Sobolev.Weighted.MixedDerivatives
import CAS.ExactTactic
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Fourier interpolation inequalities on the plane

Interpolation inequalities on `ℝ²`, stated on the Fourier side with explicit constants.
The normalization is `f̂(ξ) = ∫ exp(-i ⟨x,ξ⟩) f(x) dx`, with inverse
`f(x) = (2π)⁻² ∫ exp(i ⟨x,ξ⟩) f̂(ξ) dξ`. For `Fhat : ℝ² → ℂ`, the homogeneous norm
`homogeneousFourierNorm m Fhat = ((2π)⁻² ∫ |ξ|^{2m} |Fhat ξ|²)^{1/2}` is the
Fourier expression of `‖|D|^m F‖₂`, and the aggregate norm
`aggregateFourierNorm m Fhat` replaces `|ξ|^{2m}` by the symbol
`∑_q ξ_r^{2q} ξ_z^{2(m-q)}` of the sum of all order-`m` Cartesian derivatives.
The two symbols differ by at most a factor `2^m`.

Three families of inequalities are proved. The Hilbert interpolation
`‖|D|^j F‖ ≤ ‖|D|^k F‖^{j/k} ‖F‖^{1 - j/k}` for `j < k` is Hölder's
inequality on the Fourier side with exponents `k/j` and `k/(k-j)`. Its
additive form `‖|D|^j F‖ ≤ η ‖|D|^k F‖ + C(j,k,η) ‖F‖` follows from Young's
inequality, with the explicit constant `SobolevSpace.Weighted.youngInterpolationConstant`. The
Sobolev–Bessel comparison bounds `(1 + |ξ|²)^k` above and below by the sum of
the aggregate symbols of order at most `k`, with constants `k + 1` and `3^k`.

## Main results

* `wholePlane_hilbertInterpolation`, `wholePlane_youngInterpolation`:
  multiplicative and additive interpolation of the homogeneous norms.
* `wholePlane_aggregateInterpolation`, `wholePlane_aggregateYoungInterpolation`:
  the same for the aggregate norms, with the conversion factor `√(2^j)` and
  the constant `SobolevSpace.Weighted.aggregateYoungInterpolationConstant`.
* `aggregateFourierNorm_comparison`: two-sided comparison of the aggregate and
  homogeneous norms of the same order.
* `integerSobolevSymbol_comparison`, `sobolevBessel_integerOrder_comparison`:
  the integer-order Sobolev–Bessel norm equivalence on the Fourier side.
* `wholePlane_interpolation_of_plancherel`: the four interpolation inequalities
  restated for a profile `F` and abstract derivative maps `Dhom m`,
  conditional on Plancherel identities supplied as hypotheses.

## Implementation notes

The Fourier estimates assume `Fhat` is a.e. strongly measurable with finite
base and top energies. Every intermediate density is bounded by the sum of
the endpoint densities, so its integral is finite as well. The norm expressions
are total integrals, so outside their
integrability domains they need not describe an `L²` norm, and no membership
claim follows from their being real numbers.

`wholePlane_interpolation_of_plancherel` computes no Fourier transform.
`Dhom : ℕ → (ℝ^2 → ℝ) → (ℝ^2 → ℝ)` is an arbitrary function, and the identities
`wholePlaneL2Norm (Dhom m F) = homogeneousFourierNorm m Fhat` and their
aggregate analogue enter as the hypotheses `hPlancherel` and
`hAggregatePlancherel`; the theorem substitutes them into the four
Fourier-side inequalities. For the convention above,
`PDE.Analysis.Fourier.angularFourierTransform2D f ξ = 𝓕 f ((2π)⁻¹ • ξ)`.
The Plancherel identities for `Dhom m = |D|^m` are not proved here.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.5, Theorem 8, p. 297, for the characterization of
  `H^k(ℝⁿ)` at integer order `k` by the Fourier weight `1 + |y|^k`.
  <https://doi.org/10.1090/gsm/019>
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Chapter 5, Interpolation, Extension, and Approximation Theorems, for
  interpolation inequalities between derivative norms.
  <https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>
* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v2, Appendix B.1, (218)-(220) and
  Proposition 6, for the Fourier normalization, the Bessel norm and the comparison constants, and
  Appendix B.4, Proposition 9, (259)-(260), for the multiplicative and additive interpolation
  inequalities.
  <https://arxiv.org/abs/2609.10860v2>
-/

@[expose] public section

open SobolevSpace.Weighted

noncomputable section

open MeasureTheory
open Filter
open LineDeriv
open scoped ENNReal RealInnerProductSpace Topology

namespace SobolevSpace


/-! ## Whole-plane Sobolev input -/

/-- The homogeneous Fourier `L²` norm of order `m`, with squared factor `(2π)⁻²`.
-/
noncomputable def homogeneousFourierNorm (m : ℕ) (Fhat : (ℝ^2) → ℂ) : ℝ :=
  √((((2 * Real.pi) ^ 2)⁻¹ : ℝ) *
    ∫ ξ : (ℝ^2), ‖ξ‖ ^ (2 * m) * ‖Fhat ξ‖ ^ 2)

/-- The aggregate Fourier norm over order-`m` multiindices, with squared factor `(2π)⁻²`.
-/
noncomputable def aggregateFourierNorm (m : ℕ) (Fhat : (ℝ^2) → ℂ) : ℝ :=
  √((((2 * Real.pi) ^ 2)⁻¹ : ℝ) *
    ∫ ξ : (ℝ^2),
      SobolevSpace.Weighted.aggregateDerivativeSymbol2D m (ξ 0) (ξ 1) * ‖Fhat ξ‖ ^ 2)

/-- A pointwise bound `f ≤ C g` between integrable densities bounds the square roots of their
scaled integrals. -/
private theorem sqrt_mul_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hf : Integrable f μ)
    (hg : Integrable g μ) (h : ∀ x, f x ≤ C * g x) :
    √(c * ∫ x, f x ∂μ) ≤ √C * √(c * ∫ x, g x ∂μ) := by
  rw [← Real.sqrt_mul hC, mul_left_comm, ← integral_const_mul C]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (integral_mono hf (hg.const_mul C) h) hc)

/-- Exact two-sided conversion between the aggregate Cartesian symbol and the
homogeneous radial symbol in two dimensions.
-/
theorem aggregateFourierNorm_comparison
    (m : ℕ) (Fhat : (ℝ^2) → ℂ) (hFhat : AEStronglyMeasurable Fhat)
    (hRadial : Integrable (fun ξ : (ℝ^2) ↦
      ‖ξ‖ ^ (2 * m) * ‖Fhat ξ‖ ^ 2)) :
    aggregateFourierNorm m Fhat ≤ homogeneousFourierNorm m Fhat ∧
      homogeneousFourierNorm m Fhat ≤
        √((2 : ℝ) ^ m) * aggregateFourierNorm m Fhat := by
  have hsymbol_nonneg (ξ : ℝ^2) : 0 ≤ aggregateDerivativeSymbol2D m (ξ 0) (ξ 1) := by
    unfold aggregateDerivativeSymbol2D
    positivity
  have hsymbol_radial (ξ : ℝ^2) : aggregateDerivativeSymbol2D m (ξ 0) (ξ 1) ≤ ‖ξ‖ ^ (2 * m) :=
    (aggregateDerivativeSymbol2D_le_radialSymbol m _ _).trans_eq
      (by rw [← EuclideanSpace.norm_sq_fin_two, pow_mul])
  have hcont : Continuous fun ξ : ℝ^2 ↦ aggregateDerivativeSymbol2D m (ξ 0) (ξ 1) := by
    unfold aggregateDerivativeSymbol2D
    fun_prop
  have haggInt : Integrable fun ξ : ℝ^2 ↦
      aggregateDerivativeSymbol2D m (ξ 0) (ξ 1) * ‖Fhat ξ‖ ^ 2 :=
    hRadial.mono' (hcont.aestronglyMeasurable.mul (hFhat.norm.pow _)) (.of_forall fun ξ ↦ by
      rw [Real.norm_of_nonneg (mul_nonneg (hsymbol_nonneg ξ) (sq_nonneg _))]
      gcongr
      exact hsymbol_radial ξ)
  unfold aggregateFourierNorm homogeneousFourierNorm
  refine ⟨?_, sqrt_mul_integral_le (by positivity) (by positivity) hRadial haggInt fun ξ ↦ ?_⟩
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (integral_mono haggInt hRadial fun ξ ↦
      mul_le_mul_of_nonneg_right (hsymbol_radial ξ) (sq_nonneg _)) (by positivity))
  · rw [← mul_assoc, pow_mul, EuclideanSpace.norm_sq_fin_two]
    gcongr
    exact radialSymbol_le_twoPow_mul_aggregateDerivativeSymbol2D m _ _

/-- The integer-order Bessel norm, with squared factor `(2π)⁻²`.
-/
noncomputable def integerBesselFourierNorm (k : ℕ) (Fhat : (ℝ^2) → ℂ) : ℝ :=
  √((((2 * Real.pi) ^ 2)⁻¹ : ℝ) *
    ∫ ξ : (ℝ^2), (1 + ‖ξ‖ ^ 2) ^ k * ‖Fhat ξ‖ ^ 2)

/-- The derivative Sobolev norm written under the same Fourier integral.
-/
noncomputable def integerDerivativeFourierNorm (k : ℕ) (Fhat : (ℝ^2) → ℂ) : ℝ :=
  √((((2 * Real.pi) ^ 2)⁻¹ : ℝ) *
    ∫ ξ : (ℝ^2),
      (∑ j ∈ Finset.range (k + 1),
        SobolevSpace.Weighted.aggregateDerivativeSymbol2D j (ξ 0) (ξ 1)) * ‖Fhat ξ‖ ^ 2)

/-- General-order pointwise polynomial comparison behind the integer
Sobolev–Bessel norm equivalence.
-/
theorem integerSobolevSymbol_comparison (k : ℕ) (x y : ℝ) :
    (∑ j ∈ Finset.range (k + 1), SobolevSpace.Weighted.aggregateDerivativeSymbol2D j x y) ≤
        (k + 1 : ℝ) * (1 + (x ^ 2 + y ^ 2)) ^ k ∧
      (1 + (x ^ 2 + y ^ 2)) ^ k ≤
        (3 : ℝ) ^ k *
          ∑ j ∈ Finset.range (k + 1), SobolevSpace.Weighted.aggregateDerivativeSymbol2D j x y := by
  set s : ℝ := x ^ 2 + y ^ 2
  have hs : 0 ≤ s := by positivity
  constructor
  · calc
      (∑ j ∈ Finset.range (k + 1), aggregateDerivativeSymbol2D j x y) ≤
          ∑ _j ∈ Finset.range (k + 1), (1 + s) ^ k :=
        Finset.sum_le_sum fun m hm ↦ (aggregateDerivativeSymbol2D_le_radialSymbol m x y).trans
          ((pow_le_pow_left₀ hs (by linarith) m).trans
            (pow_le_pow_right₀ (by linarith) (Nat.le_of_lt_succ (Finset.mem_range.mp hm))))
      _ = (k + 1 : ℝ) * (1 + s) ^ k := by simp
  · rw [show 1 + s = s + 1 by ring, add_pow, Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm ↦ ?_
    have hagg : 0 ≤ aggregateDerivativeSymbol2D m x y := by
      unfold aggregateDerivativeSymbol2D
      positivity
    have hcoef : (k.choose m : ℝ) * 2 ^ m ≤ 3 ^ k := calc
      (k.choose m : ℝ) * 2 ^ m ≤ ∑ q ∈ Finset.range (k + 1), (k.choose q : ℝ) * 2 ^ q :=
        Finset.single_le_sum (f := fun q ↦ (k.choose q : ℝ) * 2 ^ q) (fun q _ ↦ by positivity) hm
      _ = 3 ^ k := by
        rw [show (3 : ℝ) = 2 + 1 by norm_num, add_pow]
        exact Finset.sum_congr rfl fun q _ ↦ by simp [mul_comm]
    have hradial := radialSymbol_le_twoPow_mul_aggregateDerivativeSymbol2D m x y
    calc s ^ m * 1 ^ (k - m) * (k.choose m : ℝ)
        ≤ (k.choose m : ℝ) * (2 ^ m * aggregateDerivativeSymbol2D m x y) := by
          rw [one_pow, mul_one, mul_comm]
          gcongr
      _ = ((k.choose m : ℝ) * 2 ^ m) * aggregateDerivativeSymbol2D m x y := by ring
      _ ≤ 3 ^ k * aggregateDerivativeSymbol2D m x y := by gcongr

/-- Sobolev–Bessel comparison on the whole plane, including order zero.
-/
theorem sobolevBessel_integerOrder_comparison
    (k : ℕ) (Fhat : (ℝ^2) → ℂ)
    (hFhat : AEStronglyMeasurable Fhat)
    (hBessel : Integrable (fun ξ : (ℝ^2) ↦
      (1 + ‖ξ‖ ^ 2) ^ k * ‖Fhat ξ‖ ^ 2)) :
    (1 / √(k + 1 : ℝ)) * integerDerivativeFourierNorm k Fhat ≤
        integerBesselFourierNorm k Fhat ∧
      integerBesselFourierNorm k Fhat ≤
        √((3 : ℝ) ^ k) * integerDerivativeFourierNorm k Fhat := by
  have hsum_nonneg (ξ : ℝ^2) :
      0 ≤ ∑ j ∈ Finset.range (k + 1), aggregateDerivativeSymbol2D j (ξ 0) (ξ 1) := by
    unfold aggregateDerivativeSymbol2D
    positivity
  have hpoint (ξ : ℝ^2) :=
    (EuclideanSpace.norm_sq_fin_two ξ).symm ▸ integerSobolevSymbol_comparison k (ξ 0) (ξ 1)
  have hcont : Continuous fun ξ : ℝ^2 ↦
      ∑ j ∈ Finset.range (k + 1), aggregateDerivativeSymbol2D j (ξ 0) (ξ 1) := by
    unfold aggregateDerivativeSymbol2D
    fun_prop
  have hDInt : Integrable fun ξ : ℝ^2 ↦
      (∑ j ∈ Finset.range (k + 1), aggregateDerivativeSymbol2D j (ξ 0) (ξ 1)) * ‖Fhat ξ‖ ^ 2 :=
    (hBessel.const_mul (k + 1 : ℝ)).mono' (hcont.aestronglyMeasurable.mul (hFhat.norm.pow _))
      (.of_forall fun ξ ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (hsum_nonneg ξ) (sq_nonneg _)), ← mul_assoc]
        gcongr
        exact (hpoint ξ).1)
  unfold integerDerivativeFourierNorm integerBesselFourierNorm
  refine ⟨?_, sqrt_mul_integral_le (by positivity) (by positivity) hBessel hDInt fun ξ ↦ ?_⟩
  · rw [one_div, inv_mul_le_iff₀ (by positivity)]
    refine sqrt_mul_integral_le (by positivity) (by positivity) hDInt hBessel fun ξ ↦ ?_
    rw [← mul_assoc]
    gcongr
    exact (hpoint ξ).1
  · rw [← mul_assoc]
    gcongr
    exact (hpoint ξ).2

/-- Integrability of the base and top Fourier energies gives every intermediate
integer-order energy. The density is bounded by the sum of the two endpoint densities. -/
theorem integrable_homogeneousFourier_density_of_le
    (Fhat : ℝ^2 → ℂ) {m k : ℕ} (hm : m ≤ k)
    (hFhat : AEStronglyMeasurable Fhat)
    (hTop : Integrable (fun ξ : ℝ^2 ↦ ‖ξ‖ ^ (2 * k) * ‖Fhat ξ‖ ^ 2))
    (hBase : Integrable (fun ξ : ℝ^2 ↦ ‖Fhat ξ‖ ^ 2)) :
    Integrable (fun ξ : ℝ^2 ↦ ‖ξ‖ ^ (2 * m) * ‖Fhat ξ‖ ^ 2) := by
  refine (hBase.add hTop).mono' ((continuous_norm.aestronglyMeasurable.pow _).mul
    (hFhat.norm.pow _)) (.of_forall fun ξ ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  change _ ≤ ‖Fhat ξ‖ ^ 2 + ‖ξ‖ ^ (2 * k) * ‖Fhat ξ‖ ^ 2
  have hpow : ‖ξ‖ ^ (2 * m) ≤ 1 + ‖ξ‖ ^ (2 * k) := by
    rcases le_total ‖ξ‖ 1 with h | h
    · linarith [pow_le_one₀ (n := 2 * m) (norm_nonneg ξ) h, pow_nonneg (norm_nonneg ξ) (2 * k)]
    · linarith [pow_le_pow_right₀ h (Nat.mul_le_mul_left 2 hm)]
  linarith [mul_le_mul_of_nonneg_right hpow (sq_nonneg ‖Fhat ξ‖)]

/-- The nonnegative Fourier energy agrees with its real integral when finite.
The real exponent on the radius matches the homogeneous-density interpolation statements. -/
theorem lintegral_homogeneousFourier_density_eq_ofReal
    (Fhat : ℝ^2 → ℂ) (m : ℕ)
    (hInt : Integrable (fun ξ : ℝ^2 ↦ ‖ξ‖ ^ (2 * m) * ‖Fhat ξ‖ ^ 2)) :
    (∫⁻ ξ : ℝ^2, (ENNReal.ofReal ‖ξ‖) ^ (2 * (m : ℝ)) *
      (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ)) =
        ENNReal.ofReal (∫ ξ : ℝ^2, ‖ξ‖ ^ (2 * m) * ‖Fhat ξ‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun ξ ↦
      mul_nonneg (pow_nonneg (norm_nonneg ξ) _) (sq_nonneg _))]
  apply lintegral_congr
  intro ξ
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg ξ)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg m))]
  rw [show 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← ENNReal.ofReal_pow (norm_nonneg (Fhat ξ))]
  rw [← ENNReal.ofReal_mul (by positivity)]

/-- Whole-plane Hilbert interpolation of the homogeneous Fourier norms.
-/
theorem wholePlane_hilbertInterpolation
    (Fhat : (ℝ^2) → ℂ) (j k : ℕ) (hjk : j < k)
    (hFhat : AEStronglyMeasurable Fhat)
    (hTop : Integrable (fun ξ : (ℝ^2) ↦ ‖ξ‖ ^ (2 * k) * ‖Fhat ξ‖ ^ 2))
    (hBase : Integrable (fun ξ : (ℝ^2) ↦ ‖Fhat ξ‖ ^ 2)) :
    homogeneousFourierNorm j Fhat ≤
      homogeneousFourierNorm k Fhat ^ ((j : ℝ) / k) *
        homogeneousFourierNorm 0 Fhat ^ (1 - (j : ℝ) / k) := by
  let energy : ℕ → ℝ := fun m ↦
    ∫ ξ : (ℝ^2), ‖ξ‖ ^ (2 * m) * ‖Fhat ξ‖ ^ 2
  have henergy_nonneg (m : ℕ) : 0 ≤ energy m :=
    integral_nonneg fun _ ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _)
  have henergy (m : ℕ) (hm : m ≤ k) :
      (∫⁻ ξ : ℝ^2, (ENNReal.ofReal ‖ξ‖) ^ (2 * (m : ℝ)) *
        (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ)) = ENNReal.ofReal (energy m) :=
    lintegral_homogeneousFourier_density_eq_ofReal Fhat m
      (integrable_homogeneousFourier_density_of_le Fhat hm hFhat hTop hBase)
  have hbase : (∫⁻ ξ : ℝ^2, (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ)) =
      ENNReal.ofReal (energy 0) := by
    simpa only [Nat.cast_zero, mul_zero, ENNReal.rpow_zero, one_mul] using
      henergy 0 (Nat.zero_le _)
  have hTopFinite :
      (∫⁻ ξ : ℝ^2, (ENNReal.ofReal ‖ξ‖) ^ (2 * (k : ℝ)) *
        (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ)) ≠ ⊤ := henergy k le_rfl ▸ ENNReal.ofReal_ne_top
  have hBaseFinite : (∫⁻ ξ : ℝ^2, (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ)) ≠ ⊤ :=
    hbase ▸ ENNReal.ofReal_ne_top
  have hraw := SobolevSpace.Weighted.lintegral_homogeneous_density_interpolation_sqrt_toReal
    (μ := volume)
    (fun ξ : (ℝ^2) ↦ ENNReal.ofReal ‖ξ‖)
    (fun ξ : (ℝ^2) ↦ (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ))
    j k hjk
    continuous_norm.measurable.ennreal_ofReal.aemeasurable
    (hFhat.aemeasurable.norm.ennreal_ofReal.pow_const (2 : ℕ))
    hTopFinite hBaseFinite
  rw [henergy j hjk.le, henergy k le_rfl, hbase,
    ENNReal.toReal_ofReal (henergy_nonneg j),
    ENNReal.toReal_ofReal (henergy_nonneg k),
    ENNReal.toReal_ofReal (henergy_nonneg 0)] at hraw
  have hraw' :
      √(energy j) ≤
        √(energy k) ^ ((j : ℝ) / k) *
          √(energy 0) ^ (1 - (j : ℝ) / k) := by
    simpa only [Real.sqrt_eq_rpow, ← Real.rpow_mul (henergy_nonneg _),
      div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using hraw
  let c : ℝ := ((2 * Real.pi) ^ 2)⁻¹
  have hc : 0 < c := by positivity
  have hnorm (m : ℕ) :
      homogeneousFourierNorm m Fhat = √c * √(energy m) := by
    change √(c * energy m) = √c * √(energy m)
    rw [Real.sqrt_mul hc.le]
  rw [hnorm j, hnorm k, hnorm 0,
    Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    mul_mul_mul_comm, ← Real.rpow_add (Real.sqrt_pos.2 hc),
    show (j : ℝ) / k + (1 - (j : ℝ) / k) = 1 by ring, Real.rpow_one]
  exact mul_le_mul_of_nonneg_left hraw' (Real.sqrt_nonneg _)

/-- Additive whole-plane interpolation with the explicit Young interpolation constant.
-/
theorem wholePlane_youngInterpolation
    (Fhat : (ℝ^2) → ℂ) (j k : ℕ) (η : ℝ)
    (hj : 0 < j) (hjk : j < k) (hη : 0 < η)
    (hFhat : AEStronglyMeasurable Fhat)
    (hTop : Integrable (fun ξ : (ℝ^2) ↦ ‖ξ‖ ^ (2 * k) * ‖Fhat ξ‖ ^ 2))
    (hBase : Integrable (fun ξ : (ℝ^2) ↦ ‖Fhat ξ‖ ^ 2)) :
    homogeneousFourierNorm j Fhat ≤ η * homogeneousFourierNorm k Fhat +
      SobolevSpace.Weighted.youngInterpolationConstant (j : ℝ) (k : ℝ) η *
        homogeneousFourierNorm 0 Fhat := by
  have hmul := wholePlane_hilbertInterpolation
    Fhat j k hjk hFhat hTop hBase
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hkR : 0 < (k : ℝ) := by exact_mod_cast lt_trans hj hjk
  have hkjR : 0 < (k : ℝ) - j := sub_pos.mpr (by exact_mod_cast hjk)
  have hθ : 0 < (j : ℝ) / k := div_pos hjR hkR
  have hθ1 : (j : ℝ) / k < 1 := (div_lt_one hkR).2 (by exact_mod_cast hjk)
  have hyoung := weightedGeometricMean_le_young (Real.sqrt_nonneg _ :
    0 ≤ homogeneousFourierNorm k Fhat) (Real.sqrt_nonneg _ : 0 ≤ homogeneousFourierNorm 0 Fhat)
    hθ hθ1 (div_pos hη hθ)
  have hfirst : ((j : ℝ) / k) * (η / ((j : ℝ) / k)) = η := by
    field_simp [hjR.ne', hkR.ne']
  have honeMinus : 1 - (j : ℝ) / k = ((k : ℝ) - j) / k := by
    field_simp [hkR.ne']
  have hexponent :
      ((j : ℝ) / k) / (1 - (j : ℝ) / k) =
        (j : ℝ) / ((k : ℝ) - j) := by
    rw [honeMinus]
    field_simp [hjR.ne', hkR.ne', hkjR.ne']
  have hbase :
      (η / ((j : ℝ) / k))⁻¹ = (j : ℝ) / ((k : ℝ) * η) := by
    field_simp [hjR.ne', hkR.ne', hη.ne']
  have hcoefficient :
      (1 - (j : ℝ) / k) *
          (η / ((j : ℝ) / k)) ^
            (-((j : ℝ) / k) / (1 - (j : ℝ) / k)) =
        SobolevSpace.Weighted.youngInterpolationConstant (j : ℝ) (k : ℝ) η := by
    rw [show -((j : ℝ) / k) / (1 - (j : ℝ) / k) =
        -(((j : ℝ) / k) / (1 - (j : ℝ) / k)) by ring]
    rw [Real.rpow_neg_eq_inv_rpow, hbase, hexponent, honeMinus]
    rfl
  rw [hfirst, hcoefficient] at hyoung
  exact hmul.trans hyoung

/-- Aggregate multiplicative interpolation for physical multiindex derivatives.
-/
theorem wholePlane_aggregateInterpolation
    (Fhat : (ℝ^2) → ℂ) (j k : ℕ) (hjk : j < k)
    (hFhat : AEStronglyMeasurable Fhat)
    (hTop : Integrable (fun ξ : (ℝ^2) ↦ ‖ξ‖ ^ (2 * k) * ‖Fhat ξ‖ ^ 2))
    (hBase : Integrable (fun ξ : (ℝ^2) ↦ ‖Fhat ξ‖ ^ 2)) :
    aggregateFourierNorm j Fhat ≤
      √((2 : ℝ) ^ j) *
        aggregateFourierNorm k Fhat ^ ((j : ℝ) / k) *
        homogeneousFourierNorm 0 Fhat ^ (1 - (j : ℝ) / k) := by
  have hRadialJ := integrable_homogeneousFourier_density_of_le Fhat hjk.le hFhat hTop hBase
  have hcompJ := aggregateFourierNorm_comparison j Fhat hFhat hRadialJ
  have hcompK := aggregateFourierNorm_comparison k Fhat hFhat hTop
  have hhilbert := wholePlane_hilbertInterpolation
    Fhat j k hjk hFhat hTop hBase
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_le j).trans_lt hjk
  have hθ0 : 0 ≤ (j : ℝ) / k := div_nonneg (Nat.cast_nonneg j) hkR.le
  have hpow := Real.rpow_le_rpow (Real.sqrt_nonneg _) hcompK.2 hθ0
  have hbasePow : 0 ≤ homogeneousFourierNorm 0 Fhat ^
      (1 - (j : ℝ) / k) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hAggKNonneg : 0 ≤ aggregateFourierNorm k Fhat := Real.sqrt_nonneg _
  have hfactor :
      (√((2 : ℝ) ^ k)) ^ ((j : ℝ) / k) =
        √((2 : ℝ) ^ j) := by
    calc
      (√((2 : ℝ) ^ k)) ^ ((j : ℝ) / k) =
          ((2 : ℝ) ^ k) ^ ((1 / 2 : ℝ) * ((j : ℝ) / k)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      _ = (2 : ℝ) ^ ((k : ℝ) * ((1 / 2 : ℝ) * ((j : ℝ) / k))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      _ = (2 : ℝ) ^ ((j : ℝ) * (1 / 2 : ℝ)) := by
        congr 1
        field_simp [hkR.ne']
      _ = ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)), Real.rpow_natCast]
      _ = √((2 : ℝ) ^ j) := by rw [Real.sqrt_eq_rpow]
  calc
    aggregateFourierNorm j Fhat ≤ homogeneousFourierNorm j Fhat := hcompJ.1
    _ ≤ homogeneousFourierNorm k Fhat ^ ((j : ℝ) / k) *
        homogeneousFourierNorm 0 Fhat ^ (1 - (j : ℝ) / k) := hhilbert
    _ ≤ (√((2 : ℝ) ^ k) * aggregateFourierNorm k Fhat) ^
          ((j : ℝ) / k) *
        homogeneousFourierNorm 0 Fhat ^ (1 - (j : ℝ) / k) :=
      mul_le_mul_of_nonneg_right hpow hbasePow
    _ = √((2 : ℝ) ^ j) *
        aggregateFourierNorm k Fhat ^ ((j : ℝ) / k) *
        homogeneousFourierNorm 0 Fhat ^ (1 - (j : ℝ) / k) := by
      rw [Real.mul_rpow (x := √((2 : ℝ) ^ k))
        (y := aggregateFourierNorm k Fhat) (Real.sqrt_nonneg _) hAggKNonneg,
        hfactor]

/-- Aggregate additive interpolation with the conversion factor `√(2^j)`.
-/
theorem wholePlane_aggregateYoungInterpolation
    (Fhat : (ℝ^2) → ℂ) (j k : ℕ) (η : ℝ)
    (hj : 0 < j) (hjk : j < k) (hη : 0 < η)
    (hFhat : AEStronglyMeasurable Fhat)
    (hTop : Integrable (fun ξ : (ℝ^2) ↦ ‖ξ‖ ^ (2 * k) * ‖Fhat ξ‖ ^ 2))
    (hBase : Integrable (fun ξ : (ℝ^2) ↦ ‖Fhat ξ‖ ^ 2)) :
    aggregateFourierNorm j Fhat ≤ η * aggregateFourierNorm k Fhat +
      SobolevSpace.Weighted.aggregateYoungInterpolationConstant (j : ℝ) (k : ℝ) η *
        homogeneousFourierNorm 0 Fhat := by
  let θ : ℝ := (j : ℝ) / k
  let D : ℝ := √((2 : ℝ) ^ j)
  let p : ℝ := θ / (1 - θ)
  let χ : ℝ := η / (D * θ)
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hkR : 0 < (k : ℝ) := by exact_mod_cast lt_trans hj hjk
  have hkjR : 0 < (k : ℝ) - j := sub_pos.mpr (by exact_mod_cast hjk)
  have hθ : 0 < θ := by exact div_pos hjR hkR
  have hθ1 : θ < 1 := by
    dsimp [θ]
    rw [div_lt_one hkR]
    exact_mod_cast hjk
  have hD : 0 < D := by dsimp [D]; positivity
  have hχ : 0 < χ := by dsimp [χ]; positivity
  have hA : 0 ≤ aggregateFourierNorm k Fhat := Real.sqrt_nonneg _
  have hB : 0 ≤ homogeneousFourierNorm 0 Fhat := Real.sqrt_nonneg _
  have hmul := wholePlane_aggregateInterpolation
    Fhat j k hjk hFhat hTop hBase
  have hyoung := SobolevSpace.Weighted.weightedGeometricMean_le_young hA hB hθ hθ1 hχ
  have hscaled := mul_le_mul_of_nonneg_left hyoung hD.le
  have htopCoefficient : D * (θ * χ) = η := by
    dsimp [χ]
    field_simp [hD.ne', hθ.ne']
  have honeMinus : 1 - θ = ((k : ℝ) - j) / k := by
    dsimp [θ]
    field_simp [hkR.ne']
  have hp : p = (j : ℝ) / ((k : ℝ) - j) := by
    dsimp only [p, θ]
    cas
  let num : ℝ := η / θ
  have hnum : 0 < num := div_pos hη hθ
  have hchiRewrite : χ = num / D := by
    dsimp [χ, num]
    field_simp [hD.ne', hθ.ne']
  have hDExponent : 1 + p = 1 / (1 - θ) := by
    dsimp only [p]
    cas
  have hDpow :
      D ^ (1 / (1 - θ)) =
        Real.rpow 2 ((j : ℝ) * k / (2 * ((k : ℝ) - j))) := by
    dsimp [D, θ]
    calc
      √((2 : ℝ) ^ j) ^
          (1 / (1 - (j : ℝ) / k)) =
          ((2 : ℝ) ^ j) ^
            ((1 / 2 : ℝ) * (1 / (1 - (j : ℝ) / k))) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      _ = (2 : ℝ) ^ ((j : ℝ) *
          ((1 / 2 : ℝ) * (1 / (1 - (j : ℝ) / k)))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      _ = Real.rpow 2 ((j : ℝ) * k / (2 * ((k : ℝ) - j))) := by
        congr 1
        field_simp [hkR.ne', hkjR.ne']
  have hDcombine :
      D * D ^ p = Real.rpow 2 ((j : ℝ) * k / (2 * ((k : ℝ) - j))) := by
    calc
      D * D ^ p = D ^ (1 : ℝ) * D ^ p := by rw [Real.rpow_one]
      _ = D ^ (1 + p) := (Real.rpow_add hD 1 p).symm
      _ = D ^ (1 / (1 - θ)) := by rw [hDExponent]
      _ = Real.rpow 2 ((j : ℝ) * k / (2 * ((k : ℝ) - j))) := hDpow
  have hscalePower :
      D * χ ^ (-p) =
        Real.rpow 2 ((j : ℝ) * k / (2 * ((k : ℝ) - j))) *
          num ^ (-p) := by
    rw [hchiRewrite, Real.div_rpow hnum.le hD.le]
    rw [Real.rpow_neg hD.le]
    have hDp : 0 < D ^ p := Real.rpow_pos_of_pos hD _
    field_simp [hDp.ne']
    linarith [hDcombine]
  have hbase : num⁻¹ = (j : ℝ) / ((k : ℝ) * η) := by
    dsimp [num, θ]
    field_simp [hjR.ne', hkR.ne', hη.ne']
  have hordinaryCoefficient :
      (1 - θ) * num ^ (-p) =
        SobolevSpace.Weighted.youngInterpolationConstant (j : ℝ) (k : ℝ) η := by
    rw [show -p = -(p) by rfl, Real.rpow_neg_eq_inv_rpow, hbase, hp, honeMinus]
    rfl
  have haggregateCoefficient :
      D * ((1 - θ) * χ ^ (-p)) =
        SobolevSpace.Weighted.aggregateYoungInterpolationConstant (j : ℝ) (k : ℝ) η := by
    calc
      D * ((1 - θ) * χ ^ (-p)) = (1 - θ) * (D * χ ^ (-p)) := by ring
      _ = Real.rpow 2 ((j : ℝ) * k / (2 * ((k : ℝ) - j))) *
          ((1 - θ) * num ^ (-p)) := by rw [hscalePower]; ring
      _ = SobolevSpace.Weighted.aggregateYoungInterpolationConstant (j : ℝ) (k : ℝ) η := by
        rw [hordinaryCoefficient]
        rfl
  calc
    aggregateFourierNorm j Fhat ≤
        D * (aggregateFourierNorm k Fhat ^ θ *
          homogeneousFourierNorm 0 Fhat ^ (1 - θ)) := by
      simpa [D, θ, mul_assoc] using hmul
    _ ≤ D * (θ * χ * aggregateFourierNorm k Fhat +
        (1 - θ) * χ ^ (-θ / (1 - θ)) *
          homogeneousFourierNorm 0 Fhat) := by
      simpa [p, mul_assoc] using hscaled
    _ = η * aggregateFourierNorm k Fhat +
        SobolevSpace.Weighted.aggregateYoungInterpolationConstant (j : ℝ) (k : ℝ) η *
          homogeneousFourierNorm 0 Fhat := by
      calc
        D * (θ * χ * aggregateFourierNorm k Fhat +
            (1 - θ) * χ ^ (-θ / (1 - θ)) *
              homogeneousFourierNorm 0 Fhat) =
            (D * (θ * χ)) * aggregateFourierNorm k Fhat +
              (D * ((1 - θ) * χ ^ (-p))) *
                homogeneousFourierNorm 0 Fhat := by
          dsimp [p]
          ring_nf
        _ = η * aggregateFourierNorm k Fhat +
            SobolevSpace.Weighted.aggregateYoungInterpolationConstant (j : ℝ) (k : ℝ) η *
              homogeneousFourierNorm 0 Fhat := by
          rw [htopCoefficient, haggregateCoefficient]

/-- Physical whole-plane `L²` norm.
-/
noncomputable def wholePlaneL2Norm (f : (ℝ^2 → ℝ)) : ℝ :=
  √(∫ x : (ℝ^2), f x ^ 2)

/-- Physical aggregate norm of all order-`m` Cartesian derivatives.
-/
noncomputable def wholePlaneAggregateDerivativeNorm (m : ℕ) (f : (ℝ^2 → ℝ)) : ℝ :=
  √(∑ a : Fin (m + 1),
    ∫ x : (ℝ^2),
      (mixedDerivative2D m a
        (fun r z ↦ f (EuclideanSpace.single (0 : Fin 2) r +
          EuclideanSpace.single (1 : Fin 2) z)) (x 0) (x 1)) ^ 2)

/-- Physical-space Hilbert, Young, and aggregate interpolation for a profile
`F`, conditional on Plancherel identities supplied as hypotheses.  `Dhom` is
an arbitrary family of maps `(ℝ^2 → ℝ) → (ℝ^2 → ℝ)`, and no Fourier transform of
`F` is computed here: `hPlancherel` and `hAggregatePlancherel` assert that
the physical norms of `Dhom m F` and of the order-`m` derivative aggregate
coincide with the Fourier-side norms of `Fhat`, and the theorem substitutes
these identities into the four Fourier-side inequalities above.  Identifying
`Dhom m` with `|D|^m` for the Fourier convention above is not part of
this statement.
-/
theorem wholePlane_interpolation_of_plancherel
    (F : (ℝ^2 → ℝ)) (Fhat : (ℝ^2) → ℂ) (Dhom : ℕ → (ℝ^2 → ℝ) → (ℝ^2 → ℝ))
    (j k : ℕ) (η : ℝ) (hj : 0 < j) (hjk : j < k) (hη : 0 < η)
    (hFhat : AEStronglyMeasurable Fhat)
    (hTop : Integrable (fun ξ : (ℝ^2) ↦ ‖ξ‖ ^ (2 * k) * ‖Fhat ξ‖ ^ 2))
    (hBase : Integrable (fun ξ : (ℝ^2) ↦ ‖Fhat ξ‖ ^ 2))
    (hDzero : Dhom 0 F = F)
    (hPlancherel : ∀ m ∈ ({0, j, k} : Set ℕ),
      wholePlaneL2Norm (Dhom m F) = homogeneousFourierNorm m Fhat)
    (hAggregatePlancherel : ∀ m ∈ ({j, k} : Set ℕ),
      wholePlaneAggregateDerivativeNorm m F = aggregateFourierNorm m Fhat) :
    wholePlaneL2Norm (Dhom j F) ≤
        wholePlaneL2Norm (Dhom k F) ^ ((j : ℝ) / k) *
          wholePlaneL2Norm F ^ (1 - (j : ℝ) / k) ∧
      wholePlaneL2Norm (Dhom j F) ≤
        η * wholePlaneL2Norm (Dhom k F) +
          SobolevSpace.Weighted.youngInterpolationConstant (j : ℝ) (k : ℝ) η * wholePlaneL2Norm F ∧
      wholePlaneAggregateDerivativeNorm j F ≤
        √((2 : ℝ) ^ j) *
          wholePlaneAggregateDerivativeNorm k F ^ ((j : ℝ) / k) *
          wholePlaneL2Norm F ^ (1 - (j : ℝ) / k) ∧
      wholePlaneAggregateDerivativeNorm j F ≤
        η * wholePlaneAggregateDerivativeNorm k F +
          SobolevSpace.Weighted.aggregateYoungInterpolationConstant (j : ℝ) (k : ℝ) η *
            wholePlaneL2Norm F := by
  have h0 := hPlancherel 0 (by simp)
  rw [hDzero] at h0
  rw [hPlancherel j (by simp), hPlancherel k (by simp), h0, hAggregatePlancherel j (by simp),
    hAggregatePlancherel k (by simp)]
  exact ⟨wholePlane_hilbertInterpolation Fhat j k hjk hFhat hTop hBase,
    wholePlane_youngInterpolation Fhat j k η hj hjk hη hFhat hTop hBase,
    wholePlane_aggregateInterpolation Fhat j k hjk hFhat hTop hBase,
    wholePlane_aggregateYoungInterpolation Fhat j k η hj hjk hη hFhat hTop hBase⟩


end SobolevSpace
