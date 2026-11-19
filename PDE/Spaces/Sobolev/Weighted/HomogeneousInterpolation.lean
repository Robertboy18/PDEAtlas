/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.Interpolation
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
import CAS.ExactTactic

/-!
# Homogeneous weighted interpolation

Homogeneous density interpolation, planar derivative symbols, and explicit Young constants.
The measure-theoretic statements retain all endpoint finiteness hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace SobolevSpace.Weighted

/-- The coefficient of the base norm after choosing the top-order coefficient
`η` in homogeneous interpolation between orders zero and `k`. -/
def youngInterpolationConstant (j k η : ℝ) : ℝ :=
  ((k - j) / k) * (j / (k * η)) ^ (j / (k - j))

/--
Additive interpolation constant for the unweighted aggregate of all
two-dimensional order-`j` multiindex derivatives.  The extra power of two is
the explicit conversion from the homogeneous `|D|^m` norm to that aggregate,
raised to the exponent `1/(1-θ)` with `θ = j/k` that the Young step produces.
It is positive for `0 < j < k` and `0 < η` (`aggregateYoungInterpolationConstant_pos`), and
`aggregateYoungInterpolationConstant_eq` gives its explicit product formula. The aggregate
Fourier-norm inequality is `SobolevSpace.wholePlane_aggregateYoungInterpolation`
in `PDE.Spaces.Sobolev.Inequalities.PlanarInterpolation`.
-/
def aggregateYoungInterpolationConstant (j k η : ℝ) : ℝ :=
  (2 : ℝ) ^ (j * k / (2 * (k - j))) * youngInterpolationConstant j k η

/-- The two-dimensional aggregate symbol
`sum_{q=0}^m xi_r^(2q) xi_z^(2(m-q))`, with one term per mixed derivative. -/
def aggregateDerivativeSymbol2D (m : ℕ) (x y : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (m + 1), (x ^ 2) ^ q * (y ^ 2) ^ (m - q)

/-- The aggregate symbol is bounded above by the homogeneous radial symbol. -/
theorem aggregateDerivativeSymbol2D_le_radialSymbol
    (m : ℕ) (x y : ℝ) :
    aggregateDerivativeSymbol2D m x y ≤ (x ^ 2 + y ^ 2) ^ m := by
  rw [add_pow]
  apply Finset.sum_le_sum
  intro q hq
  have hqm : q ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
  have hterm : 0 ≤ (x ^ 2) ^ q * (y ^ 2) ^ (m - q) := by positivity
  have hchooseNat : 1 ≤ m.choose q := Nat.choose_pos hqm
  have hchoose : (1 : ℝ) ≤ (m.choose q : ℝ) := by exact_mod_cast hchooseNat
  nlinarith

/-- The radial symbol is bounded by `2^m` times the unweighted aggregate,
since each binomial coefficient of order `m` is at most `2^m`. -/
theorem radialSymbol_le_twoPow_mul_aggregateDerivativeSymbol2D
    (m : ℕ) (x y : ℝ) :
    (x ^ 2 + y ^ 2) ^ m ≤
      (2 : ℝ) ^ m * aggregateDerivativeSymbol2D m x y := by
  rw [add_pow]
  calc
    (∑ q ∈ Finset.range (m + 1),
        (x ^ 2) ^ q * (y ^ 2) ^ (m - q) * (m.choose q : ℝ)) ≤
        ∑ q ∈ Finset.range (m + 1),
          (2 : ℝ) ^ m * ((x ^ 2) ^ q * (y ^ 2) ^ (m - q)) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hterm : 0 ≤ (x ^ 2) ^ q * (y ^ 2) ^ (m - q) := by positivity
      have hchoose : (m.choose q : ℝ) ≤ (2 : ℝ) ^ m := by
        exact_mod_cast Nat.choose_le_two_pow m q
      nlinarith
    _ = (2 : ℝ) ^ m * aggregateDerivativeSymbol2D m x y := by
      unfold aggregateDerivativeSymbol2D
      rw [Finset.mul_sum]

/--
The exact homogeneous-density interpolation used in the Fourier proof.  Here
`radius` stands for `|xi|` and `density` for `|Fhat(xi)|^2`.  The statement is
an `ℝ≥0∞` inequality, so it needs no finiteness hypothesis.
-/
theorem lintegral_homogeneous_density_interpolation
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (radius density : α → ℝ≥0∞) (j k : ℕ) (hjk : j < k)
    (hradius : AEMeasurable radius μ) (hdensity : AEMeasurable density μ) :
    (∫⁻ x, radius x ^ (2 * (j : ℝ)) * density x ∂μ) ≤
      (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ) ^ ((j : ℝ) / k) *
        (∫⁻ x, density x ∂μ) ^ (1 - (j : ℝ) / k) := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_le j).trans_lt hjk
  have hθ0 : 0 ≤ (j : ℝ) / k := div_nonneg (Nat.cast_nonneg j) hk.le
  have hθ1 : (j : ℝ) / k ≤ 1 := by
    rw [div_le_one hk]
    exact_mod_cast hjk.le
  have htop : AEMeasurable
      (fun x ↦ radius x ^ (2 * (k : ℝ)) * density x) μ :=
    (hradius.pow_const _).mul hdensity
  have hholder :
      (∫⁻ x,
          (radius x ^ (2 * (k : ℝ)) * density x) ^ ((j : ℝ) / k) *
            density x ^ (1 - (j : ℝ) / k) ∂μ) ≤
        (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ) ^ ((j : ℝ) / k) *
          (∫⁻ x, density x ∂μ) ^ (1 - (j : ℝ) / k) := by
    have h := SobolevSpace.Weighted.lintegral_le_geometric_interpolation
      (μ := μ)
      (F₀ := density)
      (F₁ := fun x ↦ radius x ^ (2 * (k : ℝ)) * density x)
      (Fθ := fun x ↦
        (radius x ^ (2 * (k : ℝ)) * density x) ^ ((j : ℝ) / k) *
          density x ^ (1 - (j : ℝ) / k))
      hdensity htop hθ0 hθ1
      (Filter.Eventually.of_forall fun x ↦ by
        simpa only [mul_comm] using
          (le_refl
            (density x ^ (1 - (j : ℝ) / k) *
              (density x * radius x ^ ((k : ℝ) * 2)) ^ ((j : ℝ) / k))))
    simpa only [mul_comm] using h
  calc
    (∫⁻ x, radius x ^ (2 * (j : ℝ)) * density x ∂μ) =
        ∫⁻ x,
          (radius x ^ (2 * (k : ℝ)) * density x) ^ ((j : ℝ) / k) *
            density x ^ (1 - (j : ℝ) / k) ∂μ := by
      apply lintegral_congr
      intro x
      rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0, ← ENNReal.rpow_mul]
      rw [mul_assoc]
      rw [← ENNReal.rpow_add_of_nonneg ((j : ℝ) / k) (1 - (j : ℝ) / k)
        hθ0 (sub_nonneg.mpr hθ1)]
      have hexponent : (2 * (k : ℝ)) * ((j : ℝ) / k) = 2 * (j : ℝ) := by
        field_simp
      rw [hexponent]
      norm_num
    _ ≤ (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ) ^ ((j : ℝ) / k) *
        (∫⁻ x, density x ∂μ) ^ (1 - (j : ℝ) / k) := hholder

/-- Square-root form of homogeneous interpolation, i.e. the Fourier-energy
version of `|||D|^j F||₂ ≤ |||D|^k F||₂^(j/k) ||F||₂^(1-j/k)`. -/
theorem lintegral_homogeneous_density_interpolation_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (radius density : α → ℝ≥0∞) (j k : ℕ) (hjk : j < k)
    (hradius : AEMeasurable radius μ) (hdensity : AEMeasurable density μ) :
    (∫⁻ x, radius x ^ (2 * (j : ℝ)) * density x ∂μ) ^ (1 / 2 : ℝ) ≤
      (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ) ^
          (((j : ℝ) / k) / 2) *
        (∫⁻ x, density x ∂μ) ^ ((1 - (j : ℝ) / k) / 2) := by
  have h := lintegral_homogeneous_density_interpolation
    radius density j k hjk hradius hdensity
  have hsqrt := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hsqrt
  simpa only [← ENNReal.rpow_mul, div_eq_mul_inv, one_mul] using hsqrt

/-- Density interpolation on `ℝ²` for the squared norm of a measurable complex
function. No Fourier-transform identification or Plancherel theorem is needed. -/
theorem lintegral_fourier_homogeneous_interpolation_sqrt
    (Fhat : (ℝ^2) → ℂ) (hFhat : AEStronglyMeasurable Fhat)
    (j k : ℕ) (hjk : j < k) :
    (∫⁻ ξ : (ℝ^2),
        (ENNReal.ofReal ‖ξ‖) ^ (2 * (j : ℝ)) *
          (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
      (∫⁻ ξ : (ℝ^2),
        (ENNReal.ofReal ‖ξ‖) ^ (2 * (k : ℝ)) *
          (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ)) ^ (((j : ℝ) / k) / 2) *
        (∫⁻ ξ : (ℝ^2), (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ)) ^
          ((1 - (j : ℝ) / k) / 2) := by
  apply lintegral_homogeneous_density_interpolation_sqrt
    (fun ξ : (ℝ^2) ↦ ENNReal.ofReal ‖ξ‖)
    (fun ξ : (ℝ^2) ↦ (ENNReal.ofReal ‖Fhat ξ‖) ^ (2 : ℕ))
    j k hjk
  · exact continuous_norm.measurable.ennreal_ofReal.aemeasurable
  · exact hFhat.aemeasurable.norm.ennreal_ofReal.pow_const (2 : ℕ)

/-- Convert an extended nonnegative interpolation bound to an ordinary real
bound once the two endpoint quantities are known to be finite. -/
theorem ennreal_interpolation_toReal
    {A B C : ℝ≥0∞} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (h : C ≤ A ^ a * B ^ b) :
    C.toReal ≤ A.toReal ^ a * B.toReal ^ b := by
  have hR : A ^ a * B ^ b ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ha hA)
      (ENNReal.rpow_ne_top_of_nonneg hb hB)
  have hC : C ≠ ⊤ := ne_top_of_le_ne_top hR h
  have hreal := (ENNReal.toReal_le_toReal hC hR).2 h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at hreal
  exact hreal

/-- Finite real-energy form of the homogeneous interpolation theorem. -/
theorem lintegral_homogeneous_density_interpolation_sqrt_toReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (radius density : α → ℝ≥0∞) (j k : ℕ) (hjk : j < k)
    (hradius : AEMeasurable radius μ) (hdensity : AEMeasurable density μ)
    (hTop : (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ) ≠ ⊤)
    (hBase : (∫⁻ x, density x ∂μ) ≠ ⊤) :
    (ENNReal.toReal (∫⁻ x, radius x ^ (2 * (j : ℝ)) * density x ∂μ)) ^
        (1 / 2 : ℝ) ≤
      (ENNReal.toReal (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ)) ^
          (((j : ℝ) / k) / 2) *
        (ENNReal.toReal (∫⁻ x, density x ∂μ)) ^
          ((1 - (j : ℝ) / k) / 2) := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_le j).trans_lt hjk
  have hθ0 : 0 ≤ (j : ℝ) / k := div_nonneg (Nat.cast_nonneg j) hk.le
  have hθ1 : (j : ℝ) / k ≤ 1 := by
    rw [div_le_one hk]
    exact_mod_cast hjk.le
  have h := lintegral_homogeneous_density_interpolation_sqrt
    radius density j k hjk hradius hdensity
  have hreal := ennreal_interpolation_toReal
    (div_nonneg hθ0 (by norm_num : (0 : ℝ) ≤ 2))
    (div_nonneg (sub_nonneg.mpr hθ1) (by norm_num : (0 : ℝ) ≤ 2))
    hTop hBase h
  rw [← ENNReal.toReal_rpow] at hreal
  exact hreal

/-- The Young-interpolation constant is positive for `0 < j < k` and `0 < η`. -/
theorem youngInterpolationConstant_pos
    {j k η : ℝ} (hη : 0 < η) (hj : 0 < j) (hjk : j < k) :
    0 < youngInterpolationConstant j k η := by
  have hk : 0 < k := lt_trans hj hjk
  have hkj : 0 < k - j := sub_pos.mpr hjk
  have hbase : 0 < j / (k * η) := div_pos hj (mul_pos hk hη)
  exact mul_pos (div_pos hkj hk) (Real.rpow_pos_of_pos hbase _)

/-- The aggregate interpolation constant is positive for `0 < j < k` and `0 < η`. -/
theorem aggregateYoungInterpolationConstant_pos
    {j k η : ℝ} (hη : 0 < η) (hj : 0 < j) (hjk : j < k) :
    0 < aggregateYoungInterpolationConstant j k η := by
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (youngInterpolationConstant_pos hη hj hjk)

/-- Explicit product formula for the aggregate interpolation constant. -/
theorem aggregateYoungInterpolationConstant_eq
    (j k η : ℝ) :
    aggregateYoungInterpolationConstant j k η =
      (2 : ℝ) ^ (j * k / (2 * (k - j))) *
        ((k - j) / k) * (j / (k * η)) ^ (j / (k - j)) := by
  simp [aggregateYoungInterpolationConstant, youngInterpolationConstant, mul_assoc]

/--
Parameterized weighted Young inequality used to turn multiplicative Hilbert
interpolation into an additive estimate.
-/
theorem weightedGeometricMean_le_young
    {a b θ χ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hχ : 0 < χ) :
    a ^ θ * b ^ (1 - θ) ≤
      θ * χ * a +
        (1 - θ) * χ ^ (-θ / (1 - θ)) * b := by
  have hOneMinus : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1.le
  have hχpow : 0 ≤ χ ^ (-θ / (1 - θ)) :=
    Real.rpow_nonneg hχ.le _
  have hAM := Real.geom_mean_le_arith_mean2_weighted
    hθ0.le hOneMinus (mul_nonneg hχ.le ha) (mul_nonneg hχpow hb)
    (by ring : θ + (1 - θ) = 1)
  have hden : 1 - θ ≠ 0 := (sub_pos.mpr hθ1).ne'
  have hexponent : (-θ / (1 - θ)) * (1 - θ) = -θ := by
    field_simp [hden]
  have hcancel : χ ^ θ * χ ^ (-θ) = 1 := by
    calc
      χ ^ θ * χ ^ (-θ) = χ ^ (θ + -θ) :=
        (Real.rpow_add hχ θ (-θ)).symm
      _ = 1 := by simp
  have hleft :
      (χ * a) ^ θ *
          (χ ^ (-θ / (1 - θ)) * b) ^ (1 - θ) =
        a ^ θ * b ^ (1 - θ) := by
    rw [Real.mul_rpow hχ.le ha, Real.mul_rpow hχpow hb,
      ← Real.rpow_mul hχ.le, hexponent]
    calc
      (χ ^ θ * a ^ θ) * (χ ^ (-θ) * b ^ (1 - θ)) =
          (χ ^ θ * χ ^ (-θ)) * (a ^ θ * b ^ (1 - θ)) := by ring
      _ = a ^ θ * b ^ (1 - θ) := by rw [hcancel, one_mul]
  rw [hleft] at hAM
  simpa [mul_assoc] using hAM

/-- Additive finite-energy interpolation after weighted Young, with the local
Young parameter left explicit. -/
theorem lintegral_homogeneous_density_interpolation_young_toReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (radius density : α → ℝ≥0∞) (j k : ℕ) (χ : ℝ)
    (hj : 0 < j) (hjk : j < k) (hχ : 0 < χ)
    (hradius : AEMeasurable radius μ) (hdensity : AEMeasurable density μ)
    (hTop : (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ) ≠ ⊤)
    (hBase : (∫⁻ x, density x ∂μ) ≠ ⊤) :
    (ENNReal.toReal (∫⁻ x, radius x ^ (2 * (j : ℝ)) * density x ∂μ)) ^
        (1 / 2 : ℝ) ≤
      ((j : ℝ) / k) * χ *
          (ENNReal.toReal (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ)) ^
            (1 / 2 : ℝ) +
        (1 - (j : ℝ) / k) * χ ^
            (-((j : ℝ) / k) / (1 - (j : ℝ) / k)) *
          (ENNReal.toReal (∫⁻ x, density x ∂μ)) ^ (1 / 2 : ℝ) := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast lt_trans hj hjk
  have hθ0 : 0 < (j : ℝ) / k := div_pos (by exact_mod_cast hj) hk
  have hθ1 : (j : ℝ) / k < 1 := by
    rw [div_lt_one hk]
    exact_mod_cast hjk
  have hmul := lintegral_homogeneous_density_interpolation_sqrt_toReal
    radius density j k hjk hradius hdensity hTop hBase
  have hmul' :
      (ENNReal.toReal (∫⁻ x, radius x ^ (2 * (j : ℝ)) * density x ∂μ)) ^
          (1 / 2 : ℝ) ≤
        ((ENNReal.toReal (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ)) ^
            (1 / 2 : ℝ)) ^ ((j : ℝ) / k) *
          ((ENNReal.toReal (∫⁻ x, density x ∂μ)) ^ (1 / 2 : ℝ)) ^
            (1 - (j : ℝ) / k) := by
    simpa only [← Real.rpow_mul (ENNReal.toReal_nonneg), div_eq_mul_inv,
      one_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
  exact hmul'.trans (weightedGeometricMean_le_young
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _) hθ0 hθ1 hχ)

/-- Let `0 < j < k` and `0 < η`, let `radius` and `density` be a.e. measurable, and let
`∫⁻ radius ^ (2k) * density` and `∫⁻ density` be finite. With
`I m = (∫⁻ radius ^ (2m) * density).toReal`, we have
`I j ^ (1/2) ≤ η * I k ^ (1/2) + youngInterpolationConstant j k η * (∫⁻ density).toReal ^ (1/2)`.
The proof applies `lintegral_homogeneous_density_interpolation_young_toReal` with the Young
parameter `η / (j / k)`, which makes the top-order coefficient exactly `η`. -/
theorem lintegral_homogeneous_density_interpolation_eta_toReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (radius density : α → ℝ≥0∞) (j k : ℕ) (η : ℝ)
    (hj : 0 < j) (hjk : j < k) (hη : 0 < η)
    (hradius : AEMeasurable radius μ) (hdensity : AEMeasurable density μ)
    (hTop : (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ) ≠ ⊤)
    (hBase : (∫⁻ x, density x ∂μ) ≠ ⊤) :
    (ENNReal.toReal (∫⁻ x, radius x ^ (2 * (j : ℝ)) * density x ∂μ)) ^
        (1 / 2 : ℝ) ≤
      η *
          (ENNReal.toReal (∫⁻ x, radius x ^ (2 * (k : ℝ)) * density x ∂μ)) ^
            (1 / 2 : ℝ) +
        youngInterpolationConstant (j : ℝ) (k : ℝ) η *
          (ENNReal.toReal (∫⁻ x, density x ∂μ)) ^ (1 / 2 : ℝ) := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hkR : 0 < (k : ℝ) := by exact_mod_cast lt_trans hj hjk
  have hkjR : 0 < (k : ℝ) - j := sub_pos.mpr (by exact_mod_cast hjk)
  have htheta : 0 < (j : ℝ) / k := div_pos hjR hkR
  have hchi : 0 < η / ((j : ℝ) / k) := div_pos hη htheta
  have hraw := lintegral_homogeneous_density_interpolation_young_toReal
    radius density j k (η / ((j : ℝ) / k)) hj hjk hchi
    hradius hdensity hTop hBase
  have hfirst :
      ((j : ℝ) / k) * (η / ((j : ℝ) / k)) = η := by
    cas
  have honeMinus :
      1 - (j : ℝ) / k = ((k : ℝ) - j) / k := by
    cas
  have hexponent :
      ((j : ℝ) / k) / (1 - (j : ℝ) / k) =
        (j : ℝ) / ((k : ℝ) - j) := by
    cas
  have hbase :
      (η / ((j : ℝ) / k))⁻¹ = (j : ℝ) / ((k : ℝ) * η) := by
    cas
  have hcoefficient :
      (1 - (j : ℝ) / k) *
          (η / ((j : ℝ) / k)) ^
            (-((j : ℝ) / k) / (1 - (j : ℝ) / k)) =
        youngInterpolationConstant (j : ℝ) (k : ℝ) η := by
    rw [show -((j : ℝ) / k) / (1 - (j : ℝ) / k) =
        -(((j : ℝ) / k) / (1 - (j : ℝ) / k)) by ring]
    rw [Real.rpow_neg_eq_inv_rpow, hbase, hexponent, honeMinus]
    rfl
  rw [hfirst, hcoefficient] at hraw
  exact hraw

end SobolevSpace.Weighted
