/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.VectorHarmonics
public import PDE.FDeriv.Euclidean.RadialPolynomial
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Zonal solid harmonics

Write `P_l = ∑ᵢ cᵢ Xⁱ` for the Legendre polynomial of degree `l` and `S = X₀² + X₁² + X₂²`. The
zonal solid harmonic of degree `l` is the polynomial `H_l = ∑ᵢ cᵢ X₂ⁱ S^((l - i) / 2)` in three
variables. A coefficient `cᵢ` vanishes unless `l - i` is even, because `P_l` has the parity of
`l`, so `H_l` is homogeneous of degree `l` and takes the value `r^l P_l (cos θ)` at the spherical
point of radius `r` and polar angle `θ`.

The Laplacian of `X₂ⁱ Sᵐ` is `i (i - 1) X₂ⁱ⁻² Sᵐ + 2 m (2 i + 2 m + 1) X₂ⁱ Sᵐ⁻¹`, and the Legendre
equation gives the recursion `(i + 2) (i + 1) c_{i+2} + (l - i) (l + i + 1) cᵢ = 0`. The two
contributions to `Δ H_l` cancel term by term, so `H_l` is harmonic.

The partial derivatives are `∂ₖ H_l = [k = 2] A + Xₖ B`, where `A` and `B` are again sums of
terms `X₂ⁱ Sᵐ`. At the spherical point `(r, θ, φ)` this gives the gradient
`l r^(l - 1) S_l (θ) e_r + r^(l - 1) S_l' (θ) e_θ` for every real `r`. Since `A` and `B` depend
only on `X₂` and `S`, the gradient commutes with the rotations about the third axis, and under
the equatorial reflection `σ` it satisfies `∇H_l (σ x) = (-1)ˡ σ (∇H_l (x))`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open CAS.Analysis.SpecialFunctions
open MvPolynomial PDE.CoordinateSystems PDE.CoordinateSystems.Spherical

/-! ### Polynomials in three variables -/

/-- The polynomial `X₀² + X₁² + X₂²`, the squared Euclidean norm. -/
def normSqPolynomial : MvPolynomial (Fin 3) ℝ := X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2

/-- The zonal solid harmonic `r^l P_l(x₂ / r)` as a polynomial: the terms with `l - i` odd
vanish because `P_l` has the parity of `l`. -/
def zonalSolidHarmonicPolynomial (l : ℕ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i ∈ Finset.range (l + 1),
    C ((legendre l).coeff i) * X 2 ^ i * normSqPolynomial ^ ((l - i) / 2)

/-- The gradient of a polynomial evaluated at a point of `ℝ^3`. -/
def polynomialGradient (P : MvPolynomial (Fin 3) ℝ) (x : ℝ^3) : ℝ^3 :=
  WithLp.toLp 2 fun i ↦ eval x.ofLp (pderiv i P)

/-- The partial derivative `∂ᵢ (X₀² + X₁² + X₂²) = 2 Xᵢ`. -/
theorem pderiv_normSqPolynomial (i : Fin 3) : pderiv i normSqPolynomial = 2 * X i := by
  fin_cases i <;> simp [normSqPolynomial, pderiv_X]

/-- `normSqPolynomial` evaluates to the squared Euclidean norm. -/
theorem eval_normSqPolynomial (x : ℝ^3) : eval x.ofLp normSqPolynomial = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [normSqPolynomial]

/-- `normSqPolynomial` is homogeneous of degree two. -/
theorem isHomogeneous_normSqPolynomial : normSqPolynomial.IsHomogeneous 2 :=
  ((isHomogeneous_X_pow 0 2).add (isHomogeneous_X_pow 1 2)).add (isHomogeneous_X_pow 2 2)

/-! ### Derivatives of the products `X₂ⁱ Sᵐ` -/

/-- A numeral is a constant polynomial, with vanishing partial derivatives. -/
private theorem pderiv_ofNat (k : Fin 3) (n : ℕ) [n.AtLeastTwo] :
    pderiv k (no_index (OfNat.ofNat n) : MvPolynomial (Fin 3) ℝ) = 0 :=
  (pderiv k).map_natCast n

/-- `∂ₖ (X₂ⁱ Sᵐ) = [k = 2] i X₂ⁱ⁻¹ Sᵐ + 2 m Xₖ X₂ⁱ Sᵐ⁻¹`, with `S = normSqPolynomial`. -/
theorem pderiv_X_two_pow_mul_normSqPolynomial_pow (k : Fin 3) (i m : ℕ) :
    pderiv k (X 2 ^ i * normSqPolynomial ^ m) =
      (if k = 2 then (i : MvPolynomial (Fin 3) ℝ) * (X 2 ^ (i - 1) * normSqPolynomial ^ m)
        else 0) +
        2 * (m : MvPolynomial (Fin 3) ℝ) * X k * (X 2 ^ i * normSqPolynomial ^ (m - 1)) := by
  rw [pderiv_mul, pderiv_pow, pderiv_pow, pderiv_normSqPolynomial]
  by_cases hk : k = 2
  · subst hk
    simp only [pderiv_X_self, ite_true]
    ring
  · simp only [pderiv_X_of_ne (Ne.symm hk), hk, ite_false]
    ring

/-- The Laplacian `Δ (X₂ⁱ Sᵐ) = i (i - 1) X₂ⁱ⁻² Sᵐ + 2 m (2 i + 2 m + 1) X₂ⁱ Sᵐ⁻¹`, with
`S = normSqPolynomial`. -/
theorem polynomialLaplacian_X_two_pow_mul_normSqPolynomial_pow (i m : ℕ) :
    polynomialLaplacian (X 2 ^ i * normSqPolynomial ^ m) =
      (i * (i - 1) : MvPolynomial (Fin 3) ℝ) * (X 2 ^ (i - 2) * normSqPolynomial ^ m) +
        (2 * m * (2 * i + 2 * m + 1) : MvPolynomial (Fin 3) ℝ) *
          (X 2 ^ i * normSqPolynomial ^ (m - 1)) := by
  simp only [polynomialLaplacian, Fin.sum_univ_three, pderiv_X_two_pow_mul_normSqPolynomial_pow]
  simp only [Fin.reduceEq, ite_true, ite_false, zero_add, map_add, pderiv_mul,
    (pderiv _).map_natCast, pderiv_ofNat, pderiv_X_self, zero_mul, mul_zero, add_zero,
    ↓pderiv_X_two_pow_mul_normSqPolynomial_pow]
  have F1 : (i : MvPolynomial (Fin 3) ℝ) * (X 2 * X 2 ^ (i - 1)) =
      (i : MvPolynomial (Fin 3) ℝ) * X 2 ^ i := by
    cases i <;> simp [pow_succ, mul_comm]
  have F2 : ((m - 1 : ℕ) : MvPolynomial (Fin 3) ℝ) *
      (normSqPolynomial * normSqPolynomial ^ (m - 1 - 1)) =
        (m - 1 : ℕ) * normSqPolynomial ^ (m - 1) := by
    rcases m with _ | _ | m <;> simp [pow_succ, mul_comm]
  have F3 : (m : MvPolynomial (Fin 3) ℝ) * ((m - 1 : ℕ) : MvPolynomial (Fin 3) ℝ) =
      m * (m - 1) := by
    cases m <;> simp
  have F4 : (i : MvPolynomial (Fin 3) ℝ) * ((i - 1 : ℕ) : MvPolynomial (Fin 3) ℝ) =
      i * (i - 1) := by
    cases i <;> simp
  have hS : normSqPolynomial = X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 := rfl
  rw [show i - 2 = i - 1 - 1 by omega]
  linear_combination
    (-4 * (m : MvPolynomial (Fin 3) ℝ) * (m - 1 : ℕ) * X 2 ^ i * normSqPolynomial ^ (m - 1 - 1)) *
      hS + 4 * (m : MvPolynomial (Fin 3) ℝ) * X 2 ^ i * F2 +
    4 * X 2 ^ i * normSqPolynomial ^ (m - 1) * F3 + X 2 ^ (i - 1 - 1) * normSqPolynomial ^ m * F4 +
    4 * (m : MvPolynomial (Fin 3) ℝ) * normSqPolynomial ^ (m - 1) * F1

/-! ### The Laplacian -/

/-- The zonal solid harmonic is harmonic. -/
theorem polynomialLaplacian_zonalSolidHarmonicPolynomial (l : ℕ) :
    polynomialLaplacian (zonalSolidHarmonicPolynomial l) = 0 := by
  simp only [zonalSolidHarmonicPolynomial, polynomialLaplacian_sum, mul_assoc,
    polynomialLaplacian_C_mul]
  simp only [polynomialLaplacian_X_two_pow_mul_normSqPolynomial_pow]
  rw [Finset.sum_congr rfl fun i _ ↦ mul_add _ _ _, Finset.sum_add_distrib]
  rcases Nat.lt_or_ge l 2 with hl | hl
  · interval_cases l <;> simp [Finset.sum_range_succ]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hl
  conv_lhs =>
    arg 1
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
  conv_lhs =>
    arg 2
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [show (n + 2 - (n + 1)) / 2 = 0 by omega, Nat.sub_self, Nat.zero_div, Nat.cast_zero,
    mul_zero, zero_mul, add_zero, Nat.cast_one, sub_self, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rw [show k + 1 + 1 - 2 = k by omega,
    show (n + 2 - (k + 1 + 1)) / 2 = (n + 2 - k) / 2 - 1 by omega]
  have hpar := coeff_legendre_eq_zero_or (n + 2) k
  generalize (n + 2 - k) / 2 = m at hpar ⊢
  generalize X 2 ^ k * normSqPolynomial ^ (m - 1) = T
  have key :
      (legendre (n + 2)).coeff (k + 1 + 1) * (((k + 1 + 1 : ℕ) : ℝ) * ((k + 1 + 1 : ℕ) - 1)) +
        (legendre (n + 2)).coeff k * (2 * m * (2 * k + 2 * m + 1)) = 0 := by
    have hrec := coeff_legendre_recursion (n + 2) k
    push_cast at hrec ⊢
    rcases hpar with h0 | h
    · rw [h0] at hrec ⊢
      linear_combination hrec
    · have hm : (k : ℝ) + 2 * m = n + 2 := by exact_mod_cast h
      linear_combination hrec + (legendre (n + 2)).coeff k * (2 * m + (n + 2 - k) + 2 * k + 1) * hm
  have hC := congrArg (C : ℝ → MvPolynomial (Fin 3) ℝ) key
  simp only [map_add, map_mul, map_natCast, map_sub, map_one, map_ofNat, map_zero] at hC
  linear_combination T * hC

/-! ### Homogeneity -/

/-- The zonal solid harmonic is homogeneous of degree `l`. -/
theorem isHomogeneous_zonalSolidHarmonicPolynomial (l : ℕ) :
    (zonalSolidHarmonicPolynomial l).IsHomogeneous l := by
  refine IsHomogeneous.sum _ _ _ fun i _ ↦ ?_
  rcases coeff_legendre_eq_zero_or l i with h | h
  · rw [h, C_0, zero_mul, zero_mul]
    exact isHomogeneous_zero _ _ _
  · have hi := (isHomogeneous_C_mul_X_pow ((legendre l).coeff i) 2 i).mul
      (isHomogeneous_normSqPolynomial.pow ((l - i) / 2))
    rwa [h] at hi

/-- Euler's identity for the zonal solid harmonic: `∑ᵢ Xᵢ ∂ᵢ H = l H`. -/
theorem sum_X_mul_pderiv_zonalSolidHarmonicPolynomial (l : ℕ) :
    ∑ i, X i * pderiv i (zonalSolidHarmonicPolynomial l) =
      (l : MvPolynomial (Fin 3) ℝ) * zonalSolidHarmonicPolynomial l := by
  rw [(isHomogeneous_zonalSolidHarmonicPolynomial l).sum_X_mul_pderiv, nsmul_eq_mul]

/-! ### The gradient -/

/-- The polynomial `∑ᵢ i cᵢ X₂ⁱ⁻¹ S^((l - i) / 2)`, with `cᵢ` the coefficients of `P_l` and
`S = normSqPolynomial`: the coefficient of the third basis vector in the gradient of the zonal
solid harmonic. -/
def zonalSolidHarmonicAxialPolynomial (l : ℕ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i ∈ Finset.range (l + 1),
    C ((legendre l).coeff i * i) * X 2 ^ (i - 1) * normSqPolynomial ^ ((l - i) / 2)

/-- The polynomial `∑ᵢ 2 ((l - i) / 2) cᵢ X₂ⁱ S^((l - i) / 2 - 1)`, with `cᵢ` the coefficients
of `P_l` and `S = normSqPolynomial`: the coefficient of the position vector in the gradient of
the zonal solid harmonic. -/
def zonalSolidHarmonicRadialPolynomial (l : ℕ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i ∈ Finset.range (l + 1),
    C ((legendre l).coeff i * (2 * ((l - i) / 2 : ℕ))) * X 2 ^ i *
      normSqPolynomial ^ ((l - i) / 2 - 1)

/-- The partial derivatives of the zonal solid harmonic are `∂ₖ H = [k = 2] A + Xₖ B`, with
`A = zonalSolidHarmonicAxialPolynomial l` and `B = zonalSolidHarmonicRadialPolynomial l`. -/
theorem pderiv_zonalSolidHarmonicPolynomial (k : Fin 3) (l : ℕ) :
    pderiv k (zonalSolidHarmonicPolynomial l) =
      (if k = 2 then zonalSolidHarmonicAxialPolynomial l else 0) +
        X k * zonalSolidHarmonicRadialPolynomial l := by
  simp only [zonalSolidHarmonicPolynomial, zonalSolidHarmonicAxialPolynomial,
    zonalSolidHarmonicRadialPolynomial, map_sum, Finset.mul_sum]
  split_ifs with hk
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_assoc, pderiv_C_mul, pderiv_X_two_pow_mul_normSqPolynomial_pow, ite_eq_left hk]
    simp only [map_mul, map_natCast, map_ofNat]
    ring
  · rw [zero_add]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_assoc, pderiv_C_mul, pderiv_X_two_pow_mul_normSqPolynomial_pow, ite_eq_right hk]
    simp only [map_mul, map_natCast, map_ofNat]
    ring

/-- The gradient of the zonal solid harmonic at `x` is `A (x) e₃ + B (x) x`, with
`A = zonalSolidHarmonicAxialPolynomial l` and `B = zonalSolidHarmonicRadialPolynomial l`. -/
theorem polynomialGradient_zonalSolidHarmonicPolynomial (l : ℕ) (x : ℝ^3) :
    polynomialGradient (zonalSolidHarmonicPolynomial l) x =
      WithLp.toLp 2 ![x 0 * eval x.ofLp (zonalSolidHarmonicRadialPolynomial l),
        x 1 * eval x.ofLp (zonalSolidHarmonicRadialPolynomial l),
        eval x.ofLp (zonalSolidHarmonicAxialPolynomial l) +
          x 2 * eval x.ofLp (zonalSolidHarmonicRadialPolynomial l)] := by
  ext k
  fin_cases k <;> simp [polynomialGradient, pderiv_zonalSolidHarmonicPolynomial]

/-! ### Evaluation -/

/-- The value of the zonal solid harmonic at `x` is `∑ᵢ cᵢ x₂ⁱ ‖x‖^(2 ((l - i) / 2))`. -/
theorem eval_zonalSolidHarmonicPolynomial (l : ℕ) (x : ℝ^3) :
    eval x.ofLp (zonalSolidHarmonicPolynomial l) =
      ∑ i ∈ Finset.range (l + 1), (legendre l).coeff i * x 2 ^ i * (‖x‖ ^ 2) ^ ((l - i) / 2) := by
  simp [zonalSolidHarmonicPolynomial, eval_normSqPolynomial]

/-- The value of `zonalSolidHarmonicAxialPolynomial l` at `x`. -/
theorem eval_zonalSolidHarmonicAxialPolynomial (l : ℕ) (x : ℝ^3) :
    eval x.ofLp (zonalSolidHarmonicAxialPolynomial l) =
      ∑ i ∈ Finset.range (l + 1),
        (legendre l).coeff i * i * x 2 ^ (i - 1) * (‖x‖ ^ 2) ^ ((l - i) / 2) := by
  simp [zonalSolidHarmonicAxialPolynomial, eval_normSqPolynomial]

/-- The value of `zonalSolidHarmonicRadialPolynomial l` at `x`. -/
theorem eval_zonalSolidHarmonicRadialPolynomial (l : ℕ) (x : ℝ^3) :
    eval x.ofLp (zonalSolidHarmonicRadialPolynomial l) =
      ∑ i ∈ Finset.range (l + 1),
        (legendre l).coeff i * (2 * ((l - i) / 2 : ℕ)) * x 2 ^ i *
          (‖x‖ ^ 2) ^ ((l - i) / 2 - 1) := by
  simp [zonalSolidHarmonicRadialPolynomial, eval_normSqPolynomial]

/-! ### Rotations about the symmetry axis and the equatorial reflection -/

/-- The zonal solid harmonic is invariant under rotations about the third coordinate axis. -/
theorem eval_zonalSolidHarmonicPolynomial_axisRotation (l : ℕ) (θ : ℝ) (x : ℝ^3) :
    eval (axisRotation θ x).ofLp (zonalSolidHarmonicPolynomial l) =
      eval x.ofLp (zonalSolidHarmonicPolynomial l) := by
  rw [eval_zonalSolidHarmonicPolynomial, eval_zonalSolidHarmonicPolynomial,
    show ‖axisRotation θ x‖ = ‖x‖ from (axialRotation θ).norm_map x, axisRotation_apply_two]

/-- `zonalSolidHarmonicAxialPolynomial l` is invariant under rotations about the third coordinate
axis. -/
theorem eval_zonalSolidHarmonicAxialPolynomial_axisRotation (l : ℕ) (θ : ℝ) (x : ℝ^3) :
    eval (axisRotation θ x).ofLp (zonalSolidHarmonicAxialPolynomial l) =
      eval x.ofLp (zonalSolidHarmonicAxialPolynomial l) := by
  rw [eval_zonalSolidHarmonicAxialPolynomial, eval_zonalSolidHarmonicAxialPolynomial,
    show ‖axisRotation θ x‖ = ‖x‖ from (axialRotation θ).norm_map x, axisRotation_apply_two]

/-- `zonalSolidHarmonicRadialPolynomial l` is invariant under rotations about the third
coordinate axis. -/
theorem eval_zonalSolidHarmonicRadialPolynomial_axisRotation (l : ℕ) (θ : ℝ) (x : ℝ^3) :
    eval (axisRotation θ x).ofLp (zonalSolidHarmonicRadialPolynomial l) =
      eval x.ofLp (zonalSolidHarmonicRadialPolynomial l) := by
  rw [eval_zonalSolidHarmonicRadialPolynomial, eval_zonalSolidHarmonicRadialPolynomial,
    show ‖axisRotation θ x‖ = ‖x‖ from (axialRotation θ).norm_map x, axisRotation_apply_two]

/-- The gradient of the zonal solid harmonic is equivariant under rotations about the third
coordinate axis. -/
theorem polynomialGradient_zonalSolidHarmonicPolynomial_axisRotation (l : ℕ) (θ : ℝ)
    (x : ℝ^3) :
    polynomialGradient (zonalSolidHarmonicPolynomial l) (axisRotation θ x) =
      axisRotation θ (polynomialGradient (zonalSolidHarmonicPolynomial l) x) := by
  rw [polynomialGradient_zonalSolidHarmonicPolynomial,
    polynomialGradient_zonalSolidHarmonicPolynomial,
    eval_zonalSolidHarmonicAxialPolynomial_axisRotation,
    eval_zonalSolidHarmonicRadialPolynomial_axisRotation]
  ext k
  fin_cases k <;> simp [axisRotation] <;> ring

/-- The zonal solid harmonic has the parity of `l` under the equatorial reflection. -/
theorem eval_zonalSolidHarmonicPolynomial_equatorialReflection (l : ℕ) (x : ℝ^3) :
    eval (equatorialReflection x).ofLp (zonalSolidHarmonicPolynomial l) =
      (-1) ^ l * eval x.ofLp (zonalSolidHarmonicPolynomial l) := by
  rw [eval_zonalSolidHarmonicPolynomial, eval_zonalSolidHarmonicPolynomial,
    LinearIsometryEquiv.norm_map, equatorialReflection_apply_two, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [neg_pow]
  linear_combination (x 2 ^ i * (‖x‖ ^ 2) ^ ((l - i) / 2)) * neg_one_pow_mul_coeff_legendre l i

/-- `zonalSolidHarmonicAxialPolynomial l` has the parity of `l + 1` under the equatorial
reflection. -/
theorem eval_zonalSolidHarmonicAxialPolynomial_equatorialReflection (l : ℕ) (x : ℝ^3) :
    eval (equatorialReflection x).ofLp (zonalSolidHarmonicAxialPolynomial l) =
      -((-1) ^ l * eval x.ofLp (zonalSolidHarmonicAxialPolynomial l)) := by
  rw [eval_zonalSolidHarmonicAxialPolynomial, eval_zonalSolidHarmonicAxialPolynomial,
    LinearIsometryEquiv.norm_map, equatorialReflection_apply_two, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases i with
  | zero => simp
  | succ j =>
    have h := neg_one_pow_mul_coeff_legendre l (j + 1)
    rw [pow_succ] at h
    rw [Nat.add_sub_cancel, neg_pow]
    linear_combination (-((j + 1 : ℕ) : ℝ) * x 2 ^ j * (‖x‖ ^ 2) ^ ((l - (j + 1)) / 2)) * h

/-- `zonalSolidHarmonicRadialPolynomial l` has the parity of `l` under the equatorial
reflection. -/
theorem eval_zonalSolidHarmonicRadialPolynomial_equatorialReflection (l : ℕ) (x : ℝ^3) :
    eval (equatorialReflection x).ofLp (zonalSolidHarmonicRadialPolynomial l) =
      (-1) ^ l * eval x.ofLp (zonalSolidHarmonicRadialPolynomial l) := by
  rw [eval_zonalSolidHarmonicRadialPolynomial, eval_zonalSolidHarmonicRadialPolynomial,
    LinearIsometryEquiv.norm_map, equatorialReflection_apply_two, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [neg_pow]
  linear_combination
    ((2 * ((l - i) / 2 : ℕ)) * x 2 ^ i * (‖x‖ ^ 2) ^ ((l - i) / 2 - 1)) *
      neg_one_pow_mul_coeff_legendre l i

/-- The gradient of the zonal solid harmonic under the equatorial reflection `σ`:
`∇H (σ x) = (-1)ˡ σ (∇H (x))`. -/
theorem polynomialGradient_zonalSolidHarmonicPolynomial_equatorialReflection (l : ℕ)
    (x : ℝ^3) :
    polynomialGradient (zonalSolidHarmonicPolynomial l) (equatorialReflection x) =
      ((-1 : ℝ) ^ l) •
        equatorialReflection (polynomialGradient (zonalSolidHarmonicPolynomial l) x) := by
  rw [polynomialGradient_zonalSolidHarmonicPolynomial,
    polynomialGradient_zonalSolidHarmonicPolynomial,
    eval_zonalSolidHarmonicAxialPolynomial_equatorialReflection,
    eval_zonalSolidHarmonicRadialPolynomial_equatorialReflection]
  ext k
  fin_cases k <;> simp <;> ring

/-! ### Spherical coordinates -/

/-- The value of the zonal solid harmonic at the spherical point `(r, θ, φ)` is
`r^l P_l (cos θ)`. -/
theorem eval_zonalSolidHarmonicPolynomial_point (l : ℕ) (r θ φ : ℝ) :
    eval (point r θ φ).ofLp (zonalSolidHarmonicPolynomial l) = r ^ l * zonalHarmonic l θ := by
  have h2 : point r θ φ 2 = r * Real.cos θ := by simp [point, radialFrame]
  rw [eval_zonalSolidHarmonicPolynomial, norm_point_sq, h2, zonalHarmonic,
    Polynomial.eval_eq_sum_range, natDegree_legendre, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases coeff_legendre_eq_zero_or l i with h | h
  · simp [h]
  · generalize (l - i) / 2 = m at h ⊢
    subst h
    ring

/-- The value of `zonalSolidHarmonicAxialPolynomial l` at the spherical point `(r, θ, φ)` is
`r^(l - 1) P_l' (cos θ)`. -/
theorem eval_zonalSolidHarmonicAxialPolynomial_point (l : ℕ) (r θ φ : ℝ) :
    eval (point r θ φ).ofLp (zonalSolidHarmonicAxialPolynomial l) =
      r ^ (l - 1) * (Polynomial.derivative (legendre l)).eval (Real.cos θ) := by
  have h2 : point r θ φ 2 = r * Real.cos θ := by simp [point, radialFrame]
  rw [eval_zonalSolidHarmonicAxialPolynomial, norm_point_sq, h2, Polynomial.derivative_eval,
    Polynomial.sum_over_range _ (fun n ↦ by simp), natDegree_legendre, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases coeff_legendre_eq_zero_or l i with h | h
  · simp [h]
  · generalize (l - i) / 2 = m at h ⊢
    subst h
    cases i with
    | zero => simp
    | succ j =>
      rw [Nat.add_sub_cancel, show j + 1 + 2 * m - 1 = j + 2 * m by omega]
      ring

/-- At the spherical point `(r, θ, φ)`, with `A = zonalSolidHarmonicAxialPolynomial l` and
`B = zonalSolidHarmonicRadialPolynomial l`, the radial component `cos θ · A + r B` of the gradient
of the zonal solid harmonic is `l r^(l - 1) P_l (cos θ)`. -/
private theorem cos_mul_eval_axial_add_mul_eval_radial_point (l : ℕ) (r θ φ : ℝ) :
    Real.cos θ * eval (point r θ φ).ofLp (zonalSolidHarmonicAxialPolynomial l) +
        r * eval (point r θ φ).ofLp (zonalSolidHarmonicRadialPolynomial l) =
      l * r ^ (l - 1) * (legendre l).eval (Real.cos θ) := by
  have h2 : point r θ φ 2 = r * Real.cos θ := by simp [point, radialFrame]
  rw [eval_zonalSolidHarmonicAxialPolynomial, eval_zonalSolidHarmonicRadialPolynomial,
    norm_point_sq, h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    Polynomial.eval_eq_sum_range, natDegree_legendre, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases coeff_legendre_eq_zero_or l i with h | h
  · simp [h]
  · generalize (l - i) / 2 = m at h ⊢
    subst h
    have h₁ : Real.cos θ * ((legendre (i + 2 * m)).coeff i * i * (r * Real.cos θ) ^ (i - 1) *
        (r ^ 2) ^ m) = (legendre (i + 2 * m)).coeff i * i * r ^ (i + 2 * m - 1) *
          Real.cos θ ^ i := by
      cases i with
      | zero => simp
      | succ j =>
        rw [Nat.add_sub_cancel, show j + 1 + 2 * m - 1 = j + 2 * m by omega]
        ring
    have h₂ : r * ((legendre (i + 2 * m)).coeff i * (2 * (m : ℝ)) * (r * Real.cos θ) ^ i *
        (r ^ 2) ^ (m - 1)) = (legendre (i + 2 * m)).coeff i * (2 * (m : ℝ)) *
          r ^ (i + 2 * m - 1) * Real.cos θ ^ i := by
      cases m with
      | zero => simp
      | succ n =>
        rw [Nat.add_sub_cancel, show i + 2 * (n + 1) - 1 = i + 2 * n + 1 by omega]
        ring
    rw [h₁, h₂]
    push_cast
    ring

/-- The gradient of the zonal solid harmonic at the spherical point `(r, θ, φ)` is
`l r^(l - 1) S_l (θ) e_r + r^(l - 1) S_l' (θ) e_θ`, for every real `r`. -/
theorem polynomialGradient_zonalSolidHarmonicPolynomial_point (l : ℕ) (r θ φ : ℝ) :
    polynomialGradient (zonalSolidHarmonicPolynomial l) (point r θ φ) =
      ((l : ℝ) * r ^ (l - 1) * zonalHarmonic l θ) • radialFrame θ φ +
        (r ^ (l - 1) * zonalHarmonicDeriv l θ) • polarFrame θ φ := by
  have ha := eval_zonalSolidHarmonicAxialPolynomial_point l r θ φ
  have hab := cos_mul_eval_axial_add_mul_eval_radial_point l r θ φ
  rw [polynomialGradient_zonalSolidHarmonicPolynomial]
  generalize eval (point r θ φ).ofLp (zonalSolidHarmonicAxialPolynomial l) = a at ha hab ⊢
  generalize eval (point r θ φ).ofLp (zonalSolidHarmonicRadialPolynomial l) = b at hab ⊢
  ext k
  fin_cases k <;>
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, point, radialFrame,
      PiLp.smul_apply, Matrix.cons_val_zero, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zonalHarmonic, zonalHarmonicDeriv, mul_neg,
      polarFrame, neg_smul, PiLp.add_apply, PiLp.neg_apply, neg_neg]
  · linear_combination (Real.sin θ * Real.cos φ) * hab -
      (Real.sin θ * Real.cos φ * Real.cos θ) * ha
  · linear_combination (Real.sin θ * Real.sin φ) * hab -
      (Real.sin θ * Real.sin φ * Real.cos θ) * ha
  · linear_combination Real.cos θ * hab + Real.sin θ ^ 2 * ha - a * Real.sin_sq_add_cos_sq θ

/-! ### Degrees zero and one -/

/-- The zonal solid harmonic of degree zero is the constant `1`. -/
theorem zonalSolidHarmonicPolynomial_zero : zonalSolidHarmonicPolynomial 0 = 1 := by
  simp [zonalSolidHarmonicPolynomial, legendre_zero]

/-- The zonal solid harmonic of degree one is the coordinate `X₂`. -/
theorem zonalSolidHarmonicPolynomial_one : zonalSolidHarmonicPolynomial 1 = X 2 := by
  simp [zonalSolidHarmonicPolynomial, Finset.sum_range_succ, legendre_one]

end PDE.Analysis.SpecialFunctions
