/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Analytic.FrozenOperator

/-!
# A weighted Bernstein inequality for derivatives of every order

## Motivation

Can the square norm of the derivatives of order `k + 1` of a function be bounded from the
derivatives of order `k` and from the operator applied to the function, with the maximum
principle as the only tool and with no loss near the boundary of a ball?

## The idea

Bernstein's technique applies an elliptic operator `L = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ` to the square of a
derivative. For a smooth `z`,

`L(z²) = 2 q(∇z) + 2 z Lz ≥ 2 λ |∇z|² + 2 z Lz`,

so the square of the next derivative appears with a good sign. To stay inside a ball we multiply
by a power of the weight `θ(y) = R² - |y - x₀|²`, which vanishes on the sphere. The weight costs
a term with one derivative of `z` and a term without, and the first one is absorbed by half of
the good term: `q(θ ∇z + 2 (m + 2) z ∇θ) ≥ 0`. The result is the scalar inequality

`L(θᵐ⁺² z²) ≥ λ θᵐ⁺² |∇z|² + 2 θᵐ⁺² z Lz - c Λ R² θᵐ z²`.

Summing it over all coordinate derivatives of order `k` of a function `f` gives the same
inequality for the coordinate square norms, because `L` has constant coefficients and commutes
with the derivatives; the term `z Lz` becomes a product of two coordinate norms by the
Cauchy–Schwarz inequality.

## Main results

* `le_frozenOperator_ballWeight_pow_mul_sq`: the scalar inequality, for all `C²` functions `z`,
  all `m` and all points of the closed ball.
* `le_frozenOperator_ballWeight_pow_mul_iteratedCoordinateNormSq`: the inequality for the
  coordinate square norm of order `k`, for all `f` that are `C^{k+2}` at the point.

## Relations

The scalar inequality uses `frozenOperator_mul`, `frozenOperator_pow` and `frozenOperator_sq`.
The second result is an induction on `k` from the first, with
`frozenOperator_partialDeriv_eventuallyEq`. It is used in
`PDE.Elliptic.Regularity.Analytic.Improvement` at an interior maximum of
`θ^{2j} |Dʲv|² + μ θ^{2j-2} |D^{j-1}v|²`, where `frozenOperator_nonpos_of_isLocalMax` applies.

## What stays open

The inequality is for operators without lower-order terms and for the weight of a ball. Applying
the maximum principle to squares of derivatives times a cutoff is a classical device; the
weighted inequality for all orders was worked out for this library and follows no written
source.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology
open SobolevSpace.GraphSpace.BoundaryRegularity (principalEnergy principalPairing)

namespace PDE.Elliptic.Regularity.Analytic

variable {n : ℕ}

/-- The weight of the ball of radius `R` around `x₀`: `R² - |y - x₀|²`, positive inside and zero
on the sphere. -/
def ballWeight (x₀ : ℝ^n) (R : ℝ) (y : ℝ^n) : ℝ := R ^ 2 - ‖y - x₀‖ ^ 2

section Weight

variable (x₀ : ℝ^n) (R : ℝ)

/-- The weight of a ball is smooth. -/
theorem contDiff_ballWeight {m : WithTop ℕ∞} : ContDiff ℝ m (ballWeight x₀ R) :=
  contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)

variable {x₀ R}

/-- The weight is nonnegative on the closed ball. -/
theorem ballWeight_nonneg {x : ℝ^n} (hx : ‖x - x₀‖ ≤ R) : 0 ≤ ballWeight x₀ R x :=
  sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hx 2)

/-- The weight is positive on the open ball. -/
theorem ballWeight_pos {x : ℝ^n} (hx : ‖x - x₀‖ < R) : 0 < ballWeight x₀ R x :=
  sub_pos.mpr (pow_lt_pow_left₀ hx (norm_nonneg _) two_ne_zero)

variable (x₀ R)

/-- The weight is at most `R²`. -/
theorem ballWeight_le (x : ℝ^n) : ballWeight x₀ R x ≤ R ^ 2 :=
  sub_le_self _ (sq_nonneg _)

/-- The coordinate derivatives of the weight: `∂ᵢ θ(y) = -2 (yᵢ - x₀ᵢ)`. -/
theorem partialDeriv_ballWeight (i : Fin n) (y : ℝ^n) :
    (∂[i] (ballWeight x₀ R)) y = -2 * (y i - x₀ i) := by
  have h : HasFDerivAt (ballWeight x₀ R)
      (-(2 • (innerSL ℝ (y - x₀)).comp (ContinuousLinearMap.id ℝ (ℝ^n)))) y :=
    ((hasFDerivAt_id y).sub_const x₀).norm_sq.const_sub (R ^ 2)
  simp [partialDeriv, h.fderiv, EuclideanSpace.inner_single_right]

/-- The second coordinate derivatives of the weight: `∂ᵢ∂ⱼ θ = -2 δᵢⱼ`. -/
theorem partialDeriv_partialDeriv_ballWeight (i j : Fin n) (y : ℝ^n) :
    (∂[i] (∂[j] (ballWeight x₀ R))) y = if i = j then -2 else 0 := by
  have hj : ∂[j] (ballWeight x₀ R) = fun y ↦ -2 * (y j - x₀ j) :=
    funext fun y ↦ partialDeriv_ballWeight x₀ R j y
  have hd : DifferentiableAt ℝ (fun y : ℝ^n ↦ y j) y :=
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).differentiableAt
  rw [hj, partialDeriv_const_mul_fun]
  beta_reduce
  rw [partialDeriv_sub hd (differentiableAt_const _), partialDeriv_coord, partialDeriv_const]
  split_ifs <;> norm_num

/-- The frozen operator of the weight is `-2 tr A`. -/
theorem frozenOperator_ballWeight (A : Fin n → Fin n → ℝ) (y : ℝ^n) :
    frozenOperator A (ballWeight x₀ R) y = -2 * ∑ i, A i i := by
  unfold frozenOperator
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i (fun j _ hji ↦ by
      rw [partialDeriv_partialDeriv_ballWeight, ite_eq_right (Ne.symm hji), mul_zero])
    (fun h ↦ absurd (Finset.mem_univ i) h), partialDeriv_partialDeriv_ballWeight, ite_eq_left rfl]
  ring

/-- The squared length of the gradient of the weight is `4 |y - x₀|²`. -/
theorem sum_sq_partialDeriv_ballWeight (y : ℝ^n) :
    ∑ i, (∂[i] (ballWeight x₀ R)) y ^ 2 = 4 * ‖y - x₀‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [partialDeriv_ballWeight]; simp only [PiLp.sub_apply]; ring

end Weight

/-- The constant of the weighted Bernstein inequality with weight exponent `m + 2` in dimension
`n`. -/
def bernsteinConstant (n m : ℕ) : ℝ := 2 * n * (m + 2) + 4 * (m + 2) * (3 * m + 7)

/-- The Bernstein constant is nonnegative. -/
theorem bernsteinConstant_nonneg (n m : ℕ) : 0 ≤ bernsteinConstant n m := by
  unfold bernsteinConstant
  positivity

section Inequality

variable {A : Fin n → Fin n → ℝ} {lam Lam : ℝ} {x₀ x : ℝ^n} {R : ℝ}

/-- **Weighted Bernstein inequality, scalar case.** Let `λ |ξ|² ≤ q(ξ) ≤ Λ |ξ|²` for the
quadratic form `q` of `A`, let `θ` be the weight of the ball of radius `R` around `x₀` and let
`x` be in the closed ball. Then for every `z` that is `C²` at `x` and every `m`,
`L(θᵐ⁺² z²) ≥ λ θᵐ⁺² |∇z|² + 2 θᵐ⁺² z Lz - c Λ R² θᵐ z²` at `x`, with
`c = bernsteinConstant n m`. The cross term of the product rule is absorbed by
`q(θ ∇z + 2 (m + 2) z ∇θ) ≥ 0`. -/
theorem le_frozenOperator_ballWeight_pow_mul_sq
    (hlow : ∀ ξ : Fin n → ℝ, lam * ∑ i, ξ i ^ 2 ≤ principalEnergy A ξ)
    (hup : ∀ ξ : Fin n → ℝ, principalEnergy A ξ ≤ Lam * ∑ i, ξ i ^ 2)
    (hlam : 0 ≤ lam) (hLam : 0 ≤ Lam) (hx : ‖x - x₀‖ ≤ R) (m : ℕ) {z : ℝ^n → ℝ}
    (hz : ContDiffAt ℝ 2 z x) :
    lam * ballWeight x₀ R x ^ (m + 2) * ∑ i, (∂[i] z) x ^ 2 +
        2 * ballWeight x₀ R x ^ (m + 2) * z x * frozenOperator A z x -
        bernsteinConstant n m * Lam * R ^ 2 * ballWeight x₀ R x ^ m * z x ^ 2 ≤
      frozenOperator A (fun y ↦ ballWeight x₀ R y ^ (m + 2) * z y ^ 2) x := by
  have hθc : ContDiffAt ℝ 2 (ballWeight x₀ R) x := (contDiff_ballWeight x₀ R).contDiffAt
  have hθd : DifferentiableAt ℝ (ballWeight x₀ R) x := hθc.differentiableAt (by norm_num)
  have hzd : DifferentiableAt ℝ z x := hz.differentiableAt (by norm_num)
  set θ := ballWeight x₀ R x with hθ
  set ξ : Fin n → ℝ := fun i ↦ (∂[i] z) x with hξ
  set ζ : Fin n → ℝ := fun i ↦ (∂[i] (ballWeight x₀ R)) x with hζ
  have hθ0 : 0 ≤ θ := ballWeight_nonneg hx
  have hθR : θ ≤ R ^ 2 := ballWeight_le x₀ R x
  -- the operator applied to the product, by the product rule
  have hmul := frozenOperator_mul A (hθc.pow (m + 2)) (hz.pow 2)
  have hgradW : (fun i ↦ (∂[i] (fun y ↦ ballWeight x₀ R y ^ (m + 2))) x) =
      fun i ↦ (((m : ℝ) + 2) * θ ^ (m + 1)) * ζ i := by
    funext i
    rw [hθd.partialDeriv_fun_pow_succ (m + 1) i]
    push_cast
    ring
  have hgradz : (fun i ↦ (∂[i] (fun y ↦ z y ^ 2)) x) = fun i ↦ (2 * z x) * ξ i := by
    funext i
    rw [hzd.partialDeriv_fun_pow_succ 1 i]
    push_cast
    ring
  rw [hgradW, hgradz, principalPairing_smul_smul, principalPairing_smul_smul,
    frozenOperator_pow A hθc m, frozenOperator_sq A hz, frozenOperator_ballWeight] at hmul
  rw [hmul]
  -- the quantities that enter
  have hkey := (mul_nonneg hlam (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)).trans
    (hlow fun i ↦ θ * ξ i + (2 * ((m : ℝ) + 2) * z x) * ζ i)
  rw [principalEnergy_smul_add_smul] at hkey
  have hqξ : lam * ∑ i, ξ i ^ 2 ≤ principalEnergy A ξ := hlow ξ
  have hqζ : principalEnergy A ζ ≤ Lam * (4 * R ^ 2) := by
    refine (hup ζ).trans (mul_le_mul_of_nonneg_left ?_ hLam)
    rw [hζ, sum_sq_partialDeriv_ballWeight]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) (by norm_num)
  have htr : ∑ i, A i i ≤ n * Lam := by
    have hi (i : Fin n) : A i i ≤ Lam := by
      have h := hup (Pi.single i 1)
      simpa [principalEnergy, Pi.single_apply] using h
    calc ∑ i, A i i ≤ ∑ _i : Fin n, Lam := Finset.sum_le_sum fun i _ ↦ hi i
      _ = n * Lam := by simp
  -- powers of the weight in terms of `θᵐ`
  set t := θ ^ m with ht
  have ht0 : 0 ≤ t := pow_nonneg hθ0 m
  have e1 : θ ^ (m + 1) = t * θ := pow_succ θ m
  have e2 : θ ^ (m + 2) = t * θ * θ := by rw [pow_succ, pow_succ]
  rw [e1, e2]
  rw [e1] at hmul
  set S := ∑ i, ξ i ^ 2
  set qξ := principalEnergy A ξ
  set qζ := principalEnergy A ζ
  set C := principalPairing A ξ ζ + principalPairing A ζ ξ with hC
  set T := ∑ i, A i i
  set Lz := frozenOperator A z x
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hz2 : 0 ≤ z x ^ 2 := sq_nonneg _
  -- the four estimates, each multiplied by its nonnegative weight
  have b1 : 0 ≤ t * (θ ^ 2 * qξ + (2 * ((m : ℝ) + 2) * z x) ^ 2 * qζ +
      θ * (2 * ((m : ℝ) + 2) * z x) * C) := mul_nonneg ht0 hkey
  have b2 : t * θ * θ * (lam * S) ≤ t * θ * θ * qξ :=
    mul_le_mul_of_nonneg_left hqξ (mul_nonneg (mul_nonneg ht0 hθ0) hθ0)
  have b3 : (((m : ℝ) + 2) * (3 * m + 7) * t * z x ^ 2) * qζ ≤
      (((m : ℝ) + 2) * (3 * m + 7) * t * z x ^ 2) * (Lam * (4 * R ^ 2)) :=
    mul_le_mul_of_nonneg_left hqζ (by positivity)
  have b4 : (2 * ((m : ℝ) + 2) * t * θ * z x ^ 2) * T ≤
      (2 * ((m : ℝ) + 2) * t * θ * z x ^ 2) * (n * Lam) :=
    mul_le_mul_of_nonneg_left htr (by positivity)
  have b5 : (2 * ((m : ℝ) + 2) * n * Lam * t * z x ^ 2) * θ ≤
      (2 * ((m : ℝ) + 2) * n * Lam * t * z x ^ 2) * R ^ 2 :=
    mul_le_mul_of_nonneg_left hθR (by positivity)
  have hC' : principalPairing A ζ ξ + principalPairing A ξ ζ = C := by rw [hC, add_comm]
  unfold bernsteinConstant
  have hcross : ((m : ℝ) + 2) * (t * θ) * (2 * z x) * principalPairing A ζ ξ +
      2 * z x * (((m : ℝ) + 2) * (t * θ)) * principalPairing A ξ ζ =
        2 * ((m : ℝ) + 2) * t * θ * z x * C := by rw [← hC']; ring
  rw [hcross]
  nlinarith [b1, b2, b3, b4, b5]

/-- **Weighted Bernstein inequality for the coordinate square norm of order `k`.** In the
setting of `le_frozenOperator_ballWeight_pow_mul_sq`, for every `f` that is `C^{k+2}` at `x`,
`L(θᵐ⁺² |Dᵏf|²) ≥ λ θᵐ⁺² |Dᵏ⁺¹f|² - 2 θᵐ⁺² |Dᵏf| |Dᵏ(Lf)| - c Λ R² θᵐ |Dᵏf|²` at `x`. The proof
sums the scalar inequality over the coordinate derivatives of order `k`, which commute with the
frozen operator. -/
theorem le_frozenOperator_ballWeight_pow_mul_iteratedCoordinateNormSq
    (hlow : ∀ ξ : Fin n → ℝ, lam * ∑ i, ξ i ^ 2 ≤ principalEnergy A ξ)
    (hup : ∀ ξ : Fin n → ℝ, principalEnergy A ξ ≤ Lam * ∑ i, ξ i ^ 2)
    (hlam : 0 ≤ lam) (hLam : 0 ≤ Lam) (hx : ‖x - x₀‖ ≤ R) (m k : ℕ) {f : ℝ^n → ℝ}
    (hf : ContDiffAt ℝ (k + 2 : ℕ) f x) :
    lam * ballWeight x₀ R x ^ (m + 2) * iteratedCoordinateNormSq (k + 1) f x -
        2 * ballWeight x₀ R x ^ (m + 2) * (iteratedCoordinateNorm k f x *
          iteratedCoordinateNorm k (frozenOperator A f) x) -
        bernsteinConstant n m * Lam * R ^ 2 * ballWeight x₀ R x ^ m *
          iteratedCoordinateNormSq k f x ≤
      frozenOperator A (fun y ↦ ballWeight x₀ R y ^ (m + 2) * iteratedCoordinateNormSq k f y)
        x := by
  have hθ0 : 0 ≤ ballWeight x₀ R x := ballWeight_nonneg hx
  induction k generalizing f with
  | zero =>
    have h2 : ContDiffAt ℝ 2 f x := by simpa using hf
    have h := le_frozenOperator_ballWeight_pow_mul_sq hlow hup hlam hLam hx m h2
    have hsq (y : ℝ^n) : iteratedCoordinateNormSq 0 f y = f y ^ 2 := by
      simp [iteratedCoordinateNormSq]
    have hfun : (fun y ↦ ballWeight x₀ R y ^ (m + 2) * iteratedCoordinateNormSq 0 f y) =
        fun y ↦ ballWeight x₀ R y ^ (m + 2) * f y ^ 2 := funext fun y ↦ by rw [hsq]
    have h1 : iteratedCoordinateNormSq 1 f x = ∑ i, (∂[i] f) x ^ 2 := by
      simp [iteratedCoordinateNormSq]
    rw [hfun, hsq, h1, iteratedCoordinateNorm_zero, iteratedCoordinateNorm_zero]
    have habs : -(‖f x‖ * ‖frozenOperator A f x‖) ≤ f x * frozenOperator A f x := by
      rw [← norm_mul, Real.norm_eq_abs]
      exact neg_abs_le _
    have hw : 0 ≤ 2 * ballWeight x₀ R x ^ (m + 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left habs hw]
  | succ k ih =>
    have h3 : ContDiffAt ℝ 3 f x := hf.of_le (by exact_mod_cast (by omega : 3 ≤ k + 1 + 2))
    have hfi (i : Fin n) : ContDiffAt ℝ (k + 2 : ℕ) (∂[i] f) x :=
      hf.partialDeriv i (by exact_mod_cast (by omega : k + 2 + 1 ≤ k + 1 + 2))
    -- the inequality of order `k` for each `∂ᵢ f`, with `L ∂ᵢ f = ∂ᵢ L f` near `x`
    have hi (i : Fin n) := ih (hfi i)
    have hcomm (i : Fin n) : iteratedCoordinateNorm k (frozenOperator A (∂[i] f)) x =
        iteratedCoordinateNorm k (∂[i] (frozenOperator A f)) x :=
      (frozenOperator_partialDeriv_eventuallyEq A h3 i).iteratedCoordinateNorm k
    -- the operator is additive over the sum that defines the square norm of order `k + 1`
    have hC2 (i : Fin n) : ContDiffAt ℝ 2
        (fun y ↦ ballWeight x₀ R y ^ (m + 2) * iteratedCoordinateNormSq k (∂[i] f) y) x :=
      ((contDiff_ballWeight x₀ R).contDiffAt.pow (m + 2)).mul
        (ContDiffAt.iteratedCoordinateNormSq k (m := 2) (hfi i))
    have hsum : frozenOperator A
        (fun y ↦ ballWeight x₀ R y ^ (m + 2) * iteratedCoordinateNormSq (k + 1) f y) x =
        ∑ i, frozenOperator A
          (fun y ↦ ballWeight x₀ R y ^ (m + 2) * iteratedCoordinateNormSq k (∂[i] f) y) x := by
      rw [← frozenOperator_sum A Finset.univ fun i _ ↦ hC2 i]
      simp only [iteratedCoordinateNormSq, Finset.mul_sum]
    -- the Cauchy–Schwarz inequality for the cross terms
    have hcs : ∑ i, iteratedCoordinateNorm k (∂[i] f) x *
        iteratedCoordinateNorm k (∂[i] (frozenOperator A f)) x ≤
          iteratedCoordinateNorm (k + 1) f x *
            iteratedCoordinateNorm (k + 1) (frozenOperator A f) x := by
      rw [iteratedCoordinateNorm_succ, iteratedCoordinateNorm_succ]
      exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    rw [hsum]
    calc lam * ballWeight x₀ R x ^ (m + 2) * iteratedCoordinateNormSq (k + 1 + 1) f x -
          2 * ballWeight x₀ R x ^ (m + 2) * (iteratedCoordinateNorm (k + 1) f x *
            iteratedCoordinateNorm (k + 1) (frozenOperator A f) x) -
          bernsteinConstant n m * Lam * R ^ 2 * ballWeight x₀ R x ^ m *
            iteratedCoordinateNormSq (k + 1) f x
        ≤ ∑ i, (lam * ballWeight x₀ R x ^ (m + 2) * iteratedCoordinateNormSq (k + 1) (∂[i] f) x -
            2 * ballWeight x₀ R x ^ (m + 2) * (iteratedCoordinateNorm k (∂[i] f) x *
              iteratedCoordinateNorm k (frozenOperator A (∂[i] f)) x) -
            bernsteinConstant n m * Lam * R ^ 2 * ballWeight x₀ R x ^ m *
              iteratedCoordinateNormSq k (∂[i] f) x) := by
          simp only [hcomm, Finset.sum_sub_distrib, ← Finset.mul_sum]
          have hw : 0 ≤ 2 * ballWeight x₀ R x ^ (m + 2) := by positivity
          have h := mul_le_mul_of_nonneg_left hcs hw
          simp only [iteratedCoordinateNormSq] at h ⊢
          linarith
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦ hi i

end Inequality

end PDE.Elliptic.Regularity.Analytic
