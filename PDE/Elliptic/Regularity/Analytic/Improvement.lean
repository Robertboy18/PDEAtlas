/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Analytic.Structure

/-!
# The improvement step for weighted derivative bounds

## Motivation

If a smooth solution `v` of the autonomous diagonal system near a closed ball with weight `θ`
satisfies `θⁱ |Dⁱv| ≤ i! · 2M · ψ(i) · Bⁱ` on the ball for `1 ≤ i ≤ N`, is the same true with `M`
in place of `2M`?

## The idea

Yes, when `M` is small and `B` is large. A bound that improves itself can be pushed down from
any large `B` to a fixed one.

Fix `j ≥ 2` and look at `Ψ = θ^{2j} |Dʲv|² + μ θ^{2j-2} |D^{j-1}v|²` with `μ = j² B² / 32`. It
is continuous on the closed ball and vanishes on the sphere, so it has a maximum, and if the
maximum is positive it is attained inside. There the operator with coefficients frozen at the
maximum point is nonpositive on `Ψ` (`frozenOperator_nonpos_of_isLocalMax`). The weighted
Bernstein inequality bounds the operator from below by `λ θ^{2j} |D^{j+1}v|²` and
`μ λ θ^{2j-2} |Dʲv|²` minus cross terms, and the structure estimate `weighted_cross_le` bounds
the cross terms. The derivative of order `j + 1` enters linearly and is absorbed by the first
good term. What is left is an inequality between `X j = θʲ |Dʲv|` and `X (j-1)` at the maximum
point, and `sq_le_of_bernstein` turns it into `X j ≤ T/2` there, with `T` the target. Since `Ψ`
is largest at that point, `X j ≤ T` on the whole ball.

## Main results

* `SolutionOnBall`: the standing hypotheses (a smooth solution near a closed ball, ellipticity
  of the frozen coefficients and derivative bounds for the coefficients along the solution).
* `sq_le_of_bernstein`: the arithmetic at the maximum point, for all real numbers with the
  stated bounds.
* `WeightedBound.improve`: the improvement from `2M` to `M`, for all `N`, when
  `K M ≤ 1/8`, `c M ≤ λ/18432` and `B` is large in terms of `R`, `M`, `Λ/λ`.

## Relations

`WeightedBound.improve` uses `le_frozenOperator_ballWeight_pow_mul_iteratedCoordinateNormSq`,
`weighted_cross_le` and `frozenOperator_nonpos_of_isLocalMax`. It is iterated in
`PDE.Elliptic.Regularity.Analytic.DerivativeBounds`.

## What stays open

The order `i = 1` is not improved here; it is the hypothesis `hbase`, which holds for large `B`
because the first derivatives are bounded.

## References

* S. Blatt, *On the analyticity of solutions to non-linear elliptic partial differential
  equations*, arXiv:2009.08762v2, 2024, §3.2 (a recursive inequality for weighted derivatives,
  with the top order absorbed). There the linear estimate is in `L²`; here it is the maximum
  principle.
  <https://arxiv.org/abs/2009.08762>
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped ContDiff Topology
open PDE.Analysis
open SobolevSpace.GraphSpace.BoundaryRegularity (principalEnergy)

namespace PDE.Elliptic.Regularity.Analytic

/-- **The arithmetic at the maximum point.** Let `m > 0` and `μ = m²/32`. If
`λ Xp² + (μ λ - κ) X² ≤ 2 X (τ Xp + D) + 2 μ Xm D' + μ κ Xm²` with `X ≤ 2T`, `m Xm ≤ (9/2) T` and
with `κ`, `τ²`, `D`, `D'` small multiples of `m² λ`, `m² λ²`, `m² λ T`, `m λ T`, then
`X² ≤ T²/4`. The term `2 X τ Xp` is absorbed by `λ Xp²`. -/
theorem sq_le_of_bernstein {lam m T Xp X Xm τ D D' κ : ℝ} (hlam : 0 < lam) (hm : 0 < m)
    (hT : 0 ≤ T) (hD0 : 0 ≤ D) (hD'0 : 0 ≤ D')
    (h1 : lam * Xp ^ 2 + (m ^ 2 / 32 * lam - κ) * X ^ 2 ≤
      2 * X * (τ * Xp + D) + 2 * (m ^ 2 / 32) * (Xm * D') + m ^ 2 / 32 * κ * Xm ^ 2)
    (hX : X ≤ 2 * T) (hXm0 : 0 ≤ Xm) (hXm : m * Xm ≤ 9 / 2 * T)
    (hκ : κ ≤ m ^ 2 * lam / 486) (hτ : τ ^ 2 ≤ m ^ 2 * lam ^ 2 / 128)
    (hD : D ≤ m ^ 2 * lam * T / 3072) (hD' : D' ≤ m * lam * T / 216) : X ^ 2 ≤ T ^ 2 / 4 := by
  -- absorb the top order: `2 X τ Xp ≤ λ Xp² + τ² X² / λ`
  have a1 : 2 * X * τ * Xp ≤ lam * Xp ^ 2 + τ ^ 2 * X ^ 2 / lam := by
    have h2 : lam * Xp ^ 2 + τ ^ 2 * X ^ 2 / lam - 2 * X * τ * Xp =
        (lam * Xp - τ * X) ^ 2 / lam := by field_simp; ring
    have h3 : 0 ≤ (lam * Xp - τ * X) ^ 2 / lam := by positivity
    linarith
  have a2 : τ ^ 2 * X ^ 2 / lam ≤ m ^ 2 * lam / 128 * X ^ 2 := by
    rw [div_le_iff₀ hlam]
    have h := mul_le_mul_of_nonneg_right hτ (sq_nonneg X)
    linarith
  have hmXm0 : 0 ≤ m * Xm := mul_nonneg hm.le hXm0
  have hmT : 0 ≤ m ^ 2 * lam * T / 3072 := by positivity
  have hmT' : 0 ≤ m * lam * T / 216 := by positivity
  -- the three terms on the right are each at most `m² λ T² / 768`
  have b1 : 2 * X * D ≤ m ^ 2 * lam * T ^ 2 / 768 := by
    rcases le_or_gt 0 X with hX0 | hX0
    · have h := mul_le_mul hX hD hD0 (by positivity : (0 : ℝ) ≤ 2 * T)
      linarith
    · have h : 0 ≤ m ^ 2 * lam * T ^ 2 / 768 := by positivity
      have h' : 2 * X * D ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hD0
      linarith
  have b2 : 2 * (m ^ 2 / 32) * (Xm * D') ≤ m ^ 2 * lam * T ^ 2 / 768 := by
    have h := mul_le_mul hXm hD' hD'0 (by positivity : (0 : ℝ) ≤ 9 / 2 * T)
    have e : 2 * (m ^ 2 / 32) * (Xm * D') = m / 16 * (m * Xm * D') := by ring
    rw [e]
    have h' := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ m / 16)
    linarith
  have b3 : m ^ 2 / 32 * κ * Xm ^ 2 ≤ m ^ 2 * lam * T ^ 2 / 768 := by
    have hsq : (m * Xm) ^ 2 ≤ (9 / 2 * T) ^ 2 := pow_le_pow_left₀ hmXm0 hXm 2
    rcases le_or_gt 0 κ with hκ0 | hκ0
    · have h := mul_le_mul hκ hsq (sq_nonneg _) (by positivity : (0 : ℝ) ≤ m ^ 2 * lam / 486)
      have e : m ^ 2 / 32 * κ * Xm ^ 2 = κ * (m * Xm) ^ 2 / 32 := by ring
      rw [e]
      linarith
    · have h : 0 ≤ m ^ 2 * lam * T ^ 2 / 768 := by positivity
      have h' : m ^ 2 / 32 * κ * Xm ^ 2 ≤ 0 := by
        have : m ^ 2 / 32 * κ * Xm ^ 2 = κ * (m ^ 2 / 32 * Xm ^ 2) := by ring
        rw [this]
        exact mul_nonpos_of_nonpos_of_nonneg hκ0.le (by positivity)
      linarith
  have c1 : κ * X ^ 2 ≤ m ^ 2 * lam / 486 * X ^ 2 := mul_le_mul_of_nonneg_right hκ (sq_nonneg X)
  -- collect
  have hx2 : 0 ≤ m ^ 2 * lam * X ^ 2 := by positivity
  have hmain : m ^ 2 * lam * (X ^ 2 / 64) ≤ m ^ 2 * lam * (T ^ 2 / 256) := by linarith
  have hpos : 0 < m ^ 2 * lam := by positivity
  have := le_of_mul_le_mul_left hmain hpos
  linarith

/-- The Bernstein constant increases with the weight exponent. -/
theorem bernsteinConstant_le_add_two (n m : ℕ) :
    bernsteinConstant n m ≤ bernsteinConstant n (m + 2) := by
  unfold bernsteinConstant
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast
  nlinarith [mul_nonneg hn hm]

/-- The Bernstein constant of the weight exponent `2j + 4` is at most `(2n + 52) (j + 2)²`. -/
theorem bernsteinConstant_le (n j : ℕ) :
    bernsteinConstant n (2 * j + 2) ≤ (2 * n + 52) * ((j : ℝ) + 2) ^ 2 := by
  unfold bernsteinConstant
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast
  nlinarith [mul_nonneg hn hj, mul_nonneg hn (mul_nonneg hj hj), mul_nonneg hj hj]

variable {n : ℕ} {I : Type*} [Fintype I] {a : Fin n → Fin n → (I → ℝ) → ℝ}
  {f : I → Fin n → (I → ℝ) → ℝ} {v : ℝ^n → I → ℝ}

/-- The standing hypotheses of the derivative estimates: `v` is a smooth solution of the
autonomous diagonal system `∑ᵢ ∂ᵢ (∑ⱼ aᵢⱼ(v) ∂ⱼ v_l - f_{l i}(v)) = 0` on an open set `U` that
contains the closed ball of radius `R` around `x₀`; the coefficients and the forcing are smooth
along `v`; on the closed ball the frozen coefficient matrix has quadratic form between `λ` and
`Λ`, and the derivatives of the coefficients and of the forcing at the values of `v` are at most
`m! C Kᵐ`. -/
structure SolutionOnBall (a : Fin n → Fin n → (I → ℝ) → ℝ) (f : I → Fin n → (I → ℝ) → ℝ)
    (v : ℝ^n → I → ℝ) (U : Set (ℝ^n)) (x₀ : ℝ^n) (R lam Lam C K : ℝ) : Prop where
  /-- The domain is open. -/
  isOpen : IsOpen U
  /-- The closed ball lies in the domain. -/
  closedBall_subset : closedBall x₀ R ⊆ U
  /-- The solution is smooth on the domain. -/
  contDiffOn : ContDiffOn ℝ ∞ v U
  /-- The coefficients are smooth at the values of the solution. -/
  coeff_contDiffAt : ∀ y ∈ U, ∀ i j, ContDiffAt ℝ ∞ (a i j) (v y)
  /-- The forcing is smooth at the values of the solution. -/
  forcing_contDiffAt : ∀ y ∈ U, ∀ l i, ContDiffAt ℝ ∞ (f l i) (v y)
  /-- The system holds on the domain. -/
  equation : ∀ y ∈ U, ∀ l, ∑ i, (∂[i] (flux a f v l i)) y = 0
  /-- The radius is positive. -/
  radius_pos : 0 < R
  /-- The lower ellipticity constant is positive. -/
  lam_pos : 0 < lam
  /-- The upper ellipticity constant is nonnegative. -/
  Lam_nonneg : 0 ≤ Lam
  /-- The frozen coefficients are elliptic from below on the closed ball. -/
  lower : ∀ x ∈ closedBall x₀ R, ∀ ξ : Fin n → ℝ,
    lam * ∑ i, ξ i ^ 2 ≤ principalEnergy (fun i j ↦ a i j (v x)) ξ
  /-- The frozen coefficients are bounded from above on the closed ball. -/
  upper : ∀ x ∈ closedBall x₀ R, ∀ ξ : Fin n → ℝ,
    principalEnergy (fun i j ↦ a i j (v x)) ξ ≤ Lam * ∑ i, ξ i ^ 2
  /-- The constant in the derivative bounds is nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- The rate in the derivative bounds is nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- The derivatives of the coefficients at the values of the solution on the closed ball. -/
  coeff_bound : ∀ x ∈ closedBall x₀ R, ∀ i j m,
    ‖iteratedFDeriv ℝ m (a i j) (v x)‖ ≤ m.factorial * C * K ^ m
  /-- The derivatives of the forcing at the values of the solution on the closed ball. -/
  forcing_bound : ∀ x ∈ closedBall x₀ R, ∀ l i m,
    ‖iteratedFDeriv ℝ m (f l i) (v x)‖ ≤ m.factorial * C * K ^ m

/-- The weighted norm of order `k` of the family `v` at `x`: `θ(x)ᵏ |Dᵏv(x)|` with the weight
`θ` of the ball of radius `R` around `x₀`. -/
def weightedNorm (x₀ : ℝ^n) (R : ℝ) (k : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n) : ℝ :=
  ballWeight x₀ R x ^ k * familyNorm k v x

/-- The square of the weighted norm. -/
theorem weightedNorm_sq (x₀ : ℝ^n) (R : ℝ) (k : ℕ) (v : ℝ^n → I → ℝ) (x : ℝ^n) :
    weightedNorm x₀ R k v x ^ 2 = ballWeight x₀ R x ^ (2 * k) * familyNormSq k v x := by
  rw [weightedNorm, mul_pow, familyNorm_sq, ← pow_mul, mul_comm k 2]

/-- The weighted derivative bounds of the orders `1 ≤ i ≤ N` with the constants `M`, `B`:
`θⁱ |Dⁱv| ≤ i! M ψ(i) Bⁱ` on the open ball, with the convolution weight `ψ`. -/
def WeightedBound (v : ℝ^n → I → ℝ) (x₀ : ℝ^n) (R M B : ℝ) (N : ℕ) : Prop :=
  ∀ x ∈ ball x₀ R, ∀ i, 1 ≤ i → i ≤ N →
    weightedNorm x₀ R i v x ≤ i.factorial * M * convolutionWeight i * B ^ i

/-- The family square norm of order `k` of a family that is `C^{k+m}` at a point is `C^m`
there. -/
theorem _root_.ContDiffAt.familyNormSq (k : ℕ) {m : ℕ} {x : ℝ^n}
    (hv : ContDiffAt ℝ (k + m : ℕ) v x) :
    ContDiffAt ℝ m (PDE.Elliptic.Regularity.Analytic.familyNormSq k v) x := by
  have h (l : I) : ContDiffAt ℝ m (iteratedCoordinateNormSq k (fun y ↦ v y l)) x :=
    ContDiffAt.iteratedCoordinateNormSq k (contDiffAt_pi.mp hv l)
  exact ContDiffAt.sum fun l _ ↦ h l

/-- **Weighted Bernstein inequality for a family.** The inequality
`le_frozenOperator_ballWeight_pow_mul_iteratedCoordinateNormSq` summed over the members of a
family that is `C^{k+2}` at the point. -/
theorem le_frozenOperator_ballWeight_pow_mul_familyNormSq {A : Fin n → Fin n → ℝ}
    {lam Lam : ℝ} {x₀ x : ℝ^n} {R : ℝ}
    (hlow : ∀ ξ : Fin n → ℝ, lam * ∑ i, ξ i ^ 2 ≤ principalEnergy A ξ)
    (hup : ∀ ξ : Fin n → ℝ, principalEnergy A ξ ≤ Lam * ∑ i, ξ i ^ 2)
    (hlam : 0 ≤ lam) (hLam : 0 ≤ Lam) (hx : ‖x - x₀‖ ≤ R) (m k : ℕ)
    (hv : ContDiffAt ℝ (k + 2 : ℕ) v x) :
    lam * ballWeight x₀ R x ^ (m + 2) * familyNormSq (k + 1) v x -
        2 * ballWeight x₀ R x ^ (m + 2) * ∑ l, iteratedCoordinateNorm k (fun z ↦ v z l) x *
          iteratedCoordinateNorm k (frozenOperator A (fun z ↦ v z l)) x -
        bernsteinConstant n m * Lam * R ^ 2 * ballWeight x₀ R x ^ m * familyNormSq k v x ≤
      frozenOperator A (fun y ↦ ballWeight x₀ R y ^ (m + 2) * familyNormSq k v y) x := by
  have hl (l : I) := le_frozenOperator_ballWeight_pow_mul_iteratedCoordinateNormSq (A := A)
    hlow hup hlam hLam hx m k (contDiffAt_pi.mp hv l)
  have hC2 (l : I) : ContDiffAt ℝ 2
      (fun y ↦ ballWeight x₀ R y ^ (m + 2) * iteratedCoordinateNormSq k (fun z ↦ v z l) y) x :=
    ((contDiff_ballWeight x₀ R).contDiffAt.pow (m + 2)).mul
      (ContDiffAt.iteratedCoordinateNormSq k (m := 2) (contDiffAt_pi.mp hv l))
  have hfun : (fun y ↦ ballWeight x₀ R y ^ (m + 2) * familyNormSq k v y) =
      fun y ↦ ∑ l, ballWeight x₀ R y ^ (m + 2) *
        iteratedCoordinateNormSq k (fun z ↦ v z l) y := by
    funext y
    simp only [familyNormSq, Finset.mul_sum]
  rw [hfun, frozenOperator_sum (fun i j ↦ A i j) Finset.univ fun l _ ↦ hC2 l]
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun l _ ↦ hl l)
  simp only [familyNormSq, Finset.mul_sum, Finset.sum_sub_distrib]

/-- The bound on `m X (j+1)` in terms of the target of order `j + 2`. -/
private theorem mul_prev_le {j : ℕ} {M B Xm : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hXm : Xm ≤ (j + 1).factorial * (2 * M) * convolutionWeight (j + 1) * B ^ (j + 1)) :
    ((j : ℝ) + 2) * B * Xm ≤
      9 / 2 * ((j + 2).factorial * M * convolutionWeight (j + 2) * B ^ (j + 2)) := by
  have hfac : ((j + 2).factorial : ℝ) = ((j : ℝ) + 2) * (j + 1).factorial := by
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.factorial_succ]
    push_cast
    ring
  have hψ : convolutionWeight (j + 1) ≤ 9 / 4 * convolutionWeight (j + 2) :=
    convolutionWeight_le_mul_succ (j := j + 1) (by omega)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hf2 : (0 : ℝ) ≤ (j + 2).factorial := Nat.cast_nonneg _
  have hBp : 0 ≤ B ^ (j + 2) := pow_nonneg hB _
  calc ((j : ℝ) + 2) * B * Xm
      ≤ ((j : ℝ) + 2) * B *
          ((j + 1).factorial * (2 * M) * convolutionWeight (j + 1) * B ^ (j + 1)) :=
        mul_le_mul_of_nonneg_left hXm (by positivity)
    _ = 2 * ((j + 2).factorial * M * B ^ (j + 2)) * convolutionWeight (j + 1) := by
        rw [hfac]; ring
    _ ≤ 2 * ((j + 2).factorial * M * B ^ (j + 2)) * (9 / 4 * convolutionWeight (j + 2)) :=
        mul_le_mul_of_nonneg_left hψ (by positivity)
    _ = _ := by ring

/-- The bound on the coefficient of the top order. -/
private theorem top_sq_le {j : ℕ} {cM lam B : ℝ} (hcM0 : 0 ≤ cM) (hcM : cM ≤ lam / 18432)
    (hB : 0 ≤ B) :
    (cM * ((j : ℝ) + 3) * B) ^ 2 ≤ (((j : ℝ) + 2) * B) ^ 2 * lam ^ 2 / 128 := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlam : 0 ≤ lam := by linarith
  have h1 : cM * ((j : ℝ) + 3) * B ≤ lam / 18432 * (3 / 2 * ((j : ℝ) + 2)) * B := by
    have h2 : cM * ((j : ℝ) + 3) ≤ lam / 18432 * (3 / 2 * ((j : ℝ) + 2)) :=
      mul_le_mul hcM (by linarith) (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h2 hB
  have h3 := pow_le_pow_left₀ (by positivity : 0 ≤ cM * ((j : ℝ) + 3) * B) h1 2
  have h4 : 0 ≤ (((j : ℝ) + 2) * B) ^ 2 * lam ^ 2 := by positivity
  have e : (lam / 18432 * (3 / 2 * ((j : ℝ) + 2)) * B) ^ 2 =
      (((j : ℝ) + 2) * B) ^ 2 * lam ^ 2 / 150994944 := by ring
  rw [e] at h3
  linarith

/-- The bound on the remainder of order `j + 2`. -/
private theorem remainder_top_le {j : ℕ} {cM lam M B : ℝ} (hcM0 : 0 ≤ cM)
    (hcM : cM ≤ lam / 18432) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    cM * M * ((j + 4).factorial * convolutionWeight (j + 4) * B ^ (j + 4)) ≤
      (((j : ℝ) + 2) * B) ^ 2 * lam *
        ((j + 2).factorial * M * convolutionWeight (j + 2) * B ^ (j + 2)) / 3072 := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlam : 0 ≤ lam := by linarith
  have hf4 : ((j + 4).factorial : ℝ) = ((j : ℝ) + 4) * ((j : ℝ) + 3) * (j + 2).factorial := by
    rw [show j + 4 = (j + 2) + 1 + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hψ : convolutionWeight (j + 4) ≤ convolutionWeight (j + 2) :=
    convolutionWeight_antitone (by omega)
  have hpoly : ((j : ℝ) + 4) * ((j : ℝ) + 3) ≤ 3 * ((j : ℝ) + 2) ^ 2 := by nlinarith
  have hf2 : (0 : ℝ) ≤ (j + 2).factorial := Nat.cast_nonneg _
  have hBp : 0 ≤ B ^ (j + 2) := pow_nonneg hB _
  have hψ0 := (convolutionWeight_pos (j + 4)).le
  have hψ2 := (convolutionWeight_pos (j + 2)).le
  set T := ((j + 2).factorial : ℝ) * M * convolutionWeight (j + 2) * B ^ (j + 2) with hT
  have hT0 : 0 ≤ T := by positivity
  have h1 : ((j + 2).factorial : ℝ) * M * convolutionWeight (j + 4) * B ^ (j + 2) ≤ T := by
    rw [hT]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψ (by positivity)) hBp
  have h2 : ((j : ℝ) + 4) * ((j : ℝ) + 3) * B ^ 2 *
      (((j + 2).factorial : ℝ) * M * convolutionWeight (j + 4) * B ^ (j + 2)) ≤
      3 * ((j : ℝ) + 2) ^ 2 * B ^ 2 * T :=
    mul_le_mul (mul_le_mul_of_nonneg_right hpoly (sq_nonneg B)) h1 (by positivity)
      (by positivity)
  have h3 : cM * (((j : ℝ) + 4) * ((j : ℝ) + 3) * B ^ 2 *
      (((j + 2).factorial : ℝ) * M * convolutionWeight (j + 4) * B ^ (j + 2))) ≤
      lam / 18432 * (3 * ((j : ℝ) + 2) ^ 2 * B ^ 2 * T) :=
    mul_le_mul hcM h2 (by positivity) (by positivity)
  have e : cM * M * ((j + 4).factorial * convolutionWeight (j + 4) * B ^ (j + 4)) =
      cM * (((j : ℝ) + 4) * ((j : ℝ) + 3) * B ^ 2 *
        (((j + 2).factorial : ℝ) * M * convolutionWeight (j + 4) * B ^ (j + 2))) := by
    rw [hf4]; ring
  have h4 : 0 ≤ ((j : ℝ) + 2) ^ 2 * B ^ 2 * lam * T := by positivity
  rw [e]
  linarith

/-- The bound on the remainder of order `j + 1` together with the term of order `j + 2`. -/
private theorem remainder_prev_le {j : ℕ} {cM lam M B : ℝ} (hcM0 : 0 ≤ cM)
    (hcM : cM ≤ lam / 18432) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    cM * ((j : ℝ) + 2) * B *
        (2 * ((j + 2).factorial * M * convolutionWeight (j + 2) * B ^ (j + 2))) +
      cM * M * ((j + 3).factorial * convolutionWeight (j + 3) * B ^ (j + 3)) ≤
      ((j : ℝ) + 2) * B * lam *
        ((j + 2).factorial * M * convolutionWeight (j + 2) * B ^ (j + 2)) / 216 := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hlam : 0 ≤ lam := by linarith
  have hf3 : ((j + 3).factorial : ℝ) = ((j : ℝ) + 3) * (j + 2).factorial := by
    rw [show j + 3 = (j + 2) + 1 from rfl, Nat.factorial_succ]
    push_cast
    ring
  have hψ : convolutionWeight (j + 3) ≤ convolutionWeight (j + 2) :=
    convolutionWeight_antitone (by omega)
  have hf2 : (0 : ℝ) ≤ (j + 2).factorial := Nat.cast_nonneg _
  have hBp : 0 ≤ B ^ (j + 2) := pow_nonneg hB _
  have hψ0 := (convolutionWeight_pos (j + 3)).le
  have hψ2 := (convolutionWeight_pos (j + 2)).le
  set T := ((j + 2).factorial : ℝ) * M * convolutionWeight (j + 2) * B ^ (j + 2) with hT
  have hT0 : 0 ≤ T := by positivity
  have h1 : ((j + 2).factorial : ℝ) * M * convolutionWeight (j + 3) * B ^ (j + 2) ≤ T := by
    rw [hT]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψ (by positivity)) hBp
  have h2 : ((j : ℝ) + 3) * B *
      (((j + 2).factorial : ℝ) * M * convolutionWeight (j + 3) * B ^ (j + 2)) ≤
      3 / 2 * ((j : ℝ) + 2) * B * T :=
    mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hB) h1 (by positivity) (by positivity)
  have e : cM * M * ((j + 3).factorial * convolutionWeight (j + 3) * B ^ (j + 3)) =
      cM * (((j : ℝ) + 3) * B *
        (((j + 2).factorial : ℝ) * M * convolutionWeight (j + 3) * B ^ (j + 2))) := by
    rw [hf3]; ring
  have h3 : cM * (((j : ℝ) + 3) * B *
      (((j + 2).factorial : ℝ) * M * convolutionWeight (j + 3) * B ^ (j + 2))) ≤
      cM * (3 / 2 * ((j : ℝ) + 2) * B * T) := mul_le_mul_of_nonneg_left h2 hcM0
  have h4 : cM * (7 / 2 * ((j : ℝ) + 2) * B * T) ≤
      lam / 18432 * (7 / 2 * ((j : ℝ) + 2) * B * T) :=
    mul_le_mul_of_nonneg_right hcM (by positivity)
  have h5 : 0 ≤ ((j : ℝ) + 2) * B * lam * T := by positivity
  rw [e]
  linarith

/-- The arithmetic of the improvement step at an interior maximum: from the Bernstein
inequality `hbern`, the bounds `hc2`, `hc1` on the two weighted cross terms and the bounds on
the constants, the value `X² + μ Xm²` of the Bernstein function is at most `T²`. -/
private theorem value_le_of_bernstein {lam m T Xp X Xm τ D D' κ₁ κ₂ P₂ P₁ : ℝ} (hlam : 0 < lam)
    (hm : 0 < m) (hT : 0 ≤ T) (hD0 : 0 ≤ D) (hD'0 : 0 ≤ D') (hXm0 : 0 ≤ Xm)
    (hbern : lam * Xp ^ 2 - 2 * P₂ - κ₁ * X ^ 2 +
      m ^ 2 / 32 * (lam * X ^ 2 - 2 * P₁ - κ₂ * Xm ^ 2) ≤ 0)
    (hc2 : P₂ ≤ X * (τ * Xp + D)) (hc1 : P₁ ≤ Xm * D') (hκ : κ₂ ≤ κ₁) (hX : X ≤ 2 * T)
    (hXm : m * Xm ≤ 9 / 2 * T) (hκ₁ : κ₁ ≤ m ^ 2 * lam / 486)
    (hτ : τ ^ 2 ≤ m ^ 2 * lam ^ 2 / 128) (hD : D ≤ m ^ 2 * lam * T / 3072)
    (hD' : D' ≤ m * lam * T / 216) : X ^ 2 + m ^ 2 / 32 * Xm ^ 2 ≤ T ^ 2 := by
  have hm2 : 0 ≤ m ^ 2 / 32 := by positivity
  have h3 : m ^ 2 / 32 * (κ₂ * Xm ^ 2) ≤ m ^ 2 / 32 * (κ₁ * Xm ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκ (sq_nonneg Xm)) hm2
  have h4 := mul_le_mul_of_nonneg_left hc1 hm2
  have hfin : lam * Xp ^ 2 + (m ^ 2 / 32 * lam - κ₁) * X ^ 2 ≤
      2 * X * (τ * Xp + D) + 2 * (m ^ 2 / 32) * (Xm * D') + m ^ 2 / 32 * κ₁ * Xm ^ 2 := by
    linarith
  have hXsq := sq_le_of_bernstein hlam hm hT hD0 hD'0 hfin hX hXm0 hXm hκ₁ hτ hD hD'
  have hmXm2 : (m * Xm) ^ 2 ≤ (9 / 2 * T) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hm.le hXm0) hXm 2
  have e : m ^ 2 / 32 * Xm ^ 2 = (m * Xm) ^ 2 / 32 := by ring
  have h9 : (9 / 2 * T) ^ 2 = 81 / 4 * T ^ 2 := by ring
  have hT2 : 0 ≤ T ^ 2 := sq_nonneg T
  rw [e]
  linarith

/-- **Bernstein inequality at a local maximum.** In the setting of `SolutionOnBall`, let `xs` be
a point of the closed ball where the function
`θ^{2j+4} |D^{j+2}v|² + μ θ^{2j+2} |D^{j+1}v|²` has a local maximum, `μ ≥ 0`. Then, with
`X i = θⁱ |Dⁱv|` at `xs`, with the operator `L` frozen at `xs` and the cross terms
`c_k = ∑_l |Dᵏv_l| |Dᵏ(L v_l)|`,
`λ X(j+3)² - 2 θ^{2j+6} c_{j+2} - κ₁ X(j+2)² + μ (λ X(j+2)² - 2 θ^{2j+4} c_{j+1} - κ₂ X(j+1)²) ≤ 0`,
where `κ₁`, `κ₂` are the Bernstein constants of the two weights times `Λ R²`. -/
theorem bernstein_at_isLocalMax {U : Set (ℝ^n)} {x₀ : ℝ^n} {R lam Lam C K μ : ℝ} {j : ℕ}
    (hS : SolutionOnBall a f v U x₀ R lam Lam C K) (hμ0 : 0 ≤ μ) {xs : ℝ^n}
    (hxs : xs ∈ closedBall x₀ R)
    (hloc : IsLocalMax (fun y ↦ ballWeight x₀ R y ^ (2 * j + 4) * familyNormSq (j + 2) v y +
      μ * (ballWeight x₀ R y ^ (2 * j + 2) * familyNormSq (j + 1) v y)) xs) :
    lam * weightedNorm x₀ R (j + 3) v xs ^ 2 -
        2 * (ballWeight x₀ R xs ^ (2 * (j + 2) + 2) *
          ∑ l, iteratedCoordinateNorm (j + 2) (fun z ↦ v z l) xs *
            iteratedCoordinateNorm (j + 2)
              (frozenOperator (fun i j ↦ a i j (v xs)) (fun z ↦ v z l)) xs) -
        bernsteinConstant n (2 * j + 2) * Lam * R ^ 2 * weightedNorm x₀ R (j + 2) v xs ^ 2 +
      μ * (lam * weightedNorm x₀ R (j + 2) v xs ^ 2 -
        2 * (ballWeight x₀ R xs ^ (2 * (j + 1) + 2) *
          ∑ l, iteratedCoordinateNorm (j + 1) (fun z ↦ v z l) xs *
            iteratedCoordinateNorm (j + 1)
              (frozenOperator (fun i j ↦ a i j (v xs)) (fun z ↦ v z l)) xs) -
        bernsteinConstant n (2 * j) * Lam * R ^ 2 * weightedNorm x₀ R (j + 1) v xs ^ 2) ≤ 0 := by
  have hlam := hS.lam_pos
  have hle (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hvx : ContDiffAt ℝ ∞ v xs :=
    hS.contDiffOn.contDiffAt (hS.isOpen.mem_nhds (hS.closedBall_subset hxs))
  have hxsn : ‖xs - x₀‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hxs
  have hP : ContDiffAt ℝ 2
      (fun z ↦ ballWeight x₀ R z ^ (2 * j + 4) * familyNormSq (j + 2) v z) xs :=
    ((contDiff_ballWeight x₀ R).contDiffAt.pow _).mul
      (ContDiffAt.familyNormSq (j + 2) (hvx.of_le (hle _)))
  have hQ : ContDiffAt ℝ 2
      (fun z ↦ ballWeight x₀ R z ^ (2 * j + 2) * familyNormSq (j + 1) v z) xs :=
    ((contDiff_ballWeight x₀ R).contDiffAt.pow _).mul
      (ContDiffAt.familyNormSq (j + 1) (hvx.of_le (hle _)))
  have hlow := hS.lower xs hxs
  have hup := hS.upper xs hxs
  -- the frozen operator is nonpositive at the maximum, and it is additive
  have hop := frozenOperator_nonpos_of_isLocalMax (A := fun i j ↦ a i j (v xs))
    (fun ξ ↦ (mul_nonneg hlam.le (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)).trans (hlow ξ))
    hloc (hP.add ((contDiffAt_const (c := μ)).mul hQ))
  rw [frozenOperator_add _ hP ((contDiffAt_const (c := μ)).mul hQ),
    frozenOperator_const_mul] at hop
  -- the Bernstein inequality for the two parts
  have hb1 := le_frozenOperator_ballWeight_pow_mul_familyNormSq
    (A := fun i j ↦ a i j (v xs)) (v := v) hlow hup hlam.le hS.Lam_nonneg hxsn (2 * j + 2)
    (j + 2) (hvx.of_le (hle _))
  have hb2 := le_frozenOperator_ballWeight_pow_mul_familyNormSq
    (A := fun i j ↦ a i j (v xs)) (v := v) hlow hup hlam.le hS.Lam_nonneg hxsn (2 * j)
    (j + 1) (hvx.of_le (hle _))
  simp only [Nat.add_assoc, Nat.reduceAdd] at hb1 hb2
  have hb2' := mul_le_mul_of_nonneg_left hb2 hμ0
  -- multiply by `θ²` and collect the powers of the weight
  obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = ballWeight x₀ R xs := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθd]; exact ballWeight_nonneg hxsn
  simp only [weightedNorm_sq]
  rw [← hθd] at hb1 hb2' ⊢
  have hsum := add_le_add hb1 hb2'
  have hmul := mul_le_mul_of_nonneg_left (hsum.trans hop) (sq_nonneg θ)
  have e3 : θ ^ (2 * (j + 3)) = θ ^ 2 * θ ^ (2 * j + 4) := by ring
  have e2 : θ ^ (2 * (j + 2)) = θ ^ 2 * θ ^ (2 * j + 2) := by ring
  have e1 : θ ^ (2 * (j + 1)) = θ ^ 2 * θ ^ (2 * j) := by ring
  have ec2 : θ ^ (2 * (j + 2) + 2) = θ ^ 2 * θ ^ (2 * j + 4) := by ring
  have ec1 : θ ^ (2 * (j + 1) + 2) = θ ^ 2 * θ ^ (2 * j + 2) := by ring
  rw [e3, e2, e1, ec2, ec1]
  linarith only [hmul]

/-- **The improvement step.** In the setting of `SolutionOnBall`, let `K M ≤ 1/8` and
`c M ≤ λ/18432` with the structure constant `c`, and let `B` satisfy `R² ≤ M B` and
`486 (2n + 52) Λ R² ≤ B² λ`. If the weighted bound of the first order holds with `M`, then the
weighted bounds of the orders up to `N` with the constant `2M` imply the same bounds with `M`.
For each order `j ≥ 2` the proof looks at an interior maximum of
`θ^{2j} |Dʲv|² + μ θ^{2j-2} |D^{j-1}v|²`. -/
theorem WeightedBound.improve {U : Set (ℝ^n)} {x₀ : ℝ^n} {R lam Lam C K M B : ℝ} {N : ℕ}
    (hS : SolutionOnBall a f v U x₀ R lam Lam C K) (hM : 0 < M) (hKM : K * M ≤ 1 / 8)
    (hcM : structureConstant n I C K * M ≤ lam / 18432) (hB : 0 < B) (hRB : R ^ 2 ≤ M * B)
    (hBκ : 486 * ((2 * n + 52) * (Lam * R ^ 2)) ≤ B ^ 2 * lam)
    (hbase : ∀ x ∈ ball x₀ R, weightedNorm x₀ R 1 v x ≤ M * convolutionWeight 1 * B)
    (h : WeightedBound v x₀ R (2 * M) B N) : WeightedBound v x₀ R M B N := by
  intro x hx i hi1 hiN
  rcases Nat.lt_or_ge i 2 with hi2 | hi2
  · obtain rfl : i = 1 := by omega
    simpa using hbase x hx
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  have hR := hS.radius_pos
  have hlam := hS.lam_pos
  have hcM0 : 0 ≤ structureConstant n I C K * M :=
    mul_nonneg (structureConstant_nonneg n I hS.C_nonneg hS.K_nonneg) hM.le
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hle (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hnorm (y : ℝ^n) (hy : y ∈ closedBall x₀ R) : ‖y - x₀‖ ≤ R := by
    rwa [mem_closedBall, dist_eq_norm] at hy
  -- the Bernstein function, continuous on the closed ball
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((j : ℝ) + 2) * B := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have hμ0 : 0 ≤ m ^ 2 / 32 := by positivity
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ^n → ℝ, Ψ = fun y ↦
      ballWeight x₀ R y ^ (2 * j + 4) * familyNormSq (j + 2) v y +
        m ^ 2 / 32 * (ballWeight x₀ R y ^ (2 * j + 2) * familyNormSq (j + 1) v y) := ⟨_, rfl⟩
  have hΨc : ContinuousOn Ψ (closedBall x₀ R) := by
    intro y hy
    have hvy : ContDiffAt ℝ ∞ v y :=
      hS.contDiffOn.contDiffAt (hS.isOpen.mem_nhds (hS.closedBall_subset hy))
    have h2 (k : ℕ) : ContinuousAt (familyNormSq k v) y :=
      (ContDiffAt.familyNormSq k (m := 0) (hvy.of_le (hle _))).continuousAt
    have hθc : ContinuousAt (ballWeight x₀ R) y :=
      (contDiff_ballWeight x₀ R (m := 0)).continuous.continuousAt
    rw [hΨ]
    exact (((hθc.pow _).mul (h2 _)).add
      (continuousAt_const.mul ((hθc.pow _).mul (h2 _)))).continuousWithinAt
  obtain ⟨xs, hxs, hmax⟩ := (isCompact_closedBall x₀ R).exists_isMaxOn
    ⟨x₀, mem_closedBall_self hR.le⟩ hΨc
  -- the target
  obtain ⟨T, hT⟩ : ∃ T : ℝ,
      T = (j + 2).factorial * M * convolutionWeight (j + 2) * B ^ (j + 2) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by
    have := (convolutionWeight_pos (j + 2)).le
    rw [hT]
    positivity
  -- the value at the maximum point is at most the square of the target
  have hclaim : Ψ xs ≤ T ^ 2 := by
    have hxsn : ‖xs - x₀‖ ≤ R := hnorm xs hxs
    have hθ0 : 0 ≤ ballWeight x₀ R xs := ballWeight_nonneg hxsn
    rcases hθ0.eq_or_lt with hθz | hθpos
    · -- on the sphere the function vanishes
      have hz : Ψ xs = 0 := by
        have h4 : 2 * j + 4 ≠ 0 := by omega
        have h2 : 2 * j + 2 ≠ 0 := by omega
        rw [hΨ]
        simp only [← hθz, zero_pow h4, zero_pow h2, zero_mul, mul_zero, add_zero]
      rw [hz]
      exact sq_nonneg T
    -- the maximum point is inside, so it is a local maximum
    have hxsb : xs ∈ ball x₀ R := by
      rw [mem_ball, dist_eq_norm]
      by_contra hcon
      have hRn : ‖xs - x₀‖ = R := le_antisymm hxsn (not_lt.mp hcon)
      rw [ballWeight, hRn, sub_self] at hθpos
      exact lt_irrefl _ hθpos
    have hloc : IsLocalMax Ψ xs := hmax.isLocalMax (closedBall_mem_nhds_of_mem hxsb)
    rw [hΨ] at hloc
    have hbern := bernstein_at_isLocalMax hS hμ0 hxs hloc
    -- the structure estimate for the two cross terms
    have hθB : ballWeight x₀ R xs ≤ M * B := (ballWeight_le x₀ R xs).trans hRB
    have hXs (i : ℕ) (h1 : 1 ≤ i) (hN : i ≤ N) : ballWeight x₀ R xs ^ i * familyNorm i v xs ≤
        i.factorial * (2 * M) * convolutionWeight i * B ^ i := h xs hxsb i h1 hN
    have hc2 := weighted_cross_le (k := j + 2) hS.isOpen (hS.closedBall_subset hxs)
      hS.contDiffOn hS.coeff_contDiffAt hS.forcing_contDiffAt hS.equation
      (hS.coeff_bound xs hxs) (hS.forcing_bound xs hxs) hS.C_nonneg hS.K_nonneg hM.le hB.le
      hθpos hθB hKM hXs (by omega) hiN
    have hc1 := weighted_cross_le (k := j + 1) hS.isOpen (hS.closedBall_subset hxs)
      hS.contDiffOn hS.coeff_contDiffAt hS.forcing_contDiffAt hS.equation
      (hS.coeff_bound xs hxs) (hS.forcing_bound xs hxs) hS.C_nonneg hS.K_nonneg hM.le hB.le
      hθpos hθB hKM hXs (by omega) (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd] at hc1 hc2
    -- names for the quantities at the maximum point
    obtain ⟨Xp, hXp⟩ : ∃ Xp : ℝ, Xp = weightedNorm x₀ R (j + 3) v xs := ⟨_, rfl⟩
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = weightedNorm x₀ R (j + 2) v xs := ⟨_, rfl⟩
    obtain ⟨Xm, hXm⟩ : ∃ Xm : ℝ, Xm = weightedNorm x₀ R (j + 1) v xs := ⟨_, rfl⟩
    obtain ⟨P₂, hP₂⟩ : ∃ P₂ : ℝ, P₂ = ballWeight x₀ R xs ^ (2 * (j + 2) + 2) *
        ∑ l, iteratedCoordinateNorm (j + 2) (fun z ↦ v z l) xs *
          iteratedCoordinateNorm (j + 2)
            (frozenOperator (fun i j ↦ a i j (v xs)) (fun z ↦ v z l)) xs := ⟨_, rfl⟩
    obtain ⟨P₁, hP₁⟩ : ∃ P₁ : ℝ, P₁ = ballWeight x₀ R xs ^ (2 * (j + 1) + 2) *
        ∑ l, iteratedCoordinateNorm (j + 1) (fun z ↦ v z l) xs *
          iteratedCoordinateNorm (j + 1)
            (frozenOperator (fun i j ↦ a i j (v xs)) (fun z ↦ v z l)) xs := ⟨_, rfl⟩
    change ballWeight x₀ R xs ^ (2 * (j + 2) + 2) * _ ≤
      weightedNorm x₀ R (j + 2) v xs * (_ * weightedNorm x₀ R (j + 3) v xs + _) at hc2
    change ballWeight x₀ R xs ^ (2 * (j + 1) + 2) * _ ≤
      weightedNorm x₀ R (j + 1) v xs * (_ * weightedNorm x₀ R (j + 2) v xs + _) at hc1
    rw [← hP₂, ← hX, ← hXp] at hc2
    rw [← hP₁, ← hXm, ← hX] at hc1
    rw [← hXp, ← hX, ← hXm, ← hP₂, ← hP₁] at hbern
    have hθ0' : 0 ≤ ballWeight x₀ R xs := hθpos.le
    have hX0 : 0 ≤ X := by
      rw [hX]; exact mul_nonneg (pow_nonneg hθ0' _) (familyNorm_nonneg _ _ _)
    have hXm0 : 0 ≤ Xm := by
      rw [hXm]; exact mul_nonneg (pow_nonneg hθ0' _) (familyNorm_nonneg _ _ _)
    -- the constants of the arithmetic lemma
    obtain ⟨cM, hcMd⟩ : ∃ cM : ℝ, cM = structureConstant n I C K * M := ⟨_, rfl⟩
    rw [← hcMd] at hcM hcM0
    have hc2' : P₂ ≤ X * (cM * ((j : ℝ) + 3) * B * Xp +
        cM * M * ((j + 4).factorial * convolutionWeight (j + 4) * B ^ (j + 4))) := by
      refine hc2.trans_eq ?_
      rw [hcMd]
      push_cast
      ring
    have hc1' : P₁ ≤ Xm * (cM * ((j : ℝ) + 2) * B * X +
        cM * M * ((j + 3).factorial * convolutionWeight (j + 3) * B ^ (j + 3))) := by
      refine hc1.trans_eq ?_
      rw [hcMd]
      push_cast
      ring
    have hX2T : X ≤ 2 * T := by
      have h2 := hXs (j + 2) (by omega) hiN
      rw [hX, hT]
      exact h2.trans_eq (by ring)
    have hXmb : Xm ≤ (j + 1).factorial * (2 * M) * convolutionWeight (j + 1) * B ^ (j + 1) := by
      rw [hXm]
      exact hXs (j + 1) (by omega) (by omega)
    -- the term of order `j + 2` in the second cross term is bounded by the hypothesis
    have hc1'' : P₁ ≤ Xm * (cM * ((j : ℝ) + 2) * B * (2 * T) +
        cM * M * ((j + 3).factorial * convolutionWeight (j + 3) * B ^ (j + 3))) := by
      refine hc1'.trans (mul_le_mul_of_nonneg_left ?_ hXm0)
      have h3 : cM * ((j : ℝ) + 2) * B * X ≤ cM * ((j : ℝ) + 2) * B * (2 * T) :=
        mul_le_mul_of_nonneg_left hX2T (by positivity)
      linarith only [h3]
    have hD0 : 0 ≤ cM * M * ((j + 4).factorial * convolutionWeight (j + 4) * B ^ (j + 4)) := by
      have := (convolutionWeight_pos (j + 4)).le
      positivity
    have hD'0 : 0 ≤ cM * ((j : ℝ) + 2) * B * (2 * T) +
        cM * M * ((j + 3).factorial * convolutionWeight (j + 3) * B ^ (j + 3)) := by
      have := (convolutionWeight_pos (j + 3)).le
      positivity
    have hDle : cM * M * ((j + 4).factorial * convolutionWeight (j + 4) * B ^ (j + 4)) ≤
        m ^ 2 * lam * T / 3072 := by
      rw [hm, hT]
      exact remainder_top_le hcM0 hcM hM.le hB.le
    have hD'le : cM * ((j : ℝ) + 2) * B * (2 * T) +
        cM * M * ((j + 3).factorial * convolutionWeight (j + 3) * B ^ (j + 3)) ≤
          m * lam * T / 216 := by
      rw [hm, hT]
      exact remainder_prev_le hcM0 hcM hM.le hB.le
    have hτle : (cM * ((j : ℝ) + 3) * B) ^ 2 ≤ m ^ 2 * lam ^ 2 / 128 := by
      rw [hm]
      exact top_sq_le hcM0 hcM hB.le
    have hmXm : m * Xm ≤ 9 / 2 * T := by
      rw [hm, hT]
      exact mul_prev_le hM.le hB.le hXmb
    have hLR : 0 ≤ Lam * R ^ 2 := mul_nonneg hS.Lam_nonneg (sq_nonneg R)
    have hκ21 : bernsteinConstant n (2 * j) * Lam * R ^ 2 ≤
        bernsteinConstant n (2 * j + 2) * Lam * R ^ 2 := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (bernsteinConstant_le_add_two n (2 * j)) hLR
    have hκle : bernsteinConstant n (2 * j + 2) * Lam * R ^ 2 ≤ m ^ 2 * lam / 486 := by
      have h1 := mul_le_mul_of_nonneg_right (bernsteinConstant_le n j) hLR
      have h2 := mul_le_mul_of_nonneg_left hBκ (sq_nonneg ((j : ℝ) + 2))
      rw [hm]
      linarith only [h1, h2]
    have hval : Ψ xs = X ^ 2 + m ^ 2 / 32 * Xm ^ 2 := by
      rw [hΨ, hX, hXm, weightedNorm_sq, weightedNorm_sq]
      beta_reduce
      ring
    rw [hval]
    exact value_le_of_bernstein hlam hm0 hT0 hD0 hD'0 hXm0 hbern hc2' hc1'' hκ21 hX2T hmXm hκle
      hτle hDle hD'le
  -- the bound at an arbitrary point of the ball
  have hxc : x ∈ closedBall x₀ R := ball_subset_closedBall hx
  have hθx : 0 ≤ ballWeight x₀ R x := ballWeight_nonneg (hnorm x hxc)
  have hΨx : weightedNorm x₀ R (j + 2) v x ^ 2 ≤ Ψ x := by
    rw [weightedNorm_sq, hΨ]
    have h0 : 0 ≤ m ^ 2 / 32 * (ballWeight x₀ R x ^ (2 * j + 2) * familyNormSq (j + 1) v x) :=
      mul_nonneg hμ0 (mul_nonneg (pow_nonneg hθx _) (familyNormSq_nonneg _ _ _))
    rw [show 2 * (j + 2) = 2 * j + 4 by ring]
    linarith only [h0]
  have hsq : weightedNorm x₀ R (j + 2) v x ^ 2 ≤ T ^ 2 := hΨx.trans ((hmax hxc).trans hclaim)
  have hw0 : 0 ≤ weightedNorm x₀ R (j + 2) v x :=
    mul_nonneg (pow_nonneg hθx _) (familyNorm_nonneg _ _ _)
  rw [← hT]
  exact (pow_le_pow_iff_left₀ hw0 hT0 two_ne_zero).mp hsq

end PDE.Elliptic.Regularity.Analytic
