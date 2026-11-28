/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Analytic.Improvement
public import PDE.FDeriv.PartialDeriv.HigherNormSq.Analytic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Factorial derivative bounds for solutions of the autonomous diagonal system

## Motivation

Does a smooth solution `v` of the system `∑ᵢ ∂ᵢ (∑ⱼ aᵢⱼ(v) ∂ⱼ v_l - f_{l i}(v)) = 0`, with
elliptic coefficients whose derivatives along `v` grow at most like `m! C Kᵐ`, have derivatives
of size `i! M K₀ⁱ` near a point?

## The idea

Yes. Fix a closed ball where the hypotheses hold (`SolutionOnBall`), with weight `θ`. For a
fixed number `N` of derivatives the weighted bounds `θⁱ |Dⁱv| ≤ i! M ψ(i) Bⁱ`, `1 ≤ i ≤ N`, hold
for some large `B`, because finitely many continuous functions are bounded on the closed ball.
Lowering `B` by a factor `q` with `q^N ≤ 2` costs at most a factor `2` in `M`, and the
improvement step `WeightedBound.improve` gives the factor back, as long as `B` stays above a
threshold `B₀` that does not depend on `N`. So the bounds descend to `B₀`, for every `N`, with
the same `M` and `B₀`. On the ball of half the radius the weight is at least `3R²/4`, which
turns the weighted bounds into `|Dⁱv| ≤ i! M K₀ⁱ`, and such bounds make `v` analytic.

## Main results

* `SolutionOnBall.exists_weightedBound`: there are `M`, `B` with the weighted bounds of all
  orders on the ball. For all solutions as in `SolutionOnBall`.
* `SolutionOnBall.exists_familyNorm_le`: `|Dⁱv| ≤ i! M K₀ⁱ` on the ball of half the radius, for
  all `i ≥ 1`.
* `SolutionOnBall.analyticAt`: the solution is real-analytic at the centre.

## Relations

`SolutionOnBall.analyticAt` is `SolutionOnBall.exists_familyNorm_le` followed by
`PDE.analyticAt_of_iteratedCoordinateNorm_le`. The descent uses `WeightedBound.improve` once
for every step. The statement for an open set and analytic coefficients is
`PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_autonomous_system`.

## What stays open

The constants `M`, `K₀` are not explicit.

## References

* S. Blatt, *On the analyticity of solutions to non-linear elliptic partial differential
  equations*, arXiv:2009.08762v2, 2024, §3 (weighted derivatives and a recursion; there the
  recursion is closed by a majorant differential equation, here by the descent in `B`).
  <https://arxiv.org/abs/2009.08762>
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped ContDiff Topology
open PDE.Analysis

namespace PDE.Elliptic.Regularity.Analytic

variable {n : ℕ} {I : Type*} [Fintype I] {a : Fin n → Fin n → (I → ℝ) → ℝ}
  {f : I → Fin n → (I → ℝ) → ℝ} {v : ℝ^n → I → ℝ} {U : Set (ℝ^n)} {x₀ : ℝ^n}
  {R lam Lam C K : ℝ}

/-- The weighted bounds persist when `B` grows. -/
theorem WeightedBound.mono {M B B' : ℝ} {N : ℕ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hBB' : B ≤ B')
    (h : WeightedBound v x₀ R M B N) : WeightedBound v x₀ R M B' N := by
  intro x hx i hi1 hiN
  refine (h x hx i hi1 hiN).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hBB' i)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) (convolutionWeight_pos i).le)

/-- Lowering `B` by a factor `q` with `q^N ≤ 2` costs at most a factor `2` in `M`. -/
theorem WeightedBound.scale {M B q : ℝ} {N : ℕ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hq : 1 ≤ q)
    (hqN : q ^ N ≤ 2) (h : WeightedBound v x₀ R M (B * q) N) :
    WeightedBound v x₀ R (2 * M) B N := by
  intro x hx i hi1 hiN
  refine (h x hx i hi1 hiN).trans ?_
  have hqi : q ^ i ≤ 2 := (pow_le_pow_right₀ hq hiN).trans hqN
  have hw : 0 ≤ (i.factorial : ℝ) * M * convolutionWeight i * B ^ i :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) (convolutionWeight_pos i).le)
      (pow_nonneg hB i)
  calc (i.factorial : ℝ) * M * convolutionWeight i * (B * q) ^ i
      = (i.factorial * M * convolutionWeight i * B ^ i) * q ^ i := by rw [mul_pow]; ring
    _ ≤ (i.factorial * M * convolutionWeight i * B ^ i) * 2 := mul_le_mul_of_nonneg_left hqi hw
    _ = _ := by ring

/-- The factor `1 + 1/(2N + 1)` has `N`-th power at most `2`. -/
theorem one_add_inv_pow_le_two (N : ℕ) : (1 + 1 / (2 * (N : ℝ) + 1)) ^ N ≤ 2 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : 1 + 1 / (2 * (N : ℝ) + 1) ≤ Real.exp (1 / (2 * (N : ℝ) + 1)) := by
    have := Real.add_one_le_exp (1 / (2 * (N : ℝ) + 1))
    linarith
  have h2 : (1 + 1 / (2 * (N : ℝ) + 1)) ^ N ≤ Real.exp (1 / (2 * (N : ℝ) + 1)) ^ N :=
    pow_le_pow_left₀ (by positivity) h1 N
  have h3 : Real.exp (1 / (2 * (N : ℝ) + 1)) ^ N = Real.exp (N * (1 / (2 * (N : ℝ) + 1))) :=
    (Real.exp_nat_mul _ N).symm
  have h4 : (N : ℝ) * (1 / (2 * (N : ℝ) + 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h5 : Real.exp (N * (1 / (2 * (N : ℝ) + 1))) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr h4
  have h6 : Real.exp (1 / 2) ≤ 2 := by
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have hlt := Real.exp_one_lt_d9
    have hpos := Real.exp_pos (1 / 2)
    by_contra hcon
    have hgt : 2 < Real.exp (1 / 2) := not_le.mp hcon
    nlinarith
  rw [h3] at h2
  exact h2.trans (h5.trans h6)

/-- **The descent in `B`.** If the weighted bounds with `2M` improve to `M` for every `B` above
a threshold `B₀`, then the weighted bounds with `M` at any `B₁` hold at `B₀` too. Each step
lowers `B` by the factor `1 + 1/(2N + 1)`, whose `N`-th power is at most `2`. -/
theorem WeightedBound.descend {M B₀ B₁ : ℝ} {N : ℕ} (hM : 0 ≤ M) (hB₀ : 0 < B₀)
    (himp : ∀ B, B₀ ≤ B → WeightedBound v x₀ R (2 * M) B N → WeightedBound v x₀ R M B N)
    (hB₁ : 0 ≤ B₁) (h : WeightedBound v x₀ R M B₁ N) : WeightedBound v x₀ R M B₀ N := by
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 + 1 / (2 * (N : ℝ) + 1) := ⟨_, rfl⟩
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hq1 : 1 < q := by
    have : (0 : ℝ) < 1 / (2 * (N : ℝ) + 1) := by positivity
    rw [hqdef]
    linarith
  have hqN : q ^ N ≤ 2 := hqdef ▸ one_add_inv_pow_le_two N
  -- the descent, one factor `q` at a time
  have hstep : ∀ t : ℕ, WeightedBound v x₀ R M (B₀ * q ^ t) N → WeightedBound v x₀ R M B₀ N := by
    intro t
    induction t with
    | zero => intro ht; simpa using ht
    | succ t ih =>
      intro ht
      have hpos : 0 ≤ B₀ * q ^ t := mul_nonneg hB₀.le (pow_nonneg (by linarith) t)
      have hle : B₀ ≤ B₀ * q ^ t :=
        le_mul_of_one_le_right hB₀.le (one_le_pow₀ hq1.le)
      refine ih (himp _ hle (WeightedBound.scale hM hpos hq1.le hqN ?_))
      rwa [mul_assoc, ← pow_succ]
  -- start high enough
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (B₁ / B₀) hq1
  refine hstep t (h.mono hM hB₁ ?_)
  rw [div_lt_iff₀ hB₀] at ht
  linarith

/-- In the setting of `SolutionOnBall` the family norm of every order is bounded on the closed
ball. -/
theorem SolutionOnBall.exists_familyNorm_bound (hS : SolutionOnBall a f v U x₀ R lam Lam C K)
    (k : ℕ) : ∃ S : ℝ, 0 ≤ S ∧ ∀ x ∈ closedBall x₀ R, familyNorm k v x ≤ S := by
  have hcont : ContinuousOn (familyNormSq k v) (closedBall x₀ R) := by
    intro y hy
    have hvy : ContDiffAt ℝ ∞ v y :=
      hS.contDiffOn.contDiffAt (hS.isOpen.mem_nhds (hS.closedBall_subset hy))
    have h0 : ContDiffAt ℝ ((0 : ℕ) : WithTop ℕ∞) (familyNormSq k v) y :=
      ContDiffAt.familyNormSq k (hvy.of_le (by exact_mod_cast le_top))
    exact h0.continuousAt.continuousWithinAt
  obtain ⟨S, hS'⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn hcont
  refine ⟨√|S|, Real.sqrt_nonneg _, fun x hx ↦ Real.sqrt_le_sqrt ?_⟩
  exact (le_abs_self _).trans ((hS' x hx).trans (le_abs_self S))

/-- **Weighted derivative bounds of all orders.** In the setting of `SolutionOnBall` there are
`M > 0` and `B > 0` such that `θⁱ |Dⁱv| ≤ i! M ψ(i) Bⁱ` on the open ball for all `i ≥ 1`. For a
fixed number of orders the bounds hold for a large `B`, and the improvement step lets `B`
descend to a threshold that does not depend on the number of orders. -/
theorem SolutionOnBall.exists_weightedBound (hS : SolutionOnBall a f v U x₀ R lam Lam C K) :
    ∃ M B : ℝ, 0 < M ∧ 0 < B ∧ ∀ N, WeightedBound v x₀ R M B N := by
  have hR := hS.radius_pos
  have hlam := hS.lam_pos
  have hK := hS.K_nonneg
  have hcS := structureConstant_nonneg n I hS.C_nonneg hS.K_nonneg
  have hLR : 0 ≤ Lam * R ^ 2 := mul_nonneg hS.Lam_nonneg (sq_nonneg R)
  choose S hS0 hSb using fun k ↦ hS.exists_familyNorm_bound k
  have hnorm (y : ℝ^n) (hy : y ∈ closedBall x₀ R) : ‖y - x₀‖ ≤ R := by
    rwa [mem_closedBall, dist_eq_norm] at hy
  -- the small constant
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = min (1 / (8 * (K + 1)))
      (lam / (18432 * (structureConstant n I C K + 1))) := ⟨_, rfl⟩
  have hM : 0 < M := by
    rw [hMdef]
    exact lt_min (by positivity) (by positivity)
  have hKM : K * M ≤ 1 / 8 := by
    have h1 : M ≤ 1 / (8 * (K + 1)) := hMdef ▸ min_le_left _ _
    have h2 : K / (K + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    calc K * M ≤ K * (1 / (8 * (K + 1))) := mul_le_mul_of_nonneg_left h1 hK
      _ = K / (K + 1) / 8 := by field_simp
      _ ≤ 1 / 8 := by linarith
  have hcM : structureConstant n I C K * M ≤ lam / 18432 := by
    have h1 : M ≤ lam / (18432 * (structureConstant n I C K + 1)) := hMdef ▸ min_le_right _ _
    have h2 : structureConstant n I C K / (structureConstant n I C K + 1) ≤ 1 :=
      (div_le_one (by linarith)).mpr (by linarith)
    calc structureConstant n I C K * M
        ≤ structureConstant n I C K * (lam / (18432 * (structureConstant n I C K + 1))) :=
          mul_le_mul_of_nonneg_left h1 hcS
      _ = lam / 18432 * (structureConstant n I C K / (structureConstant n I C K + 1)) := by
          field_simp
      _ ≤ lam / 18432 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = lam / 18432 := mul_one _
  -- the threshold for `B`
  have hψ1 := convolutionWeight_pos 1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨B₀, hB₀def⟩ : ∃ B₀ : ℝ, B₀ = 1 + R ^ 2 / M +
      486 * ((2 * n + 52) * (Lam * R ^ 2)) / lam + R ^ 2 * S 1 / (M * convolutionWeight 1) :=
    ⟨_, rfl⟩
  have ht1 : 0 ≤ R ^ 2 / M := by positivity
  have ht2 : 0 ≤ 486 * ((2 * n + 52) * (Lam * R ^ 2)) / lam := by positivity
  have ht3 : 0 ≤ R ^ 2 * S 1 / (M * convolutionWeight 1) := by
    have := hS0 1
    positivity
  have hB₀1 : 1 ≤ B₀ := by rw [hB₀def]; linarith
  -- the improvement step applies to every `B ≥ B₀`
  have himp (N : ℕ) (B : ℝ) (hB : B₀ ≤ B) (h : WeightedBound v x₀ R (2 * M) B N) :
      WeightedBound v x₀ R M B N := by
    have hB1 : 1 ≤ B := hB₀1.trans hB
    have hB0 : 0 < B := by linarith
    refine h.improve hS hM hKM hcM hB0 ?_ ?_ ?_
    · have h1 : R ^ 2 / M ≤ B := by rw [hB₀def] at hB; linarith
      calc R ^ 2 = M * (R ^ 2 / M) := by field_simp
        _ ≤ M * B := mul_le_mul_of_nonneg_left h1 hM.le
    · have h1 : 486 * ((2 * n + 52) * (Lam * R ^ 2)) / lam ≤ B := by
        rw [hB₀def] at hB; linarith
      have h2 : 486 * ((2 * n + 52) * (Lam * R ^ 2)) ≤ B * lam := (div_le_iff₀ hlam).mp h1
      have h3 : B * lam ≤ B ^ 2 * lam := by
        have : B ≤ B ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hlam.le
      linarith
    · intro x hx
      have hxc : x ∈ closedBall x₀ R := ball_subset_closedBall hx
      have hθ0 : 0 ≤ ballWeight x₀ R x := ballWeight_nonneg (hnorm x hxc)
      have h1 : R ^ 2 * S 1 / (M * convolutionWeight 1) ≤ B := by
        rw [hB₀def] at hB; linarith
      have h2 : R ^ 2 * S 1 ≤ B * (M * convolutionWeight 1) :=
        (div_le_iff₀ (by positivity)).mp h1
      calc weightedNorm x₀ R 1 v x = ballWeight x₀ R x * familyNorm 1 v x := by
            simp [weightedNorm]
        _ ≤ R ^ 2 * S 1 :=
            mul_le_mul (ballWeight_le x₀ R x) (hSb 1 x hxc) (familyNorm_nonneg _ _ _)
              (sq_nonneg R)
        _ ≤ B * (M * convolutionWeight 1) := h2
        _ = M * convolutionWeight 1 * B := by ring
  refine ⟨M, B₀, hM, by linarith, fun N ↦ ?_⟩
  -- for the orders up to `N` the bounds hold for a large `B₁`
  obtain ⟨B₁, hB₁def⟩ : ∃ B₁ : ℝ, B₁ = B₀ + ∑ i ∈ Finset.range (N + 1),
      R ^ (2 * i) * S i / (M * convolutionWeight i) := ⟨_, rfl⟩
  have hterm0 (i : ℕ) : 0 ≤ R ^ (2 * i) * S i / (M * convolutionWeight i) := by
    have := convolutionWeight_pos i
    have := hS0 i
    positivity
  have hB₁ : B₀ ≤ B₁ := by
    rw [hB₁def]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hterm0 i)
  have hB₁1 : 1 ≤ B₁ := hB₀1.trans hB₁
  have hbd : WeightedBound v x₀ R M B₁ N := by
    intro x hx i hi1 hiN
    have hxc : x ∈ closedBall x₀ R := ball_subset_closedBall hx
    have hθ0 : 0 ≤ ballWeight x₀ R x := ballWeight_nonneg (hnorm x hxc)
    have hψi := convolutionWeight_pos i
    have hterm : R ^ (2 * i) * S i / (M * convolutionWeight i) ≤ B₁ := by
      have h1 := Finset.single_le_sum (f := fun i ↦ R ^ (2 * i) * S i / (M * convolutionWeight i))
        (fun i _ ↦ hterm0 i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hiN))
      rw [hB₁def]
      linarith
    have h2 : R ^ (2 * i) * S i ≤ B₁ * (M * convolutionWeight i) :=
      (div_le_iff₀ (by positivity)).mp hterm
    have hfac : (1 : ℝ) ≤ i.factorial := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos i)
    have hpow : B₁ ≤ B₁ ^ i := le_self_pow₀ hB₁1 (by omega)
    have hMψ : 0 ≤ M * convolutionWeight i := by positivity
    calc weightedNorm x₀ R i v x
        ≤ (R ^ 2) ^ i * S i :=
          mul_le_mul (pow_le_pow_left₀ hθ0 (ballWeight_le x₀ R x) i) (hSb i x hxc)
            (familyNorm_nonneg _ _ _) (by positivity)
      _ = R ^ (2 * i) * S i := by rw [← pow_mul]
      _ ≤ B₁ * (M * convolutionWeight i) := h2
      _ ≤ B₁ ^ i * (M * convolutionWeight i) := mul_le_mul_of_nonneg_right hpow hMψ
      _ = 1 * (M * convolutionWeight i * B₁ ^ i) := by ring
      _ ≤ i.factorial * (M * convolutionWeight i * B₁ ^ i) :=
          mul_le_mul_of_nonneg_right hfac (by positivity)
      _ = _ := by ring
  exact hbd.descend hM.le (by linarith) (himp N) (by linarith)

/-- **Factorial derivative bounds.** In the setting of `SolutionOnBall` there are `M > 0` and
`K₀ > 0` such that `|Dⁱv(x)| ≤ i! M K₀ⁱ` in the family norm for all `i ≥ 1` and all `x` in the
ball of half the radius. There the weight is at least `3R²/4`. -/
theorem SolutionOnBall.exists_familyNorm_le (hS : SolutionOnBall a f v U x₀ R lam Lam C K) :
    ∃ M K₀ : ℝ, 0 < M ∧ 0 < K₀ ∧ ∀ i, 1 ≤ i → ∀ x ∈ ball x₀ (R / 2),
      familyNorm i v x ≤ i.factorial * M * K₀ ^ i := by
  have hR := hS.radius_pos
  obtain ⟨M, B, hM, hB, hw⟩ := hS.exists_weightedBound
  refine ⟨M, 4 * B / (3 * R ^ 2), hM, by positivity, fun i hi x hx ↦ ?_⟩
  have hxn : ‖x - x₀‖ < R / 2 := by rwa [mem_ball, dist_eq_norm] at hx
  have hxR : x ∈ ball x₀ R := ball_subset_ball (by linarith) hx
  -- the weight is at least `3R²/4`
  have hθ : 3 * R ^ 2 / 4 ≤ ballWeight x₀ R x := by
    have h1 : ‖x - x₀‖ ^ 2 ≤ (R / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxn.le 2
    unfold ballWeight
    nlinarith
  have hθpos : 0 < ballWeight x₀ R x := lt_of_lt_of_le (by positivity) hθ
  have hwi := hw i x hxR i hi le_rfl
  have hψ : convolutionWeight i ≤ 1 := convolutionWeight_le_one i
  have hψ0 := (convolutionWeight_pos i).le
  have hfac : (0 : ℝ) ≤ i.factorial := Nat.cast_nonneg _
  -- divide the weighted bound by the weight
  have h1 : (3 * R ^ 2 / 4) ^ i * familyNorm i v x ≤ i.factorial * M * B ^ i := by
    calc (3 * R ^ 2 / 4) ^ i * familyNorm i v x
        ≤ ballWeight x₀ R x ^ i * familyNorm i v x :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hθ i)
            (familyNorm_nonneg _ _ _)
      _ ≤ i.factorial * M * convolutionWeight i * B ^ i := hwi
      _ ≤ i.factorial * M * 1 * B ^ i :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hψ (by positivity))
            (by positivity)
      _ = _ := by ring
  have hpos : 0 < (3 * R ^ 2 / 4) ^ i := by positivity
  calc familyNorm i v x = (3 * R ^ 2 / 4) ^ i * familyNorm i v x / (3 * R ^ 2 / 4) ^ i := by
        field_simp
    _ ≤ i.factorial * M * B ^ i / (3 * R ^ 2 / 4) ^ i := div_le_div_of_nonneg_right h1 hpos.le
    _ = i.factorial * M * (4 * B / (3 * R ^ 2)) ^ i := by
        have hRne : R ≠ 0 := hR.ne'
        have e : 4 * B / (3 * R ^ 2) = B / (3 * R ^ 2 / 4) := by field_simp
        rw [e, div_pow B, mul_div_assoc]

/-- **Analyticity at the centre.** In the setting of `SolutionOnBall` the solution `v` is
real-analytic at `x₀`. The factorial bounds of `SolutionOnBall.exists_familyNorm_le` hold for
each component, and such bounds give a convergent Taylor series. -/
theorem SolutionOnBall.analyticAt (hS : SolutionOnBall a f v U x₀ R lam Lam C K) :
    AnalyticAt ℝ v x₀ := by
  have hR := hS.radius_pos
  obtain ⟨M, K₀, _, _, hb⟩ := hS.exists_familyNorm_le
  have hsub : ball x₀ (R / 2) ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans
      hS.closedBall_subset
  have hv : ContDiffOn ℝ ∞ v (ball x₀ (R / 2)) := hS.contDiffOn.mono hsub
  refine analyticAt_pi_iff.mpr fun l ↦ ?_
  refine analyticAt_of_iteratedCoordinateNorm_le (r := R / 2) (M := M) (K := K₀) (by linarith)
    (contDiffOn_pi.mp hv l) fun i hi x hx ↦ ?_
  exact (iteratedCoordinateNorm_apply_le_familyNorm i v x l).trans (hb i hi x hx)

end PDE.Elliptic.Regularity.Analytic
