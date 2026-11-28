/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.MixedConvection
public import PDE.Spaces.Sobolev.Fractional.Integer.RealOrders

/-!
# The convection term between Sobolev spaces of real order, in three dimensions

The convection term `(u·∇)v` of the Navier–Stokes equations maps `H³ × H³` to `H²`. Does it map
`H^{σ+1} × H^{σ+1}` to `H^σ` for every real `σ ≥ 2`? A bootstrap that gains a fraction of a
derivative at each step applies the nonlinearity at orders that are not integers. This module
proves `‖(u·∇)v‖_{H^σ} ≲ ‖u‖_{H^{σ+1}} ‖v‖_{H^{σ+1}}` for every real `σ ≥ 2`, in three
dimensions, where the convection of the library lives. The tame form with `‖u‖_{H^σ}` in place
of `‖u‖_{H^{σ+1}}` and other dimensions are not treated. The product of two functions in `H^σ`,
`σ > n/2`, without derivatives and in every dimension, is
`SobolevSpace.Fractional.besselEnergy_mul_le_mul`.

## Main results

* `besselEnergy_mixedConvection_le`: for every integer `k ≥ 2`, every `u ∈ H^{k+1}`, every real
  `k ≤ σ ≤ k + 1` and every `v ∈ H³`, `E_σ((u·∇)v) ≤ (C ‖u‖_{H^{k+1}})² E_{σ+1}(v)`.
* `besselEnergy_convection_le`: for the same orders and all `u`, `v` in `H³` with
  `E_{k+1}(u) < ∞`, `E_σ((u·∇)v) ≤ C E_{k+1}(u) E_{σ+1}(v)`.
* `exists_besselEnergy_convection_le`: for every real `σ ≥ 2` there is `C` with
  `E_σ((u·∇)v) ≤ C E_{σ+1}(u) E_{σ+1}(v)` for all `u`, `v` in `H³`.

## How it works

Freeze the first factor. For `u ∈ H^{k+1}`, `k ≥ 2`, the operator `v ↦ (u·∇)v` loses one
derivative, and `mixedConvection` gives it at the integer orders `k` and `k + 1`, with norms at
most a constant times `‖u‖_{H^{k+1}}` and compatible when derivatives are forgotten
(`vectorLowerOrderCLM_mixedConvection`). An operator with such lifts is bounded from
`H^{σ+1}` to `H^σ` for `k ≤ σ ≤ k + 1` (`besselEnergy_le_of_lift_pair`). Only the second factor
is interpolated. The first factor is measured at the integer order `k + 1`, which is at most
`σ + 1`, so `‖(u·∇)v‖_{H^σ} ≲ ‖u‖_{H^{k+1}} ‖v‖_{H^{σ+1}} ≤ ‖u‖_{H^{σ+1}} ‖v‖_{H^{σ+1}}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open scoped ENNReal NNReal Sobolev

namespace NavierStokes.SobolevConvection

/-- The constant of the convection between the real orders `σ + 1` and `σ`, `k ≤ σ ≤ k + 1`. -/
def convectionOrderConst (k : ℕ) (hk : (3 : ℝ) < 2 * k) (hk' : (3 : ℝ) < 2 * (k + 1 : ℕ)) : ℝ :=
  orderConst 3 (k + 1) k * (‖mixedConvection k hk‖ + ‖mixedConvection (k + 1) hk'‖ + 1)

/-- The constant is positive. -/
theorem convectionOrderConst_pos (k : ℕ) (hk : (3 : ℝ) < 2 * k)
    (hk' : (3 : ℝ) < 2 * (k + 1 : ℕ)) : 0 < convectionOrderConst k hk hk' :=
  mul_pos (orderConst_pos 3 (k + 1) k) (by positivity)

/-- The convection of order `k` with the coefficient lowered from order `k + 1` is bounded by
the norm of the coefficient. -/
theorem norm_mixedConvection_vectorLower_le {k : ℕ} (hk : (3 : ℝ) < 2 * k)
    (U : VectorH 3 (k + 1)) :
    ‖mixedConvection k hk (vectorLower 3 k U)‖ ≤ ‖mixedConvection k hk‖ * ‖U‖ :=
  ((mixedConvection k hk).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_vectorLower_le U) (mixedConvection k hk).opNorm_nonneg)

/-- The convection of order `k` with the coefficient lowered from order `k + 1` lies over the
convection of order two. -/
private theorem vectorLowerOrderCLM_mixedConvection_vectorLower {k : ℕ}
    (h2 : (3 : ℝ) < 2 * (2 : ℕ)) (hk : (3 : ℝ) < 2 * k) (h2k : 2 ≤ k) (U : VectorH 3 (k + 1))
    (w : VectorH 3 (k + 1)) :
    vectorLowerOrderCLM h2k (mixedConvection k hk (vectorLower 3 k U) w) =
      mixedConvection 2 h2 (vectorLowerOrderCLM (h2k.trans (Nat.le_succ k)) U)
        (vectorLowerOrderCLM (Nat.succ_le_succ h2k) w) := by
  rw [vectorLowerOrderCLM_mixedConvection h2 hk h2k]
  exact congrArg (fun W ↦ mixedConvection 2 h2 W _)
    (vectorLowerOrderCLM_trans_apply h2k (Nat.le_succ k) U)

/-- The two lifts of the convection with a frozen coefficient are bounded by a common
constant times the norm of the coefficient. -/
private theorem norm_mixedConvection_lifts_le {k : ℕ} (hk : (3 : ℝ) < 2 * k)
    (hk' : (3 : ℝ) < 2 * (k + 1 : ℕ)) (U : VectorH 3 (k + 1)) :
    ‖mixedConvection k hk (vectorLower 3 k U)‖ ≤
        (‖mixedConvection k hk‖ + ‖mixedConvection (k + 1) hk'‖ + 1) * ‖U‖ ∧
      ‖mixedConvection (k + 1) hk' U‖ ≤
        (‖mixedConvection k hk‖ + ‖mixedConvection (k + 1) hk'‖ + 1) * ‖U‖ := by
  have ha : 0 ≤ ‖mixedConvection k hk‖ := (mixedConvection k hk).opNorm_nonneg
  have hb : 0 ≤ ‖mixedConvection (k + 1) hk'‖ := (mixedConvection (k + 1) hk').opNorm_nonneg
  have hu : 0 ≤ ‖U‖ := norm_nonneg U
  have h₀ := norm_mixedConvection_vectorLower_le hk U
  have h₁ := (mixedConvection (k + 1) hk').le_opNorm U
  generalize ‖mixedConvection k hk‖ = a at *
  generalize ‖mixedConvection (k + 1) hk'‖ = b at *
  generalize ‖U‖ = u at *
  exact ⟨by nlinarith [mul_nonneg hb hu], by nlinarith [mul_nonneg ha hu]⟩

/-- **The convection with a frozen coefficient, between real orders.** Let `k ≥ 2` and
`u ∈ H^{k+1}(ℝ³; ℝ³)`. Then, for every real `k ≤ σ ≤ k + 1` and every `v ∈ H³`,

`E_σ((u·∇)v) ≤ (C ‖u‖_{H^{k+1}})² E_{σ+1}(v)`, `C = convectionOrderConst k`.

The field `(u·∇)v` is the transport `mixedConvection 2` with the coefficient `u` lowered to
`H²`. -/
theorem besselEnergy_mixedConvection_le {k : ℕ} (h2 : (3 : ℝ) < 2 * (2 : ℕ))
    (hk : (3 : ℝ) < 2 * k) (hk' : (3 : ℝ) < 2 * (k + 1 : ℕ)) (h2k : 2 ≤ k)
    (U : VectorH 3 (k + 1)) {σ : ℝ} (hσ : (k : ℝ) ≤ σ) (hσ1 : σ ≤ k + 1) (v : VectorH 3 3) :
    besselEnergy σ (vectorBaseL2 (mixedConvection 2 h2
        (vectorLowerOrderCLM (h2k.trans (Nat.le_succ k)) U) v)) ≤
      ENNReal.ofReal ((convectionOrderConst k hk hk' * ‖U‖) ^ 2) *
        besselEnergy (σ + 1) (vectorBaseL2 v) := by
  rcases (norm_nonneg U).eq_or_lt with hzero | hpos
  · -- no coefficient: the convection vanishes
    rw [norm_eq_zero.mp hzero.symm, map_zero, map_zero, zero_apply, vectorBaseL2_zero,
      besselEnergy_fun_zero]
    exact zero_le
  -- the lifts at the orders `k` and `k + 1`
  have hK0 : 0 < (‖mixedConvection k hk‖ + ‖mixedConvection (k + 1) hk'‖ + 1) * ‖U‖ :=
    mul_pos (by
      have ha := (mixedConvection k hk).opNorm_nonneg
      have hb := (mixedConvection (k + 1) hk').opNorm_nonneg
      linarith) hpos
  obtain ⟨hn₀, hn₁⟩ := norm_mixedConvection_lifts_le hk hk' U
  have h := besselEnergy_le_of_lift_pair (d := 3) (e := 2) (j := k + 1) (l := k) rfl rfl
    (T := fun v : VectorH 3 3 ↦ mixedConvection 2 h2
      (vectorLowerOrderCLM (h2k.trans (Nat.le_succ k)) U) v)
    (fun x y ↦ map_add _ x y)
    (G₀ := mixedConvection k hk (vectorLower 3 k U)) (G₁ := mixedConvection (k + 1) hk' U)
    (vectorLowerOrderCLM_mixedConvection_vectorLower h2 hk h2k U)
    (vectorLowerOrderCLM_mixedConvection h2 hk' (h2k.trans (Nat.le_succ k)) U)
    hK0 hn₀ hn₁ hσ hσ1 v
  have e' : σ + ((k + 1 : ℕ) : ℝ) - (k : ℝ) = σ + 1 := by
    push_cast
    ring
  rw [e'] at h
  rw [convectionOrderConst, mul_assoc]
  exact h

/-- **The convection `(u·∇)v` from `H^{σ+1} × H^{σ+1}` to `H^σ`, at real orders.** Let `k ≥ 2`
and `k ≤ σ ≤ k + 1`. For all `u`, `v` in `H³(ℝ³; ℝ³)` with `E_{k+1}(u) < ∞`,

`E_σ((u·∇)v) ≤ C E_{k+1}(u) E_{σ+1}(v)`,

with a constant that depends on `k` only. Since `k + 1 ≤ σ + 1`, the first factor is controlled
by `E_{σ+1}(u)`. -/
theorem besselEnergy_convection_le {k : ℕ} (hk : (3 : ℝ) < 2 * k)
    (hk' : (3 : ℝ) < 2 * (k + 1 : ℕ)) (h2k : 2 ≤ k) {σ : ℝ} (hσ : (k : ℝ) ≤ σ)
    (hσ1 : σ ≤ k + 1) (u v : VectorH 3 3)
    (hu : besselEnergy ((k + 1 : ℕ) : ℝ) (vectorBaseL2 u) < ⊤) :
    besselEnergy σ (vectorBaseL2 (convection u v)) ≤
      ENNReal.ofReal ((convectionOrderConst k hk hk' * toWkpSpaceNormBound 3 (k + 1)) ^ 2) *
        (besselEnergy ((k + 1 : ℕ) : ℝ) (vectorBaseL2 u) *
          besselEnergy (σ + 1) (vectorBaseL2 v)) := by
  have h2 : (3 : ℝ) < 2 * (2 : ℕ) := by norm_num
  have h3k : 3 ≤ k + 1 := Nat.succ_le_succ h2k
  -- lift `u` to order `k + 1`
  rw [← vectorBaseL2_vectorLowerOrderCLM (Nat.zero_le 3) u] at hu
  obtain ⟨U, hU, hUn⟩ := exists_vectorH_of_besselEnergy_lt_top _ hu
  rw [vectorBaseL2_vectorLowerOrderCLM (Nat.zero_le 3) u] at hUn
  have hUu : vectorLowerOrderCLM h3k U = u := by
    apply vectorLowerOrderCLM_injective (Nat.zero_le 3) isOpen_univ
    rw [vectorLowerOrderCLM_trans_apply]
    exact hU
  have hconv : convection u v = mixedConvection 2 h2
      (vectorLowerOrderCLM (h2k.trans (Nat.le_succ k)) U) v := by
    rw [convection_eq_mixedConvection h2, ← hUu]
    exact congrArg (fun W ↦ mixedConvection 2 h2 W v)
      (vectorLowerOrderCLM_trans_apply (Nat.le_succ 2) h3k U)
  rw [hconv]
  refine (besselEnergy_mixedConvection_le h2 hk hk' h2k U hσ hσ1 v).trans ?_
  have hc := convectionOrderConst_pos k hk hk'
  have hB := toWkpSpaceNormBound_nonneg (n := 3) (k := k + 1)
  rw [← mul_assoc]
  refine mul_le_mul' ?_ le_rfl
  calc ENNReal.ofReal ((convectionOrderConst k hk hk' * ‖U‖) ^ 2)
      = ENNReal.ofReal (convectionOrderConst k hk hk' ^ 2) * ENNReal.ofReal (‖U‖ ^ 2) := by
        rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ ENNReal.ofReal (convectionOrderConst k hk hk' ^ 2) *
          (ENNReal.ofReal (toWkpSpaceNormBound 3 (k + 1) ^ 2) *
            besselEnergy ((k + 1 : ℕ) : ℝ) (vectorBaseL2 u)) := mul_le_mul' le_rfl hUn
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]

/-- **The convection `(u·∇)v` maps `H^{σ+1} × H^{σ+1}` to `H^σ` for every real `σ ≥ 2`**: there
is `C` such that, for all `u`, `v` in `H³(ℝ³; ℝ³)`,

`E_σ((u·∇)v) ≤ C E_{σ+1}(u) E_{σ+1}(v)`,

that is `‖(u·∇)v‖_{H^σ} ≲ ‖u‖_{H^{σ+1}} ‖v‖_{H^{σ+1}}`. Nothing is assumed finite: if one factor is
not in `H^{σ+1}` and the other is not zero, the right side is infinite, and if the other is
zero, both sides are zero. -/
theorem exists_besselEnergy_convection_le {σ : ℝ} (hσ : 2 ≤ σ) :
    ∃ C : ℝ≥0, ∀ u v : VectorH 3 3,
      besselEnergy σ (vectorBaseL2 (convection u v)) ≤
        C * (besselEnergy (σ + 1) (vectorBaseL2 u) * besselEnergy (σ + 1) (vectorBaseL2 v)) := by
  have hk2 : 2 ≤ ⌊σ⌋₊ := Nat.le_floor (by exact_mod_cast hσ)
  have hk2' : (2 : ℝ) ≤ (⌊σ⌋₊ : ℝ) := by exact_mod_cast hk2
  have hk : (3 : ℝ) < 2 * (⌊σ⌋₊ : ℝ) := by linarith
  have hk' : (3 : ℝ) < 2 * ((⌊σ⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hσk : ((⌊σ⌋₊ : ℕ) : ℝ) ≤ σ := Nat.floor_le (by linarith)
  have hle : ((⌊σ⌋₊ + 1 : ℕ) : ℝ) ≤ σ + 1 := by
    push_cast
    linarith
  refine ⟨((convectionOrderConst ⌊σ⌋₊ hk hk' *
    toWkpSpaceNormBound 3 (⌊σ⌋₊ + 1)) ^ 2).toNNReal + 1, fun u v ↦ ?_⟩
  by_cases hu : besselEnergy (σ + 1) (vectorBaseL2 u) < ⊤
  · refine (besselEnergy_convection_le hk hk' hk2 hσk (Nat.lt_floor_add_one σ).le u v
      ((besselEnergy_mono hle _).trans_lt hu)).trans ?_
    exact mul_le_mul' (ENNReal.coe_le_coe.2 le_self_add)
      (mul_le_mul' (besselEnergy_mono hle _) le_rfl)
  · rw [not_lt, top_le_iff] at hu
    by_cases hv : besselEnergy (σ + 1) (vectorBaseL2 v) = 0
    · -- the second factor is zero, and so is the convection
      have hv0 : v = 0 := vectorBaseL2_injective
        ((besselEnergy_eq_zero_iff.1 hv).trans vectorBaseL2_zero.symm)
      have h0 : besselEnergy σ (vectorBaseL2 (convection u v)) = 0 := by
        rw [hv0, map_zero, vectorBaseL2_zero]
        exact besselEnergy_fun_zero σ
      rw [h0]
      exact zero_le
    · rw [hu, ENNReal.top_mul hv, ENNReal.mul_top (by simp)]
      exact le_top

end NavierStokes.SobolevConvection
