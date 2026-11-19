/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolynomialBump.WeightedExpansion
import CAS.ExactTactic

/-!
# Expanding ball profiles with power decay

The squared radius grows as `r² + t`. A reciprocal natural-number power damps
the cubic bump, giving unit initial height and a lower bound on the expanding
half-ball which is a power of `r² / (r² + t)`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A normalized expanding cubic bump with a natural-number decay exponent. -/
def powerExpandingPolynomialBump (z : E) (r : ℝ) (p : ℕ) (x : E) (t : ℝ) : ℝ :=
  (r ^ 2) ^ p / (r ^ 2 + t) ^ (p + 3) * (r ^ 2 + t - ‖x - z‖ ^ 2)⁺ ^ 3

/-- The logarithmic derivative of the power amplitude. -/
theorem hasDerivAt_power_expansion_amplitude (r : ℝ) (p : ℕ) {t : ℝ}
    (ht : r ^ 2 + t ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (r ^ 2) ^ p / (r ^ 2 + s) ^ (p + 3))
      (-((p : ℝ) + 3) / (r ^ 2 + t) *
        ((r ^ 2) ^ p / (r ^ 2 + t) ^ (p + 3))) t := by
  have hbase : HasDerivAt (fun s : ℝ ↦ r ^ 2 + s) 1 t := by cas
  have hpow := hbase.pow (p + 3)
  convert! (hasDerivAt_const t ((r ^ 2) ^ p)).div hpow (pow_ne_zero _ ht) using 1
  simp only [Nat.cast_add, Nat.cast_ofNat, zero_mul, zero_sub,
    mul_one, pow_succ]
  cas using ht

/-- The power profile is jointly C² wherever its squared radius is positive. -/
theorem contDiffAt_powerExpandingPolynomialBump
    (z : E) (r : ℝ) (p : ℕ) (x : E) {t : ℝ} (ht : 0 < r ^ 2 + t) :
    ContDiffAt ℝ 2 (Function.uncurry (powerExpandingPolynomialBump z r p)) (x, t) := by
  unfold powerExpandingPolynomialBump
  refine contDiffAt_weightedPolynomialBallBump z (ρ := fun s ↦ r ^ 2 + s)
    (w := fun s ↦ (r ^ 2) ^ p / (r ^ 2 + s) ^ (p + 3))
    (contDiffAt_const.add contDiffAt_id) ?_
  exact contDiffAt_const.div ((contDiffAt_const.add contDiffAt_id).pow _) (pow_ne_zero _ ht.ne')

omit [InnerProductSpace ℝ E] in
/-- Exact temporal derivative of the power profile, including its support sphere. -/
theorem hasDerivAt_powerExpandingPolynomialBump
    (z : E) (r : ℝ) (p : ℕ) (x : E) {t : ℝ} (ht : r ^ 2 + t ≠ 0) :
    HasDerivAt (powerExpandingPolynomialBump z r p x)
      (((r ^ 2) ^ p / (r ^ 2 + t) ^ (p + 3)) *
        (-((p : ℝ) + 3) / (r ^ 2 + t) * (r ^ 2 + t - ‖x - z‖ ^ 2)⁺ ^ 3 +
          3 * (r ^ 2 + t - ‖x - z‖ ^ 2)⁺ ^ 2)) t := by
  have hbase : HasDerivAt (fun s : ℝ ↦ r ^ 2 + s) 1 t := by cas
  convert! hasDerivAt_weightedPolynomialBallBump z x hbase
    (hasDerivAt_power_expansion_amplitude r p ht) using 1
  cas

omit [InnerProductSpace ℝ E] in
/-- Nonnegativity of the power profile on the nonnegative-time slab. -/
theorem powerExpandingPolynomialBump_nonneg
    (z : E) (r : ℝ) (p : ℕ) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ powerExpandingPolynomialBump z r p x t := by
  unfold powerExpandingPolynomialBump
  positivity

omit [InnerProductSpace ℝ E] in
/-- The initial profile has height at most one. -/
theorem powerExpandingPolynomialBump_start_le_one
    (z : E) {r : ℝ} (hr : 0 < r) (p : ℕ) (x : E) :
    powerExpandingPolynomialBump z r p x 0 ≤ 1 := by
  have hgap : (r ^ 2 - ‖x - z‖ ^ 2)⁺ ^ 3 ≤ (r ^ 2) ^ 3 :=
    pow_le_pow_left₀ (posPart_nonneg _)
      (sup_le (sub_le_self _ (sq_nonneg _)) (sq_nonneg _)) 3
  unfold powerExpandingPolynomialBump
  rw [add_zero]
  calc
    _ ≤ (r ^ 2) ^ p / (r ^ 2) ^ (p + 3) * (r ^ 2) ^ 3 :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    _ = 1 := by
      rw [pow_add]
      have hp := pow_ne_zero p (pow_ne_zero 2 hr.ne')
      cas using hp

omit [InnerProductSpace ℝ E] in
/-- The expanding profile vanishes at and beyond its support sphere. -/
theorem powerExpandingPolynomialBump_eq_zero
    (z : E) {r t : ℝ} (p : ℕ) (x : E) (hout : r ^ 2 + t ≤ ‖x - z‖ ^ 2) :
    powerExpandingPolynomialBump z r p x t = 0 := by
  simp [powerExpandingPolynomialBump, posPart_eq_zero.mpr (sub_nonpos.mpr hout)]

omit [InnerProductSpace ℝ E] in
/-- A lower bound on the expanding half-ball with polynomial dependence on the
initial radius. The estimate also holds when the target space is trivial. -/
theorem powerExpandingPolynomialBump_halfBall_le
    (z : E) (r : ℝ) (p : ℕ) {x : E} {t : ℝ} (ht : 0 < r ^ 2 + t)
    (hx : x ∈ closedBall z (√(r ^ 2 + t) / 2)) :
    (r ^ 2 / (r ^ 2 + t)) ^ p / 8 ≤ powerExpandingPolynomialBump z r p x t := by
  have hxnorm : ‖x - z‖ ≤ √(r ^ 2 + t) / 2 := by
    simpa only [mem_closedBall, dist_eq_norm] using hx
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hxnorm
  have hgap : (r ^ 2 + t) / 2 ≤ (r ^ 2 + t - ‖x - z‖ ^ 2)⁺ := by
    have hsqrt := Real.sq_sqrt ht.le
    exact (by nlinarith : (r ^ 2 + t) / 2 ≤ r ^ 2 + t - ‖x - z‖ ^ 2).trans le_sup_left
  have hcube := pow_le_pow_left₀ (by positivity : 0 ≤ (r ^ 2 + t) / 2) hgap 3
  calc
    _ = (r ^ 2) ^ p / (r ^ 2 + t) ^ (p + 3) * ((r ^ 2 + t) / 2) ^ 3 := by
      rw [div_pow, pow_add]
      have hp := pow_ne_zero p ht.ne'
      cas using hp
    _ ≤ _ := mul_le_mul_of_nonneg_left hcube (by positivity)

end PDE.Analysis
