/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Dirichlet.IntegralBound
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Iteration

/-!
# Stampacchia's superlevel iteration

The estimate `‖(u-k)₊‖q ≤ C |{u>k}|^(1-1/q)`, with `q>2`, gives a
uniform upper bound. Chebyshev's inequality produces a superlinear
recurrence for the level-set measures. Its initial value is made small
using the estimate at level zero, so the resulting bound depends only
on `C`, `q` and the total measure, rather than on the function.

This is the measure iteration in Stampacchia's truncation argument for
the boundedness of scalar elliptic Dirichlet solutions.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.Elliptic.Regularity.DeGiorgi

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
private theorem superlevel_measure_step
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞) {f : X → ℝ}
    {C k h : ℝ} (hC : 0 ≤ C) (hkh : k < h)
    (hf : MemLp (fun x ↦ max (f x - k) 0) q μ)
    (hnorm : (eLpNorm (fun x ↦ max (f x - k) 0) q μ).toReal ≤
      C * μ.real {x | k < f x} ^ (1 - 1 / q.toReal)) :
    (h - k) ^ q.toReal * μ.real {x | h < f x} ≤
      C ^ q.toReal * μ.real {x | k < f x} ^ (q.toReal - 1) := by
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  have hm := measure_mul_rpow_le_eLpNorm hq0 hqt hf (sub_pos.mpr hkh)
    (E := {x | h < f x}) (Filter.Eventually.of_forall fun x hx ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact (sub_le_sub_right hx.le k).trans (le_max_left _ _))
  have hp := Real.rpow_le_rpow ENNReal.toReal_nonneg hnorm hqr.le
  rw [Real.mul_rpow hC (Real.rpow_nonneg measureReal_nonneg _),
    ← Real.rpow_mul measureReal_nonneg] at hp
  have he : (1 - 1 / q.toReal) * q.toReal = q.toReal - 1 := by
    field_simp
  rw [he] at hp
  exact hm.trans hp

/-- A superlevel Sobolev bound with a strict integrability gain gives a
uniform almost-everywhere upper bound. The bound is chosen before the
function and depends only on the displayed constant, exponent and measure. -/
theorem exists_upper_bound_of_superlevel_eLpNorm
    {q : ℝ≥0∞} (hq : 2 < q) (hqt : q ≠ ∞) {C : ℝ} (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : X → ℝ,
      (∀ k : ℝ, 0 ≤ k →
        MemLp (fun x ↦ max (f x - k) 0) q μ ∧
          (eLpNorm (fun x ↦ max (f x - k) 0) q μ).toReal ≤
            C * μ.real {x | k < f x} ^ (1 - 1 / q.toReal)) →
      ∀ᵐ x ∂μ, f x ≤ K := by
  have hq0 : q ≠ 0 := (lt_trans (by norm_num) hq).ne'
  have hqr : 2 < q.toReal := by
    simpa only [ENNReal.toReal_ofNat] using
      (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hqt).mpr hq
  have hqr0 : 0 < q.toReal := by linarith
  let B := (2 : ℝ) ^ q.toReal
  have hB : 0 < B := by positivity
  obtain ⟨ε, hε, hiteration⟩ := exists_small_energy_threshold
    (mul_pos (Real.rpow_pos_of_pos hC q.toReal) hB) hB
      (show 0 < q.toReal - 2 by linarith)
  let D := C ^ q.toReal * μ.real univ ^ (q.toReal - 1)
  have hD : 0 ≤ D := by positivity
  let k₀ := (D / ε) ^ q.toReal⁻¹ + 1
  have hk₀ : 0 < k₀ := by positivity
  have hscale : D ≤ k₀ ^ q.toReal * ε := by
    apply (div_le_iff₀ hε).mp
    calc
      D / ε = ((D / ε) ^ q.toReal⁻¹) ^ q.toReal :=
        (Real.rpow_inv_rpow (div_nonneg hD hε.le) hqr0.ne').symm
      _ ≤ k₀ ^ q.toReal := Real.rpow_le_rpow
        (Real.rpow_nonneg (div_nonneg hD hε.le) _) (le_add_of_nonneg_right zero_le_one)
        hqr0.le
  refine ⟨k₀ + 1, by positivity, ?_⟩
  intro f hf
  let l (j : ℕ) := k₀ + 1 - 1 / (2 : ℝ) ^ j
  let Y (j : ℕ) := μ.real {x | l j < f x}
  have hl0 : l 0 = k₀ := by simp only [l, pow_zero, div_one, add_sub_cancel_right]
  have hlk (j : ℕ) : k₀ ≤ l j := by
    have hh := div_le_self (show (0 : ℝ) ≤ 1 by norm_num)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j))
    dsimp only [l]
    linarith
  have hlgap (j : ℕ) : l (j + 1) - l j = 1 / (2 : ℝ) ^ (j + 1) := by
    dsimp only [l]
    rw [pow_succ]
    field_simp
    ring
  have hllt (j : ℕ) : l j < l (j + 1) :=
    sub_pos.mp ((hlgap j).symm ▸ one_div_pos.mpr (by positivity))
  have hY (j : ℕ) : 0 ≤ Y j := measureReal_nonneg
  have hY0 : Y 0 ≤ ε := by
    have hm := superlevel_measure_step hq0 hqt hC.le hk₀ (hf 0 le_rfl).1 (hf 0 le_rfl).2
    simp only [sub_zero] at hm
    have hb : k₀ ^ q.toReal * Y 0 ≤ D := by
      dsimp only [Y]
      rw [hl0]
      exact hm.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow measureReal_nonneg
        (measureReal_mono (subset_univ _)) (by linarith)) (by positivity))
    exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hk₀ _)).mp (hb.trans hscale)
  have hstep (j : ℕ) :
      Y (j + 1) ≤ (C ^ q.toReal * B) * B ^ j * Y j ^ (1 + (q.toReal - 2)) := by
    obtain ⟨hm, hn⟩ := hf (l j) (hk₀.le.trans (hlk j))
    have hh := superlevel_measure_step hq0 hqt hC.le (hllt j) hm hn
    have hgap : (1 / (2 : ℝ) ^ (j + 1)) ^ q.toReal = (B ^ (j + 1))⁻¹ := by
      rw [Real.div_rpow zero_le_one (by positivity), Real.one_rpow,
        ← Real.rpow_pow_comm (by norm_num)]
      exact one_div _
    rw [hlgap, hgap, inv_mul_le_iff₀ (pow_pos hB _)] at hh
    rw [show 1 + (q.toReal - 2) = q.toReal - 1 by ring]
    refine hh.trans_eq ?_
    rw [pow_succ]
    ring
  have hlim := hiteration Y hY hY0 hstep
  have hfinal : μ.real {x | k₀ + 1 < f x} = 0 :=
    le_antisymm (ge_of_tendsto hlim (.of_forall fun j ↦ measureReal_mono fun x hx ↦
      (sub_le_self _ (by positivity : (0 : ℝ) ≤ 1 / 2 ^ j)).trans_lt hx)) measureReal_nonneg
  rw [ae_iff]
  simpa only [not_le] using (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hfinal

end PDE.Elliptic.Regularity.DeGiorgi
