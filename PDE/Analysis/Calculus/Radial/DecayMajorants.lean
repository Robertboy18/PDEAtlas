/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.AngularLipschitz
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Nonsingular decay majorants

A function bounded on the closed unit ball and by `C / ‖x‖ ^ n` away from the origin is bounded
by one majorant `C' / (1 + ‖x‖) ^ n` on the whole space. Such a majorant gives `Lᵖ` membership
on a finite-dimensional space whenever the dimension is less than `n p`. A radial factor
bounded by `w(x) b` times a continuous field of the normalized point is bounded by `w(x) C`,
and these weighted bounds add over finite sums.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Radial

open MeasureTheory Filter NormedSpace
open scoped ENNReal

variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]

/-- A nonnegative function bounded on the closed unit ball and by `C / ‖x‖ ^ n` away from the
origin has a nonsingular majorant `C' / (1 + ‖x‖) ^ n`. -/
theorem exists_one_add_norm_pow_bound_of_near_far {g : E → ℝ} (n : ℕ) (hg : ∀ x, 0 ≤ g x)
    (hnear : ∃ K, ∀ x : E, ‖x‖ ≤ 1 → g x ≤ K)
    (hfar : ∃ C ≥ 0, ∀ x : E, x ≠ 0 → g x ≤ C / ‖x‖ ^ n) :
    ∃ C ≥ 0, ∀ x : E, g x ≤ C / (1 + ‖x‖) ^ n := by
  obtain ⟨K, hK⟩ := hnear
  obtain ⟨C, hC, hbound⟩ := hfar
  have hKpos : 0 ≤ K := (hg 0).trans (hK 0 (by simp))
  refine ⟨2 ^ n * (K + C), by positivity, fun x ↦ ?_⟩
  have hpos : 0 < (1 + ‖x‖) ^ n := by positivity
  rw [le_div_iff₀ hpos]
  by_cases hx : ‖x‖ ≤ 1
  · have hr : (1 + ‖x‖) ^ n ≤ 2 ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      g x * (1 + ‖x‖) ^ n ≤ K * 2 ^ n :=
        mul_le_mul (hK x hx) hr hpos.le hKpos
      _ ≤ 2 ^ n * (K + C) := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) n]
  · have hrpos : 0 < ‖x‖ := by linarith
    have hu := (le_div_iff₀ (pow_pos hrpos n)).mp (hbound x (norm_ne_zero_iff.mp hrpos.ne'))
    have hr : (1 + ‖x‖) ^ n ≤ 2 ^ n * ‖x‖ ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    calc
      g x * (1 + ‖x‖) ^ n ≤ g x * (2 ^ n * ‖x‖ ^ n) :=
        mul_le_mul_of_nonneg_left hr (hg x)
      _ = 2 ^ n * (g x * ‖x‖ ^ n) := by ring
      _ ≤ 2 ^ n * C := mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ 2 ^ n * (K + C) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

section Integrability

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A majorant `C / (1 + ‖x‖) ^ k` makes `‖f‖ ^ q` integrable once the dimension is less than
`k q`. -/
theorem integrable_norm_rpow_of_one_add_norm_pow_bound {f : E → G}
    (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C / (1 + ‖x‖) ^ k) {q : ℝ}
    (hq : (Module.finrank ℝ E : ℝ) < k * q) :
    Integrable (fun x ↦ ‖f x‖ ^ q) μ := by
  have hkq : 0 < (k : ℝ) * q := lt_of_le_of_lt (Nat.cast_nonneg _) hq
  have hq0 : 0 ≤ q := by
    by_contra h
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), not_le.mp h]
  apply ((integrable_one_add_norm (μ := μ) hq).const_mul (C ^ q)).mono'
  · exact hf.norm.aemeasurable.pow_const q |>.aestronglyMeasurable
  · filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      ‖f x‖ ^ q ≤ (C / (1 + ‖x‖) ^ k) ^ q :=
        Real.rpow_le_rpow (norm_nonneg _) hx hq0
      _ = C ^ q * (1 + ‖x‖) ^ (-((k : ℝ) * q)) := by
        rw [Real.div_rpow hC (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity), Real.rpow_neg (by positivity)]
        exact div_eq_mul_inv _ _

/-- A majorant `C / (1 + ‖x‖) ^ k` gives `Lᵖ` membership once the dimension is less than
`k p`. -/
theorem memLp_of_one_add_norm_pow_bound {f : E → G} (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hC : 0 ≤ C) {k : ℕ} (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C / (1 + ‖x‖) ^ k)
    {p : ℝ≥0∞} (hp : (Module.finrank ℝ E : ℝ) < k * p.toReal) : MemLp f p μ := by
  have hkp : 0 < (k : ℝ) * p.toReal := lt_of_le_of_lt (Nat.cast_nonneg _) hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hkp
  have hptop : p ≠ ∞ := by
    rintro rfl
    simp at hkp
  exact (integrable_norm_rpow_iff hf hp0 hptop).mp
    (integrable_norm_rpow_of_one_add_norm_pow_bound hf hC hbound hp)

end Integrability

/-- Weighted bounds add. -/
theorem exists_weighted_bound_add {α : Type*} {w : α → ℝ} {U V : α → G}
    (hU : ∃ C ≥ 0, ∀ x, ‖U x‖ ≤ w x * C) (hV : ∃ C ≥ 0, ∀ x, ‖V x‖ ≤ w x * C) :
    ∃ C ≥ 0, ∀ x, ‖U x + V x‖ ≤ w x * C := by
  obtain ⟨A, hA, hUb⟩ := hU
  obtain ⟨B, hB, hVb⟩ := hV
  refine ⟨A + B, add_nonneg hA hB, fun x ↦ ?_⟩
  calc
    ‖U x + V x‖ ≤ ‖U x‖ + ‖V x‖ := norm_add_le _ _
    _ ≤ w x * A + w x * B := add_le_add (hUb x) (hVb x)
    _ = w x * (A + B) := by ring

/-- Weighted bounds add over finite sums. -/
theorem exists_weighted_bound_sum {α ι : Type*} (s : Finset ι) {w : α → ℝ}
    {U : ι → α → G} (hU : ∀ i, ∃ C ≥ 0, ∀ x, ‖U i x‖ ≤ w x * C) :
    ∃ C ≥ 0, ∀ x, ‖∑ i ∈ s, U i x‖ ≤ w x * C := by
  choose C hC hbound using hU
  refine ⟨∑ i ∈ s, C i, Finset.sum_nonneg (fun i _ ↦ hC i), fun x ↦ ?_⟩
  calc
    ‖∑ i ∈ s, U i x‖ ≤ ∑ i ∈ s, ‖U i x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, w x * C i := Finset.sum_le_sum (fun i _ ↦ hbound i x)
    _ = w x * ∑ i ∈ s, C i := (Finset.mul_sum _ _ _).symm

section Weighted

variable [NormedSpace ℝ E] [ProperSpace E] [NormedSpace ℝ G]

/-- A radial factor bounded by `w(x) b` times a continuous field of the normalized point is
bounded by `w(x) C`. -/
theorem exists_weighted_bound_radial_smul_normalize {w : E → ℝ} {f : ℝ → ℝ} {b : ℝ}
    (hw : ∀ x, 0 ≤ w x) (hb : 0 ≤ b) (hf : ∀ x : E, |f ‖x‖| ≤ w x * b) {H : E → G}
    (hH : Continuous H) :
    ∃ C ≥ 0, ∀ x : E, ‖f ‖x‖ • H (normalize x)‖ ≤ w x * C := by
  obtain ⟨A, hA, hbound⟩ := exists_norm_comp_normalize_le hH
  refine ⟨b * A, mul_nonneg hb hA.le, fun x ↦ ?_⟩
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |f ‖x‖| * ‖H (normalize x)‖ ≤ (w x * b) * A :=
      mul_le_mul (hf x) (hbound x) (norm_nonneg _) (mul_nonneg (hw x) hb)
    _ = w x * (b * A) := by ring

end Weighted

end PDE.Analysis.Radial
