/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.LocalMeasure
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Uniform local bounds for rescaled periodic functions

Integer multiplication preserves Haar measure on the torus. A bounded Euclidean
set fits inside a scaled cell whose side length is an integer multiple of the
period. The change of variables on that cell bounds the pushforward measure
uniformly as the period tends to zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.Analysis.PeriodicAveraging

/-- The quotient commutes with integer dilation of Euclidean coordinates. -/
theorem toTorus_int_smul {n : ℕ} (k : ℤ) (x : ℝ^n) :
    toTorus n ((k : ℝ) • x) = k • toTorus n x := by
  ext i
  simp only [toTorus, ContinuousMap.coe_mk, Pi.smul_apply, PiLp.smul_apply,
    smul_eq_mul, ← zsmul_eq_mul, AddCircle.coe_zsmul]

/-- A nonzero integer dilation followed by quotienting preserves cell measure. -/
theorem measurePreserving_toTorus_int_smul {n : ℕ} (a : Fin n → ℝ)
    (k : ℤ) (hk : k ≠ 0) :
    MeasurePreserving (fun x : ℝ^n ↦ toTorus n ((k : ℝ) • x))
      (volume.restrict (unitCell a)) (cellMeasure n) := by
  let : (cellMeasure n).IsAddHaarMeasure := by
    unfold cellMeasure
    infer_instance
  simp only [toTorus_int_smul]
  convert! (Measure.measurePreserving_zsmul (cellMeasure n) hk).comp
    (measurePreserving_toTorus a) using 1

/-- An exact change of variables on a cell containing an integer number of periods. -/
theorem measurePreserving_toTorus_scaledCell {n : ℕ} (a : Fin n → ℝ)
    (c r : ℝ) (hr : r ≠ 0) (k : ℤ) (hk : k ≠ 0) (hperiod : c * r = k) :
    MeasurePreserving (fun x : ℝ^n ↦ toTorus n (c • x))
      (volume.restrict ((fun x : ℝ^n ↦ r⁻¹ • x) ⁻¹' unitCell a))
      (ENNReal.ofReal (|r| ^ n) • cellMeasure n) := by
  have hd : MeasurePreserving (fun x : ℝ^n ↦ r⁻¹ • x)
      volume (ENNReal.ofReal (|r| ^ n) • volume) := by
    refine ⟨measurable_const_smul _, ?_⟩
    simpa only [inv_pow, inv_inv, abs_pow, finrank_euclideanSpace, Fintype.card_fin] using
      Measure.map_addHaar_smul (volume : Measure (ℝ^n)) (inv_ne_zero hr)
  have hrestrict := hd.restrict_preimage (measurableSet_unitCell a)
  rw [Measure.restrict_smul] at hrestrict
  have hp := ((measurePreserving_toTorus_int_smul a k hk).smul_measure
    (ENNReal.ofReal (|r| ^ n))).comp hrestrict
  convert! hp using 1
  funext x
  rw [Function.comp_apply, smul_smul, ← hperiod, mul_assoc, mul_inv_cancel₀ hr, mul_one]

/-- A bounded domain has a uniform measure bound for every sufficiently small positive period. -/
theorem exists_map_toTorus_rescale_le {n : ℕ} {Ω : Set (ℝ^n)}
    (hΩ : Bornology.IsBounded Ω) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Measure.map (fun x : ℝ^n ↦ toTorus n (ε⁻¹ • x)) (volume.restrict Ω) ≤
        C • cellMeasure n := by
  obtain ⟨R, hR, hbound⟩ := hΩ.exists_pos_norm_lt
  refine ⟨ENNReal.ofReal ((2 * R + 1) ^ n), ENNReal.ofReal_ne_top, ?_⟩
  intro ε hε hε1
  let k : ℤ := ⌈2 * R / ε⌉
  have hkpos : 0 < (k : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos (by norm_num) hR) hε) (Int.le_ceil _)
  have hk : k ≠ 0 := by exact_mod_cast hkpos.ne'
  let r : ℝ := ε * k
  have hrpos : 0 < r := mul_pos hε hkpos
  have hrlower : 2 * R ≤ r := by
    simpa only [r, k, mul_comm] using (div_le_iff₀ hε).mp (Int.le_ceil (2 * R / ε))
  have hrupper : r ≤ 2 * R + 1 := by
    have ht := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (2 * R / ε)) hε
    have heq : ε * (2 * R / ε) = 2 * R := by
      rw [mul_div_cancel₀ _ hε.ne']
    rw [mul_add, heq, mul_one] at ht
    exact ht.le.trans (by linarith)
  have hsubset : Ω ⊆
      (fun x : ℝ^n ↦ r⁻¹ • x) ⁻¹' unitCell (fun _ ↦ -(1 / 2)) := by
    intro x hx i
    have hxi : |x i| < R := (Real.norm_eq_abs (x i)).symm ▸
      (PiLp.norm_apply_le x i).trans_lt (hbound x hx)
    have hleft := (abs_lt.mp hxi).1
    have hright := (abs_lt.mp hxi).2
    change -(1 / 2 : ℝ) < r⁻¹ * x i ∧ r⁻¹ * x i ≤ -(1 / 2 : ℝ) + 1
    rw [inv_mul_eq_div, lt_div_iff₀ hrpos, div_le_iff₀ hrpos]
    constructor <;> nlinarith
  have hp := measurePreserving_toTorus_scaledCell (n := n) (fun _ ↦ -(1 / 2))
    ε⁻¹ r hrpos.ne' k hk (by simp [r, hε.ne'])
  calc
    _ ≤ Measure.map (fun x : ℝ^n ↦ toTorus n (ε⁻¹ • x))
        (volume.restrict ((fun x : ℝ^n ↦ r⁻¹ • x) ⁻¹'
          unitCell (fun _ ↦ -(1 / 2)))) :=
      Measure.map_mono (Measure.restrict_mono_set volume hsubset)
        ((toTorus n).measurable.comp (measurable_const_smul _))
    _ = ENNReal.ofReal (|r| ^ n) • cellMeasure n := hp.map_eq
    _ ≤ ENNReal.ofReal ((2 * R + 1) ^ n) • cellMeasure n := by
      gcongr
      rwa [abs_of_pos hrpos]

end PDE.Analysis.PeriodicAveraging
