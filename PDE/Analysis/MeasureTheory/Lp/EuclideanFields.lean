/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Products
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import PDE.Common.Euclidean
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Lebesgue integrability of fields on `ℝⁿ`

A field with measurable components is measurable, products of two components of an `L⁴`
field are square integrable, and a field bounded by `C (1 + ‖x‖)^{-a}` lies in `Lᵖ(ℝⁿ)` as soon
as `a p > n`.
-/

@[expose] public section

namespace MeasureTheory

variable {n : ℕ}

/-- A Euclidean vector field with measurable components is measurable. -/
theorem aestronglyMeasurable_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : Fin n → α → ℝ} (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x ↦ WithLp.toLp 2 (fun i ↦ f i x) : α → ℝ^n) μ :=
  memLp_zero_iff_aestronglyMeasurable.mp
    (memLp_piLp_iff.mpr fun i ↦ memLp_zero_iff_aestronglyMeasurable.mpr (hf i))

/-- Products of components of an `L⁴` field are square integrable. -/
theorem memLp_two_mul_of_memLp_four {μ : Measure (ℝ^n)} {u : ℝ^n → ℝ^n} (hu : MemLp u 4 μ)
    (i j : Fin n) : MemLp (fun x ↦ u x i * u x j) 2 μ := by
  have hi : MemLp (fun x ↦ u x i) 4 μ :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).comp_memLp' hu
  have hj : MemLp (fun x ↦ u x j) 4 μ :=
    (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).comp_memLp' hu
  exact hi.fun_mul (r := 2) hj

/-- A field on `ℝⁿ` bounded by `C (1 + ‖x‖)^{-a}` with `n < a p` lies in `Lᵖ` for finite
`p`. -/
theorem memLp_of_norm_le_mul_one_add_norm_rpow_neg {E : Type*} [NormedAddCommGroup E]
    {f : ℝ^n → E} (hf : AEStronglyMeasurable f volume) {p : ENNReal} (hp0 : p ≠ 0)
    (hpt : p ≠ ⊤) {a C : ℝ} (hna : (n : ℝ) < a * p.toReal)
    (h : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-a)) : MemLp f p volume := by
  have hint : Integrable (fun x : ℝ^n ↦ (1 + ‖x‖) ^ (-(a * p.toReal))) volume :=
    integrable_one_add_norm (by simpa using hna)
  have hgm : AEStronglyMeasurable (fun x : ℝ^n ↦ |C| * (1 + ‖x‖) ^ (-a)) volume :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hg : MemLp (fun x : ℝ^n ↦ |C| * (1 + ‖x‖) ^ (-a)) p volume := by
    rw [← integrable_norm_rpow_iff hgm hp0 hpt]
    refine (hint.const_mul (|C| ^ p.toReal)).congr (Filter.Eventually.of_forall fun x ↦ ?_)
    have hpos : 0 < 1 + ‖x‖ := by positivity
    beta_reduce
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _),
      Real.mul_rpow (abs_nonneg C) (Real.rpow_nonneg hpos.le _), ← Real.rpow_mul hpos.le,
      neg_mul]
  refine hg.of_le hf (Filter.Eventually.of_forall fun x ↦ ?_)
  have hpos : 0 < 1 + ‖x‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (h x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))

end MeasureTheory
