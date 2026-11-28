/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Products
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import PDE.Common.Euclidean
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Lebesgue integrability of fields on `ℝⁿ`

A field with measurable components is measurable, products of two components of an `L⁴`
field are square integrable, and a field bounded by `C (1 + ‖x‖)^{-a}` lies in `Lᵖ(ℝⁿ)` as soon
as `a p > n`.

Three inequalities for the lengths of fields hold on every measure space, in `[0, ∞]`, with no
finiteness assumed. Minkowski's inequality for the squares of the components gives
`‖F‖_q² ≤ ∑ᵢ ‖Fᵢ‖_q²` for `q = 2p`, `p ≥ 1` (`eLpNorm_euclidean_rpow_two_le_sum`), which passes a
scalar Sobolev inequality to fields with finitely many components. Hölder's inequality with the
exponents `6` and `3`, and once more with `4` and `12`, gives
`‖|F| |G|‖₂ ≤ ‖F‖₆ ‖G‖₂^{1/2} ‖G‖₆^{1/2}` (`eLpNorm_norm_mul_norm_two_le`), and
`‖|F|²‖₂ = ‖F‖₄²` (`eLpNorm_norm_mul_norm_self`).
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

open scoped ENNReal

/-! ## Minkowski and Hölder for the lengths of fields -/

/-- **Minkowski's inequality for the squared components of a Euclidean field.** For `p ≥ 1`,
`q = 2 p` and an almost everywhere strongly measurable field `F` with values in a Euclidean
space,

`‖F‖_q² = ‖∑ᵢ Fᵢ²‖_p ≤ ∑ᵢ ‖Fᵢ²‖_p = ∑ᵢ ‖Fᵢ‖_q²`,

where `‖F‖_q` is the `L^q` seminorm of the length of `F` and `Fᵢ` are the components. -/
theorem eLpNorm_euclidean_rpow_two_le_sum {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} {F : α → EuclideanSpace ℝ ι} (hF : AEStronglyMeasurable F μ) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : q = 2 * p) :
    eLpNorm F q μ ^ (2 : ℝ) ≤ ∑ i : ι, eLpNorm (fun x ↦ F x i) q μ ^ (2 : ℝ) := by
  have hq' : p * ENNReal.ofReal 2 = q := by
    rw [hq, ENNReal.ofReal_ofNat]
    exact mul_comm p 2
  have hcomp (i : ι) : AEStronglyMeasurable (fun x ↦ F x i) μ :=
    memLp_zero_iff_aestronglyMeasurable.mp
      (memLp_piLp_iff.mp (memLp_zero_iff_aestronglyMeasurable.mpr hF) i)
  have hpt : (fun x ↦ ‖F x‖ ^ (2 : ℝ)) = ∑ i : ι, fun x ↦ ‖F x i‖ ^ (2 : ℝ) := by
    funext x
    rw [Finset.sum_apply, Real.rpow_two, EuclideanSpace.norm_sq_eq]
    simp only [Real.rpow_two]
  calc eLpNorm F q μ ^ (2 : ℝ)
      = eLpNorm (fun x ↦ ‖F x‖ ^ (2 : ℝ)) p μ := by
        rw [eLpNorm_norm_rpow F hF (by norm_num), hq']
    _ = eLpNorm (∑ i : ι, fun x ↦ ‖F x i‖ ^ (2 : ℝ)) p μ := by rw [hpt]
    _ ≤ ∑ i : ι, eLpNorm (fun x ↦ ‖F x i‖ ^ (2 : ℝ)) p μ := eLpNorm_sum_le hp
    _ = ∑ i : ι, eLpNorm (fun x ↦ F x i) q μ ^ (2 : ℝ) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [eLpNorm_norm_rpow _ (hcomp i) (by norm_num), hq']

/-- **Hölder's inequality and interpolation between `L²` and `L⁶`.** For almost everywhere
strongly measurable `F`, `G` with values in normed groups,

`‖|F| |G|‖₂ ≤ ‖F‖₆ ‖G‖₃ ≤ ‖F‖₆ ‖G‖₂^{1/2} ‖G‖₆^{1/2}`.

The first step is Hölder's inequality with the exponents `6` and `3`. The second is Hölder's
inequality with the exponents `4` and `12` for `|G| = |G|^{1/2} |G|^{1/2}`. No finiteness is
assumed: the inequality holds in `[0, ∞]`. -/
theorem eLpNorm_norm_mul_norm_two_le {α X Y : Type*} [MeasurableSpace α]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] {μ : Measure α} {F : α → X} {G : α → Y}
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) :
    eLpNorm (fun x ↦ ‖F x‖ * ‖G x‖) 2 μ ≤
      eLpNorm F 6 μ * (eLpNorm G 2 μ ^ (1 / 2 : ℝ) * eLpNorm G 6 μ ^ (1 / 2 : ℝ)) := by
  have hH : eLpNorm (fun x ↦ ‖F x‖ * ‖G x‖) 2 μ ≤ eLpNorm F 6 μ * eLpNorm G 3 μ := by
    have : ENNReal.HolderTriple 6 3 2 := ⟨by
      change ((6 : NNReal) : ℝ≥0∞)⁻¹ + ((3 : NNReal) : ℝ≥0∞)⁻¹ = ((2 : NNReal) : ℝ≥0∞)⁻¹
      rw [← ENNReal.coe_inv (by norm_num : (6 : NNReal) ≠ 0),
        ← ENNReal.coe_inv (by norm_num : (3 : NNReal) ≠ 0),
        ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0), ← ENNReal.coe_add, ENNReal.coe_inj]
      norm_num⟩
    have h := eLpNorm_smul_le_mul_eLpNorm_of_pos (φ := fun x ↦ ‖F x‖) (f := fun x ↦ ‖G x‖)
      (μ := μ) (p := 6) (q := 3) (r := 2) (by norm_num)
    rw [eLpNorm_norm F hF, eLpNorm_norm G hG] at h
    exact h
  have hI : eLpNorm G 3 μ ≤ eLpNorm G 2 μ ^ (1 / 2 : ℝ) * eLpNorm G 6 μ ^ (1 / 2 : ℝ) := by
    have : ENNReal.HolderTriple 4 12 3 := ⟨by
      rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp),
        ENNReal.toReal_add (by simp) (by simp)]
      simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
      norm_num⟩
    have h := eLpNorm_smul_le_mul_eLpNorm_of_pos (φ := fun x ↦ ‖G x‖ ^ (1 / 2 : ℝ))
      (f := fun x ↦ ‖G x‖ ^ (1 / 2 : ℝ)) (μ := μ) (p := 4) (q := 12) (r := 3) (by norm_num)
    have heq : (fun x ↦ ‖G x‖ ^ (1 / 2 : ℝ)) • (fun x ↦ ‖G x‖ ^ (1 / 2 : ℝ)) =
        fun x ↦ ‖G x‖ := by
      ext x
      change ‖G x‖ ^ (1 / 2 : ℝ) * ‖G x‖ ^ (1 / 2 : ℝ) = _
      rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
      norm_num
    have h4 : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 2 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num
    have h12 : (12 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 6 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num
    rw [heq, eLpNorm_norm G hG, eLpNorm_norm_rpow G hG (by norm_num),
      eLpNorm_norm_rpow G hG (by norm_num), h4, h12] at h
    exact h
  exact hH.trans (mul_le_mul' le_rfl hI)

/-- The `L²` norm of `|F|²` is the square of the `L⁴` norm of `F`. -/
theorem eLpNorm_norm_mul_norm_self {α X : Type*} [MeasurableSpace α] [NormedAddCommGroup X]
    {μ : Measure α} {F : α → X} (hF : AEStronglyMeasurable F μ) :
    eLpNorm (fun x ↦ ‖F x‖ * ‖F x‖) 2 μ = eLpNorm F 4 μ ^ (2 : ℝ) := by
  have hfun : (fun x ↦ ‖F x‖ * ‖F x‖) = fun x ↦ ‖F x‖ ^ (2 : ℝ) := by
    funext x
    rw [Real.rpow_two, sq]
  rw [hfun, eLpNorm_norm_rpow _ hF (by norm_num)]
  norm_num

end MeasureTheory
