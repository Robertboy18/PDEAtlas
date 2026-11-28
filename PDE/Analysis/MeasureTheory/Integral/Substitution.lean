/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Lower integrals under maps that preserve or scale the measure

Two lower integrals can sometimes be compared only after a substitution, not point by point. Two
such cases come up in symmetrization. If every map `T i` of a nonempty finite family preserves
the measure, then a comparison of the sums `∑ i, f (T i x)` and `∑ i, g (T i x)` at every point
compares `∫ f` and `∫ g`: with the two maps `id` and a reflection `σ`, it is enough to compare
`f x + f (σ x)` with `g x + g (σ x)`. This carries the polarization arguments
`PDE.Analysis.Rearrangement.lintegral_comp_polarize` (two maps) and
`PDE.Analysis.Rearrangement.diffEnergy_polarize_le` (four maps). The second case is the
substitution `y = x + t z` for an additive Haar measure on a real normed space of finite
dimension `n`, which scales lower integrals by `|t|⁻ⁿ`, with no measurability needed. Families
that are not finite, such as an average over a compact group of measure preserving maps, are
not treated.

## Main results

* `MeasureTheory.lintegral_le_of_sum_comp_le`, `MeasureTheory.lintegral_eq_of_sum_comp_eq`: for
  a nonempty finite family of measure preserving maps and measurable `f`, `g` with values in
  `[0, ∞]`, the comparison of the integrals from the comparison of the sums over the family.
* `MeasureTheory.Measure.lintegral_comp_add_smul`: for an additive Haar measure on a
  finite-dimensional real normed space, every `F` with values in `[0, ∞]`, every `x` and every
  `t ≠ 0`, `∫ F (x + t z) dz = |t|⁻ⁿ ∫ F`. It is the lower integral form of Mathlib's
  `MeasureTheory.Measure.integral_comp_smul`, with a translation.
  `MeasureTheory.lintegral_comp_pos_smul` and `HeatEquation.WholeSpace.lintegral_comp_smul_eq`
  are its cases `x = 0`.

## How it works

Since each `T i` preserves the measure, the integral of `∑ i, f (T i x)` is the number of maps
times `∫ f`, and the same holds for `g`. For the substitution, `z ↦ t z` is a measurable
embedding that maps the Haar measure to `|t|⁻ⁿ` times itself
(`MeasureTheory.Measure.map_addHaar_smul`), and translations preserve it.

## References

* F. Brock and A. Yu. Solynin, "An approach to symmetrization via polarization",
  *Trans. Amer. Math. Soc.* 352 (2000), 1759-1796: integrals are compared on the pairs
  `{x, σ x}` of a reflection `σ`. <https://doi.org/10.1090/S0002-9947-99-02558-1>
-/

@[expose] public noncomputable section

open Set Module
open scoped ENNReal

namespace MeasureTheory

section Family

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι] [Nonempty ι]
  {T : ι → α → α} {f g : α → ℝ≥0∞}

/-- If the maps `T i` of a nonempty finite family preserve the measure and
`∑ i, f (T i x) ≤ ∑ i, g (T i x)` at every point, then `∫ f ≤ ∫ g`, for measurable `f` and
`g`. Both integrals are averages over the family. -/
theorem lintegral_le_of_sum_comp_le (hT : ∀ i, MeasurePreserving (T i) μ μ) (hf : Measurable f)
    (hg : Measurable g) (h : ∀ x, ∑ i, f (T i x) ≤ ∑ i, g (T i x)) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ := by
  have key (k : α → ℝ≥0∞) (hk : Measurable k) :
      ∫⁻ x, ∑ i, k (T i x) ∂μ = Fintype.card ι * ∫⁻ x, k x ∂μ := by
    have e : ∫⁻ x, ∑ i, k (T i x) ∂μ = ∑ i, ∫⁻ x, k (T i x) ∂μ :=
      lintegral_finsetSum Finset.univ fun i _ ↦ hk.comp (hT i).measurable
    rw [e, Finset.sum_congr rfl fun i _ ↦ (hT i).lintegral_comp hk, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have h2 := lintegral_mono (μ := μ) h
  rw [key f hf, key g hg] at h2
  exact (ENNReal.mul_le_mul_iff_right (by simp) (ENNReal.natCast_ne_top _)).mp h2

/-- If the maps `T i` of a nonempty finite family preserve the measure and
`∑ i, f (T i x) = ∑ i, g (T i x)` at every point, then `∫ f = ∫ g`, for measurable `f` and
`g`. -/
theorem lintegral_eq_of_sum_comp_eq (hT : ∀ i, MeasurePreserving (T i) μ μ) (hf : Measurable f)
    (hg : Measurable g) (h : ∀ x, ∑ i, f (T i x) = ∑ i, g (T i x)) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ :=
  le_antisymm (lintegral_le_of_sum_comp_le hT hf hg fun x ↦ (h x).le)
    (lintegral_le_of_sum_comp_le hT hg hf fun x ↦ (h x).ge)

end Family

/-- **The substitution `y = x + t z`** for an additive Haar measure on a real normed space of
finite dimension `n`: `∫ F (x + t z) dz = |t|⁻ⁿ ∫ F (y) dy` for `t ≠ 0`. The function `F` need
not be measurable: `z ↦ t z` is a measurable embedding. -/
theorem Measure.lintegral_comp_add_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (F : V → ℝ≥0∞) (x : V) {t : ℝ} (ht : t ≠ 0) :
    ∫⁻ z, F (x + t • z) ∂μ = ENNReal.ofReal |(t ^ finrank ℝ V)⁻¹| * ∫⁻ y, F y ∂μ := by
  have h1 : ∫⁻ z, F (x + t • z) ∂μ = ∫⁻ y, F (x + y) ∂(Measure.map (t • ·) μ) :=
    ((measurableEmbedding_const_smul₀ ht).lintegral_map fun y ↦ F (x + y)).symm
  rw [h1, Measure.map_addHaar_smul μ ht, lintegral_smul_measure, lintegral_add_left_eq_self,
    smul_eq_mul]

end MeasureTheory
