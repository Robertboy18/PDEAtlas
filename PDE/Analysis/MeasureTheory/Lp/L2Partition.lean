/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.Restriction
public import PDE.Analysis.MeasureTheory.Lp.IndicatorExtension
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Function.L2Space
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# L² decomposition over a countable measurable partition

Restriction identifies the square norm with the sum of local square norms.
For disjoint pieces, extension by zero gives a convergent decomposition of
every global class. Conversely, summable local energies give global membership.
These arguments apply to any countable partition and any density.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace MeasureTheory.Lp

variable {α ι : Type*} [MeasurableSpace α]

/-- Restriction preserves the representative on the smaller measure. -/
private theorem restriction_norm_sq (μ : Measure α) (s : Set α)
    (f : Lp ℝ 2 μ) :
    ‖Lp.restrictionCLMOfLE (Measure.restrict_le_self (μ := μ) (s := s)) f‖ ^ 2 =
      ∫ x in s, (f x) ^ 2 ∂μ := by
  rw [norm_sq_eq_integral_sq]
  apply integral_congr_ae
  filter_upwards [Lp.restrictionCLMOfLE_apply_ae
    (Measure.restrict_le_self (μ := μ) (s := s)) f] with x hx
  exact congrArg (fun t : ℝ ↦ t ^ 2) hx

/-- The square norm splits because integration commutes with a countable
sum of measures for an integrable function. -/
theorem hasSum_norm_restrictionL2_sq (μ : Measure α)
    (s : ι → Set α)
    (hpartition : μ = Measure.sum (fun j : ι ↦ μ.restrict (s j))) (f : Lp ℝ 2 μ) :
    HasSum (fun j : ι ↦
      ‖Lp.restrictionCLMOfLE
        (Measure.restrict_le_self (μ := μ) (s := s j)) f‖ ^ 2)
      (‖f‖ ^ 2) := by
  have hsum := hpartition
  have hf : Integrable (fun x : α ↦ (f x) ^ 2)
      (Measure.sum (fun j : ι ↦ μ.restrict (s j))) := by
    rw [← hsum]
    exact (Lp.memLp f).integrable_sq
  have h := hasSum_integral_measure hf
  rw [← hsum] at h
  simpa only [restriction_norm_sq μ, norm_sq_eq_integral_sq f] using h

/-- Restriction to a countable measurable partition is an isometry into the
Hilbert sum of the local L² spaces. The measure decomposition supplies the
square-norm identity. -/
theorem exists_restrictionL2_isometry (μ : Measure α)
    (s : ι → Set α)
    (hpartition : μ = Measure.sum (fun j : ι ↦ μ.restrict (s j))) :
    ∃ J : Lp ℝ 2 μ →ₗᵢ[ℝ]
        lp (fun j : ι ↦ Lp ℝ 2 (μ.restrict (s j))) 2,
      ∀ f j, J f j = Lp.restrictionCLMOfLE
        (Measure.restrict_le_self (μ := μ) (s := s j)) f := by
  let R (j : ι) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.restrict (s j)) :=
    Lp.restrictionCLMOfLE Measure.restrict_le_self
  have hmem (f : Lp ℝ 2 μ) : Memℓp (fun j ↦ R j f) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, R] using
      (hasSum_norm_restrictionL2_sq μ s hpartition f).summable
  let J : Lp ℝ 2 μ →ₗᵢ[ℝ]
      lp (fun j : ι ↦ Lp ℝ 2 (μ.restrict (s j))) 2 :=
    { toFun := fun f ↦ ⟨fun j ↦ R j f, hmem f⟩
      map_add' := by
        intro f g
        apply lp.ext
        funext j
        exact map_add (R j) f g
      map_smul' := by
        intro c f
        apply lp.ext
        funext j
        change R j (c • f) = c • R j f
        exact map_smul (R j) c f
      norm_map' := by
        intro f
        change ‖(⟨fun j ↦ R j f, hmem f⟩ :
          lp (fun j : ι ↦ Lp ℝ 2 (μ.restrict (s j))) 2)‖ = ‖f‖
        have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
        have hnorm := lp.norm_rpow_eq_tsum hp
          (⟨fun j ↦ R j f, hmem f⟩ :
            lp (fun j : ι ↦ Lp ℝ 2 (μ.restrict (s j))) 2)
        simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hnorm
        have hsum := (hasSum_norm_restrictionL2_sq μ s hpartition f).tsum_eq
        change (∑' j : ι, ‖R j f‖ ^ 2) = ‖f‖ ^ 2 at hsum
        rw [hsum] at hnorm
        nlinarith [norm_nonneg f,
          norm_nonneg (⟨fun j ↦ R j f, hmem f⟩ :
            lp (fun j : ι ↦ Lp ℝ 2 (μ.restrict (s j))) 2)] }
  exact ⟨J, fun _ _ ↦ rfl⟩

/-- Restriction followed by extension is the original representative on the
set and zero off it. -/
theorem extension_restriction_ae (μ : Measure α) (s : Set α)
    (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    (Lp.extendByZeroₗᵢ (𝕜 := ℝ) hs
      (Lp.restrictionCLMOfLE
        (Measure.restrict_le_self (μ := μ) (s := s)) f) : α → ℝ) =ᵐ[μ]
      s.indicator (fun x ↦ f x) := by
  exact (Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ) hs _).trans
    ((ae_eq_restrict_iff_indicator_ae_eq hs).mp
      (Lp.restrictionCLMOfLE_apply_ae Measure.restrict_le_self f))

/-- The disjoint pieces sum to the original L² class in norm, with the sum
indexed by all finite subsets. No pointwise convergence premise is needed. -/
theorem hasSum_restrictionL2_pieces (μ : Measure α)
    (s : ι → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (s i) (s j)))
    (hpartition : μ = Measure.sum (fun j : ι ↦ μ.restrict (s j))) (f : Lp ℝ 2 μ) :
    HasSum (fun j : ι ↦
      Lp.extendByZeroₗᵢ (𝕜 := ℝ) (hs j)
        (Lp.restrictionCLMOfLE
          (Measure.restrict_le_self (μ := μ) (s := s j)) f)) f := by
  classical
  obtain ⟨J, hJ⟩ := exists_restrictionL2_isometry μ s hpartition
  let p (j : ι) : Lp ℝ 2 μ :=
    Lp.extendByZeroₗᵢ (𝕜 := ℝ) (hs j)
      (Lp.restrictionCLMOfLE Measure.restrict_le_self f)
  have hp (j : ι) : J (p j) = lp.single 2 j (J f j) := by
    apply lp.ext
    funext i
    rw [hJ]
    apply Lp.ext
    have hrestrict := Lp.restrictionCLMOfLE_apply_ae
      (Measure.restrict_le_self (μ := μ) (s := s i)) (p j)
    have hpj := extension_restriction_ae μ (s j)
      (hs j) f
    by_cases hij : i = j
    · subst i
      rw [lp.single_apply_self, hJ]
      have hf := Lp.restrictionCLMOfLE_apply_ae
        (Measure.restrict_le_self (μ := μ) (s := s j)) f
      filter_upwards [hrestrict, ae_restrict_of_ae hpj, hf,
        ae_restrict_mem (hs j)] with x hx hy hz hxs
      change _ = (p j : α → ℝ) x at hx
      exact hx.trans ((hy.trans (Set.indicator_of_mem hxs _)).trans hz.symm)
    · rw [lp.single_apply_ne
        (E := fun i : ι ↦ Lp ℝ 2 (μ.restrict (s i))) 2 j (J f j) hij]
      have hzero := Lp.coeFn_zero ℝ 2 (μ.restrict (s i))
      filter_upwards [hrestrict, ae_restrict_of_ae hpj, hzero,
        ae_restrict_mem (hs i)] with x hx hy hz hxs
      have hxj : x ∉ s j := by
        intro hxj
        exact Set.disjoint_left.mp
          (hdisjoint hij) hxs hxj
      exact hx.trans ((hy.trans (Set.indicator_of_notMem hxj _)).trans hz.symm)
  have hsingle := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (J f)
  have hsum : HasSum (J ∘ p) (J f) := by
    simpa only [Function.comp_def, hp] using hsingle
  exact (J.isEmbedding.isInducing.hasSum_iff p f).mp hsum

variable [Countable ι]

/-- Square-summable component norms give `L²` membership for the sum of the measures
and the exact squared norm. Measurability also follows from the component memberships. -/
theorem exists_memLp_two_of_sum_measure (μ : ι → Measure α) (f : α → ℝ)
    (hf : ∀ j : ι, MemLp f 2 (μ j))
    (hs : Summable (fun j : ι ↦ ‖(hf j).toLp f‖ ^ 2)) :
    ∃ hg : MemLp f 2 (Measure.sum μ),
      ‖hg.toLp f‖ ^ 2 = ∑' j : ι, ‖(hf j).toLp f‖ ^ 2 := by
  have hnorm (j : ι) :
      ‖(hf j).toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ j := by
    rw [norm_sq_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [(hf j).coeFn_toLp] with x hx
    exact congrArg (fun t : ℝ ↦ t ^ 2) hx
  have hsint : Summable
      (fun j : ι ↦ ∫ x, ‖(f x) ^ 2‖ ∂μ j) := by
    simpa only [Real.norm_of_nonneg (sq_nonneg _), ← hnorm] using hs
  have hint : Integrable (fun x : α ↦ (f x) ^ 2) (Measure.sum μ) :=
    integrable_sum_measure (fun j ↦ (hf j).integrable_sq) hsint
  have hmeas : AEStronglyMeasurable f (Measure.sum μ) :=
    aestronglyMeasurable_sum_measure_iff.mpr (fun j ↦ (hf j).aestronglyMeasurable)
  have hg : MemLp f 2 (Measure.sum μ) := (memLp_two_iff_integrable_sq hmeas).mpr hint
  refine ⟨hg, ?_⟩
  have hglobal : ‖hg.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂Measure.sum μ := by
    rw [norm_sq_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    exact congrArg (fun t : ℝ ↦ t ^ 2) hx
  simpa only [hnorm, hglobal] using (hasSum_integral_measure hint).tsum_eq.symm

/-- Summable squared budgets give an `L²` bound for any measure dominated by their
sum. For a regional cover, overlaps only increase the bound, so disjointness is
unnecessary. Comparison with the budgets proves summability of the norms. -/
theorem exists_memLp_two_of_measure_bounds (ν : Measure α) (μ : ι → Measure α)
    (hcover : ν ≤ Measure.sum μ)
    (f : α → ℝ) (budget : ι → ℝ)
    (hf : ∀ j : ι, MemLp f 2 (μ j))
    (hbound : ∀ j, ‖(hf j).toLp f‖ ^ 2 ≤ budget j)
    (hs : Summable budget) :
    ∃ hg : MemLp f 2 ν, ‖hg.toLp f‖ ^ 2 ≤ ∑' j, budget j := by
  have hnorms : Summable (fun j ↦ ‖(hf j).toLp f‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) hbound hs
  obtain ⟨hg, heq⟩ := exists_memLp_two_of_sum_measure μ f hf hnorms
  refine ⟨hg.mono_measure hcover, ?_⟩
  have hnorm : ‖(hg.mono_measure hcover).toLp f‖ ≤ ‖hg.toLp f‖ := by
    rw [norm_toLp, norm_toLp]
    exact ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_measure f hcover)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
    (heq.trans_le (hnorms.tsum_le_tsum hbound hs))

end MeasureTheory.Lp
