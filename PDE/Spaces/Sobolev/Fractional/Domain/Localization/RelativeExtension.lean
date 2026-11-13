/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.EdgeEstimates
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.SupportGap
public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.C1

/-!
# Relative zero extension with a support gap

For measurable `A ⊆ B`, the extension is the ordinary function `A.indicator u`.
For every finite positive exponent, its Lᵖ energy is unchanged and its fractional
energy consists of the original energy and two equal mixed-domain tails. A positive
gap from the active support to `B \ A` bounds those tails by the original Lᵖ energy.
Only `s > 0` is required; all statements include dimension zero.
Quadratic versions of these formulas are also given.

Applied to `A = U ∩ B`, a compact cutoff supported in the open patch `U`
provides this gap. The physical domain `B` need not have a regular boundary.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Fractional.Localization

variable {n : ℕ} {s δ : ℝ} {A B U : Set (ℝ^n)} {p : ℝ≥0∞}
variable {F : Type*} [NormedAddCommGroup F] {u : ℝ^n → F}

/-- Relative zero extension preserves the exact Lᵖ energy. -/
theorem lintegral_enorm_rpow_indicator (hA : MeasurableSet A) (hAB : A ⊆ B)
    (u : ℝ^n → F) (hp : 0 < p.toReal) :
    (∫⁻ x in B, ‖A.indicator u x‖ₑ ^ p.toReal) =
      ∫⁻ x in A, ‖u x‖ₑ ^ p.toReal := by
  classical
  calc
    _ = ∫⁻ x in B, A.indicator (fun y ↦ ‖u y‖ₑ ^ p.toReal) x := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ A <;> simp [hx, ENNReal.zero_rpow_of_pos hp]
    _ = _ := by
      rw [setLIntegral_indicator hA, inter_eq_left.mpr hAB]

/-- Relative zero extension preserves the exact L2 square. -/
theorem lintegral_nnnorm_indicator_sq (hA : MeasurableSet A) (hAB : A ⊆ B)
    (u : ℝ^n → F) :
    (∫⁻ x in B, (‖A.indicator u x‖₊ : ℝ≥0∞) ^ 2) =
      ∫⁻ x in A, (‖u x‖₊ : ℝ≥0∞) ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_eq_nnnorm] using
    lintegral_enorm_rpow_indicator (p := 2) hA hAB u (by norm_num)

/-- Relative zero extension preserves Lᵖ membership, including the endpoints. -/
theorem memLp_indicator_of_subset (hA : MeasurableSet A) (hAB : A ⊆ B)
    (hu : MemLp u p (volume.restrict A)) :
    MemLp (A.indicator u) p (volume.restrict B) := by
  rw [memLp_indicator_iff_restrict hA.nullMeasurableSet, Measure.restrict_restrict hA,
    inter_eq_left.mpr hAB]
  exact hu

variable [NormedSpace ℝ F]

/-- The fractional energy splits into its original part and two equal mixed tails.
No measurability of the function is needed for this nonnegative integral identity. -/
theorem lintegral_diffQuot_indicator_eq (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (u : ℝ^n → F) (hp : 0 < p.toReal) :
    (∫⁻ z, ‖diffQuot n s (A.indicator u) z (p := p)‖ₑ ^ p.toReal
      ∂gagliardoProductMeasure n B) =
      (∫⁻ z, ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal
        ∂gagliardoProductMeasure n A) +
      2 * ∫⁻ z, ‖diffQuot n s (A.indicator u) z (p := p)‖ₑ ^ p.toReal
        ∂(volume.restrict A).prod (volume.restrict (B \ A)) := by
  classical
  have hμ : (volume : Measure (ℝ^n)).restrict B =
      volume.restrict A + volume.restrict (B \ A) := by
    simpa only [inter_eq_right.mpr hAB] using
      (Measure.restrict_inter_add_sdiff (μ := (volume : Measure (ℝ^n))) B hA).symm
  have hOn : A.indicator u =ᵐ[volume.restrict A] u := by
    filter_upwards [ae_restrict_mem hA] with x hx
    exact indicator_of_mem hx u
  have hOff : A.indicator u =ᵐ[volume.restrict (B \ A)] (0 : ℝ^n → F) := by
    filter_upwards [ae_restrict_mem (hB.diff hA)] with x hx
    exact indicator_of_notMem hx.2 u
  have hAA :
      (∫⁻ z, ‖diffQuot n s (A.indicator u) z (p := p)‖ₑ ^ p.toReal
        ∂(volume.restrict A).prod (volume.restrict A)) =
      ∫⁻ z, ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal ∂gagliardoProductMeasure n A :=
    lintegral_congr_ae ((diffQuot_congr_ae (s := s) hOn).fun_comp
      (fun a : F ↦ ‖a‖ₑ ^ p.toReal))
  have hCC :
      (∫⁻ z, ‖diffQuot n s (A.indicator u) z (p := p)‖ₑ ^ p.toReal
        ∂(volume.restrict (B \ A)).prod (volume.restrict (B \ A))) = 0 := by
    have h := lintegral_congr_ae ((diffQuot_congr_ae (s := s) (p := p) hOff).fun_comp
      (fun a : F ↦ ‖a‖ₑ ^ p.toReal))
    simpa only [Function.comp_apply, diffQuot_zero, Pi.zero_apply, enorm_zero,
      ENNReal.zero_rpow_of_pos hp, lintegral_zero] using h
  have hCA := lintegral_diffQuot_rpow_prod_swap (n := n) (s := s) (p := p)
    (A := A) (C := B \ A) (A.indicator u)
  change (∫⁻ z, ‖diffQuot n s (A.indicator u) z (p := p)‖ₑ ^ p.toReal
    ∂(volume.restrict B).prod (volume.restrict B)) = _
  rw [hμ, Measure.add_prod, Measure.prod_add, Measure.prod_add,
    lintegral_add_measure, lintegral_add_measure, lintegral_add_measure, hAA, hCC, hCA]
  simp only [add_zero, two_mul, add_assoc]

/-- The exact quadratic decomposition used in relative-extension norm estimates. -/
theorem gagliardoSq_indicator_eq (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (u : ℝ^n → F) :
    gagliardoSq n s B (A.indicator u) = gagliardoSq n s A u +
      2 * ∫⁻ z, (‖diffQuot n s (A.indicator u) z‖₊ : ℝ≥0∞) ^ 2
        ∂(volume.restrict A).prod (volume.restrict (B \ A)) := by
  simpa only [gagliardoSq, ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_eq_nnnorm] using
    lintegral_diffQuot_indicator_eq (s := s) (p := 2) hA hB hAB u (by norm_num)

/-- A positive support gap controls the p-energy of relative zero extension. -/
theorem lintegral_diffQuot_indicator_le_of_gap
    (hs : 0 < s) (hδ : 0 < δ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B)
    (hgap : ∀ x ∈ A, u x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    (∫⁻ z, ‖diffQuot n s (A.indicator u) z (p := p)‖ₑ ^ p.toReal
      ∂gagliardoProductMeasure n B) ≤
      (∫⁻ z, ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal ∂gagliardoProductMeasure n A) +
      2 * ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s)) *
        ((∫⁻ x in A, ‖u x‖ₑ ^ p.toReal) * edgeMass n s (p := p)) := by
  rw [lintegral_diffQuot_indicator_eq hA hB hAB u (ENNReal.toReal_pos hp0 hptop)]
  have hm := lintegral_diffQuot_indicator_mixed_le hs hδ hA (hB.diff hA)
    (show Disjoint A (B \ A) from Set.disjoint_left.mpr (fun _ hx hy ↦ hy.2 hx))
    hgap hp0 hptop
  simpa only [mul_assoc] using add_le_add (le_refl
    (∫⁻ z, ‖diffQuot n s u z (p := p)‖ₑ ^ p.toReal ∂gagliardoProductMeasure n A))
    (mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ≥0∞) ≤ 2))

/-- A support gap controls the squared seminorm of the relative zero extension.
The coefficient uses the finite radial integral from `EdgeKernel`. -/
theorem gagliardoSq_indicator_le_of_gap
    (hs : 0 < s) (hδ : 0 < δ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B)
    (hgap : ∀ x ∈ A, u x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y) :
    gagliardoSq n s B (A.indicator u) ≤ gagliardoSq n s A u +
      2 * ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + 2 * s)) *
        ((∫⁻ x in A, (‖u x‖₊ : ℝ≥0∞) ^ 2) * edgeMass n s) := by
  simpa only [gagliardoSq, ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_eq_nnnorm] using
    lintegral_diffQuot_indicator_le_of_gap (p := 2) hs hδ hA hB hAB hgap
      (by norm_num) (by norm_num)

/-- Relative zero extension preserves intrinsic membership when the active
support is separated from the added portion of the domain. Only `s > 0` and
`0 < p < ∞` are needed, with no boundary regularity or completeness assumption. -/
theorem memGagliardo_indicator_of_gap
    (hs : 0 < s) (hδ : 0 < δ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B)
    (hgap : ∀ x ∈ A, u x ≠ 0 → ∀ y ∈ B \ A, δ ≤ dist x y)
    (hu : MemGagliardo n s A u (p := p))
    (hp0 : p ≠ 0 := by norm_num) (hptop : p ≠ ∞ := by norm_num) :
    MemGagliardo n s B (A.indicator u) (p := p) := by
  have hbase := memLp_indicator_of_subset hA hAB hu.1
  refine ⟨hbase, ?_⟩
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop
    (aestronglyMeasurable_diffQuot hbase.aestronglyMeasurable)]
  apply (lintegral_diffQuot_indicator_le_of_gap hs hδ hA hB hAB hgap hp0 hptop).trans_lt
  have hbaseEnergy := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop
    hu.1.eLpNorm_lt_top
  have hdiffEnergy := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop
    hu.2.eLpNorm_lt_top
  exact ENNReal.add_lt_top.mpr
    ⟨hdiffEnergy, ENNReal.mul_lt_top (by finiteness)
      (ENNReal.mul_lt_top hbaseEnergy (edgeMass_lt_top hs p (ENNReal.toReal_pos hp0 hptop)))⟩

variable {φ : ℝ^n → ℝ}

/-- A compact C¹ cutoff lets us extend a function valued in a real normed space
from a patch to the surrounding measurable domain. The cutoff supplies the support gap;
`s < 1` is used only for multiplication by the cutoff. -/
theorem memGagliardo_indicator_smul_of_contDiff
    (hs0 : 0 < s) (hs1 : s < 1) (hU : IsOpen U) (hB : MeasurableSet B)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hu : MemGagliardo n s (U ∩ B) u (p := p))
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    MemGagliardo n s B ((U ∩ B).indicator (fun x ↦ φ x • u x)) (p := p) := by
  obtain ⟨δ, hδ, hgap⟩ :=
    exists_pos_le_dist_sdiff_inter_of_isCompact (B := B) hc hU hφU
  apply memGagliardo_indicator_of_gap hs0 hδ (hU.measurableSet.inter hB) hB
    inter_subset_right ?_
    (memGagliardo_smul_of_contDiff_hasCompactSupport hs0 hs1 hφ hc hu hp0 hptop)
    hp0 hptop
  intro x _ hx y hy
  apply hgap x ?_ y hy
  apply subset_closure
  exact fun hzero ↦ hx (by simp only [hzero, zero_smul])

variable {u : ℝ^n → ℝ}

/-- A compact C1 cutoff permits extension from a patch of a measurable physical
domain to that physical domain. There is no zero extension across its boundary. -/
theorem memGagliardo_indicator_mul_of_contDiff
    (hs0 : 0 < s) (hs1 : s < 1) (hU : IsOpen U) (hB : MeasurableSet B)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hu : MemGagliardo n s (U ∩ B) u (p := p))
    (hp0 : p ≠ 0 := by norm_num) (hptop : p ≠ ∞ := by norm_num) :
    MemGagliardo n s B ((U ∩ B).indicator (fun x ↦ φ x * u x)) (p := p) :=
  memGagliardo_indicator_smul_of_contDiff hs0 hs1 hU hB hφ hc hφU hu hp0 hptop

end SobolevSpace.Fractional.Localization
