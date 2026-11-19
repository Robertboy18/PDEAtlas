/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Primitive.Parametric
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Compactly supported primitives with parameters

A smooth compactly supported function whose integral vanishes on every fiber
has a smooth compactly supported primitive in that coordinate. The primitive
retains support in any open product containing the original support.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Vanishing fiber integrals make the coordinate primitive compactly supported,
with no enlargement beyond the original open product. -/
theorem exists_compactSupport_partial_primitive
    {a b : ℝ} {U : Set E} {φ : ℝ × E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ioo a b ×ˢ U)
    (hzero : ∀ x, ∫ t, φ (t, x) = 0) :
    ∃ ψ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo a b ×ˢ U ∧
      ∀ p, fderiv ℝ ψ p (1, 0) = φ p := by
  rcases (tsupport φ).eq_empty_or_nonempty with hempty | hne
  · have hz : φ = 0 := by
      ext x
      exact image_eq_zero_of_notMem_tsupport (by simp [hempty])
    subst φ
    exact ⟨0, contDiff_const, HasCompactSupport.zero, by simp, by simp⟩
  let K := Prod.snd '' tsupport φ
  have hK : IsCompact K := hcs.image continuous_snd
  have hfirst : IsCompact (Prod.fst '' tsupport φ) := hcs.image continuous_fst
  obtain ⟨l, hl⟩ := hfirst.exists_isLeast (hne.image Prod.fst)
  obtain ⟨r, hr⟩ := hfirst.exists_isGreatest (hne.image Prod.fst)
  have hal : a < l := by
    obtain ⟨p, hp, heq⟩ := hl.1
    exact heq ▸ (hsupp hp).1.1
  have hrb : r < b := by
    obtain ⟨p, hp, heq⟩ := hr.1
    exact heq ▸ (hsupp hp).1.2
  let ψ := -backwardPrimitive φ b
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := (contDiff_backwardPrimitive hφ b).neg
  have hsupport : Function.support ψ ⊆ Icc l r ×ˢ K := by
    intro p hp
    by_contra hnot
    apply hp
    change -(∫ t in p.1..b, φ (t, p.2)) = 0
    rw [neg_eq_zero]
    by_cases hx : p.2 ∈ K
    · have ht : p.1 ∉ Icc l r := fun ht ↦ hnot ⟨ht, hx⟩
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · rw [intervalIntegral.integral_eq_integral_of_support_subset, hzero]
        intro t htφ
        have hs : (t, p.2) ∈ tsupport φ := subset_tsupport φ htφ
        exact ⟨ht.trans_le (hl.2 ⟨(t, p.2), hs, rfl⟩), (hsupp hs).1.2.le⟩
      · apply intervalIntegral.integral_zero_ae
        filter_upwards with t ht'
        apply image_eq_zero_of_notMem_tsupport
        intro hs
        have hrt : r < t :=
          (lt_min ht hrb).trans_le ht'.1.le
        exact (not_lt_of_ge (hr.2 ⟨(t, p.2), hs, rfl⟩)) hrt
    · apply intervalIntegral.integral_zero_ae
      filter_upwards with t _
      exact image_eq_zero_of_notMem_tsupport (fun hs ↦ hx ⟨(t, p.2), hs, rfl⟩)
  have htsupport : tsupport ψ ⊆ Icc l r ×ˢ K :=
    closure_minimal hsupport (isClosed_Icc.prod hK.isClosed)
  refine ⟨ψ, hψ,
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod hK) hsupport,
    htsupport.trans ?_, ?_⟩
  · rintro ⟨t, x⟩ ⟨ht, hx⟩
    obtain ⟨p, hp, heq⟩ := hx
    exact ⟨⟨hal.trans_le ht.1, ht.2.trans_lt hrb⟩, heq ▸ (hsupp hp).2⟩
  · intro p
    rw [fderiv_neg]
    simp only [neg_apply]
    rw [fderiv_backwardPrimitive_time (hφ.of_le (by simp)), neg_neg]

end PDE.Analysis
