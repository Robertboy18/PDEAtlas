/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import PDE.Analysis.Calculus.Jet.Localization

import PDE.Analysis.Calculus.LocalExtension.Cubic.DerivativeBounds
import PDE.Analysis.Calculus.LocalExtension.Cubic.Profile
import CAS.ExactTactic

/-!
# Compact cubic corrections and amplitude localization

A fixed cubic product admits compact corrections with uniformly small derivatives
through order two. The product construction preserves every pointwise zero of
its amplitude, including in the cutoff transition region.

For a residual smooth only on an open parameter domain, a compact state coordinate
and a fixed strip determine a globally smooth compact amplitude. Its zeros are
retained before any correction scale is chosen. Both constructions apply to
normed spaces independently of any conservation law or characteristic family.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace PDE.Analysis

section CubicCorrection

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Localize a fixed cubic product below any positive scale cap, retaining every
pointwise zero of its amplitude. This extra conclusion holds for all states,
including the transition region where only the cutoff formula is available.
The original support bound, uniform bounds through order two, and zero jets on
`m = 0` are unchanged. -/
theorem exists_localized_small_compact_cubic_correction_preserving_zeros
    {m : E → ℝ} {A : E → V}
    (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (εcap : ℝ) (hcap : 0 < εcap)
    {η : ℝ} (hη : 0 < η) :
    ∃ (ε : ℝ) (P : E → V),
      0 < ε ∧ ε < εcap ∧ ε ≤ 1 ∧ ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ tsupport A ∩ {x | |m x| ≤ 2 * ε} ∧
      (∀ x, |m x| ≤ ε → P x = (m x) ^ 3 • A x) ∧
      (∀ x, A x = 0 → P x = 0) ∧
      (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P x‖ < η) ∧
      ∀ x, m x = 0 → ∀ n ≤ 2, iteratedFDeriv ℝ n P x = 0 := by
  obtain ⟨φ, C, hC, hφ, _, _, hφ0, hφ1, hφ2, hz0, hz1, hz2, hscale⟩ :=
    exists_cubic_cutoff_profile
  obtain ⟨Dₘ, _, hDₘ⟩ := hmc.exists_bound_iteratedFDeriv hm 2
  obtain ⟨Dₐ, _, hDₐ⟩ := hAc.exists_bound_iteratedFDeriv hA 2
  let D : ℝ := max 1 (max Dₘ Dₐ)
  have hD : 1 ≤ D := le_max_left _ _
  have hmBound (i : ℕ) (hi : i ≤ 2) (x : E) :
      ‖iteratedFDeriv ℝ i m x‖ ≤ D :=
    (hDₘ i hi x).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hABound (i : ℕ) (hi : i ≤ 2) (x : E) :
      ‖iteratedFDeriv ℝ i A x‖ ≤ D :=
    (hDₐ i hi x).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  let K : ℝ := 8 * D ^ 3 * C
  have hK : 0 < K := by positivity
  -- The input functions and their derivative bounds are fixed before this choice.
  let ε : ℝ := min (εcap / 2) (min 1 (η / (2 * K)))
  have hε : 0 < ε :=
    lt_min (half_pos hcap) (lt_min zero_lt_one (div_pos hη (mul_pos (by norm_num) hK)))
  have hεcap : ε < εcap := (min_le_left _ _).trans_lt (half_lt_self hcap)
  have hεone : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεratio : ε ≤ η / (2 * K) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : K * ε < η := by
    have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hK)).mp hεratio
    cas using [hmul, hη]
  let g : ℝ → ℝ := cubicRescale φ ε
  let P : E → V := fun x ↦ g (m x) • A x
  have hg : ContDiff ℝ ∞ g := contDiff_cubicRescale hφ ε
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by simp)
  have hm2 : ContDiff ℝ 2 m := hm.of_le (by simp)
  have hA2 : ContDiff ℝ 2 A := hA.of_le (by simp)
  -- continuity transports the closed support bound of `g`, including its boundary
  have hsupport : tsupport P ⊆ tsupport A ∩ {x | |m x| ≤ 2 * ε} := fun x hx ↦
    ⟨tsupport_smul_subset_right (g ∘ m) A hx, by
      simpa only [mem_ofPred_eq, mem_closedBall_zero_iff, Real.norm_eq_abs] using (hscale ε hε).2.1
        (tsupport_comp_subset_preimage g hm.continuous (tsupport_smul_subset_left (g ∘ m) A hx))⟩
  refine ⟨ε, P, hε, hεcap, hεone, (hg.comp hm).smul hA, hAc.smul_left,
    hsupport, ?_, ?_, ?_, ?_⟩
  · exact fun x hx ↦ congrArg (· • A x) ((hscale ε hε).1 (m x) hx)
  · exact fun x hx ↦ by simp only [P, hx, smul_zero]
  · intro n hn x
    exact (norm_iteratedFDeriv_cubicRescale_comp_smul_le
      (hφ.of_le (by simp)) hm2 hA2 hD hε hεone hφ0 hφ1 hφ2 x
      (fun i _ hi ↦ hmBound i hi x) (fun i hi ↦ hABound i hi x) hn).trans_lt hsmall
  · intro x hx n hn
    -- Zero scalar jets force zero composition jets, then zero product jets.
    obtain ⟨hg0, hg1, hg2zero⟩ :=
      cubicRescale_zero_jets (hφ.of_le (by simp)) hε.ne' hz0 hz1 hz2
    have hscalar (i : ℕ) (hi : i ≤ 2) :
        ‖iteratedFDeriv ℝ i g (m x)‖ ≤ 0 := by
      rw [hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      interval_cases i
      · simp only [iteratedDeriv_zero, g, hg0, norm_zero, le_refl]
      · simp only [iteratedDeriv_one, g, hg1, norm_zero, le_refl]
      · simp only [iteratedDeriv_succ, iteratedDeriv_zero,
          g, hg2zero, norm_zero, le_refl]
    have hinner (i : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2) :
        ‖iteratedFDeriv ℝ i m x‖ ≤ D ^ i := by
      refine (hmBound i hi2 x).trans ?_
      interval_cases i
      · simp only [pow_one, le_refl]
      · cas using [hD]
    have hcomp (i : ℕ) (hi : i ≤ 2) :
        ‖iteratedFDeriv ℝ i (g ∘ m) x‖ = 0 := by
      have hiOrder : (i : ℕ∞ω) ≤ 2 := by exact_mod_cast hi
      apply le_antisymm _ (norm_nonneg _)
      simpa only [mul_zero, zero_mul] using
        norm_iteratedFDeriv_comp_le hg2 hm2 hiOrder x
          (fun j hj ↦ hscalar j (hj.trans hi))
          (fun j hj hji ↦ hinner j hj (hji.trans hi))
    have hnOrder : (n : ℕ∞ω) ≤ 2 := by exact_mod_cast hn
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_iteratedFDeriv_smul_le (hg2.comp hm2) hA2 x hnOrder).trans ?_
    apply Finset.sum_nonpos
    intro i hi
    have hi2 : i ≤ 2 := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn
    rw [hcomp i hi2, mul_zero, zero_mul]

end CubicCorrection

/-- Localize the residual around a fixed compact strip and preserve its zeros
under the state coordinate. The residual need only be smooth on its open domain.
Outside the localization domain the indicator is zero; inside it the amplitude
is a scalar multiple of the pulled-back residual. Thus the zero implication has
no domain premise and precedes every choice of correction scale. -/
theorem exists_compact_amplitude_of_strip_coordinates_preserving_zeros
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {w R : ℝ × ℝ → E} {coord : E → (ℝ × ℝ) × ℝ}
    {K : Set ℝ} {Ω : Set (ℝ × ℝ)} {U : Set E} {r : ℝ}
    (hw : Continuous w) (hK : IsCompact K) (hcoord : ContDiff ℝ ∞ coord)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hR : ContDiffOn ℝ ∞ R Ω)
    (hstate : MapsTo w (K ×ˢ Icc (-r) r) U)
    (hdomain : K ×ˢ Icc (-r) r ⊆ Ω)
    (hrecover : ∀ p ∈ K ×ˢ Icc (-r) r, coord (w p) = (p, 0)) :
    ∃ A : E → E, ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
      tsupport A ⊆ U ∩ (fun x ↦ (coord x).1) ⁻¹' Ω ∧
      (∀ p ∈ K ×ˢ Icc (-r) r, A (w p) = R p) ∧
      ∀ x, R ((coord x).1) = 0 → A x = 0 := by
  classical
  let V : Set E := U ∩ (fun x ↦ (coord x).1) ⁻¹' Ω
  let Q : E → E := fun x ↦ R (coord x).1
  have hV : IsOpen V := hU.inter (hΩ.preimage hcoord.fst.continuous)
  have hQ : ContDiffOn ℝ ∞ Q V :=
    hR.comp hcoord.fst.contDiffOn (fun _ hx ↦ hx.2)
  have himage : w '' (K ×ˢ Icc (-r) r) ⊆ V := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨hstate hp, show (coord (w p)).1 ∈ Ω by rw [hrecover p hp]; exact hdomain hp⟩
  obtain ⟨χ, N, _, _, _, _, _, himageN, _, _, hrep⟩ :=
    exists_smooth_cutoff_localization hQ hV ((hK.prod isCompact_Icc).image hw) himage
  let A : E → E := V.indicator (fun x ↦ χ x • Q x)
  refine ⟨A, hrep.1, hrep.2.1, hrep.2.2.1, ?_, ?_⟩
  · intro p hp
    have hpN : w p ∈ N := himageN ⟨p, hp, rfl⟩
    calc
      A (w p) = Q (w p) := hrep.2.2.2 hpN
      _ = R p := by
        change R (coord (w p)).1 = R p
        rw [hrecover p hp]
  · intro x hx
    change V.indicator (fun y ↦ χ y • R ((coord y).1)) x = 0
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem hxV, hx, smul_zero]
    · rw [indicator_of_notMem hxV]

end PDE.Analysis
