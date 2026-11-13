/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Normalization
import CAS.ExactTactic

/-!
# Smooth compact data matching a Goursat family

Annular gluing gives one jointly smooth compact Cauchy-data family with a common support radius,
an exact radial match and the prescribed zero-amplitude baseline.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- A globally normalized characteristic field yields compact varying smooth
data with a prescribed zero-parameter baseline and exact scaled Goursat traces
on a fixed narrow annulus. -/
theorem exists_smooth_compact_goursat_data_with_baseline {W Z : Parameter → ℝ} (hZ : ContDiff ℝ ∞ Z)
    {η σ : ℝ} (hσsmall : σ ≤ 1 / 4) (hση : σ < η)
    (hzero : ∀ a b : ℝ, |a| < η → |b| < η → Z (a, b, 0) = a)
    (hscale : ∀ a b : ℝ, |a| < η → |b| < η → ∀ ε : ℝ, ε * Z (a, b, ε) = W (a, b, ε))
    {g₀ h₀ : ℝ^3 → ℝ} (hg₀ : ContDiff ℝ ∞ g₀) (hh₀ : ContDiff ℝ ∞ h₀) (hgs₀ : HasCompactSupport g₀)
    (hhs₀ : HasCompactSupport h₀)
    (hdata₀ : ∀ x : ℝ^3, |‖x‖ - 1| < σ → g₀ x = (‖x‖ - 1) / ‖x‖ ∧ h₀ x = 1 / ‖x‖) :
    ∃ g h : ℝ → ℝ^3 → ℝ, ContDiff ℝ ∞ (Function.uncurry g) ∧
      ContDiff ℝ ∞ (Function.uncurry h) ∧ g 0 = g₀ ∧ h 0 = h₀ ∧
      ∃ K : Set (ℝ^3), IsCompact K ∧
        (∀ ε : ℝ, ∀ x ∉ K, g ε x = 0 ∧ h ε x = 0) ∧
        ∀ ε : ℝ, ∀ x : ℝ^3, |‖x‖ - 1| < σ →
          ε * g ε x = W (‖x‖ - 1, 1 - ‖x‖, ε) / ‖x‖ ∧
          HasDerivAt (fun t : ℝ ↦
            W (t + ‖x‖ - 1, t - ‖x‖ + 1, ε) / ‖x‖) (ε * h ε x) 0 := by
  have hn : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ^3 ↦ ‖x‖) {0}ᶜ := fun x hx ↦
    (contDiffAt_norm ℝ hx).contDiffWithinAt
  have hi : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ^3 ↦ (‖x‖)⁻¹) {0}ᶜ := fun x hx ↦
    ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).contDiffWithinAt
  obtain ⟨ρ, hρ, _, hρeq⟩ := hn.exists_contDiff_compactSupport_eqOn_annulus
    (a := 1 / 2) (b := 3 / 2) (by norm_num) (by norm_num)
  obtain ⟨j, hj, hjs, hjeq⟩ := hi.exists_contDiff_compactSupport_eqOn_annulus
    (a := 1 / 2) (b := 3 / 2) (by norm_num) (by norm_num)
  let A : ℝ × ℝ^3 → ℝ := fun p ↦ j p.2 * Z (ρ p.2 - 1, 1 - ρ p.2, p.1)
  let B : ℝ × ℝ^3 → ℝ := fun p ↦ j p.2 * fderiv ℝ Z (ρ p.2 - 1, 1 - ρ p.2, p.1) (1, 1, 0)
  have hpath : ContDiff ℝ ∞ (fun p : ℝ × ℝ^3 ↦ (ρ p.2 - 1, 1 - ρ p.2, p.1)) :=
    ((hρ.comp contDiff_snd).sub contDiff_const).prodMk
      ((contDiff_const.sub (hρ.comp contDiff_snd)).prodMk contDiff_fst)
  have hA : ContDiff ℝ ∞ A := (hj.comp contDiff_snd).mul (hZ.comp hpath)
  have hdZ : ContDiff ℝ ∞ (fderiv ℝ Z) := hZ.fderiv_right (by simp)
  have hB : ContDiff ℝ ∞ B := (hj.comp contDiff_snd).mul ((hdZ.comp hpath).clm_apply contDiff_const)
  let g : ℝ → ℝ^3 → ℝ := fun ε x ↦ g₀ x + (A (ε, x) - A (0, x))
  let h : ℝ → ℝ^3 → ℝ := fun ε x ↦ h₀ x + (B (ε, x) - B (0, x))
  let K : Set (ℝ^3) := tsupport g₀ ∪ tsupport h₀ ∪ tsupport j
  refine ⟨g, h, (hg₀.comp contDiff_snd).add (hA.sub (hA.comp (contDiff_const.prodMk contDiff_snd))),
    (hh₀.comp contDiff_snd).add (hB.sub (hB.comp (contDiff_const.prodMk contDiff_snd))),
    by funext x; simp only [g, sub_self, add_zero],
    by funext x; simp only [h, sub_self, add_zero],
    K, (hgs₀.isCompact.union hhs₀.isCompact).union hjs.isCompact, ?_, ?_⟩
  · intro ε x hx
    have hxg : x ∉ tsupport g₀ := fun hmem ↦ hx (Or.inl (Or.inl hmem))
    have hxh : x ∉ tsupport h₀ := fun hmem ↦ hx (Or.inl (Or.inr hmem))
    have hxj : x ∉ tsupport j := fun hmem ↦ hx (Or.inr hmem)
    simp only [g, h, A, B, image_eq_zero_of_notMem_tsupport hxg,
      image_eq_zero_of_notMem_tsupport hxh, image_eq_zero_of_notMem_tsupport hxj,
      zero_mul, sub_self, add_zero, and_self]
  · intro ε x hx
    have hx' := abs_lt.mp hx
    have hlow : (1 : ℝ) / 2 ≤ ‖x‖ := by linarith
    have hhigh : ‖x‖ ≤ (3 : ℝ) / 2 := by linarith
    have ha : |‖x‖ - 1| < η := hx.trans hση
    have hb : |1 - ‖x‖| < η := by simpa only [abs_sub_comm] using ha
    have hρx := hρeq x hlow hhigh
    have hjx := hjeq x hlow hhigh
    have hAx : A (0, x) = g₀ x := by
      rw [(hdata₀ x hx).1]
      simp only [A, hρx, hjx, hzero _ _ ha hb, div_eq_inv_mul]
    have hBx : B (0, x) = h₀ x := by
      rw [(hdata₀ x hx).2]
      simp only [B, hρx, hjx,
        normalized_goursat_zero_time_fderiv (hZ.of_le (by simp)) hzero ha hb, mul_one, one_div]
    have hgx : g ε x = A (ε, x) := by simp [g, ← hAx]
    have hhx : h ε x = B (ε, x) := by simp [h, ← hBx]
    constructor
    · rw [hgx]
      dsimp only [A]
      rw [hρx, hjx, ← hscale _ _ ha hb ε]
      generalize Z (‖x‖ - 1, 1 - ‖x‖, ε) = z
      generalize ‖x‖ = r
      cas
    · have hpathD : HasDerivAt (fun t : ℝ ↦ (t + ‖x‖ - 1, t - ‖x‖ + 1, ε)) (1, 1, 0) 0 :=
        (((hasDerivAt_id' 0).add_const _).sub_const _).prodMk
          ((((hasDerivAt_id' 0).sub_const _).add_const _).prodMk (hasDerivAt_const _ ε))
      have hd := ((hZ.differentiable (by norm_num)
        (0 + ‖x‖ - 1, 0 - ‖x‖ + 1, ε)).hasFDerivAt.comp_hasDerivAt 0 hpathD).div_const ‖x‖
      have hcomm : -‖x‖ + 1 = 1 - ‖x‖ := by ring
      have hd' : HasDerivAt (fun t : ℝ ↦
          Z (t + ‖x‖ - 1, t - ‖x‖ + 1, ε) / ‖x‖) (B (ε, x)) 0 := by
        simpa only [Function.comp_def, zero_add, zero_sub, B, hρx, hjx,
          div_eq_inv_mul, hcomm] using hd
      rw [hhx]
      apply (hd'.const_mul ε).congr_of_eventuallyEq
      have hca : Continuous (fun t : ℝ ↦ |t + ‖x‖ - 1|) := by fun_prop
      have hcb : Continuous (fun t : ℝ ↦ |t - ‖x‖ + 1|) := by fun_prop
      filter_upwards [hca.continuousAt.eventually (gt_mem_nhds (by simpa using ha)),
        hcb.continuousAt.eventually (gt_mem_nhds (by simpa [hcomm] using hb))] with t hta htb
      rw [← hscale _ _ hta htb ε]
      generalize Z (t + ‖x‖ - 1, t - ‖x‖ + 1, ε) = z
      generalize ‖x‖ = r
      cas

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
