/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Characteristics.OneDimension
import PDE.Analysis.Topology.Order.FirstZero

/-!
# Short-time bounds for a continuous semilinear reaction

A finite-triangle first-contact argument turns bounded Cauchy data and continuity
of the scalar reaction into a uniform amplitude bound on a short slab. The
characteristic estimates then bound both first derivatives. The PDE is
required only on the stated finite time band, which permits time reflection
without prescribing an equation outside the original forward domain.
-/

@[expose] public noncomputable section

open PDE Set Filter
open scoped Topology

namespace WaveEquation

/-- Finite-triangle first contact gives a uniform amplitude bound on a short slab.
Only the initial first jet and the reaction on a fixed bounded scalar interval enter
its size. There is no uniform spatial support hypothesis. -/
theorem norm_lt_of_short_time_semilinearWave {u : ℝ^2 → ℝ} {f : ℝ → ℝ} {a b G B F M : ℝ}
    (hu : ContDiff ℝ 2 u) (hab : a ≤ b) (hBnonneg : 0 ≤ B) (hFnonneg : 0 ≤ F) (hGM : G < M)
    (hsmall : G + (B + F * (b - a)) * (b - a) < M) (hG : ∀ p : ℝ^2, p 0 = a → ‖u p‖ ≤ G)
    (hB : ∀ p : ℝ^2, p 0 = a → ∀ ε : ℝ, ε ^ 2 = 1 → ‖(∂[0] u) p + ε * (∂[1] u) p‖ ≤ B)
    (hf : ∀ z : ℝ, ‖z‖ ≤ M → ‖f z‖ ≤ F)
    (hwave : ∀ p : ℝ^2, p 0 ∈ Icc a b → waveOperator u p + f (u p) = 0) :
    ∀ p : ℝ^2, p 0 ∈ Icc a b → ‖u p‖ < M := by
  intro q hq
  by_contra hfail
  let Ψ : ℝ × ℝ → ℝ^2 := fun z ↦ z.2 • EuclideanSpace.single 0 1 +
      (q 1 + (b - z.2) * z.1) • EuclideanSpace.single 1 1
  have hΨ0 (z : ℝ × ℝ) : Ψ z 0 = z.2 := by simp [Ψ]
  have hΨ1 (z : ℝ × ℝ) : Ψ z 1 = q 1 + (b - z.2) * z.1 := by simp [Ψ]
  have hΨcont : Continuous Ψ := by unfold Ψ; fun_prop
  have hΨq : Ψ (0, q 0) = q := by
    ext i
    fin_cases i <;> simp [Ψ]
  have htest : ∃ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b, M - ‖u (Ψ z)‖ ≤ 0 := by
    refine ⟨(0, q 0), ⟨by norm_num, hq⟩, ?_⟩
    rw [hΨq]
    linarith [le_of_not_gt hfail]
  obtain ⟨z, hz, hzero, hpast⟩ := PDE.Analysis.exists_first_zero_with_nonneg_past
    isCompact_Icc (continuous_const.sub (hu.continuous.comp hΨcont).norm).continuousOn
    (fun x _ ↦ sub_pos.mpr ((hG (Ψ (x, a)) (hΨ0 (x, a))).trans_lt hGM)) htest
  have hprevious (p : ℝ^2) (hp : p 0 ∈ Icc a z.2)
      (hc : |p 1 - q 1| ≤ b - p 0) : ‖u p‖ ≤ M := by
    have hr : 0 ≤ b - p 0 := sub_nonneg.mpr (hp.2.trans hz.2.2)
    have hmem : p 1 - q 1 ∈ (fun x : ℝ ↦ (b - p 0) * x) '' Icc (-1) 1 := by
      rw [image_mul_left_Icc hr (by norm_num : (-1 : ℝ) ≤ 1)]
      simpa only [mul_neg_one, mul_one, mem_Icc] using abs_le.mp hc
    obtain ⟨x, hx, heq⟩ := hmem
    have hmap : Ψ (x, p 0) = p := by
      ext i
      fin_cases i
      · exact hΨ0 _
      · change Ψ (x, p 0) 1 = p 1
        rw [hΨ1]
        change q 1 + (b - p 0) * x = p 1
        linarith
    have he := hpast (x, p 0) ⟨hx, hp⟩
    change 0 ≤ M - ‖u (Ψ (x, p 0))‖ at he
    rw [hmap] at he
    linarith
  have hforcing (p : ℝ^2) (hp : p 0 ∈ Icc a z.2)
      (hc : |p 1 - q 1| ≤ b - p 0) : ‖waveOperator u p‖ ≤ F := by
    have he := hwave p ⟨hp.1, hp.2.trans hz.2.2⟩
    rw [add_eq_zero_iff_eq_neg.mp he, norm_neg]
    exact hf _ (hprevious p hp hc)
  have hztime : Ψ z 0 ∈ Icc a z.2 := by rw [hΨ0]; exact ⟨hz.2.1.le, le_rfl⟩
  have hzcone : |Ψ z 1 - q 1| ≤ b - Ψ z 0 := by
    rw [hΨ0, hΨ1, add_sub_cancel_left, abs_mul, abs_of_nonneg (sub_nonneg.mpr hz.2.2)]
    exact mul_le_of_le_one_right (sub_nonneg.mpr hz.2.2) (abs_le.mpr hz.1)
  have hd := norm_sub_initial_le_on_triangle hFnonneg
    (fun _ _ _ ↦ hu.contDiffAt) hforcing (fun p hp _ ↦ hB p hp) hztime hzcone
  have hinit := hG (Ψ z + (a - Ψ z 0) • EuclideanSpace.single 0 1) (by simp)
  have hnorm := norm_le_norm_sub_add (u (Ψ z)) (u (Ψ z + (a - Ψ z 0) • EuclideanSpace.single 0 1))
  rw [hΨ0] at hd hinit hnorm
  have htime0 : 0 ≤ z.2 - a := sub_nonneg.mpr hz.2.1.le
  have htimele : z.2 - a ≤ b - a := sub_le_sub_right hz.2.2 a
  have hmul : (B + F * (z.2 - a)) * (z.2 - a) ≤ (B + F * (b - a)) * (b - a) :=
    mul_le_mul (add_le_add_right (mul_le_mul_of_nonneg_left htimele hFnonneg) B)
      htimele htime0 (add_nonneg hBnonneg (mul_nonneg hFnonneg (sub_nonneg.mpr hab)))
  change M - ‖u (Ψ z)‖ = 0 at hzero
  linarith

/-- A continuous reaction and a bounded initial first jet yield a uniform bound
for both first derivatives on some forward slab. -/
theorem exists_pos_uniform_partialDeriv_bound_of_semilinearWave {u : ℝ^2 → ℝ} {f : ℝ → ℝ}
    {a b G B : ℝ} (hab : a < b) (hu : ContDiff ℝ 2 u) (hf : Continuous f) (hBnonneg : 0 ≤ B)
    (hG : ∀ p : ℝ^2, p 0 = a → ‖u p‖ ≤ G)
    (hB : ∀ p : ℝ^2, p 0 = a → ∀ ε : ℝ, ε ^ 2 = 1 → ‖(∂[0] u) p + ε * (∂[1] u) p‖ ≤ B)
    (hwave : ∀ p : ℝ^2, p 0 ∈ Icc a b → waveOperator u p + f (u p) = 0) :
    ∃ δ > 0, ∃ L ≥ 0, ∀ p : ℝ^2, p 0 ∈ Icc a (a + δ) → ∀ i : Fin 2, ‖(∂[i] u) p‖ ≤ L := by
  obtain ⟨F₀, hF₀⟩ := (isCompact_Icc.image hf).isBounded.exists_norm_le
    (s := f '' Icc (-(G + 1)) (G + 1))
  let F := max F₀ 0
  have hFnonneg : 0 ≤ F := le_max_right _ _
  have hF (z : ℝ) (hz : ‖z‖ ≤ G + 1) : ‖f z‖ ≤ F :=
    (hF₀ _ ⟨z, abs_le.mp (by simpa only [Real.norm_eq_abs] using hz), rfl⟩).trans (le_max_left _ _)
  have hnear : ∀ᶠ d : ℝ in 𝓝 0, G + (B + F * d) * d < G + 1 := by
    have hc : Continuous (fun d : ℝ ↦ G + (B + F * d) * d) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simp))
  have hright : ∀ᶠ d : ℝ in 𝓝[>] 0, G + (B + F * d) * d < G + 1 := nhdsWithin_le_nhds hnear
  have htime : ∀ᶠ d : ℝ in 𝓝[>] 0, d < b - a := nhdsWithin_le_nhds (gt_mem_nhds (sub_pos.mpr hab))
  obtain ⟨δ, ⟨hδsmall, hδtime⟩, hδ⟩ := ((hright.and htime).and eventually_mem_nhdsWithin).exists
  have hδpos : 0 < δ := hδ
  have hab : a ≤ a + δ := le_add_of_nonneg_right hδpos.le
  have hamp := norm_lt_of_short_time_semilinearWave hu hab hBnonneg hFnonneg
    (by linarith : G < G + 1)
    (by simpa only [add_sub_cancel_left] using hδsmall) hG hB hF
    (fun p hp ↦ hwave p ⟨hp.1, by linarith [hp.2]⟩)
  refine ⟨δ, hδpos, B + F * δ, by positivity, fun p hp i ↦ ?_⟩
  have hforcing (q : ℝ^2) (hq : q 0 ∈ Icc a (a + δ))
      (_ : |q 1 - p 1| ≤ a + δ - q 0) : ‖waveOperator u q‖ ≤ F := by
    rw [add_eq_zero_iff_eq_neg.mp (hwave q ⟨hq.1, by linarith [hq.2]⟩), norm_neg]
    exact hF _ (hamp q hq).le
  have he := norm_partialDeriv_le_on_triangle hFnonneg (fun _ _ _ ↦ hu.contDiffAt)
    hforcing (fun q hq _ ↦ hB q hq) hp
    (by simpa only [sub_self, abs_zero] using sub_nonneg.mpr hp.2) i
  simpa only [add_sub_cancel_left] using he

end WaveEquation
