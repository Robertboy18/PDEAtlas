/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Compactly supported approximation in Schwartz space

Multiplying a Schwartz map by expanding smooth cutoffs gives convergence in every Schwartz
seminorm. The approximants have compact support contained in the support of the original map.
-/

@[expose] public noncomputable section

open Filter Set
open scoped SchwartzMap Topology ContDiff

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The finite Leibniz bound, with the polynomial weight absorbed into Schwartz seminorms. -/
theorem norm_pow_mul_iteratedFDeriv_smul_le
    (f : 𝓢(E, F)) {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    {C : ℕ → ℝ} (hC : ∀ i x, ‖iteratedFDeriv ℝ i g x‖ ≤ C i)
    (k n : ℕ) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ g y • f y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * C i * SchwartzMap.seminorm ℝ k (n - i) f := by
  calc
    _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖ := by
      gcongr
      exact norm_iteratedFDeriv_smul_le hg f.smooth' x (mod_cast le_top)
    _ = ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
      rw [Finset.mul_sum]
      congr 1
      ext i
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have : 0 ≤ C i := (norm_nonneg _).trans (hC i x)
      gcongr
      · exact hC i x
      · exact f.le_seminorm ℝ k (n - i) x

/-- A multiplier vanishing on a large ball gains an inverse radius in each Schwartz seminorm.

One additional power of decay controls the tail, while the finite Leibniz sum controls all
derivatives of the product. -/
theorem seminorm_smulLeftCLM_le_div
    (f : 𝓢(E, F)) {g : E → ℝ} (hg : g.HasTemperateGrowth)
    {C : ℕ → ℝ} (hC : ∀ i x, ‖iteratedFDeriv ℝ i g x‖ ≤ C i)
    {R : ℝ} (hR : 0 < R) (hzero : ∀ x, ‖x‖ < R → g x = 0) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n (smulLeftCLM F g f) ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * C i * SchwartzMap.seminorm ℝ (k + 1) (n - i) f) / R := by
  have hC_nonneg (i : ℕ) : 0 ≤ C i := (norm_nonneg _).trans (hC i 0)
  have hbound : 0 ≤ (∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * C i * SchwartzMap.seminorm ℝ (k + 1) (n - i) f) / R :=
    div_nonneg (Finset.sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC_nonneg i))
        (apply_nonneg _ _)) hR.le
  apply seminorm_le_bound ℝ k n _ hbound
  intro x
  rw [smulLeftCLM_apply hg]
  by_cases hx : ‖x‖ < R
  · have heq : (fun y ↦ g y • f y) =ᶠ[𝓝 x] (fun _ ↦ (0 : F)) := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hx] with y hy
      simp [hzero y hy]
    rw [heq.iteratedFDeriv (𝕜 := ℝ) n |>.eq_of_nhds]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using hbound
  · rw [le_div_iff₀ hR]
    calc
      _ ≤ (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ g y • f y) x‖) * ‖x‖ := by
        gcongr
        exact le_of_not_gt hx
      _ = ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ n (fun y ↦ g y • f y) x‖ := by
        rw [pow_succ]
        ring
      _ ≤ _ := f.norm_pow_mul_iteratedFDeriv_smul_le hg.1 hC (k + 1) n x

/-- Contracting the argument does not increase the unweighted derivative bounds. -/
theorem norm_iteratedFDeriv_comp_smul_le_seminorm
    (f : 𝓢(E, F)) {a : ℝ} (ha : ‖a‖ ≤ 1) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ f (a • y)) x‖ ≤ SchwartzMap.seminorm ℝ 0 n f := by
  rw [iteratedFDeriv_comp_const_smul a (f.smooth n)]
  change ‖a ^ n • iteratedFDeriv ℝ n f (a • x)‖ ≤ _
  rw [norm_smul, norm_pow]
  calc
    _ ≤ 1 * SchwartzMap.seminorm ℝ 0 n f :=
      mul_le_mul (pow_le_one₀ (norm_nonneg _) ha)
        (f.norm_iteratedFDeriv_le_seminorm ℝ n (a • x)) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- The error of a dilated cutoff is controlled by one additional power of Schwartz decay. -/
theorem seminorm_smulLeftCLM_comp_smul_sub_le
    (χ : 𝓢(E, ℝ)) (hχ : ∀ x, ‖x‖ < 1 → χ x = 1) (f : 𝓢(E, F))
    {R : ℝ} (hR : 1 ≤ R) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
        (smulLeftCLM F (fun x ↦ χ (R⁻¹ • x)) f - f) ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (SchwartzMap.seminorm ℝ 0 i χ + 1) *
          SchwartzMap.seminorm ℝ (k + 1) (n - i) f) / R := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have ha : ‖R⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    exact inv_le_one_of_one_le₀ hR
  have htemp : (fun x ↦ χ (R⁻¹ • x)).HasTemperateGrowth := by fun_prop
  have htemp_sub : (fun x ↦ χ (R⁻¹ • x) - 1).HasTemperateGrowth := by fun_prop
  have heq : smulLeftCLM F (fun x ↦ χ (R⁻¹ • x)) f - f =
      smulLeftCLM F (fun x ↦ χ (R⁻¹ • x) - 1) f := by
    ext x
    simp [htemp, htemp_sub, sub_smul]
  rw [heq]
  apply f.seminorm_smulLeftCLM_le_div htemp_sub
  · intro i x
    have hconst : ‖iteratedFDeriv ℝ i (fun _ : E ↦ (1 : ℝ)) x‖ ≤ 1 := by
      cases i with
      | zero => simp [norm_iteratedFDeriv_zero]
      | succ i => simp [iteratedFDeriv_succ_const]
    change ‖iteratedFDeriv ℝ i
      ((fun y ↦ χ (R⁻¹ • y)) - (fun _ ↦ (1 : ℝ))) x‖ ≤ _
    have hsm : ContDiff ℝ i (fun y ↦ χ (R⁻¹ • y)) :=
      (χ.smooth i).comp (contDiff_const.smul contDiff_id)
    rw [iteratedFDeriv_sub hsm (show ContDiff ℝ i (fun _ : E ↦ (1 : ℝ)) from contDiff_const)]
    exact (norm_sub_le _ _).trans
      (add_le_add (χ.norm_iteratedFDeriv_comp_smul_le_seminorm ha i x) hconst)
  · exact hRpos
  · intro x hx
    rw [hχ, sub_self]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    exact (inv_mul_lt_one₀ hRpos).mpr hx

/-- Expanding a smooth cutoff equal to one on the unit ball approximates every Schwartz map
in the Schwartz topology. -/
theorem tendsto_smulLeftCLM_comp_inv_smul
    (χ : 𝓢(E, ℝ)) (hχ : ∀ x, ‖x‖ < 1 → χ x = 1) (f : 𝓢(E, F)) :
    Tendsto (fun R : ℝ ↦ smulLeftCLM F (fun x ↦ χ (R⁻¹ • x)) f) atTop (𝓝 f) := by
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds_atTop]
  rintro ⟨k, n⟩ ε hε
  let C := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * (SchwartzMap.seminorm ℝ 0 i χ + 1) *
      SchwartzMap.seminorm ℝ (k + 1) (n - i) f
  refine ⟨max 1 (C / ε + 1), fun R hR ↦ ?_⟩
  have hRone : 1 ≤ R := (le_max_left _ _).trans hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hRone
  apply (seminorm_smulLeftCLM_comp_smul_sub_le χ hχ f hRone k n).trans_lt
  change C / R < ε
  rw [div_lt_iff₀ hRpos]
  have hCR : C / ε < R :=
    (lt_add_one _).trans_le ((le_max_right _ _).trans hR)
  simpa only [mul_comm] using (div_lt_iff₀ hε).mp hCR

variable [FiniteDimensional ℝ E]

/-- Every Schwartz map is the Schwartz-topology limit of compactly supported smooth cutoffs
of itself. In particular, the approximants have support contained in its original support. -/
theorem exists_tendsto_hasCompactSupport (f : 𝓢(E, F)) :
    ∃ u : ℕ → 𝓢(E, F),
      (∀ m, HasCompactSupport (u m : E → F)) ∧
      (∀ m, tsupport (u m : E → F) ⊆ tsupport (f : E → F)) ∧
      Tendsto u atTop (𝓝 f) := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let χ : 𝓢(E, ℝ) := φ.hasCompactSupport.toSchwartzMap φ.contDiff
  have hχ : ∀ x, ‖x‖ < 1 → χ x = 1 := by
    intro x hx
    exact φ.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, dist_zero_right] using hx.le)
  let u : ℕ → 𝓢(E, F) :=
    fun m ↦ smulLeftCLM F (fun x ↦ χ (((m : ℝ) + 1)⁻¹ • x)) f
  refine ⟨u, ?_, ?_, ?_⟩
  · intro m
    have htemp : (fun x ↦ χ (((m : ℝ) + 1)⁻¹ • x)).HasTemperateGrowth := by fun_prop
    change HasCompactSupport (smulLeftCLM F _ f : E → F)
    rw [smulLeftCLM_apply htemp]
    exact (φ.hasCompactSupport.comp_smul (inv_ne_zero (by positivity))).smul_right
  · intro m
    exact (tsupport_smulLeftCLM_subset _ f).trans inter_subset_left
  · exact (tendsto_smulLeftCLM_comp_inv_smul χ hχ f).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- Compactly supported Schwartz maps with support in `Ω` approximate every Schwartz map
with support in `Ω`. No openness assumption on `Ω` is needed. -/
theorem mem_closure_hasCompactSupport_tsupport_subset
    (f : 𝓢(E, F)) {Ω : Set E} (hf : tsupport (f : E → F) ⊆ Ω) :
    f ∈ closure {g : 𝓢(E, F) | HasCompactSupport (g : E → F) ∧ tsupport (g : E → F) ⊆ Ω} := by
  obtain ⟨u, hc, hs, hu⟩ := exists_tendsto_hasCompactSupport f
  exact mem_closure_of_tendsto hu (Eventually.of_forall fun m ↦ ⟨hc m, (hs m).trans hf⟩)

/-- Requiring compact support does not change the closure of Schwartz maps supported in `Ω`. -/
theorem closure_hasCompactSupport_tsupport_subset (Ω : Set E) :
    closure {g : 𝓢(E, F) | HasCompactSupport (g : E → F) ∧ tsupport (g : E → F) ⊆ Ω} =
      closure {g : 𝓢(E, F) | tsupport (g : E → F) ⊆ Ω} := by
  apply le_antisymm
  · exact closure_mono fun _ hg ↦ hg.2
  · apply closure_minimal _ isClosed_closure
    intro f hf
    exact mem_closure_hasCompactSupport_tsupport_subset f hf

/-- Compactly supported smooth maps are dense in Schwartz space in its own topology. -/
theorem dense_hasCompactSupport : Dense {g : 𝓢(E, F) | HasCompactSupport (g : E → F)} := by
  intro f
  simpa using mem_closure_hasCompactSupport_tsupport_subset f (Ω := univ) (subset_univ _)

end SchwartzMap
