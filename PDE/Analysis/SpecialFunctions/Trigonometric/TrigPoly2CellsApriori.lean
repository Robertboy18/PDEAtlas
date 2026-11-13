/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Cells
public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Separable

/-!
# Quadratic forms on a cell with an a priori bound

For a matrix `G` of tables and a vector `u`, the quadratic form `f = |G u|²` has the second
derivative `f_ββ = 2 (|G_β u|² + ⟪G u, G_ββ u⟫)`. On a cell the second term is at most
`√M |u| ρ₂` with `M` the maximum of `f` on the cell and `ρ₂` the Frobenius norm of the moments
`μ₂₀(G_{ik})`, so the zeroth moments never enter: with the vertex values at most `V |u|²`, the
bilinear interpolation error gives `M ≤ (V + A) |u|² + B |u| √M`, where `A` collects the squared
first moments and `B` the Frobenius norms of the second moments, times the squared cell widths
over `4`. If `V + A + B ρ ≤ ρ²` and `B < ρ`, then `M ≤ ρ² |u|²` (`quadForm_le_sq_of_cell`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset Set PDE.Analysis.Approximation

variable {Mβ Mθ d d' : ℕ}

private theorem sq_sum_mul_le (u g : Fin d' → ℝ) :
    (∑ k, u k * g k) ^ 2 ≤ (∑ k, u k ^ 2) * ∑ k, g k ^ 2 :=
  sum_mul_sq_le_sq_mul_sq _ _ _

private theorem sq_le_of_abs_le {x r : ℝ} (h : |x| ≤ r) : x ^ 2 ≤ r ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- Rows of a combination: `∑ᵢ (∑ₖ uₖ gᵢₖ)² ≤ |u|² ∑ᵢ ∑ₖ rᵢₖ²` when `|gᵢₖ| ≤ rᵢₖ`. -/
private theorem sum_sq_comb_le (u : Fin d' → ℝ) {g r : Fin d → Fin d' → ℝ}
    (h : ∀ i k, |g i k| ≤ r i k) :
    ∑ i, (∑ k, u k * g i k) ^ 2 ≤ (∑ k, u k ^ 2) * ∑ i, ∑ k, r i k ^ 2 := by
  rw [mul_sum]
  exact sum_le_sum fun i _ ↦ (sq_sum_mul_le u (g i)).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum fun k _ ↦ sq_le_of_abs_le (h i k))
      (sum_nonneg fun _ _ ↦ sq_nonneg _))

/-- The a priori step: `M ≤ (V + A) U + B √U √M` with `V + A + B ρ ≤ ρ²` and `B < ρ` gives
`M ≤ ρ² U`. -/
private theorem le_sq_mul_of_apriori {Mc U V A B ρ : ℝ} (hMc : 0 ≤ Mc) (hU : 0 ≤ U)
    (hB0 : 0 ≤ B) (hV : V + A + B * ρ ≤ ρ ^ 2) (hB : B < ρ)
    (hkey : Mc ≤ (V + A) * U + B * √U * √Mc) : Mc ≤ ρ ^ 2 * U := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ s ^ 2 = U := ⟨√U, Real.sqrt_nonneg _, Real.sq_sqrt hU⟩
  obtain ⟨m, hm, rfl⟩ : ∃ m, 0 ≤ m ∧ m ^ 2 = Mc := ⟨√Mc, Real.sqrt_nonneg _, Real.sq_sqrt hMc⟩
  rw [Real.sqrt_sq hs, Real.sqrt_sq hm] at hkey
  have hρs : 0 ≤ ρ * s := mul_nonneg (hB0.trans hB.le) hs
  -- if `ρ s < m`, then `0 < (m - ρ s) (m + (ρ - B) s) = m² - B s m - (ρ² - B ρ) s²`,
  -- while `hkey` and `V + A ≤ ρ² - B ρ` give `m² - B s m ≤ (ρ² - B ρ) s²`
  have hfin : m ≤ ρ * s := by
    by_contra! h
    have hprod : 0 < (m - ρ * s) * (m + (ρ - B) * s) := mul_pos (sub_pos.2 h)
      (add_pos_of_pos_of_nonneg (hρs.trans_lt h) (mul_nonneg (sub_nonneg.2 hB.le) hs))
    have hVs : (V + A) * s ^ 2 ≤ (ρ ^ 2 - B * ρ) * s ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)
    linarith
  simpa only [mul_pow] using (sq_le_sq₀ hm hρs).2 hfin

/-- **A quadratic form on a cell with an a priori bound.** -/
theorem quadForm_le_sq_of_cell (G : Fin d → Fin d' → TrigPoly2 Mβ Mθ ℝ)
    {R1 R2 S1 S2 : Fin d → Fin d' → ℝ}
    (hR1 : ∀ i k, (G i k).moment 1 0 ≤ R1 i k) (hR2 : ∀ i k, (G i k).moment 2 0 ≤ R2 i k)
    (hS1 : ∀ i k, (G i k).moment 0 1 ≤ S1 i k) (hS2 : ∀ i k, (G i k).moment 0 2 ≤ S2 i k)
    {A₁ A₂ B₁ B₂ : ℝ} (hA₁ : ∑ i, ∑ k, R1 i k ^ 2 ≤ A₁) (hA₂ : ∑ i, ∑ k, S1 i k ^ 2 ≤ A₂)
    (hB₁ : 0 ≤ B₁) (hB₁' : ∑ i, ∑ k, R2 i k ^ 2 ≤ B₁ ^ 2) (hB₂ : 0 ≤ B₂)
    (hB₂' : ∑ i, ∑ k, S2 i k ^ 2 ≤ B₂ ^ 2) {a b c e V ρ : ℝ} (hab : a < b) (hce : c < e)
    (hV : V + ((b - a) ^ 2 * A₁ + (e - c) ^ 2 * A₂) / 4 +
      ((b - a) ^ 2 * B₁ + (e - c) ^ 2 * B₂) / 4 * ρ ≤ ρ ^ 2)
    (hB : ((b - a) ^ 2 * B₁ + (e - c) ^ 2 * B₂) / 4 < ρ) (u : Fin d' → ℝ)
    (hvert : ∀ x ∈ ({a, b} : Set ℝ), ∀ y ∈ ({c, e} : Set ℝ),
      quadForm G x y u ≤ V * ∑ k, u k ^ 2)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c e) :
    quadForm G x y u ≤ ρ ^ 2 * ∑ k, u k ^ 2 := by
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = ∑ k, u k ^ 2 := ⟨_, rfl⟩
  rw [← hUdef] at hvert ⊢
  have hU : 0 ≤ U := hUdef ▸ sum_nonneg fun _ _ ↦ sq_nonneg _
  obtain ⟨T, hTdef⟩ : ∃ T : Fin d → TrigPoly2 Mβ Mθ ℝ, T = fun i ↦ ∑ k, u k • G i k := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ → ℝ, f = fun z w ↦ ∑ i, (T i).eval z w ^ 2 := ⟨_, rfl⟩
  have hfq : ∀ z w, quadForm G z w u = f z w := fun z w ↦ by
    simp only [quadForm, hfdef, hTdef, eval_sum, eval_smul, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hTb : ∀ z w i, (T i).dβ.eval z w = ∑ k, u k * (G i k).dβ.eval z w := fun z w i ↦ by
    simp [hTdef, dβ_sum, dβ_smul, eval_sum, eval_smul]
  have hTbb : ∀ z w i, (T i).dβ.dβ.eval z w = ∑ k, u k * (G i k).dβ.dβ.eval z w :=
    fun z w i ↦ by simp [hTdef, dβ_sum, dβ_smul, eval_sum, eval_smul]
  have hTt : ∀ z w i, (T i).dθ.eval z w = ∑ k, u k * (G i k).dθ.eval z w := fun z w i ↦ by
    simp [hTdef, dθ_sum, dθ_smul, eval_sum, eval_smul]
  have hTtt : ∀ z w i, (T i).dθ.dθ.eval z w = ∑ k, u k * (G i k).dθ.dθ.eval z w :=
    fun z w i ↦ by simp [hTdef, dθ_sum, dθ_smul, eval_sum, eval_smul]
  have hfeq : ∀ z w, f z w = ∑ i, (T i).eval z w ^ 2 := fun z w ↦ by rw [hfdef]
  -- the maximum on the cell
  have hcont : Continuous fun p : ℝ × ℝ ↦ f p.1 p.2 := by
    simp only [hfeq]
    exact continuous_finsetSum _ fun i _ ↦ ((T i).continuous_eval).pow 2
  obtain ⟨p₀, hp₀, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(a, c), ⟨left_mem_Icc.mpr hab.le, left_mem_Icc.mpr hce.le⟩⟩ hcont.continuousOn
  set Mc := f p₀.1 p₀.2
  have hle : ∀ z ∈ Icc a b, ∀ w ∈ Icc c e, f z w ≤ Mc := fun z hz w hw ↦
    hmax (show (z, w) ∈ Icc a b ×ˢ Icc c e from ⟨hz, hw⟩)
  have hMc : 0 ≤ Mc := (sum_nonneg fun _ _ ↦ sq_nonneg _).trans_eq (hfeq _ _).symm
  -- second derivative bounds on the cell
  have hbound : ∀ z ∈ Icc a b, ∀ w ∈ Icc c e,
      |∑ i, 2 * ((T i).dβ.eval z w * (T i).dβ.eval z w + (T i).eval z w * (T i).dβ.dβ.eval z w)|
        ≤ 2 * (U * A₁ + √Mc * (√U * B₁)) ∧
      |∑ i, 2 * ((T i).dθ.eval z w * (T i).dθ.eval z w + (T i).eval z w * (T i).dθ.dθ.eval z w)|
        ≤ 2 * (U * A₂ + √Mc * (√U * B₂)) := by
    intro z hz w hw
    have hsq : ∀ (D DD : TrigPoly2 Mβ Mθ ℝ → TrigPoly2 Mβ Mθ ℝ) (r1 r2 : Fin d → Fin d' → ℝ)
        (A' B' : ℝ), 0 ≤ B' → (∀ i k, |(D (G i k)).eval z w| ≤ r1 i k) →
        (∀ i k, |(DD (G i k)).eval z w| ≤ r2 i k) → ∑ i, ∑ k, r1 i k ^ 2 ≤ A' →
        ∑ i, ∑ k, r2 i k ^ 2 ≤ B' ^ 2 →
        (∀ i, (D (T i)).eval z w = ∑ k, u k * (D (G i k)).eval z w) →
        (∀ i, (DD (T i)).eval z w = ∑ k, u k * (DD (G i k)).eval z w) →
        |∑ i, 2 * ((D (T i)).eval z w * (D (T i)).eval z w +
          (T i).eval z w * (DD (T i)).eval z w)| ≤ 2 * (U * A' + √Mc * (√U * B')) := by
      intro D DD r1 r2 A' B' hB' h1 h2 hA' hB'' hD hDD
      have e1 : ∑ i, (D (T i)).eval z w * (D (T i)).eval z w ≤ U * A' := by
        simp only [← sq, hD]
        rw [hUdef]
        exact (sum_sq_comb_le u h1).trans (mul_le_mul_of_nonneg_left hA' (hUdef ▸ hU))
      have e2 : ∑ i, ((DD (T i)).eval z w) ^ 2 ≤ U * B' ^ 2 := by
        simp only [hDD]; rw [hUdef]
        exact (sum_sq_comb_le u h2).trans (mul_le_mul_of_nonneg_left hB'' (hUdef ▸ hU))
      -- Cauchy-Schwarz with `∑ᵢ Tᵢ² ≤ M` on the cell
      have e3 : |∑ i, (T i).eval z w * (DD (T i)).eval z w| ≤ √Mc * (√U * B') := by
        refine (Real.abs_le_sqrt (sum_mul_sq_le_sq_mul_sq _ _ _)).trans ?_
        rw [← Real.sqrt_sq hB', ← Real.sqrt_mul hU, ← Real.sqrt_mul hMc]
        exact Real.sqrt_le_sqrt (mul_le_mul (hfeq z w ▸ hle z hz w hw) e2
          (sum_nonneg fun _ _ ↦ sq_nonneg _) hMc)
      rw [← mul_sum, sum_add_distrib, abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ e3)) (by norm_num)
      rwa [abs_of_nonneg (sum_nonneg fun _ _ ↦ mul_self_nonneg _)]
    exact ⟨hsq dβ (fun p ↦ p.dβ.dβ) R1 R2 A₁ B₁ hB₁
        (fun i k ↦ (abs_eval_dβ_le _ z w).trans (hR1 i k))
        (fun i k ↦ (abs_eval_dβ_dβ_le _ z w).trans (hR2 i k)) hA₁ hB₁' (hTb z w) (hTbb z w),
      hsq dθ (fun p ↦ p.dθ.dθ) S1 S2 A₂ B₂ hB₂
        (fun i k ↦ (abs_eval_dθ_le _ z w).trans (hS1 i k))
        (fun i k ↦ (abs_eval_dθ_dθ_le _ z w).trans (hS2 i k)) hA₂ hB₂' (hTt z w) (hTtt z w)⟩
  -- the interpolation error at every point of the cell
  have hpoint : ∀ z ∈ Icc a b, ∀ w ∈ Icc c e, f z w ≤ V * U +
      2 * (U * A₁ + √Mc * (√U * B₁)) * (b - a) ^ 2 / 8 +
      2 * (U * A₂ + √Mc * (√U * B₂)) * (e - c) ^ 2 / 8 := by
    intro z hz w hw
    have hff : f = fun z w ↦ ∑ i, (T i).eval z w ^ 2 := hfdef
    subst hff
    have hfx : ∀ s t, HasDerivAt (fun r ↦ ∑ i, (T i).eval r t ^ 2)
        (∑ i, 2 * ((T i).eval s t * (T i).dβ.eval s t)) s := fun s t ↦
      HasDerivAt.fun_sum fun i _ ↦ ((hasDerivAt_eval_β (T i) s t).pow 2).congr_deriv (by ring)
    have hfxx : ∀ s t, HasDerivAt (fun r ↦ ∑ i, 2 * ((T i).eval r t * (T i).dβ.eval r t))
        (∑ i, 2 * ((T i).dβ.eval s t * (T i).dβ.eval s t +
          (T i).eval s t * (T i).dβ.dβ.eval s t)) s := fun s t ↦ HasDerivAt.fun_sum fun i _ ↦
      ((hasDerivAt_eval_β (T i) s t).mul (hasDerivAt_eval_β (T i).dβ s t)).const_mul 2
    have hfy : ∀ s t, HasDerivAt (fun r ↦ ∑ i, (T i).eval s r ^ 2)
        (∑ i, 2 * ((T i).eval s t * (T i).dθ.eval s t)) t := fun s t ↦
      HasDerivAt.fun_sum fun i _ ↦ ((hasDerivAt_eval_θ (T i) s t).pow 2).congr_deriv (by ring)
    have hfyy : ∀ s t, HasDerivAt (fun r ↦ ∑ i, 2 * ((T i).eval s r * (T i).dθ.eval s r))
        (∑ i, 2 * ((T i).dθ.eval s t * (T i).dθ.eval s t +
          (T i).eval s t * (T i).dθ.dθ.eval s t)) t := fun s t ↦ HasDerivAt.fun_sum fun i _ ↦
      ((hasDerivAt_eval_θ (T i) s t).mul (hasDerivAt_eval_θ (T i).dθ s t)).const_mul 2
    have herr := abs_sub_bilinearInterpolant_le (f := fun z w ↦ ∑ i, (T i).eval z w ^ 2)
      (fx := fun s t ↦ ∑ i, 2 * ((T i).eval s t * (T i).dβ.eval s t))
      (fxx := fun s t ↦ ∑ i, 2 * ((T i).dβ.eval s t * (T i).dβ.eval s t +
        (T i).eval s t * (T i).dβ.dβ.eval s t))
      (fy := fun s t ↦ ∑ i, 2 * ((T i).eval s t * (T i).dθ.eval s t))
      (fyy := fun s t ↦ ∑ i, 2 * ((T i).dθ.eval s t * (T i).dθ.eval s t +
        (T i).eval s t * (T i).dθ.dθ.eval s t))
      hab hce
      (fun t _ ↦ (continuous_iff_continuousAt.2 fun r ↦ (hfx r t).continuousAt).continuousOn)
      (fun t _ s _ ↦ hfx s t) (fun t _ s _ ↦ hfxx s t)
      (fun t ht s hs ↦ (hbound s (Ioo_subset_Icc_self hs) t ht).1)
      (fun s _ ↦ (continuous_iff_continuousAt.2 fun r ↦ (hfy s r).continuousAt).continuousOn)
      (fun s _ t _ ↦ hfy s t) (fun s _ t _ ↦ hfyy s t)
      (fun s hs t ht ↦ (hbound s hs t (Ioo_subset_Icc_self ht)).2) hz hw
    have hint := bilinearInterpolant_le (f := fun z w ↦ ∑ i, (T i).eval z w ^ 2) (B := V * U)
      hab hce hz hw
      (by simpa only [hfq] using hvert a (by simp) c (by simp))
      (by simpa only [hfq] using hvert a (by simp) e (by simp))
      (by simpa only [hfq] using hvert b (by simp) c (by simp))
      (by simpa only [hfq] using hvert b (by simp) e (by simp))
    linarith [(abs_le.mp herr).2]
  -- the a priori inequality at the maximum and its consequence
  have hkey : Mc ≤ (V + ((b - a) ^ 2 * A₁ + (e - c) ^ 2 * A₂) / 4) * U +
      ((b - a) ^ 2 * B₁ + (e - c) ^ 2 * B₂) / 4 * √U * √Mc :=
    (hpoint p₀.1 hp₀.1 p₀.2 hp₀.2).trans_eq (by ring)
  rw [hfq]
  exact (hle x hx y hy).trans (le_sq_mul_of_apriori hMc hU (by positivity) hV hB hkey)

end PDE.Analysis.TrigPoly2
