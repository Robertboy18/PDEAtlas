/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import PDE.Analysis.Calculus.LocalExtension.CutoffEstimate
public import PDE.Analysis.Calculus.LocalExtension.RescaledBump

/-!
# Smooth cutoffs with a small derivative

A smooth map with zero first jet at the origin has compactly supported representatives
with arbitrarily small global Lipschitz constant. The construction uses a rescaled bump
in the original norm. Compact support also bounds all higher derivatives; in particular
the first two derivatives of the representative are globally Lipschitz.
-/

@[expose] public section

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

/-- A map of any positive differentiability order with zero first jet at zero has a
compactly supported representative of the same order and arbitrarily small Lipschitz constant. -/
theorem ContDiff.exists_compactSupport_small_lipschitz_of_one_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {N : E → F} {n : ℕ∞}
    (hN : ContDiff ℝ n N) (hn : 1 ≤ n) (hN0 : N 0 = 0) (hDN0 : fderiv ℝ N 0 = 0)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∃ (ρ : ℝ) (Ncut : E → F), 0 < ρ ∧ ρ < r ∧
      ContDiff ℝ n Ncut ∧ HasCompactSupport Ncut ∧
      tsupport Ncut ⊆ ball 0 r ∧
      (∀ x ∈ ball 0 ρ, Ncut x = N x) ∧
      LipschitzWith ⟨ε, hε.le⟩ Ncut ∧
      Ncut 0 = 0 ∧ fderiv ℝ Ncut 0 = 0 := by
  let b : ContDiffBump (0 : E) :=
    { rIn := 1, rOut := 2, rIn_pos := zero_lt_one, rIn_lt_rOut := one_lt_two }
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    b.hasCompactSupport (b.contDiff : ContDiff ℝ ∞ b) (by simp)
  let L : ℝ≥0 := ⟨ε / (1 + 2 * C), by positivity⟩
  have hL : 0 < (L : ℝ) := by
    change 0 < ε / (1 + 2 * (C : ℝ))
    positivity
  have hbudget : (L : ℝ) + 2 * C * L = ε := by
    change ε / (1 + 2 * (C : ℝ)) + 2 * C * (ε / (1 + 2 * C)) = ε
    calc
      _ = (1 + 2 * C) * (ε / (1 + 2 * C)) := by ring
      _ = ε := mul_div_cancel₀ _ (by positivity)
  have hn' : (1 : ℕ∞ω) ≤ n := by exact_mod_cast hn
  have hN1 : ContDiffAt ℝ 1 N 0 := (hN.of_le hn').contDiffAt
  obtain ⟨U, hU, hNU⟩ :=
    hN1.exists_lipschitzOnWith_of_nnnorm_lt L (by simpa [hDN0] using hL)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  let s : ℝ := min δ r / 4
  have hs : 0 < s := by dsimp [s]; positivity
  have hsδ : 2 * s < δ := by
    have := min_le_left δ r
    dsimp [s]
    linarith
  have hsr : 2 * s < r := by
    have := min_le_right δ r
    dsimp [s]
    linarith
  let φ : E → ℝ := fun x ↦ b (s⁻¹ • x)
  have hφ : ContDiff ℝ n φ := b.contDiff.comp (contDiff_const.smul contDiff_id)
  have hφLip : LipschitzWith (C * ‖s⁻¹‖₊) φ :=
    hC.comp (lipschitzWith_smul s⁻¹)
  let Ncut : E → F := fun x ↦ φ x • N x
  have hcut : ContDiff ℝ n Ncut := hφ.smul hN
  have hsupport : tsupport Ncut ⊆ closedBall 0 (2 * s) := by
    simpa only [b, mul_comm] using b.tsupport_rescaled_smul_subset N hs
  have hcompact : HasCompactSupport Ncut :=
    (isCompact_closedBall (0 : E) (2 * s)).of_isClosed_subset
      (isClosed_tsupport Ncut) hsupport
  have hnear (x : E) (hx : x ∈ ball 0 s) : Ncut x = N x := by
    apply b.rescaled_smul_eqOn N hs
    simpa only [b, mul_one] using ball_subset_closedBall hx
  have hjet : Ncut =ᶠ[𝓝 0] N :=
    Filter.mem_of_superset (ball_mem_nhds (0 : E) hs) hnear
  have hLip : LipschitzWith ⟨ε, hε.le⟩ Ncut := by
    have hφnorm (x : E) : ‖φ x‖ ≤ 1 := by
      simpa only [φ, Real.norm_eq_abs, abs_of_nonneg b.nonneg] using
        (b.le_one : b (s⁻¹ • x) ≤ 1)
    have hR : 0 ≤ 2 * s := by positivity
    have hconstant : L + (C * ‖s⁻¹‖₊) * L * ⟨2 * s, hR⟩ = ⟨ε, hε.le⟩ := by
      apply NNReal.eq
      change (L : ℝ) + (C * ‖s⁻¹‖) * L * (2 * s) = ε
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos hs]
      calc
        _ = (L : ℝ) + 2 * C * L * (s⁻¹ * s) := by ring
        _ = (L : ℝ) + 2 * C * L := by rw [inv_mul_cancel₀ hs.ne', mul_one]
        _ = ε := hbudget
    simpa only [hconstant] using
      (hNU.mono hδU).smul_of_tsupport_subset_closedBall
        (hN.of_le hn').differentiable_one (hφ.of_le hn').differentiable_one
        hφLip hφnorm hsupport hN0 hR hsδ
  exact ⟨s, Ncut, hs, by linarith only [hs, hsr], hcut, hcompact,
    hsupport.trans (closedBall_subset_ball hsr), hnear, hLip,
    hjet.eq_of_nhds.trans hN0, hjet.fderiv_eq.trans hDN0⟩

/-- A smooth map with vanishing value and derivative at zero agrees near zero with a
smooth compactly supported map of any prescribed positive Lipschitz constant. Its support
lies in any prescribed ball, and its first two derivatives are globally Lipschitz.
The domain carries its original finite-dimensional norm, including dimension zero. -/
theorem ContDiff.exists_compactSupport_small_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {N : E → F}
    (hN : ContDiff ℝ ∞ N) (hN0 : N 0 = 0) (hDN0 : fderiv ℝ N 0 = 0)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∃ (ρ : ℝ) (Ncut : E → F), 0 < ρ ∧ ρ < r ∧
      ContDiff ℝ ∞ Ncut ∧ HasCompactSupport Ncut ∧
      tsupport Ncut ⊆ ball 0 r ∧
      (∀ x ∈ ball 0 ρ, Ncut x = N x) ∧
      LipschitzWith ⟨ε, hε.le⟩ Ncut ∧
      Ncut 0 = 0 ∧ fderiv ℝ Ncut 0 = 0 ∧
      ∃ M K : ℝ≥0, LipschitzWith M (fderiv ℝ Ncut) ∧
        LipschitzWith K (fderiv ℝ (fderiv ℝ Ncut)) := by
  obtain ⟨ρ, Ncut, hρ, hρr, hcut, hcompact, hsupport, hnear, hLip, hzero, hjet⟩ :=
    hN.exists_compactSupport_small_lipschitz_of_one_le (n := ⊤) (by simp) hN0 hDN0 hε hr
  have hD := hcut.fderiv_right (m := 2) (by simp)
  have hC2 : ContDiff ℝ 2 Ncut := hcut.of_le (by simp)
  have hcompactD : HasCompactSupport (fderiv ℝ Ncut) := hcompact.fderiv ℝ
  obtain ⟨M, hM⟩ := hC2.lipschitzWith_fderiv_of_hasCompactSupport hcompact
  obtain ⟨K, hK⟩ := hD.lipschitzWith_fderiv_of_hasCompactSupport hcompactD
  exact ⟨ρ, Ncut, hρ, hρr, hcut, hcompact, hsupport, hnear, hLip,
    hzero, hjet, M, K, hM, hK⟩
