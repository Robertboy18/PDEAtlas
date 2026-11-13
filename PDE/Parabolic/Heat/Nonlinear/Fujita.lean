/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.CompactWeight
public import PDE.Parabolic.Heat.Nonlinear.FujitaTest
import CAS.ExactTactic

/-!
# Whole-space blowup below the Fujita exponent

For `1 < p < (n+2)/n`, a nonnegative nonzero continuous initial datum `g` on `ℝⁿ` admits no global
nonnegative classical solution of `uₜ - Δu = uᵖ` (`not_global_fujita_subcritical`). The datum need
not have compact support, and the solution is not assumed integrable or bounded. The form
`not_global_fujita_subcritical_of_contDiffOn` assumes only that `u` is nonnegative, `C²` in the open
cylinder and continuous up to the initial time.

This contains Evans's §9.4.1, Theorem 2, whose data are smooth with compact support and whose
solutions are smooth and integrable.

## How it works

Evans tests the equation with the heat kernel `Φ(·, s)` at a fixed time `s`, which satisfies
`ΔΦ ≥ -(n/2s) Φ`, his (8). The moment `η = ∫ u Φ` then obeys `η' ≥ -λη + ηᵖ`, (9), and the blowup
condition (10) holds for large `s`. We test instead with the compactly supported function
`fujitaCutoff z R`, the cubic positive part of `1 - ‖(x-z)/R‖²`, whose mass grows as `Rⁿ` and whose
Laplacian is at least `-C/R²` times itself (`neg_mul_fujitaCutoff_le_laplacian`). For a compactly
supported probability weight `w` with `Δw ≥ -λw`, the moment `η = ∫ w u` satisfies (9) by Jensen's
inequality (`IsClassicalWholeSpacePowerSolution.compact_moment_inequality`), and a global solution
forces `1 ≤ λ η(0)^(1-p)` (`initial_compact_moment_bound`). Since the cutoff at scale `R ≥ 1`
dominates the cutoff at scale one (`fujitaCutoff_one_le`), for the normalized cutoff this bound
reads `1 ≤ c R^(n(p-1) - 2)` (`fujita_scaling_identity`, whose exponent algebra SymLean's `cas`
tactic checks), and it fails for large `R` because `n(p - 1) < 2`. Compact tests make every
integration by parts local, so no decay of `u` at infinity is used.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, Theorem 2 (Blow-up for small data) and its proof,
  (6)-(10), pp. 549-550.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open PDE.Analysis
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {p : ℝ}

/-- The two spatial scaling powers combine into the strict Fujita exponent. -/
theorem fujita_scaling_identity {R m A : ℝ} (hR : 0 < R) (hm : 0 < m) (hA : 0 < A)
    (p C : ℝ) :
    C / R ^ 2 * (m / (R ^ n * A)) ^ (1 - p) =
      (C * A ^ (p - 1) / m ^ (p - 1)) * R ^ ((n : ℝ) * (p - 1) - 2) := by
  rw [show 1 - p = -(p - 1) by cas,
    Real.rpow_neg (div_nonneg hm.le (mul_nonneg (pow_nonneg hR.le _) hA.le)),
    Real.div_rpow hm.le (mul_nonneg (pow_nonneg hR.le _) hA.le),
    Real.mul_rpow (pow_nonneg hR.le _) hA.le,
    ← Real.rpow_natCast_mul hR.le, Real.rpow_sub hR, Real.rpow_two, inv_div]
  cas

/-- Fujita's strict subcritical whole-space nonexistence theorem.
The continuous nonnegative nonzero initial datum need not be compactly supported;
all integrals in the proof have compact spatial tests. The solution assumptions
contain the PDE and local classical regularity, with no scalar growth assumption. -/
theorem not_global_fujita_subcritical
    (hn : 0 < n) (hp : 1 < p) (hsub : p < ((n : ℝ) + 2) / (n : ℝ))
    {g : ℝ^n → ℝ} (hgc : Continuous g) (hg : ∀ x, 0 ≤ g x) (hgnz : g ≠ 0) :
    ¬ ∀ T : ℝ, 0 < T → ∃ u D, IsClassicalWholeSpacePowerSolution p T g u D := by
  intro hglobal
  have hnz : ¬ ∀ x, g x = 0 := fun h ↦ hgnz (funext h)
  obtain ⟨z, hz⟩ := not_forall.mp hnz
  let A : ℝ := ∫ x, fujitaCutoff (0 : ℝ^n) 1 x
  let m : ℝ := ∫ x, fujitaCutoff z 1 x * g x
  have hA : 0 < A := integral_fujitaCutoff_pos 0 zero_lt_one
  have him : Integrable (fun x ↦ fujitaCutoff z 1 x * g x) :=
    ((contDiff_fujitaCutoff z 1).continuous.mul hgc).integrable_of_hasCompactSupport
      (hasCompactSupport_fujitaCutoff z zero_lt_one).mul_right
  have hm : 0 < m := integral_pos_of_integrable_nonneg_nonzero (x := z)
    ((contDiff_fujitaCutoff z 1).continuous.mul hgc) him
    (fun x ↦ mul_nonneg (fujitaCutoff_nonneg z 1 x) (hg x)) (by simpa using hz)
  have hC : 0 < ((n : ℝ) + 4) ^ 2 := sq_pos_of_pos (by positivity)
  have hbound (R : ℝ) (hR : 1 ≤ R) :
      1 ≤ (((n : ℝ) + 4) ^ 2 * A ^ (p - 1) / m ^ (p - 1)) *
        R ^ ((n : ℝ) * (p - 1) - 2) := by
    have hRpos : 0 < R := zero_lt_one.trans_le hR
    let B : ℝ := ∫ x, fujitaCutoff z R x
    have hB : 0 < B := integral_fujitaCutoff_pos z hRpos
    have hBscale : B = R ^ n * A := integral_fujitaCutoff z hRpos
    let w : ℝ^n → ℝ := fun x ↦ B⁻¹ * fujitaCutoff z R x
    have hw : ContDiff ℝ 2 w := contDiff_const.mul (contDiff_fujitaCutoff z R)
    have hwcompact : HasCompactSupport w :=
      (hasCompactSupport_fujitaCutoff z hRpos).mul_left
    have hwpos : ∀ x, 0 ≤ w x := fun x ↦
      mul_nonneg (inv_nonneg.mpr hB.le) (fujitaCutoff_nonneg z R x)
    have hunit : ∫ x, w x = 1 := by
      rw [integral_const_mul]
      exact inv_mul_cancel₀ hB.ne'
    have hlap : ∀ x, -(((n : ℝ) + 4) ^ 2 / R ^ 2) * w x ≤ laplacian w x := by
      intro x
      dsimp only [w]
      rw [PDE.laplacian_const_smul]
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
        (neg_mul_fujitaCutoff_le_laplacian z hRpos x) (inv_nonneg.mpr hB.le)
    have hiR : Integrable (fun x ↦ fujitaCutoff z R x * g x) :=
      ((contDiff_fujitaCutoff z R).continuous.mul hgc).integrable_of_hasCompactSupport
        (hasCompactSupport_fujitaCutoff z hRpos).mul_right
    have hmass : m ≤ ∫ x, fujitaCutoff z R x * g x :=
      integral_mono him hiR (fun x ↦
        mul_le_mul_of_nonneg_right (fujitaCutoff_one_le z x hR) (hg x))
    have hmoment : m / B ≤ ∫ x, w x * g x := by
      dsimp only [w]
      simp_rw [mul_assoc]
      rw [integral_const_mul, div_eq_mul_inv]
      simpa only [mul_comm m B⁻¹] using
        mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hB.le)
    have hsmall : 0 < m / B := div_pos hm hB
    have hnecessary := initial_compact_moment_bound hp (div_pos hC (sq_pos_of_pos hRpos))
      hw hwcompact hwpos hunit hlap (hsmall.trans_le hmoment) hglobal
    have hpower := Real.rpow_le_rpow_of_nonpos hsmall hmoment (by linarith : 1 - p ≤ 0)
    have hle := hnecessary.trans (mul_le_mul_of_nonneg_left hpower
      (div_nonneg hC.le (sq_nonneg R)))
    rwa [hBscale, fujita_scaling_identity hRpos hm hA] at hle
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hexponent : 0 < 2 - (n : ℝ) * (p - 1) := by
    nlinarith [(lt_div_iff₀ hnR).mp hsub]
  have hlim : Tendsto
      (fun R : ℝ ↦ (((n : ℝ) + 4) ^ 2 * A ^ (p - 1) / m ^ (p - 1)) *
        R ^ ((n : ℝ) * (p - 1) - 2)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using (tendsto_rpow_neg_atTop hexponent).const_mul
      (((n : ℝ) + 4) ^ 2 * A ^ (p - 1) / m ^ (p - 1))
  have hfalse : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR using hbound R hR)
  norm_num at hfalse

/-- Fujita's strict subcritical theorem with hypotheses on the solution only: a nonzero
datum admits no global nonnegative solution that is `C²` in the open space-time cylinder and
continuous at the initial time. Such a solution would make the datum continuous and
nonnegative, and `p < (n + 2) / n` with `1 < p` forces `0 < n`. In particular, this covers the
smooth compactly supported data of Evans's §9.4.1, Theorem 2. -/
theorem not_global_fujita_subcritical_of_contDiffOn
    (hp : 1 < p) (hsub : p < ((n : ℝ) + 2) / (n : ℝ))
    {g : ℝ^n → ℝ} (hgnz : g ≠ 0) :
    ¬ ∀ T : ℝ, 0 < T → ∃ u : ℝ → ℝ^n → ℝ,
      ContinuousOn u.uncurry (Icc 0 T ×ˢ univ) ∧
      ContDiffOn ℝ 2 u.uncurry (Ioo 0 T ×ˢ univ) ∧
      (∀ t ∈ Ioo 0 T, ∀ x,
        deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ p) ∧
      (∀ t ∈ Icc 0 T, ∀ x, 0 ≤ u t x) ∧ (∀ x, u 0 x = g x) := by
  intro hglobal
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hsub; linarith)
  obtain ⟨u₁, hc₁, -, -, hnonneg₁, hinit₁⟩ := hglobal 1 one_pos
  have h0 : (0 : ℝ) ∈ Icc 0 1 := left_mem_Icc.mpr zero_le_one
  have hgc : Continuous g := by
    have h := hc₁.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x ↦ ⟨h0, mem_univ x⟩)
    simpa [Function.comp_def, Function.uncurry, hinit₁] using h
  have hg (x : ℝ^n) : 0 ≤ g x := hinit₁ x ▸ hnonneg₁ 0 h0 x
  apply not_global_fujita_subcritical hn hp hsub hgc hg hgnz
  intro T hT
  obtain ⟨u, hc, hs, heq, hnonneg, hinit⟩ := hglobal T hT
  exact ⟨u, _, IsClassicalWholeSpacePowerSolution.of_contDiffOn hc hs heq hnonneg hinit⟩

end HeatEquation.Nonlinear
