/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Continuity of dilation orbits in Lᵖ

On a finite-dimensional real vector space with Haar measure and for finite `p ≥ 1`, the dilates
`f (a • ·)` of `f ∈ Lᵖ` depend continuously on `a ≠ 0` in the `Lᵖ` seminorm.
For continuous compactly supported functions this is dominated convergence on a common ball;
the general case follows by approximation, with the change-of-variables factor bounded on a
neighbourhood of the base point.

The rescalings `x ↦ e^{τ/2} f(e^{τ/2} x)`, homogeneous of degree `-1`, have `Lᵖ` norm
`e^{(τ/2)(1 - d/p)} ‖f‖_{Lᵖ}` in dimension `d` and depend continuously on `τ` in `Lᵖ`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Module
open scoped ENNReal Topology

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- Dilation orbits of continuous compactly supported functions are continuous in `Lᵖ`. -/
theorem tendsto_eLpNorm_comp_smul_sub_of_hasCompactSupport {g : E → F} (hg : Continuous g)
    (hgc : HasCompactSupport g) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {a₀ : ℝ} (ha₀ : a₀ ≠ 0) :
    Tendsto (fun a ↦ eLpNorm (fun x ↦ g (a • x) - g (a₀ • x)) p μ) (𝓝 a₀) (𝓝 0) := by
  obtain ⟨R, hR, hball⟩ := hgc.isCompact.isBounded.subset_closedBall_lt 0 (0 : E)
  obtain ⟨M₀, hM₀⟩ := hg.bounded_above_of_compact_support hgc
  set M := max M₀ 0
  have hM : ∀ x, ‖g x‖ ≤ M := fun x ↦ (hM₀ x).trans (le_max_left _ _)
  have hδ : 0 < |a₀| / 2 := by positivity
  set B : Set E := Metric.closedBall 0 (R / (|a₀| / 2))
  have hzero (a : ℝ) (ha : |a₀| / 2 ≤ |a|) (x : E) (hx : x ∉ B) : g (a • x) = 0 := by
    by_contra hne
    have hmem := hball (subset_closure (by simpa only [Function.mem_support] using hne))
    have hlarge : R / (|a₀| / 2) < ‖x‖ := by
      simpa only [B, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hnorm : ‖a • x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hmem
    rw [norm_smul, Real.norm_eq_abs] at hnorm
    have hlt : R < |a₀| / 2 * ‖x‖ := by
      simpa only [mul_comm] using (div_lt_iff₀ hδ).1 hlarge
    exact (not_lt_of_ge hnorm) (hlt.trans_le (mul_le_mul_of_nonneg_right ha (norm_nonneg x)))
  have hnear : ∀ᶠ a in 𝓝 a₀, |a₀| / 2 ≤ |a| := by
    have h : ∀ᶠ a in 𝓝 a₀, |a₀| / 2 < |a| :=
      (continuous_abs.tendsto a₀).eventually (lt_mem_nhds (by linarith [abs_pos.mpr ha₀]))
    exact h.mono fun a ha ↦ ha.le
  set P := p.toReal
  have hP : 0 < P := ENNReal.toReal_pos hp0 hp
  let G : ℝ → E → ℝ≥0∞ := fun a x ↦ ‖g (a • x) - g (a₀ • x)‖ₑ ^ P
  let bound : E → ℝ≥0∞ := B.indicator fun _ ↦ ENNReal.ofReal (2 * M) ^ P
  have hlim : Tendsto (fun a ↦ ∫⁻ x, G a x ∂μ) (𝓝 a₀) (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' bound
      (Eventually.of_forall fun a ↦ ((hg.comp (continuous_const_smul a)).sub
        (hg.comp (continuous_const_smul a₀))).aestronglyMeasurable.enorm.pow_const P)
      ?_ ?_ (ae_of_all _ fun x ↦ ?_)
    · filter_upwards [hnear] with a ha
      refine ae_of_all _ fun x ↦ ?_
      by_cases hx : x ∈ B
      · simp only [bound, indicator_of_mem hx, G]
        gcongr
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        exact (norm_sub_le _ _).trans (by linarith [hM (a • x), hM (a₀ • x)])
      · have hle : |a₀| / 2 ≤ |a₀| := by linarith [abs_pos.mpr ha₀]
        simp [G, hzero a ha x hx, hzero a₀ hle x hx, ENNReal.zero_rpow_of_pos hP]
    · rw [lintegral_indicator Metric.isClosed_closedBall.measurableSet, setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hP.le ENNReal.ofReal_ne_top)
        (isCompact_closedBall (0 : E) _).measure_ne_top
    · have hd : Continuous fun a : ℝ ↦ g (a • x) - g (a₀ • x) :=
        (hg.comp (continuous_id.smul continuous_const)).sub continuous_const
      have hc : Continuous fun a : ℝ ↦ G a x := ENNReal.continuous_rpow_const.comp hd.enorm
      simpa [G, ENNReal.zero_rpow_of_pos hP] using hc.tendsto a₀
  rw [lintegral_zero] at hlim
  have hroot := ((ENNReal.continuous_rpow_const (y := 1 / P)).tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at hroot
  refine hroot.congr fun a ↦ ?_
  have hm : AEStronglyMeasurable (fun x ↦ g (a • x) - g (a₀ • x)) μ :=
    ((hg.comp (continuous_const_smul a)).sub
      (hg.comp (continuous_const_smul a₀))).aestronglyMeasurable
  rw [Function.comp_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hm]

variable {f : E → F} {p : ℝ≥0∞}

/-- Dilation orbits of `Lᵖ` functions, `1 ≤ p < ∞`, are continuous in the `Lᵖ` seminorm at every
nonzero dilation factor. -/
theorem tendsto_eLpNorm_comp_smul_sub [NormedSpace ℝ F] (hf : MemLp f p μ) (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) {a₀ : ℝ} (ha₀ : a₀ ≠ 0) :
    Tendsto (fun a ↦ eLpNorm (fun x ↦ f (a • x) - f (a₀ • x)) p μ) (𝓝 a₀) (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hδ : 0 < |a₀| / 2 := by positivity
  set K := dilationFactor E (|a₀| / 2) p
  have hK : K ≠ ∞ := dilationFactor_ne_top _ _
  have hK0 : K ≠ 0 := by
    simp only [K, dilationFactor]
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top).ne'
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num : (3 : ℝ≥0∞) ≠ ∞)).ne'
  obtain ⟨g, hgc, hfg, hg, hgp⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp
    (ENNReal.div_pos hε3 hK).ne'
  have hnear : ∀ᶠ a in 𝓝 a₀, |a₀| / 2 ≤ |a| := by
    have h : ∀ᶠ a in 𝓝 a₀, |a₀| / 2 < |a| :=
      (continuous_abs.tendsto a₀).eventually (lt_mem_nhds (by linarith [abs_pos.mpr ha₀]))
    exact h.mono fun a ha ↦ ha.le
  have hgclose := (ENNReal.tendsto_nhds_zero.mp
    (tendsto_eLpNorm_comp_smul_sub_of_hasCompactSupport (μ := μ) hg hgc hp0 hp ha₀)) (ε / 3)
    (ENNReal.div_pos hε.ne' (by norm_num : (3 : ℝ≥0∞) ≠ ∞))
  filter_upwards [hnear, hgclose] with a ha hga
  have ha0 : a ≠ 0 := fun h ↦ by rw [h, abs_zero] at ha; linarith
  have hfgm : AEStronglyMeasurable (f - g) μ := hf.aestronglyMeasurable.sub hg.aestronglyMeasurable
  have hdil (b : ℝ) (hb : b ≠ 0) (hbK : |a₀| / 2 ≤ |b|) :
      eLpNorm (fun x ↦ (f - g) (b • x)) p μ ≤ ε / 3 := by
    rw [eLpNorm_comp_smul hfgm hb]
    calc
      _ ≤ K * (ε / 3 / K) := by
        gcongr
        exact dilationFactor_le_of_le hδ hbK p
      _ = ε / 3 := ENNReal.mul_div_cancel hK0 hK
  have hsplit : (fun x ↦ f (a • x) - f (a₀ • x)) =
      ((fun x ↦ (f - g) (a • x)) + fun x ↦ g (a • x) - g (a₀ • x)) +
        fun x ↦ -((f - g) (a₀ • x)) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  rw [hsplit]
  refine (eLpNorm_add_le hp1).trans ?_
  refine (add_le_add (eLpNorm_add_le hp1) le_rfl).trans ?_
  rw [show (fun x ↦ -(f - g) (a₀ • x)) = -fun x ↦ (f - g) (a₀ • x) from rfl, eLpNorm_neg]
  calc
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact hdil a ha0 ha
      · exact hdil a₀ ha₀ (by linarith [abs_pos.mpr ha₀])
    _ = ε := ENNReal.add_thirds ε

section Rescaling

variable [NormedSpace ℝ F]

/-- The rescaling `x ↦ e^{τ/2} f(e^{τ/2} x)`, homogeneous of degree `-1`, preserves `Lᵖ`. -/
theorem memLp_dilate (hf : MemLp f p μ) (τ : ℝ) :
    MemLp (fun x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x)) p μ :=
  (hf.comp_smul (Real.exp_pos _).ne').const_smul _

/-- The `Lᵖ` norm of the rescaling: `‖e^{τ/2} f(e^{τ/2} ·)‖_{Lᵖ} = e^{(τ/2)(1 - d/p)} ‖f‖_{Lᵖ}`,
where `d` is the dimension. -/
theorem eLpNorm_dilate (hf : AEStronglyMeasurable f μ) (τ : ℝ) :
    eLpNorm (fun x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x)) p μ =
      ENNReal.ofReal (Real.exp (τ / 2 * (1 - finrank ℝ E * p⁻¹.toReal))) * eLpNorm f p μ := by
  change eLpNorm (Real.exp (τ / 2) • fun x ↦ f (Real.exp (τ / 2) • x)) p μ = _
  rw [eLpNorm_const_smul, eLpNorm_comp_smul hf (Real.exp_pos _).ne', ← mul_assoc,
    Real.enorm_eq_ofReal (Real.exp_pos _).le, dilationFactor,
    abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity)
      ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 2
  rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_mul, ← Real.exp_add, one_div]
  congr 1
  ring

/-- The rescalings `x ↦ e^{τ/2} f(e^{τ/2} x)` of `f ∈ Lᵖ` depend continuously on `τ` in `Lᵖ`,
`1 ≤ p < ∞`. -/
theorem tendsto_eLpNorm_dilate_sub (hf : MemLp f p μ) (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    (τ₀ : ℝ) :
    Tendsto (fun τ ↦ eLpNorm ((fun x ↦ Real.exp (τ / 2) • f (Real.exp (τ / 2) • x)) -
      fun x ↦ Real.exp (τ₀ / 2) • f (Real.exp (τ₀ / 2) • x)) p μ) (𝓝 τ₀) (𝓝 0) := by
  set a : ℝ → ℝ := fun τ ↦ Real.exp (τ / 2)
  have ha : Continuous a := by fun_prop
  have ha₀ : 0 < a τ₀ := Real.exp_pos _
  have hδ : 0 < a τ₀ / 2 := by positivity
  set M := dilationFactor E (a τ₀ / 2) p * eLpNorm f p μ
  have hM : M ≠ ∞ := ENNReal.mul_ne_top (dilationFactor_ne_top _ _) hf.eLpNorm_ne_top
  have hnear : ∀ᶠ τ in 𝓝 τ₀, a τ₀ / 2 ≤ a τ :=
    (ha.tendsto τ₀).eventually (Ici_mem_nhds (by linarith))
  have hfa (τ : ℝ) : AEStronglyMeasurable (fun x ↦ f (a τ • x)) μ :=
    (hf.comp_smul (Real.exp_pos _).ne').aestronglyMeasurable
  have hbound : ∀ᶠ τ in 𝓝 τ₀, eLpNorm ((fun x ↦ a τ • f (a τ • x)) -
      fun x ↦ a τ₀ • f (a τ₀ • x)) p μ ≤
      ‖a τ - a τ₀‖ₑ * M + ‖a τ₀‖ₑ *
        eLpNorm (fun x ↦ f (a τ • x) - f (a τ₀ • x)) p μ := by
    filter_upwards [hnear] with τ hτ
    have hsplit : ((fun x ↦ a τ • f (a τ • x)) - fun x ↦ a τ₀ • f (a τ₀ • x)) =
        (a τ - a τ₀) • (fun x ↦ f (a τ • x)) +
          a τ₀ • fun x ↦ f (a τ • x) - f (a τ₀ • x) := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, sub_smul, smul_sub]
      abel
    rw [hsplit]
    refine (eLpNorm_add_le hp1).trans (add_le_add ?_ ?_)
    · rw [eLpNorm_const_smul, eLpNorm_comp_smul hf.aestronglyMeasurable (Real.exp_pos _).ne']
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (dilationFactor_le_of_le (E := E) hδ
          (by rw [abs_of_pos (Real.exp_pos _)]; exact hτ) p) zero_le) zero_le
    · rw [eLpNorm_const_smul]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (Eventually.of_forall fun _ ↦ zero_le) hbound
  rw [show (0 : ℝ≥0∞) = 0 * M + ‖a τ₀‖ₑ * 0 by simp]
  refine Tendsto.add (ENNReal.Tendsto.mul_const ?_ (Or.inr hM))
    (ENNReal.Tendsto.const_mul ?_ (Or.inr enorm_ne_top))
  · have hc : Continuous fun τ ↦ ‖a τ - a τ₀‖ₑ := (ha.sub continuous_const).enorm
    simpa only [sub_self, enorm_zero] using hc.tendsto τ₀
  · exact (tendsto_eLpNorm_comp_smul_sub hf hp1 hp ha₀.ne').comp (ha.tendsto τ₀)

end Rescaling

end MeasureTheory
