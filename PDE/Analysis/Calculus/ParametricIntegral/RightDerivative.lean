/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Differentiation under the integral sign from the right

If every `τ ↦ F τ a` is continuous on `[t, t + δ]` and has right derivatives `F' τ a` on
`[t, t + δ)` bounded by an integrable function of `a`, then `τ ↦ ∫ F τ a` has the right derivative
`∫ F' t a` at `t`. The mean value inequality for right derivatives bounds the difference quotients
by the same function, and dominated convergence passes to the limit. This is the form needed for
quantities whose time derivatives jump, as the pairings of a solution with corners in time.

## Main results

* `hasDerivWithinAt_integral_of_dominated_of_right_deriv_le`: `τ ↦ ∫ F τ a` has the right
  derivative `∫ F' t a` at `t`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE.Analysis

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **Differentiation under the integral sign from the right.** Let `τ ↦ F τ a` be continuous on
`[t, t + δ]` with right derivatives `F' τ a` on `[t, t + δ)`, `‖F' τ a‖ ≤ bound a` there with
`bound` integrable, and `F t` integrable. Then `F' t` is integrable and `τ ↦ ∫ F τ a ∂μ` has the
right derivative `∫ F' t a ∂μ` at `t`. -/
theorem hasDerivWithinAt_integral_of_dominated_of_right_deriv_le {F F' : ℝ → α → E}
    {bound : α → ℝ} {t δ : ℝ} (hδ : 0 < δ)
    (hF_meas : ∀ τ ∈ Icc t (t + δ), AEStronglyMeasurable (F τ) μ)
    (hF_int : Integrable (F t) μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousOn (fun τ ↦ F τ a) (Icc t (t + δ)))
    (h_deriv : ∀ᵐ a ∂μ, ∀ τ ∈ Ico t (t + δ),
      HasDerivWithinAt (fun τ ↦ F τ a) (F' τ a) (Ici τ) τ)
    (h_bound : ∀ᵐ a ∂μ, ∀ τ ∈ Ico t (t + δ), ‖F' τ a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ) :
    Integrable (F' t) μ ∧
      HasDerivWithinAt (fun τ ↦ ∫ a, F τ a ∂μ) (∫ a, F' t a ∂μ) (Ici t) t := by
  have htmem : t ∈ Ico t (t + δ) := ⟨le_rfl, by linarith⟩
  have he : Ici t \ {t} = Ioi t := by
    ext τ
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h
      exact ⟨h.le, h.ne'⟩
  -- the measurability of `F' t`, as an a.e. limit of difference quotients
  have hF'_meas : AEStronglyMeasurable (F' t) μ := by
    set u : ℕ → ℝ := fun n ↦ t + δ / ((n : ℝ) + 2) with hu_def
    have hu0 : ∀ n : ℕ, 0 < δ / ((n : ℝ) + 2) := fun n ↦ by positivity
    have hu1 : ∀ n : ℕ, δ / ((n : ℝ) + 2) ≤ δ := fun n ↦
      div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have hut : Tendsto u atTop (𝓝[Ici t \ {t}] t) := by
      rw [he]
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · have h1 : Tendsto (fun n : ℕ ↦ δ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2
            tendsto_natCast_atTop_atTop)
        simpa [u] using (tendsto_const_nhds (x := t)).add h1
      · simp only [mem_Ioi, u]
        linarith [hu0 n]
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n a ↦ (u n - t)⁻¹ • (F (u n) a - F t a)) (fun n ↦ ?_) ?_
    · exact ((hF_meas (u n) ⟨by simp only [u]; linarith [hu0 n], by
        simp only [u]; linarith [hu1 n]⟩).sub (hF_meas t ⟨le_rfl, by linarith⟩)).const_smul _
    · filter_upwards [h_deriv] with a ha
      have h := (hasDerivWithinAt_iff_tendsto_slope.1 (ha t htmem)).comp hut
      refine h.congr fun n ↦ ?_
      simp only [Function.comp_apply, slope_def_module]
  -- the mean value inequality for right derivatives
  have hmv : ∀ᵐ a ∂μ, ∀ τ ∈ Icc t (t + δ), ‖F τ a - F t a‖ ≤ bound a * (τ - t) := by
    filter_upwards [h_cont, h_deriv, h_bound] with a hc hd hb
    exact norm_image_sub_le_of_norm_deriv_right_le_segment hc hd hb
  have hint : Integrable (F' t) μ :=
    Integrable.mono' bound_integrable hF'_meas
      (by filter_upwards [h_bound] with a ha using ha t htmem)
  -- the slopes
  have hslope : ∀ τ ∈ Ioc t (t + δ), slope (fun τ ↦ ∫ a, F τ a ∂μ) t τ =
      ∫ a, (τ - t)⁻¹ • (F τ a - F t a) ∂μ := by
    intro τ hτ
    have hFτ : Integrable (F τ) μ := by
      refine (hF_int.norm.add (bound_integrable.mul_const (τ - t))).mono' (hF_meas τ
        ⟨hτ.1.le, hτ.2⟩) ?_
      filter_upwards [hmv] with a ha
      calc ‖F τ a‖ ≤ ‖F t a‖ + ‖F τ a - F t a‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ ‖F t a‖ + bound a * (τ - t) := by gcongr; exact ha τ ⟨hτ.1.le, hτ.2⟩
    rw [slope_def_module, integral_smul, integral_sub hFτ hF_int]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine ⟨hint, ?_⟩
  have hl : Ioc t (t + δ) ∈ 𝓝[Ici t \ {t}] t := by
    rw [he]
    exact Ioc_mem_nhdsGT (by linarith)
  have hlim := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[Ici t \ {t}] t)
    (F := fun τ a ↦ (τ - t)⁻¹ • (F τ a - F t a)) (f := F' t) bound ?_ ?_ bound_integrable ?_
  · refine hlim.congr' ?_
    filter_upwards [hl] with τ hτ
    exact (hslope τ hτ).symm
  · filter_upwards [hl] with τ hτ
    exact ((hF_meas τ ⟨hτ.1.le, hτ.2⟩).sub (hF_meas t ⟨le_rfl, by linarith⟩)).const_smul _
  · filter_upwards [hl] with τ hτ
    filter_upwards [hmv] with a ha
    have hpos : 0 < τ - t := sub_pos.2 hτ.1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    calc (τ - t)⁻¹ * ‖F τ a - F t a‖ ≤ (τ - t)⁻¹ * (bound a * (τ - t)) := by
          gcongr; exact ha τ ⟨hτ.1.le, hτ.2⟩
      _ = bound a := by field_simp
  · filter_upwards [h_deriv] with a ha
    have h := (hasDerivWithinAt_iff_tendsto_slope.1 (ha t htmem))
    refine h.congr' ?_
    filter_upwards with τ
    rw [slope_def_module]

end PDE.Analysis
