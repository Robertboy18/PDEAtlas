/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.DominatedLp
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue

/-!
# From pointwise time derivatives to differentiation in Lᵖ

A common pointwise majorant in Lᵖ for the time derivatives controls every nearby
difference quotient by the mean value theorem. Dominated convergence then
gives the derivative in the Lᵖ norm. The measure may contain a singular
spatial weight.

The common null set and time neighborhood matter: separate almost-everywhere
statements at each time do not provide pointwise differentiable trajectories.
-/

@[expose] public section

namespace MeasureTheory

open Filter Set
open scoped ENNReal Topology

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A common pointwise `Lᵖ` majorant for the time derivatives on a neighborhood
upgrades pointwise differentiation to differentiation in the `Lᵖ` norm, for finite
`p ≥ 1`. Both derivative and bound hold outside one common null set for all nearby
times. No continuity of the pointwise derivative is required. -/
theorem hasDerivAt_toLp_of_memLp_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {u v : ℝ → α → E} {B : α → ℝ} {t₀ : ℝ} {s : Set ℝ}
    (hu : ∀ t, MemLp (u t) p μ) (hv : MemLp (v t₀) p μ)
    (hB : MemLp B p μ) (hs : s ∈ 𝓝 t₀) (hconvex : Convex ℝ s)
    (hderiv : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun τ ↦ u τ x) (v t x) t)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖v t x‖ ≤ B x) :
    HasDerivAt (fun t ↦ (hu t).toLp (u t)) (hv.toLp (v t₀)) t₀ := by
  have ht₀ : t₀ ∈ s := mem_of_mem_nhds hs
  let q : ℝ → α → E := fun t x ↦ (t - t₀)⁻¹ • (u t x - u t₀ x)
  have hq (t : ℝ) : MemLp (q t) p μ :=
    ((hu t).sub (hu t₀)).const_smul (t - t₀)⁻¹
  have hqbound : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖q t x‖ ≤ ‖B x‖ := by
    filter_upwards [hderiv, hbound] with x hx hBx
    intro t ht
    have hB₀ : 0 ≤ B x := (norm_nonneg _).trans (hBx t₀ ht₀)
    have hdiff : ‖u t x - u t₀ x‖ ≤ B x * ‖t - t₀‖ :=
      hconvex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun τ hτ ↦ (hx τ hτ).hasDerivWithinAt) hBx ht₀ ht
    by_cases heq : t = t₀
    · simp only [q, heq, sub_self, inv_zero, zero_smul, norm_zero]
      exact norm_nonneg _
    · have hne : ‖t - t₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr heq)
      calc
        ‖q t x‖ = ‖t - t₀‖⁻¹ * ‖u t x - u t₀ x‖ := by
          simp only [q, norm_smul, norm_inv]
        _ ≤ ‖t - t₀‖⁻¹ * (B x * ‖t - t₀‖) :=
          mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (norm_nonneg _))
        _ = ‖B x‖ := by
          rw [Real.norm_of_nonneg hB₀]
          field_simp
  apply hasDerivAt_iff_tendsto_slope.mpr
  change Tendsto (fun t ↦ (hq t).toLp (q t)) (𝓝[≠] t₀) (𝓝 (hv.toLp (v t₀)))
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro times htimes
  have htimes' : Tendsto times atTop (𝓝 t₀) :=
    htimes.mono_right nhdsWithin_le_nhds
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htimes'.eventually hs)
  apply (tendsto_add_atTop_iff_nat N).mp
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n ↦ hq (times (n + N)))
    _ hv).mpr
  apply tendsto_Lp_of_tendsto_ae_of_ae_norm_le (Fact.out : 1 ≤ p) hp
    (fun n ↦ (hq (times (n + N))).aestronglyMeasurable) hv hB
  · intro n
    filter_upwards [hqbound] with x hx
    exact hx _ (hN _ (Nat.le_add_left N n))
  · filter_upwards [hderiv] with x hx
    have h := (hx t₀ ht₀).tendsto_slope.comp
      (htimes.comp (tendsto_add_atTop_nat N))
    simpa only [Function.comp_def, slope_def_module, q] using h

end MeasureTheory
