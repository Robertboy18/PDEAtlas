/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Convergence from exponential decay of a Banach-space velocity

A bound on the time derivative gives both a limiting state and a quantitative
distance to that state. Mathlib gives convergence from an integrable
derivative and the fundamental theorem of calculus on a half-line. Integrating
the exponential majorant gives the rate.

The norm may be a Sobolev norm.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An exponentially integrable velocity gives a limiting state with the same
exponential convergence rate. Differentiability is in the Banach-space norm. -/
theorem exists_limit_of_hasDerivAt_norm_le_exp
    {u v : ℝ → E} {a C γ : ℝ} (hγ : 0 < γ)
    (hderiv : ∀ t ∈ Ici a, HasDerivAt u (v t) t)
    (hmeas : AEStronglyMeasurable v (volume.restrict (Ioi a)))
    (hbound : ∀ t ∈ Ioi a, ‖v t‖ ≤ C * Real.exp (-γ * t)) :
    ∃ limit : E, Tendsto u atTop (𝓝 limit) ∧
      ∀ t ∈ Ici a, ‖limit - u t‖ ≤ C * Real.exp (-γ * t) / γ := by
  have hexp : IntegrableOn (fun t : ℝ ↦ C * Real.exp (-γ * t)) (Ioi a) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hγ) a).const_mul C
  have hint : IntegrableOn v (Ioi a) := hexp.mono' hmeas <| by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact hbound t ht
  have hlimit := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (fun t ht ↦ hderiv t ht.le) hint
  refine ⟨limUnder atTop u, hlimit, ?_⟩
  intro t ht
  have hintTail := hint.mono_set (Ioi_subset_Ioi ht)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s hs ↦ hderiv s (ht.trans hs)) hintTail hlimit
  rw [← hftc]
  apply (norm_integral_le_integral_norm _).trans
  calc
    (∫ s in Ioi t, ‖v s‖) ≤ ∫ s in Ioi t, C * Real.exp (-γ * s) := by
      apply integral_mono_ae hintTail.norm (hexp.mono_set (Ioi_subset_Ioi ht))
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
      exact hbound s (ht.trans_lt hs)
    _ = C * Real.exp (-γ * t) / γ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hγ)]
      simp only [neg_div_neg_eq, mul_div_assoc]

/-- Exponential decay of the squared speed gives a limiting state in any Banach space.
The decay anchor `a` can precede the differentiability interval `[b, ∞)`, as happens
when an initial trace is extended constantly before differentiating. -/
theorem exists_limit_of_hasDerivAt_norm_sq_le_exp
    {u v : ℝ → E} {a b C δ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Ici b, HasDerivAt u (v t) t)
    (hmeas : AEStronglyMeasurable v (volume.restrict (Ioi b)))
    (hbound : ∀ t ∈ Ioi b,
      ‖v t‖ ^ 2 ≤ C * Real.exp (-(2 * δ) * (t - a))) :
    ∃ limit : E, Tendsto u atTop (𝓝 limit) ∧
      ∀ t ∈ Ici b, ‖limit - u t‖ ≤ √C * Real.exp (-δ * (t - a)) / δ := by
  have hnorm : ∀ t ∈ Ioi b,
      ‖v t‖ ≤ (√C * Real.exp (δ * a)) * Real.exp (-δ * t) := by
    intro t ht
    have hsquare : (√C * Real.exp (-δ * (t - a))) ^ 2 =
        C * Real.exp (-(2 * δ) * (t - a)) := by
      rw [mul_pow, Real.sq_sqrt hC, pow_two, ← Real.exp_add]
      congr 2
      ring
    have hn : ‖v t‖ ≤ √C * Real.exp (-δ * (t - a)) := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [hsquare]
      exact hbound t ht
    refine hn.trans_eq ?_
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  obtain ⟨limit, hlimit, hrate⟩ :=
    exists_limit_of_hasDerivAt_norm_le_exp hδ hderiv hmeas hnorm
  refine ⟨limit, hlimit, fun t ht ↦ (hrate t ht).trans_eq ?_⟩
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A nonnegative scalar quantity bounded by a decaying exponential tends to zero.
Both inequalities are only needed eventually on the time half-line. -/
theorem tendsto_zero_of_nonneg_le_exp
    {f : ℝ → ℝ} {a C γ : ℝ} (hγ : 0 < γ)
    (hnonneg : ∀ t ∈ Ici a, 0 ≤ f t)
    (hbound : ∀ t ∈ Ici a, f t ≤ C * Real.exp (-γ * (t - a))) :
    Tendsto f atTop (𝓝 0) := by
  have hshift : Tendsto (fun t : ℝ ↦ t - a) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      tendsto_atTop_add_const_right atTop (-a) tendsto_id
  have hexp : Tendsto (fun t ↦ Real.exp (-γ * (t - a))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hshift.const_mul_atTop hγ)
  apply squeeze_zero' ((eventually_ge_atTop a).mono fun t ht ↦ hnonneg t ht)
    ((eventually_ge_atTop a).mono fun t ht ↦ hbound t ht)
  simpa only [mul_zero] using hexp.const_mul C

/-- Grönwall bounds an energy whose derivative is at most `-2δ` times the energy.
For positive `δ`, this gives exponential decay at rate `2δ`. -/
theorem energy_le_exp_of_differential_inequality
    {energy production : ℝ → ℝ} {a b δ : ℝ}
    (hderiv : ∀ s ∈ Icc a b, HasDerivAt energy (production s) s)
    (hbound : ∀ s ∈ Ico a b, production s ≤ -(2 * δ) * energy s) :
    ∀ s ∈ Icc a b, energy s ≤ energy a * Real.exp (-(2 * δ) * (s - a)) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (fun s hs ↦ (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs r hr ↦
      ((hderiv s (Ico_subset_Icc_self hs)).hasDerivWithinAt).liminf_right_slope_le hr)
    le_rfl (fun s hs ↦ (hbound s hs).trans_eq (add_zero _).symm)
  simpa only [gronwallBound_ε0] using h

/-- A nonnegative energy satisfying the derived coercive differential
inequality tends to zero on the whole time half-line. -/
theorem energy_tendsto_zero_of_differential_inequality
    {energy production : ℝ → ℝ} {a δ : ℝ} (hδ : 0 < δ)
    (hnonneg : ∀ t ∈ Ici a, 0 ≤ energy t)
    (hderiv : ∀ t ∈ Ici a, HasDerivAt energy (production t) t)
    (hbound : ∀ t ∈ Ici a, production t ≤ -(2 * δ) * energy t) :
    Tendsto energy atTop (𝓝 0) := by
  have hupper : ∀ t ∈ Ici a,
      energy t ≤ energy a * Real.exp (-(2 * δ) * (t - a)) := by
    intro t ht
    exact energy_le_exp_of_differential_inequality
      (fun s hs ↦ hderiv s hs.1) (fun s hs ↦ hbound s hs.1) t ⟨ht, le_rfl⟩
  exact tendsto_zero_of_nonneg_le_exp (by positivity : 0 < 2 * δ) hnonneg hupper

end PDE.Analysis.Evolution
