/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.Reaction.PowerGrowth.Scale
public import PDE.Analysis.MeasureTheory.Integral.Reaction.WeakTrace
public import PDE.Analysis.Scalar.SmallParameter

/-!
# A seventh-power obstruction from initial superlevels

An initial level of size `s⁻²` on a set of volume comparable to `s^18`
cannot disappear quickly enough under an L² Lipschitz trace estimate.
Integrating over times of order `s^9` forces an unbounded integral of
the squared seventh-power reaction.
-/

@[expose] public section

open MeasureTheory Filter Set PDE.Analysis PDE.Analysis.Evolution
open scoped NNReal Topology

namespace MeasureTheory

/-- The seventh-power reaction cannot be square integrable if the initial
datum has the stated superlevels and its actual L² trace moves at bounded speed. -/
theorem not_integrable_pow_fourteen_of_trace_superlevels
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure ν]
    (hν : ν ≤ μ) {U : ℝ → Lp ℝ 2 μ} {G : Lp ℝ 2 μ}
    {u : ℝ × X → ℝ} {g : X → ℝ} {K T δ c : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hc : 0 < c) (S : ℝ → Set X)
    (hvol : ∀ s ∈ Ioc 0 δ, c * s ^ 18 ≤ ν.real (S s))
    (hlevel : ∀ s ∈ Ioc 0 δ,
      ∀ᵐ x ∂ν.restrict (S s), 1 / (2 * s ^ 2) + 1 ≤ g x)
    (hmeas : AEStronglyMeasurable (fun z ↦ u z - g z.2)
      ((volume.restrict (Ioc 0 T)).prod ν))
    (hsection : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (U t : X → ℝ) =ᵐ[μ] fun x ↦ u (t, x))
    (hg : (G : X → ℝ) =ᵐ[μ] g)
    (hdist : ∀ᵐ t ∂volume.restrict (Ioc 0 T), dist (U t) G ≤ K * t) :
    ¬Integrable (fun z ↦ u z ^ 14) ((volume.restrict (Ioc 0 T)).prod ν) := by
  intro hr
  have hr' : Integrable (fun z ↦ (u z ^ 7) ^ 2)
      ((volume.restrict (Ioc 0 T)).prod ν) := by
    simpa only [← pow_mul] using hr
  obtain ⟨k, hk, hcost⟩ := exists_pos_sq_mul_sq_lt hc K
  have htlim : Tendsto (fun s : ℝ ↦ k * s ^ 9) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun s : ℝ ↦ s) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_right inf_le_left
    simpa using (hid.pow 9).const_mul k
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s ∈ Ioc 0 δ ∧ k * s ^ 9 ≤ T := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ),
      htlim.eventually (Iio_mem_nhds hT)] with s hs hδs hτs
    exact ⟨⟨hs, hδs.le⟩, hτs.le⟩
  have hdiv := tendsto_seventh_power_cylinder_lower_bound hk hcost
  obtain ⟨s, hs, hlarge⟩ := (hsmall.and (hdiv.eventually_gt_atTop
    (∫ z, (u z ^ 7) ^ 2 ∂(volume.restrict (Ioc 0 T)).prod ν))).exists
  have hτ : 0 ≤ k * s ^ 9 := mul_nonneg hk.le (pow_nonneg hs.1.1.le 9)
  have htime : volume.restrict (Ioc 0 (k * s ^ 9)) ≤ volume.restrict (Ioc 0 T) :=
    volume.restrict_mono_set (Ioc_subset_Ioc_right hs.2)
  have hspace : ν.restrict (S s) ≤ ν := Measure.restrict_le_self
  have hp := Measure.prod_mono htime hspace
  have ha : 0 ≤ 1 / (2 * s ^ 2) := by positivity
  have hfloor (z : ℝ) (hz : 1 / (2 * s ^ 2) ≤ z) :
      (1 / (2 * s ^ 2)) ^ 7 ≤ |z ^ 7| :=
    (pow_le_pow_left₀ ha hz 7).trans (le_abs_self _)
  have hbound := mul_sub_le_integral_reaction_sq_of_lp_trace_bound
    (hspace.trans hν) (pow_nonneg ha 7) zero_le_one hτ (hlevel s hs.1) hfloor
    (hmeas.mono_measure hp) (hsection.filter_mono (ae_mono htime)) hg
    (hdist.filter_mono (ae_mono htime)) (hr'.mono_measure hp)
  simp only [one_pow, one_mul, measureReal_restrict_apply_univ] at hbound
  have hvolume := mul_le_mul_of_nonneg_left (hvol s hs.1) hτ
  have hlower := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hvolume (K ^ 2 * (k * s ^ 9) ^ 3))
    (sq_nonneg ((1 / (2 * s ^ 2)) ^ 7))
  exact hlarge.not_ge (hlower.trans (hbound.trans
    (integral_mono_measure hp (.of_forall fun _ ↦ sq_nonneg _) hr')))

/-- A bounded weak time derivative supplies the trace estimate in the
seventh-power obstruction; no separate displacement modulus is required. -/
theorem not_integrable_pow_fourteen_of_bounded_weak_derivative
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure ν]
    (hν : ν ≤ μ) {U V : ℝ → Lp ℝ 2 μ}
    {u : ℝ × X → ℝ} {g : X → ℝ} {T δ c : ℝ} {K : ℝ≥0}
    (hT : 0 < T) (hδ : 0 < δ) (hc : 0 < c) (S : ℝ → Set X)
    (hvol : ∀ s ∈ Ioc 0 δ, c * s ^ 18 ≤ ν.real (S s))
    (hweak : HasWeakTimeDerivativeOn (Ioo 0 T) U V)
    (hu : ∀ ell : StrongDual ℝ (Lp ℝ 2 μ),
      ContinuousOn (fun t ↦ ell (U t)) (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖V t‖ ≤ K)
    (hlevel : ∀ s ∈ Ioc 0 δ,
      ∀ᵐ x ∂ν.restrict (S s), 1 / (2 * s ^ 2) + 1 ≤ g x)
    (hmeas : AEStronglyMeasurable (fun z ↦ u z - g z.2)
      ((volume.restrict (Ioc 0 T)).prod ν))
    (hsection : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (U t : X → ℝ) =ᵐ[μ] fun x ↦ u (t, x))
    (hg : (U 0 : X → ℝ) =ᵐ[μ] g) :
    ¬Integrable (fun z ↦ u z ^ 14) ((volume.restrict (Ioc 0 T)).prod ν) := by
  apply not_integrable_pow_fourteen_of_trace_superlevels (K := (K : ℝ))
    hν hT hδ hc S hvol hlevel
    hmeas hsection hg
  have hLip := hweak.lipschitzOnWith_of_weaklyContinuousOn hT hu hbound
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht.1.le] using
    hLip.dist_le_mul t (Ioc_subset_Icc_self ht) 0
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)

end MeasureTheory
