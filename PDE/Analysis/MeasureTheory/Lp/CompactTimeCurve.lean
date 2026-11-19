/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.TimeDerivative
public import PDE.Analysis.MeasureTheory.Lp.TimeRegularity
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Essentially bounded curves from continuous coefficient fields

Continuous fields on a compact cylinder determine `L∞` classes with a
uniform norm bound. Continuous time derivatives then give a Lipschitz curve and
identify its derivative in the essential-supremum norm.

The spatial measure need only be concentrated on the compact set. The conclusions
concern the closed time interval, and the chosen classes outside it play no role.
-/

@[expose] public section

noncomputable section

namespace MeasureTheory

open Filter Set
open scoped ENNReal NNReal Topology

/-- Joint continuity on a compact cylinder gives norm continuity of its `L∞` classes. -/
theorem continuousOn_lp_top_of_continuousOn_compact
    {α E : Type*} [MetricSpace α] [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {K : Set α}
    (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) {a b : ℝ}
    (f : ℝ → α → E) (F : ℝ → Lp E ∞ μ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ K))
    (hrep : ∀ t ∈ Icc a b, (F t : α → E) =ᵐ[μ] f t) :
    ContinuousOn F (Icc a b) := by
  intro t ht
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hf) (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hst
  have hbound : ∀ᵐ x ∂μ, ‖((F s - F t : Lp E ∞ μ) : α → E) x‖ ≤ ε / 2 := by
    filter_upwards [hμ, Lp.coeFn_sub (F s) (F t), hrep s hs, hrep t ht]
      with x hx hsub hsx htx
    rw [hsub]
    change ‖(F s : α → E) x - (F t : α → E) x‖ ≤ ε / 2
    rw [hsx, htx]
    have hpair : dist (s, x) (t, x) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hst
    simpa only [Function.uncurry_def, dist_eq_norm] using
      (hmod (s, x) ⟨hs, hx⟩ (t, x) ⟨ht, hx⟩ hpair).le
  rw [dist_eq_norm, Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable (F s - F t))]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hbound)).trans_lt
    (by rw [ENNReal.toReal_ofReal (by positivity)]; linarith)

/-- A continuous field on a compact cylinder determines uniformly bounded `L∞`
classes for its time sections. The spatial measure need only be concentrated on
the compact set; its total mass need not be finite. Values outside the time
interval are chosen to be zero and play no role in the conclusions. -/
theorem exists_lp_top_curve_of_continuousOn_compact
    {α E : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E]
    {μ : Measure α} {K : Set α} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    {a b : ℝ} (f : ℝ → α → E)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ K)) :
    ∃ (F : ℝ → Lp E ∞ μ) (M : ℝ≥0), ∀ t ∈ Icc a b,
      (F t : α → E) =ᵐ[μ] f t ∧ ‖F t‖ ≤ M := by
  classical
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hf
  let M : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      ∀ᵐ x ∂μ, ‖f t x‖ ≤ M :=
    hμ.mono fun x hx ↦ (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : MemLp (f t) ∞ μ := by
    have hslice : ContinuousOn (f t) K :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x hx ↦ ⟨ht, hx⟩)
    have hmeas : AEStronglyMeasurable (f t) μ := by
      have h := hslice.aestronglyMeasurable_of_isCompact (μ := μ) hK
        hK.isClosed.measurableSet
      rwa [Measure.restrict_eq_self_of_ae_mem hμ] at h
    exact memLp_top_of_bound hmeas M (hbound t ht)
  let F (t : ℝ) : Lp E ∞ μ :=
    if ht : t ∈ Icc a b then (hmem t ht).toLp (f t) else 0
  refine ⟨F, M, ?_⟩
  intro t ht
  have hFt : F t = (hmem t ht).toLp (f t) := dite_eq_left ht
  refine ⟨?_, ?_⟩
  · rw [hFt]
    exact (hmem t ht).coeFn_toLp
  · rw [hFt, Lp.norm_toLp, eLpNorm_exponent_top (hmem t ht).aestronglyMeasurable]
    exact
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (eLpNormEssSup_le_of_ae_bound (hbound t ht))).trans_eq
        (ENNReal.toReal_ofReal M.coe_nonneg)

/-- Continuous coefficients and continuous time derivatives on a compact cylinder
give a Lipschitz `L∞` curve with the identified `L∞` derivative. The derivative
is constructed from the pointwise time derivatives, including one-sided derivatives at the
time endpoints. This is the coefficient regularity needed by the wave energy method. -/
theorem exists_lp_top_curve_with_derivative_of_continuousOn_compact
    {α E : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {K : Set α} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    {a b : ℝ} (f fdot : ℝ → α → E)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ K))
    (hfdot : ContinuousOn (Function.uncurry fdot) (Icc a b ×ˢ K))
    (hderiv : ∀ x ∈ K, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s ↦ f s x) (fdot t x) (Icc a b) t) :
    ∃ (F D : ℝ → Lp E ∞ μ) (M N : ℝ≥0),
      (∀ t ∈ Icc a b, (F t : α → E) =ᵐ[μ] f t ∧ ‖F t‖ ≤ M) ∧
      (∀ t ∈ Icc a b, (D t : α → E) =ᵐ[μ] fdot t ∧ ‖D t‖ ≤ N) ∧
      LipschitzOnWith N F (Icc a b) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt F (D t) (Icc a b) t) := by
  by_cases hab : a ≤ b
  swap
  · -- an empty time interval: every clause is vacuous
    have hI : Icc a b = ∅ := Icc_eq_empty hab
    exact ⟨0, 0, 0, 0, fun t ht ↦ by simp [hI] at ht, fun t ht ↦ by simp [hI] at ht,
      hI ▸ lipschitzOnWith_empty _ _, fun t ht ↦ by simp [hI] at ht⟩
  obtain ⟨F, M, hF⟩ := exists_lp_top_curve_of_continuousOn_compact hK hμ f hf
  obtain ⟨D, N, hD⟩ := exists_lp_top_curve_of_continuousOn_compact hK hμ fdot hfdot
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hfdot
  let B : ℝ≥0 := max N ⟨max C 0, le_max_right _ _⟩
  refine ⟨F, D, M, B, hF, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨(hD t ht).1, (hD t ht).2.trans (show (N : ℝ) ≤ B from le_max_left _ _)⟩
  · have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Icc a b, ‖fdot t x‖ ≤ B := by
      filter_upwards [hμ] with x hx t ht
      exact (hC (t, x) ⟨ht, hx⟩).trans
        ((le_max_left C 0).trans (show max C 0 ≤ (B : ℝ) from le_max_right _ _))
    have hLip := lipschitzOnWith_lp_top_of_ae_hasDerivWithinAt
      (a := a) (b := b) F f fdot B
      (by simpa only [uIcc_of_le hab] using fun t ht ↦ (hF t ht).1)
      (by simpa only [uIcc_of_le hab] using hμ.mono fun x hx ↦ hderiv x hx)
      (by simpa only [uIcc_of_le hab] using hbound)
    simpa only [uIcc_of_le hab] using hLip
  · intro t ht
    exact hasDerivWithinAt_lp_top_of_continuousOn_compact hK hμ ht F (D t) f fdot
      (fun s hs ↦ (hF s hs).1) (hD t ht).1 hderiv hfdot

end MeasureTheory
