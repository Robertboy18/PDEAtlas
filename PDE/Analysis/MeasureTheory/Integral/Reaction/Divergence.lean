/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.Reaction.WeakTrace

/-!
# Superlevel obstructions to square-integrable reactions

A finite reaction integral bounds its contribution on every smaller cylinder.
If initial superlevel sets force those contributions to diverge, the actual
squared reaction is not integrable on the encompassing cylinder `(0, T] × X`.
The cylinder contains times arbitrarily close to the initial trace.
-/

@[expose] public section

open MeasureTheory Filter Set PDE.Analysis.Evolution
open scoped NNReal

namespace MeasureTheory

/-- Diverging reaction lower bounds on smaller cylinders contradict square
integrability on the encompassing cylinder. The displacement estimate refers to
actual L² classes and their joint representatives. -/
theorem not_integrable_reaction_sq_of_trace_superlevels
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure ν]
    (hν : ν ≤ μ) {U : ℝ → Lp ℝ 2 μ} {G : Lp ℝ 2 μ}
    {u : ℝ × X → ℝ} {g : X → ℝ} {f : ℝ → ℝ} {K T : ℝ}
    (S : ℕ → Set X) (τ a b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hτ : ∀ n, τ n ∈ Icc 0 T)
    (hlevel : ∀ n, ∀ᵐ x ∂ν.restrict (S n), a n + 1 ≤ g x)
    (hf : ∀ n, ∀ z : ℝ, a n ≤ z → b n ≤ |f z|)
    (hmeas : AEStronglyMeasurable (fun z ↦ u z - g z.2)
      ((volume.restrict (Ioc 0 T)).prod ν))
    (hsection : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (U t : X → ℝ) =ᵐ[μ] fun x ↦ u (t, x))
    (hg : (G : X → ℝ) =ᵐ[μ] g)
    (hdist : ∀ᵐ t ∂volume.restrict (Ioc 0 T), dist (U t) G ≤ K * t)
    (hdiv : Tendsto (fun n ↦ (b n) ^ 2 *
      (τ n * ν.real (S n) - K ^ 2 * (τ n) ^ 3)) atTop atTop) :
    ¬Integrable (fun z ↦ (f (u z)) ^ 2)
      ((volume.restrict (Ioc 0 T)).prod ν) := by
  intro hr
  have hupper (n : ℕ) : (b n) ^ 2 *
      (τ n * ν.real (S n) - K ^ 2 * (τ n) ^ 3) ≤
        ∫ z, (f (u z)) ^ 2 ∂(volume.restrict (Ioc 0 T)).prod ν := by
    have ht : volume.restrict (Ioc 0 (τ n)) ≤ volume.restrict (Ioc 0 T) :=
      volume.restrict_mono_set (Ioc_subset_Ioc_right (hτ n).2)
    have hs : ν.restrict (S n) ≤ ν := Measure.restrict_le_self
    have hp := Measure.prod_mono ht hs
    have hsmall := mul_sub_le_integral_reaction_sq_of_lp_trace_bound (hs.trans hν)
      (hb n) zero_le_one (hτ n).1 (hlevel n) (hf n) (hmeas.mono_measure hp)
      (hsection.filter_mono (ae_mono ht)) hg (hdist.filter_mono (ae_mono ht))
      (hr.mono_measure hp)
    simp only [one_pow, one_mul, measureReal_restrict_apply_univ] at hsmall
    exact hsmall.trans (integral_mono_measure hp (.of_forall fun _ ↦ sq_nonneg _) hr)
  obtain ⟨n, hn⟩ := (hdiv.eventually_ge_atTop
    ((∫ z, (f (u z)) ^ 2 ∂(volume.restrict (Ioc 0 T)).prod ν) + 1)).exists
  linarith only [hn, hupper n]

/-- A bounded weak derivative and the prescribed weakly continuous initial trace
supply the displacement modulus in the superlevel obstruction. -/
theorem not_integrable_reaction_sq_of_bounded_weak_derivative
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure ν]
    (hν : ν ≤ μ) {U V : ℝ → Lp ℝ 2 μ}
    {u : ℝ × X → ℝ} {g : X → ℝ} {f : ℝ → ℝ} {T : ℝ} {K : ℝ≥0}
    (hT : 0 < T) (S : ℕ → Set X) (τ a b : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hτ : ∀ n, τ n ∈ Icc 0 T)
    (hweak : HasWeakTimeDerivativeOn (Ioo 0 T) U V)
    (hu : ∀ ell : StrongDual ℝ (Lp ℝ 2 μ),
      ContinuousOn (fun t ↦ ell (U t)) (Icc 0 T))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ‖V t‖ ≤ K)
    (hlevel : ∀ n, ∀ᵐ x ∂ν.restrict (S n), a n + 1 ≤ g x)
    (hf : ∀ n, ∀ z : ℝ, a n ≤ z → b n ≤ |f z|)
    (hmeas : AEStronglyMeasurable (fun z ↦ u z - g z.2)
      ((volume.restrict (Ioc 0 T)).prod ν))
    (hsection : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (U t : X → ℝ) =ᵐ[μ] fun x ↦ u (t, x))
    (hg : (U 0 : X → ℝ) =ᵐ[μ] g)
    (hdiv : Tendsto (fun n ↦ (b n) ^ 2 *
      (τ n * ν.real (S n) - (K : ℝ) ^ 2 * (τ n) ^ 3)) atTop atTop) :
    ¬Integrable (fun z ↦ (f (u z)) ^ 2)
      ((volume.restrict (Ioc 0 T)).prod ν) := by
  apply not_integrable_reaction_sq_of_trace_superlevels hν S τ a b hb hτ
    hlevel hf hmeas hsection hg _ hdiv
  have hLip := hweak.lipschitzOnWith_of_weaklyContinuousOn hT hu hbound
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht.1.le] using
    hLip.dist_le_mul t (Ioc_subset_Icc_self ht) 0 (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)

end MeasureTheory
