/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Bounded
public import PDE.Analysis.MeasureTheory.Integral.Reaction.Trace

/-!
# Reaction lower bounds for weakly differentiable L² trajectories

A bounded weak velocity controls the displacement from the actual initial trace.
On a high superlevel set of that trace, this forces a quantitative reaction cost
on short time cylinders. Both conclusions concern the same trajectory and its
joint spatial representative.
-/

@[expose] public section

open MeasureTheory Set PDE.Analysis.Evolution
open scoped NNReal

namespace MeasureTheory

/-- The weak time derivative supplies the L² trace modulus used in the reaction
lower bound. No independent distance estimate or displacement integrability is assumed. -/
theorem mul_sub_le_integral_reaction_sq_of_bounded_weak_derivative
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure ν]
    (hν : ν ≤ μ) {U V : ℝ → Lp ℝ 2 μ}
    {u : ℝ × X → ℝ} {g : X → ℝ} {f : ℝ → ℝ} {a b d τ : ℝ} {K : ℝ≥0}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hτ : 0 < τ)
    (hweak : HasWeakTimeDerivativeOn (Ioo 0 τ) U V)
    (hu : ∀ ell : StrongDual ℝ (Lp ℝ 2 μ),
      ContinuousOn (fun t ↦ ell (U t)) (Icc 0 τ))
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo 0 τ), ‖V t‖ ≤ K)
    (hlevel : ∀ᵐ x ∂ν, a + d ≤ g x) (hf : ∀ z : ℝ, a ≤ z → b ≤ |f z|)
    (hmeas : AEStronglyMeasurable (fun z ↦ u z - g z.2)
      ((volume.restrict (Ioc 0 τ)).prod ν))
    (hsection : ∀ᵐ t ∂volume.restrict (Ioc 0 τ),
      (U t : X → ℝ) =ᵐ[μ] fun x ↦ u (t, x))
    (hg : (U 0 : X → ℝ) =ᵐ[μ] g)
    (hr : Integrable (fun z ↦ (f (u z)) ^ 2)
      ((volume.restrict (Ioc 0 τ)).prod ν)) :
    b ^ 2 * (d ^ 2 * τ * ν.real univ - (K : ℝ) ^ 2 * τ ^ 3) ≤
      d ^ 2 * (∫ z, (f (u z)) ^ 2 ∂(volume.restrict (Ioc 0 τ)).prod ν) := by
  have hLip := hweak.lipschitzOnWith_of_weaklyContinuousOn hτ hu hbound
  apply mul_sub_le_integral_reaction_sq_of_lp_trace_bound hν hb hd hτ.le
    hlevel hf hmeas hsection hg _ hr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht.1.le] using
    hLip.dist_le_mul t (Ioc_subset_Icc_self ht) 0 (show (0 : ℝ) ∈ Icc 0 τ from ⟨le_rfl, hτ.le⟩)

end MeasureTheory
