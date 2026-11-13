/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Rarefaction.Fan
public import PDE.Hyperbolic.ConservationLaw.System.EntropyAffineFan
import PDE.Analysis.Calculus.Piecewise

/-!
# Entropy equality for constructed rarefaction profiles

A conservative `C¹` speed profile is extended by its endpoint tangents.
The affine-fan entropy theorem applies to this extension. Any
profile with the same fan values and outer states inherits every entropy
inequality on positive time.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open MeasureTheory Set

/-- A continuous conservative fan satisfies every convex entropy inequality.
Only the speed profile on the closed fan interval must be `C¹`; the values
of its spacetime representative at nonpositive times are immaterial. -/
theorem satisfiesEntropyInequality_rarefaction_of_profile {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 1 flux) {profile : ℝ → ℝ^m} {a b : ℝ} {left right : ℝ^m} {u : ℝ^2 → ℝ^m}
    (hab : a ≤ b) (hreg : ∀ ξ ∈ Icc a b, ContDiffAt ℝ 1 profile ξ)
    (hode : ∀ ξ ∈ Icc a b, fderiv ℝ flux (profile ξ) (deriv profile ξ) = ξ • deriv profile ξ)
    (hleft : profile a = left) (hright : profile b = right)
    (huLeft : ∀ p : ℝ^2, 0 < p 0 → p 1 < a * p 0 → u p = left)
    (huRight : ∀ p : ℝ^2, 0 < p 0 → b * p 0 ≤ p 1 → u p = right)
    (huMiddle : ∀ p : ℝ^2, 0 < p 0 → a * p 0 ≤ p 1 → p 1 < b * p 0 → u p =
      profile (similarityVariable p)) :
    SatisfiesEntropyInequality flux forwardHalfSpace u := by
  let extended := PDE.Analysis.tangentExtension profile a b
  have hext : ContDiff ℝ 1 extended := PDE.Analysis.contDiff_tangentExtension hab hreg
  have hext_eq {ξ : ℝ} (hξ : ξ ∈ Icc a b) : extended ξ = profile ξ :=
    PDE.Analysis.tangentExtension_eq_of_mem_Icc hξ
  have hext_ode {ξ : ℝ} (hξ : ξ ∈ Icc a b) :
      fderiv ℝ flux (extended ξ) (deriv extended ξ) = ξ • deriv extended ξ := by
    rw [hext_eq hξ, PDE.Analysis.deriv_tangentExtension_eq_of_mem_Icc
      hab hξ (hreg ξ hξ).differentiableAt_one]
    exact hode ξ hξ
  let middle := selfSimilarWave extended
  have hsimilarity {p : ℝ^2} (ht : 0 < p 0) (ha : a * p 0 ≤ p 1) (hb : p 1 ≤ b * p 0) :
      similarityVariable p ∈ Icc a b := ⟨(le_div_iff₀ ht).mpr ha, (div_le_iff₀ ht).mpr hb⟩
  have hfan : IsEntropyWeakSolution flux forwardHalfSpace
      (AffineFan.profile a b left middle right) := by
    apply isEntropyWeakSolution_affineFan hflux a b hab left right middle
    · exact fun p hp ↦ contDiffAt_selfSimilarWave hext.contDiffAt (ne_of_gt hp)
    · intro p hp
      apply fluxResidual_selfSimilarWave_eq_zero (ne_of_gt hp.1)
        hflux.differentiable_one.differentiableAt hext.differentiable_one.differentiableAt
      exact hext_ode (hsimilarity hp.1 (le_of_not_gt hp.2.2) hp.2.1.le)
    · intro t ht
      change extended (a * t / t) = left
      rw [mul_div_cancel_right₀ a ht.ne', hext_eq ⟨le_rfl, hab⟩, hleft]
    · intro t ht
      change extended (b * t / t) = right
      rw [mul_div_cancel_right₀ b ht.ne', hext_eq ⟨hab, le_rfl⟩, hright]
  apply hfan.entropy.congr_ae_restrict
  refine ae_restrict_of_forall_mem forwardHalfSpace.isOpen.measurableSet fun p ht ↦ ?_
  by_cases ha : p 1 < a * p 0
  · rw [AffineFan.profile_eq_left ha, huLeft p ht ha]
  by_cases hb : p 1 < b * p 0
  · rw [AffineFan.profile_eq_middle ha hb, huMiddle p ht (le_of_not_gt ha) hb]
    exact hext_eq (hsimilarity ht (le_of_not_gt ha) hb.le)
  · rw [AffineFan.profile_eq_right ha hb, huRight p ht (le_of_not_gt hb)]

end PDE.Hyperbolic.ConservationLaw.System
