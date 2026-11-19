/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Rarefaction.Profile
public import PDE.Hyperbolic.ConservationLaw.System.AffineFan
public import PDE.Hyperbolic.ConservationLaw.System.SimpleWave
import PDE.Analysis.Calculus.Piecewise

/-!
# Bounded weak rarefaction fans

A vector profile on a closed speed interval extends by its endpoint tangent
lines to a globally `C¹` middle state. The affine-fan theorem then
adjoins the constant endpoint states. Only values on the original interval
enter the assembled solution on positive time, so the profile's norm bound
is preserved even though its tangent extension need not be bounded.

The fan `u(x, t) = w(x/t)` is the self-similar form of the centered rarefaction waves of
Evans, §11.2.2, Theorem 1. The profile equation `DF(w(ξ)) w'(ξ) = ξ w'(ξ)` says that `w'(ξ)`
is a right eigenvector of `DF(w(ξ))` with eigenvalue `ξ`, so `w(x/t)` solves the system
classically inside the fan.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Set

/-- Construct a bounded measurable self-similar weak fan from a conservative
vector profile on a closed speed interval. The tangent extension justifies
the integration at both fan edges, including the case of equal speeds. -/
theorem exists_bounded_weak_rarefaction {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 1 flux)
    {profile : ℝ → ℝ^m} {a b K : ℝ} {left right : ℝ^m} (hab : a ≤ b)
    (hreg : ∀ ξ ∈ Icc a b, ContDiffAt ℝ 1 profile ξ)
    (hode : ∀ ξ ∈ Icc a b, fderiv ℝ flux (profile ξ) (deriv profile ξ) = ξ • deriv profile ξ)
    (hleft : profile a = left) (hright : profile b = right)
    (hbound : ∀ ξ ∈ Icc a b, ‖profile ξ‖ ≤ K) :
    ∃ u : ℝ^2 → ℝ^m,
      IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
      (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
      (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
      (∀ p : ℝ^2, p 1 < a * p 0 → u p = left) ∧
      (∀ p : ℝ^2, 0 < p 0 → b * p 0 ≤ p 1 → u p = right) ∧
      (∀ p : ℝ^2, 0 < p 0 → a * p 0 ≤ p 1 → p 1 < b * p 0 →
        u p = profile (similarityVariable p)) := by
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
  let u := AffineFan.profile a b left middle right
  have hsimilarity {p : ℝ^2} (ht : 0 < p 0) (ha : a * p 0 ≤ p 1) (hb : p 1 ≤ b * p 0) :
      similarityVariable p ∈ Icc a b := ⟨(le_div_iff₀ ht).mpr ha, (div_le_iff₀ ht).mpr hb⟩
  have hmiddle {p : ℝ^2} (ht : 0 < p 0) (ha : a * p 0 ≤ p 1) (hb : p 1 < b * p 0) :
      u p = profile (similarityVariable p) := by
    change AffineFan.profile a b left middle right p = _
    rw [AffineFan.profile_eq_middle (not_lt.mpr ha) hb]
    exact hext_eq (hsimilarity ht ha hb.le)
  have hweak : IsWeakSolution flux forwardHalfSpace u := by
    apply isWeakSolution_affineFan flux hflux a b hab left right middle
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
  have hmeas : Measurable u := by
    have hξ : Measurable similarityVariable := by
      change Measurable (fun p : ℝ^2 ↦ p 1 / p 0)
      fun_prop
    exact Measurable.ite (AffineInterface.measurableSet_leftHalfSpace a)
      measurable_const (Measurable.ite (AffineInterface.measurableSet_leftHalfSpace b)
        (hext.continuous.measurable.comp hξ) measurable_const)
  refine ⟨u, hweak, hmeas, ?_, ?_, ?_, ?_, ?_⟩
  · intro p ht
    by_cases ha : p 1 < a * p 0
    · rw [show u p = left from AffineFan.profile_eq_left ha, ← hleft]
      exact hbound a ⟨le_rfl, hab⟩
    · by_cases hb : p 1 < b * p 0
      · rw [hmiddle ht (le_of_not_gt ha) hb]
        exact hbound _ (hsimilarity ht (le_of_not_gt ha) hb.le)
      · rw [show u p = right from AffineFan.profile_eq_right ha hb, ← hright]
        exact hbound b ⟨hab, le_rfl⟩
  · exact fun c hc p ↦ AffineFan.profile_smul_of_pos hc a b left right middle
      (fun q ↦ selfSimilarWave_smul hc.ne' extended q) p
  · exact fun _ hp ↦ AffineFan.profile_eq_left hp
  · exact fun p ht hp ↦ AffineFan.profile_eq_right
      (not_lt.mpr ((mul_le_mul_of_nonneg_right hab ht.le).trans hp)) (not_lt.mpr hp)
  · exact fun _ ht ha hb ↦ hmiddle ht ha hb

end PDE.Hyperbolic.ConservationLaw.System
