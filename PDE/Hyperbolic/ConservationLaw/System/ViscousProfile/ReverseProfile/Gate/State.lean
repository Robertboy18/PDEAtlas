/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback

import CAS.ExactTactic

/-!
# State reductions on the upward gate for arbitrary delta

One state calculation gives the full concrete flux, its middle speed, the
normalized right eigenvectors, and the full state differential. The fast-law values
and slopes retain their arbitrary delta parameter. The signed gate needs only
pointwise differentiability at the current middle coordinate; reflected support
supplies its ordinary derivative at the negative coordinate.

The zero-delta statement is the special case `δ = 0` of this calculation. Nonzero
spectral gaps are proved separately from these algebraic formulas.
-/

@[expose] public noncomputable section

open Filter Set
open PDE.Analysis PDE.Analysis.NormalizedPulse
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- Simultaneous upward-gate reductions for the fast law at arbitrary delta.
The strict fast margins make the feedback locally constant with value one
at the current fast coordinate. The vector formulas retain the normalization, including when a
denominator vanishes; their eigenbasis interpretation requires separate gaps. -/
theorem concreteGatedFlux_upward_gate_state_general {δ A B : ℝ} {b : ℝ → ℝ} {q : ℝ^3}
    (hAB : A ^ 2 < B ^ 2) (hb : DifferentiableAt ℝ b (q 1))
    (hsupport : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10)) (hy : 205 < q 1) (hinner : 2 < q 2)
    (houter : (q 2) ^ 2 < A ^ 2) :
    concreteGatedFlux δ (clockFeedback A B) b q =
        !₂[-fastLogCosh δ (q 0) + b (q 1) * q 2,
          MiddleClock.g (q 1) + 1, fastLogCosh δ (q 2)] ∧
      GatedFlux.middleSpeed MiddleClock.g cutoff (clockFeedback A B) q =
        deriv MiddleClock.g (q 1) ∧
      GatedFlux.rightEigenvector (fastLogCosh δ) MiddleClock.g cutoff
          (clockFeedback A B) b q =
        ![!₂[1, 0, 0],
          !₂[deriv b (q 1) * q 2 /
            (deriv MiddleClock.g (q 1) + deriv (fastLogCosh δ) (q 0)), 1, 0],
          !₂[b (q 1) / (deriv (fastLogCosh δ) (q 2) +
            deriv (fastLogCosh δ) (q 0)), 0, 1]] ∧
      ∀ w : ℝ^3, fderiv ℝ (concreteGatedFlux δ (clockFeedback A B) b) q w =
        !₂[-deriv (fastLogCosh δ) (q 0) * w 0 +
            deriv b (q 1) * q 2 * w 1 + b (q 1) * w 2,
          deriv MiddleClock.g (q 1) * w 1, deriv (fastLogCosh δ) (q 2) * w 2] := by
  have hyneg : -q 1 ≤ 100 := by
    generalize q 1 = y at hy ⊢
    cas using [hy]
  have hCy : cutoff (q 1) = 0 := cutoff_of_ge hy.le
  have hCny : cutoff (-q 1) = 1 := cutoff_of_le hyneg
  have hdCy : deriv cutoff (q 1) = 0 := by
    simp only [deriv_cutoff, transitionGap_of_ge hy.le, neg_zero, zero_div]
  have hdCny : deriv cutoff (-q 1) = 0 := by
    simp only [deriv_cutoff, transitionGap_of_le hyneg, neg_zero, zero_div]
  have hnegSupport : -q 1 ∉ tsupport b :=
    fun hmem ↦ (not_lt_of_ge (hyneg.trans (by cas : (100 : ℝ) ≤ 205))) (hsupport hmem).1
  have hbneg : b (-q 1) = 0 := image_eq_zero_of_notMem_tsupport hnegSupport
  have hbnegDeriv : HasDerivAt b 0 (-q 1) := HasDerivAt.of_notMem_tsupport hnegSupport
  have hdbneg : deriv b (-q 1) = 0 := hbnegDeriv.deriv
  have hplateau : clockFeedback A B =ᶠ[𝓝 (q 2)] fun _ ↦ (1 : ℝ) := by
    have houterNear : {z : ℝ | z ^ 2 < A ^ 2} ∈ 𝓝 (q 2) :=
      (isOpen_lt (continuous_id.pow 2) continuous_const).mem_nhds houter
    filter_upwards [Ioi_mem_nhds hinner, houterNear] with z hz hzA
    change 2 < z at hz
    change z ^ 2 < A ^ 2 at hzA
    rw [clockFeedback_of_sq_le hAB hzA.le]
    exact transition_of_one_le (by cas using [hz, sq_nonneg (z - 2)])
  have hφ : clockFeedback A B (q 2) = 1 := hplateau.eq_of_nhds
  have hdφ : deriv (clockFeedback A B) (q 2) = 0 :=
    ((hasDerivAt_const (q 2) (1 : ℝ)).congr_of_eventuallyEq hplateau).deriv
  have hm : GatedFlux.middleSpeed MiddleClock.g cutoff (clockFeedback A B) q =
      deriv MiddleClock.g (q 1) := by
    simp only [GatedFlux.middleSpeed, hdCy, hdCny, zero_mul, sub_zero, add_zero]
  refine ⟨?_, hm, ?_, ?_⟩
  · simp only [concreteGatedFlux, GatedFlux.flux, hCy, hCny, hbneg, hφ,
      zero_mul, one_mul, add_zero, sub_zero]
  · simp only [GatedFlux.rightEigenvector, hm, hCy, hbneg, hdbneg, hdφ,
      neg_zero, zero_mul, mul_zero, zero_div, add_zero, sub_neg_eq_add]
  · intro w
    have hk : Differentiable ℝ (fastLogCosh δ) :=
      (contDiff_fastLogCosh δ).differentiable (by simp)
    have hg : Differentiable ℝ MiddleClock.g :=
      MiddleClock.contDiff_g.differentiable (by simp)
    have hC : Differentiable ℝ cutoff := contDiff_cutoff.differentiable (by simp)
    have hφsmooth : Differentiable ℝ (clockFeedback A B) :=
      (contDiff_clockFeedback A B).differentiable (by simp)
    simpa only [concreteGatedFlux, hm, hCy, hCny, hbneg, hdbneg, hdφ,
      zero_mul, one_mul, mul_zero, zero_add, add_zero, neg_zero] using
      GatedFlux.fderiv_flux_apply (q := q) (v := w)
        (hk (q 0)) (hk (q 2)) (hg (q 1)) (hC (q 1)) (hC (-q 1))
        (hφsmooth (q 0)) (hφsmooth (q 2)) hb hbnegDeriv.differentiableAt

/-- Simultaneous reductions at one upward-gate state, retaining the complete flux,
all three normalized vectors, and the Jacobian action in every direction.
The support bound is the broad gate interval; the state needs only its lower bound.
The strict fast-state bounds control both transitions of the feedback. -/
theorem concreteGatedFlux_upward_gate_state {A B : ℝ} {b : ℝ → ℝ} {q : ℝ^3} (hAB : A ^ 2 < B ^ 2)
    (hb : DifferentiableAt ℝ b (q 1)) (hsupport : tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10))
    (hy : 205 < q 1) (hinner : 2 < q 2) (houter : (q 2) ^ 2 < A ^ 2) :
    concreteGatedFlux 0 (clockFeedback A B) b q =
        !₂[-2 * q 0 + b (q 1) * q 2, MiddleClock.g (q 1) + 1, 2 * q 2] ∧
      GatedFlux.rightEigenvector (fastLogCosh 0) MiddleClock.g cutoff
        (clockFeedback A B) b q 0 = !₂[1, 0, 0] ∧
      GatedFlux.rightEigenvector (fastLogCosh 0) MiddleClock.g cutoff
        (clockFeedback A B) b q 1 =
          !₂[deriv b (q 1) * q 2 / (deriv MiddleClock.g (q 1) + 2), 1, 0] ∧
      GatedFlux.rightEigenvector (fastLogCosh 0) MiddleClock.g cutoff
        (clockFeedback A B) b q 2 = !₂[b (q 1) / 4, 0, 1] ∧
      ∀ w : ℝ^3, fderiv ℝ (concreteGatedFlux 0 (clockFeedback A B) b) q w =
        !₂[-2 * w 0 + deriv b (q 1) * q 2 * w 1 + b (q 1) * w 2,
          deriv MiddleClock.g (q 1) * w 1, 2 * w 2] := by
  obtain ⟨hflux, _, hr, hJac⟩ := concreteGatedFlux_upward_gate_state_general
    (δ := 0) (q := q) hAB hb hsupport hy hinner houter
  have hkvalue (s : ℝ) : fastLogCosh 0 s = 2 * s := by
    simp only [fastLogCosh, zero_mul, add_zero]
  have hkderiv (s : ℝ) : deriv (fastLogCosh 0) s = 2 := by
    simp only [deriv_fastLogCosh, zero_mul, add_zero]
  have hfour : (2 : ℝ) + 2 = 4 := by cas
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hkvalue, neg_mul] using hflux
  · exact congrFun hr (0 : Fin 3)
  · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, hkderiv] using congrFun hr (1 : Fin 3)
  · simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hkderiv, hfour] using
      congrFun hr (2 : Fin 3)
  · intro w
    simpa only [hkderiv] using hJac w

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
