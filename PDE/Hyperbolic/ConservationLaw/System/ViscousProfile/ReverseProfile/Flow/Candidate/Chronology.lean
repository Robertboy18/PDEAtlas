/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Candidate.Field

import PDE.Analysis.Evolution.ODE.Linear.Scalar.Constant
import CAS.ExactTactic

/-!
# The coupled field through the three clock phases

Before the upward cut, support keeps the scalar candidate zero. Between the
cuts, the slow cutoff vanishes. After the downward cut, the candidate and fast
state lie on their final feedback plateaus. These three facts give the same
feedback cancellation throughout the closed time interval.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Analysis.Evolution PDE.Analysis.NormalizedPulse

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The itinerary margins and the late candidate margin give the coupled
equation throughout the interval. The gate is signed and only its support is
used in the early phase. All coordinates are the same supplied clock slices. -/
theorem hasDerivAt_prescribed_coupled_candidate_of_itinerary {X Z b : ℝ → ℝ} {A B μ rUp rDown H : ℝ}
    (hforcing : Continuous (fun s ↦ b (X s)))
    (hbsupp : tsupport b ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100)) (hab : A ^ 2 < B ^ 2) (hB : 0 ≤ B)
    (hX : ∀ t ∈ Icc 0 H, HasDerivAt X (prescribedClockField A B (Z t) (X t) - μ * X t) t)
    (hZ : ∀ t ∈ Icc 0 H, HasDerivAt Z ((2 - μ) * Z t) t)
    (hearly : ∀ t ∈ Icc 0 rUp, -1 < X t ∧ X t < 20501 / 100 ∧ Z t ^ 2 < A ^ 2)
    (hmiddle : ∀ t ∈ Icc rUp rDown, (205 : ℝ) < X t)
    (hlate : ∀ t ∈ Icc rDown H, -1 < X t ∧ B ^ 2 < Z t ^ 2)
    (hresponse : ∀ t ∈ Icc rDown H, B <
      Z t * scalarLinearSolution (fun _ ↦ 4) (fun s ↦ b (X s)) 0 0 t) :
    let r := scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0 0
    let q : ℝ → ℝ^3 := fun s ↦ !₂[Z s * r s, X s, Z s]
    ∀ t ∈ Icc 0 H,
      HasDerivAt q
        (GatedFlux.flux (fun s ↦ 2 * s) MiddleClock.g cutoff (clockFeedback A B) b
          (q t) - μ • q t) t := by
  intro r q t ht
  have hrzero (t : ℝ) (ht : t ∈ Icc 0 rUp) : r t = 0 := by
    change scalarLinearSolution (fun _ ↦ 4) (fun s ↦ b (X s)) 0 0 t = 0
    rw [scalarLinearSolution_const_eq_exp_mul_add_integral]
    simp only [mul_zero, zero_add]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_le ht.1] at hs
    simp only [Function.notMem_support.mp fun hn ↦ (not_lt_of_ge
      (hearly s ⟨hs.1, hs.2.trans ht.2⟩).2.1.le) (hbsupp (subset_tsupport b hn)).1, mul_zero]
  have hφzero : clockFeedback A B 0 = 0 := by
    rw [clockFeedback_of_sq_le hab (by simpa using sq_nonneg A)]
    apply transition_of_nonpos
    simp
  have hlow : -1 < X t := by
    rcases le_or_gt t rUp with hu | hu
    · exact (hearly t ⟨ht.1, hu⟩).1
    rcases le_or_gt t rDown with hd | hd
    · linarith [hmiddle t ⟨hu.le, hd⟩]
    · exact (hlate t ⟨hd.le, ht.2⟩).1
  have hreflectCutoff : cutoff (-X t) = 1 := cutoff_of_le (by linarith)
  have hreflectGate : b (-X t) = 0 :=
    Function.notMem_support.mp fun hn ↦ by linarith [(hbsupp (subset_tsupport b hn)).1]
  have hcancel : cutoff (X t) * (clockFeedback A B (Z t * r t) +
        4 * outerTransition A B (Z t)) = 0 := by
    by_cases hu : t ≤ rUp
    · have he := hearly t ⟨ht.1, hu⟩
      rw [hrzero t ⟨ht.1, hu⟩, mul_zero, hφzero, outerTransition_of_sq_le hab he.2.2.le]
      simp
    · by_cases hd : t ≤ rDown
      · rw [cutoff_of_ge (hmiddle t ⟨(lt_of_not_ge hu).le, hd⟩).le, zero_mul]
      · have htime : t ∈ Icc rDown H := ⟨(lt_of_not_ge hd).le, ht.2⟩
        rw [clockFeedback_of_le_sq hab (pow_le_pow_left₀ hB (hresponse t htime).le 2),
          outerTransition_of_le_sq hab (hlate t htime).2.le]
        simp
  exact hasDerivAt_prescribed_coupled_candidate
    hforcing (hX t ht) (hZ t ht) hreflectCutoff hreflectGate hcancel

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
