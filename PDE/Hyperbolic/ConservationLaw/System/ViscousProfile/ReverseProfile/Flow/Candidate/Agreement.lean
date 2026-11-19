/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Candidate.Field

/-!
# Identifying the coupled trajectory

Once the candidate satisfies the full field, ordinary ODE uniqueness identifies
it with any supplied trajectory through the same initial state. Both images on
the time interval are compact. The smooth field is Lipschitz on a ball containing
them, so Mathlib's endpoint uniqueness theorem applies.
-/

@[expose] public noncomputable section

open Metric Set
open PDE.Analysis.Evolution
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The same prescribed candidate is the coupled shot once its field
equation has been established. The initial time is the left endpoint; derivatives
on the closed interval provide the right derivatives required by uniqueness. -/
theorem eqOn_prescribed_coupled_candidate {X Z b : ℝ → ℝ} {A B μ H : ℝ} {q : ℝ → ℝ^3}
    (hb : ContDiff ℝ 1 b)
    (hq : ∀ t ∈ Icc 0 H, HasDerivAt q (GatedFlux.flux (fun s ↦ 2 * s) MiddleClock.g cutoff
      (clockFeedback A B) b (q t) - μ • q t) t) :
    let r := scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0 0
    let qhat : ℝ → ℝ^3 := fun s ↦ !₂[Z s * r s, X s, Z s]
    (∀ t ∈ Icc 0 H, HasDerivAt qhat
      (GatedFlux.flux (fun s ↦ 2 * s) MiddleClock.g cutoff
        (clockFeedback A B) b (qhat t) - μ • qhat t) t) →
    q 0 = !₂[0, X 0, Z 0] →
    EqOn q qhat (Icc 0 H) := by
  dsimp only
  intro hcandidate hzero
  let r := scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0 0
  let qhat : ℝ → ℝ^3 := fun s ↦ !₂[Z s * r s, X s, Z s]
  let f : ℝ^3 → ℝ^3 := fun z ↦
    GatedFlux.flux (fun s ↦ 2 * s) MiddleClock.g cutoff (clockFeedback A B) b z - μ • z
  have hf : ContDiff ℝ 1 f := (GatedFlux.contDiff_flux (contDiff_const.mul contDiff_id)
      (MiddleClock.contDiff_g.of_le (by simp)) (contDiff_cutoff.of_le (by simp))
      ((contDiff_clockFeedback A B).of_le (by simp)) hb).sub (ContDiff.const_smul μ contDiff_id)
  have hqcont : ContinuousOn q (Icc 0 H) := HasDerivAt.continuousOn hq
  have hccont : ContinuousOn qhat (Icc 0 H) := HasDerivAt.continuousOn hcandidate
  have hcompact : IsCompact (q '' Icc 0 H ∪ qhat '' Icc 0 H) :=
    (isCompact_Icc.image_of_continuousOn hqcont).union (isCompact_Icc.image_of_continuousOn hccont)
  obtain ⟨R, _hR, hball⟩ := hcompact.isBounded.subset_closedBall_lt 0 (0 : ℝ^3)
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ℝ^3) R) (isCompact_closedBall _ _)
  have hinit : q 0 = qhat 0 := by
    simpa only [qhat, r, scalarLinearSolution_initial, mul_zero] using hzero
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ ↦ f) (s := fun _ ↦ closedBall 0 R) (fun _ _ ↦ hK)
    hqcont (fun t ht ↦ (hq t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht ↦ hball (Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩))
    hccont (fun t ht ↦ (hcandidate t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht ↦ hball (Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩)) hinit

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
