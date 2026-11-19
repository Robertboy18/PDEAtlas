/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Branches.Integrals

/-!
# Explicit passage times on prescribed clock branches

Endpoint brackets give coverage of the closed gate by the supplied flow.
The primitive identities identify those crossings with explicit integral times.
Mathlib's setwise inverse gives branch membership, evaluation at the explicit
time, and uniqueness on the same branch, without selecting a new trajectory.

All range and switching margins are hypotheses on the fixed-parameter
branch.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open MiddleClock

/-- Every level of the closed gate is attained at its explicit upward integral
time, uniquely within the supplied closed pre-switch branch. The 205
anchor need not be the left endpoint. -/
theorem prescribed_speed_up_gate_coverage {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {A B : ℝ} {p : ℝ × ℝ}
    {s e b₀ : ℝ} (hAB : A ^ 2 < B ^ 2) (hμ : |p.1| < 1 / 410)
    (hF : ∀ t ∈ Icc s e, HasDerivAt (fun u ↦ F (u, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinner : ∀ t ∈ Icc s e, 2 < (F (t, p)).2) (houter : ∀ t ∈ Icc s e, (F (t, p)).2 ^ 2 < A ^ 2)
    (hband : ∀ t ∈ Icc s e, (F (t, p)).1 ∈ Icc (0 : ℝ) 210) (hb₀ : b₀ ∈ Icc s e)
    (hhit : (F (b₀, p)).1 = 205) (hstart : (F (s, p)).1 ≤ 205)
    (hend : (2051 / 10 : ℝ) ≤ (F (e, p)).1) :
    ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
      let tHit := b₀ + (∫ v in (205 : ℝ)..y, 1 / (g v + 1 - p.1 * v)); tHit ∈ Icc s e ∧
      (F (tHit, p)).1 = y ∧ ∀ t ∈ Icc s e, (F (t, p)).1 = y ↔ t = tHit := by
  let X : ℝ → ℝ := fun t ↦ (F (t, p)).1
  let P : ℝ → ℝ := fun y ↦ b₀ + (∫ v in (205 : ℝ)..y, 1 / (g v + 1 - p.1 * v))
  have hcont : ContinuousOn X (Icc s e) := fun t ht ↦ (hF t ht).continuousAt.fst.continuousWithinAt
  have hinv : LeftInvOn P X (Icc s e) :=
    fun t ht ↦ prescribed_speed_up_primitive_eq hAB hμ hF hinner houter hband hb₀ hhit t ht
  have hcover : SurjOn X (Icc s e) (Icc (205 : ℝ) (2051 / 10)) :=
    fun y hy ↦ intermediate_value_Icc (hb₀.1.trans hb₀.2) hcont ⟨hstart.trans hy.1, hy.2.trans hend⟩
  intro y hy
  change P y ∈ Icc s e ∧ X (P y) = y ∧ ∀ t ∈ Icc s e, X t = y ↔ t = P y
  have hmem : P y ∈ Icc s e := hinv.mapsTo hcover hy
  have hvalue : X (P y) = y := hinv.rightInvOn_image (hcover hy)
  refine ⟨hmem, hvalue, fun t ht ↦ ?_⟩
  simpa only [hvalue] using hinv.injOn.eq_iff ht hmem

/-- Every level of the closed gate is attained at its explicit downward integral
time, uniquely within the supplied completed-switch branch. The primitive
retains the cutoff all the way to the zero anchor. -/
theorem prescribed_speed_down_gate_coverage {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {A B : ℝ} {p : ℝ × ℝ}
    {s e τ : ℝ} (hAB : A ^ 2 < B ^ 2) (hμ : |p.1| < 1 / 410)
    (hF : ∀ t ∈ Icc s e, HasDerivAt (fun u ↦ F (u, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hafter : ∀ t ∈ Icc s e, B ^ 2 < (F (t, p)).2 ^ 2)
    (hband : ∀ t ∈ Icc s e, (F (t, p)).1 ∈ Icc (0 : ℝ) 210) (hτ : τ ∈ Icc s e)
    (hzero : (F (τ, p)).1 = 0) (hstart : (2051 / 10 : ℝ) ≤ (F (s, p)).1)
    (hend : (F (e, p)).1 ≤ 205) :
    ∀ y ∈ Icc (205 : ℝ) (2051 / 10),
      let tHit := τ - (∫ v in (0 : ℝ)..y, 1 / (4 - g v + 4 * cutoff v + p.1 * v)); tHit ∈ Icc s e ∧
      (F (tHit, p)).1 = y ∧ ∀ t ∈ Icc s e, (F (t, p)).1 = y ↔ t = tHit := by
  let X : ℝ → ℝ := fun t ↦ (F (t, p)).1
  let P : ℝ → ℝ := fun y ↦ τ - (∫ v in (0 : ℝ)..y, 1 / (4 - g v + 4 * cutoff v + p.1 * v))
  have hcont : ContinuousOn X (Icc s e) := fun t ht ↦ (hF t ht).continuousAt.fst.continuousWithinAt
  have hinv : LeftInvOn P X (Icc s e) :=
    fun t ht ↦ prescribed_speed_down_primitive_eq hAB hμ hF hafter hband hτ hzero t ht
  have hcover : SurjOn X (Icc s e) (Icc (205 : ℝ) (2051 / 10)) :=
    fun y hy ↦ intermediate_value_Icc' (hτ.1.trans hτ.2) hcont ⟨hend.trans hy.1, hy.2.trans hstart⟩
  intro y hy
  change P y ∈ Icc s e ∧ X (P y) = y ∧ ∀ t ∈ Icc s e, X t = y ↔ t = P y
  have hmem : P y ∈ Icc s e := hinv.mapsTo hcover hy
  have hvalue : X (P y) = y := hinv.rightInvOn_image (hcover hy)
  refine ⟨hmem, hvalue, fun t ht ↦ ?_⟩
  simpa only [hvalue] using hinv.injOn.eq_iff ht hmem

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
