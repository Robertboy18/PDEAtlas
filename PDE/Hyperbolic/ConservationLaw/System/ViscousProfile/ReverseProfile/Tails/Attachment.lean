/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Gluing.PhysicalTails
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Tails.Axis

/-!
# Attaching the preserved prescribed-clock axis tails

Agreement with the seed flux along both closed axis segments transfers its
physical tails to the corrected flux. Shifting these tails to the two core
anchors allows the general gluing theorem to preserve the entire supplied core.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

namespace ViscousProfile.ReverseProfile

open PDE.Analysis

/-- A corrected flux agreeing with the seed along both complete axis segments
inherits the seed's physical tails. A supplied matched physical core then gives
a viscous profile.

Agreement includes amplitude zero: it supplies the endpoint equilibria. The
core may be the output of `glue_ode_solution_Icc`, since only within derivatives
are needed. Its incoming part must already solve the physical field at speed
`μ`, even when it was constructed by integrating backward from its anchor. -/
theorem exists_viscousProfile_of_preserved_axis_tails {f : ℝ^3 → ℝ^3} {δ A B μ lo hi : ℝ}
    {b : ℝ → ℝ} {u : ℝ → ℝ^3} (hf : ContDiff ℝ ∞ f) (hδ : 0 ≤ δ) (hA : 1 ≤ A ^ 2)
    (hAB : A ^ 2 < B ^ 2) (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10))
    (hμ : μ ∈ Ioo (0 : ℝ) (1 / 20000)) (hlohi : lo < hi)
    (haxisLeft : ∀ s ∈ Icc (0 : ℝ) 1, f !₂[0, 0, s] =
      concreteGatedFlux δ (clockFeedback A B) b !₂[0, 0, s])
    (haxisRight : ∀ s ∈ Icc (0 : ℝ) 1, f !₂[s, 2000000 * μ, 0] =
      concreteGatedFlux δ (clockFeedback A B) b !₂[s, 2000000 * μ, 0])
    (hu : ∀ t ∈ Icc lo hi, HasDerivWithinAt u (f (u t) - μ • u t) (Icc lo hi) t)
    (hulo : u lo = !₂[0, 0, 1]) (huhi : u hi = !₂[1, 2000000 * μ, 0]) :
    ∃ q : ℝ → ℝ^3, IsViscousProfile f 0 !₂[0, 2000000 * μ, 0] μ q ∧ EqOn q u (Icc lo hi) ∧
      (∀ t ≤ lo, q t = !₂[0, 0, q t 2] ∧ q t 2 ∈ Ioc (0 : ℝ) 1) ∧
      (∀ t ≥ hi, q t = !₂[q t 0, 2000000 * μ, 0] ∧ q t 0 ∈ Ioc (0 : ℝ) 1) := by
  let g : ℝ^3 → ℝ^3 := concreteGatedFlux δ (clockFeedback A B) b
  have hμabs : |μ| < 1 / 20000 := by
    simpa only [abs_of_pos hμ.1] using hμ.2
  obtain ⟨qin, qout, hqin0, hqout0, hshape, hqinData, hqoutData,
      hqinLim, _, hqoutLim, _, hgzero, hgendpoint⟩ :=
    exists_prescribed_clock_axis_tails hδ hA hAB hbsupp hμabs
  have hqinField (t : ℝ) (ht : t ≤ 0) : f (qin t) = g (qin t) := by
    rw [(hshape t).1]
    exact haxisLeft _ ⟨(hqinData t ht).1.1.le, (hqinData t ht).1.2⟩
  have hqoutField (t : ℝ) (ht : 0 ≤ t) : f (qout t) = g (qout t) := by
    rw [(hshape t).2]
    exact haxisRight _ ⟨(hqoutData t ht).1.1.le, (hqoutData t ht).1.2⟩
  have hzeroVec : (!₂[0, 0, 0] : ℝ^3) = 0 := by
    ext i
    fin_cases i <;> rfl
  have hzero : f 0 = 0 := by
    have h := haxisLeft 0 ⟨le_rfl, zero_le_one⟩
    simpa only [hzeroVec, hgzero] using h
  have hendpoint : f !₂[0, 2000000 * μ, 0] = μ • !₂[0, 2000000 * μ, 0] :=
    (haxisRight 0 ⟨le_rfl, zero_le_one⟩).trans (sub_eq_zero.mp hgendpoint)
  let left : ℝ → ℝ^3 := fun t ↦ qin (t - lo)
  let right : ℝ → ℝ^3 := fun t ↦ qout (t - hi)
  have hleftJoin : left lo = u lo := by
    simpa only [left, sub_self] using hqin0.trans hulo.symm
  have hrightJoin : u hi = right hi := by
    simpa only [right, sub_self] using huhi.trans hqout0.symm
  have hleftODE (t : ℝ) (ht : t ∈ Iic lo) :
      HasDerivWithinAt left (f (left t) - μ • left t) (Iic lo) t := by
    have htime : t - lo ≤ 0 := sub_nonpos.mpr ht
    change HasDerivWithinAt (fun s ↦ qin (s - lo)) (f (qin (t - lo)) - μ • qin (t - lo)) (Iic lo) t
    rw [hqinField (t - lo) htime]
    exact (HasDerivAt.comp_sub_const t lo (hqinData (t - lo) htime).2).hasDerivWithinAt
  have hrightODE (t : ℝ) (ht : t ∈ Ici hi) :
      HasDerivWithinAt right (f (right t) - μ • right t) (Ici hi) t := by
    have htime : 0 ≤ t - hi := sub_nonneg.mpr ht
    change HasDerivWithinAt (fun s ↦ qout (s - hi))
      (f (qout (t - hi)) - μ • qout (t - hi)) (Ici hi) t
    rw [hqoutField (t - hi) htime]
    exact (HasDerivAt.comp_sub_const t hi (hqoutData (t - hi) htime).2).hasDerivWithinAt
  have hshiftLeft : Tendsto (fun t : ℝ ↦ t - lo) atBot atBot := by
    simpa only [sub_eq_add_neg, id_eq] using
      (tendsto_atBot_add_const_right atBot (-lo) (tendsto_id : Tendsto id atBot atBot))
  have hshiftRight : Tendsto (fun t : ℝ ↦ t - hi) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      (tendsto_atTop_add_const_right atTop (-hi) (tendsto_id : Tendsto id atTop atTop))
  obtain ⟨q, hq, hqu, hql, hqr⟩ :=
    exists_viscousProfile_of_physical_core_and_tails hf hlohi hzero hendpoint
      hleftJoin hrightJoin hu hleftODE hrightODE
      (hqinLim.comp hshiftLeft) (hqoutLim.comp hshiftRight)
  refine ⟨q, hq, hqu, ?_, ?_⟩
  · intro t ht
    rw [hql ht]
    exact ⟨(hshape (t - lo)).1, (hqinData (t - lo) (sub_nonpos.mpr ht)).1⟩
  · intro t ht
    rw [hqr ht]
    exact ⟨(hshape (t - hi)).2, (hqoutData (t - hi) (sub_nonneg.mpr ht)).1⟩

end ViscousProfile.ReverseProfile
end PDE.Hyperbolic.ConservationLaw.System
