/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral

import PDE.Analysis.Evolution.ODE.Regularity

/-!
# Joining a closed physical core to two tails

Three supplied solutions of the same first-order profile equation can be joined
at matching endpoints. Within derivatives on the closed pieces give the ordinary
derivative at each join. Smoothness and the profile end conditions then follow
from the ODE and the two state limits, without a sign restriction on the speed.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Attach supplied physical tails to a closed core, preserving all three pieces.
Only within derivatives on their closed domains are required. The speed has no
sign restriction at this purely analytic attachment step. -/
theorem exists_viscousProfile_of_physical_core_and_tails {m : ℕ} {f : ℝ^m → ℝ^m} {μ lo hi : ℝ}
    {uR : ℝ^m} {u left right : ℝ → ℝ^m} (hf : ContDiff ℝ ∞ f) (hlohi : lo < hi) (hzero : f 0 = 0)
    (hendpoint : f uR = μ • uR) (hleftJoin : left lo = u lo) (hrightJoin : u hi = right hi)
    (hu : ∀ t ∈ Icc lo hi, HasDerivWithinAt u (f (u t) - μ • u t) (Icc lo hi) t)
    (hleftODE : ∀ t ∈ Iic lo, HasDerivWithinAt left (f (left t) - μ • left t) (Iic lo) t)
    (hrightODE : ∀ t ∈ Ici hi, HasDerivWithinAt right (f (right t) - μ • right t) (Ici hi) t)
    (hleft : Tendsto left atBot (𝓝 0)) (hright : Tendsto right atTop (𝓝 uR)) :
    ∃ q : ℝ → ℝ^m, IsViscousProfile f 0 uR μ q ∧ EqOn q u (Icc lo hi) ∧ EqOn q left (Iic lo) ∧
      EqOn q right (Ici hi) := by
  let q : ℝ → ℝ^m := fun t ↦ if t ≤ lo then left t else if t ≤ hi then u t else right t
  have hql (t : ℝ) (ht : t ≤ lo) : q t = left t := by
    simp only [q, ite_eq_left ht]
  have hqu (t : ℝ) (ht : t ∈ Icc lo hi) : q t = u t := by
    rcases eq_or_lt_of_le ht.1 with rfl | hlt
    · simpa only [q, ite_eq_left le_rfl] using hleftJoin
    · simp only [q, ite_eq_right (not_le.mpr hlt), ite_eq_left ht.2]
  have hqr (t : ℝ) (ht : hi ≤ t) : q t = right t := by
    have htl : ¬t ≤ lo := not_le.mpr (hlohi.trans_le ht)
    rcases eq_or_lt_of_le ht with rfl | hlt
    · simpa only [q, ite_eq_right htl, ite_eq_left le_rfl] using hrightJoin
    · simp only [q, ite_eq_right htl, ite_eq_right (not_le.mpr hlt)]
  have hqlD (t : ℝ) (ht : t ≤ lo) : HasDerivWithinAt q (f (q t) - μ • q t) (Iic lo) t :=
    hql t ht ▸ (hleftODE t ht).congr_of_mem hql ht
  have hquD (t : ℝ) (ht : t ∈ Icc lo hi) : HasDerivWithinAt q (f (q t) - μ • q t) (Icc lo hi) t :=
    hqu t ht ▸ (hu t ht).congr_of_mem hqu ht
  have hqrD (t : ℝ) (ht : hi ≤ t) : HasDerivWithinAt q (f (q t) - μ • q t) (Ici hi) t :=
    hqr t ht ▸ (hrightODE t ht).congr_of_mem hqr ht
  -- At a join, the two within derivatives have the same field value.
  have hqODE (t : ℝ) : HasDerivAt q (f (q t) - μ • q t) t := by
    rcases lt_trichotomy t lo with hlt | heq | hgt
    · exact (hqlD t hlt.le).hasDerivAt (Iic_mem_nhds hlt)
    · subst t
      have hD := (hqlD lo le_rfl).union (hquD lo ⟨le_rfl, hlohi.le⟩)
      rw [Iic_union_Icc_eq_Iic hlohi.le] at hD
      exact hD.hasDerivAt (Iic_mem_nhds hlohi)
    · rcases lt_trichotomy t hi with hlt | heq | hgt'
      · exact (hquD t ⟨hgt.le, hlt.le⟩).hasDerivAt (Icc_mem_nhds hgt hlt)
      · subst t
        have hD := (hquD hi ⟨hlohi.le, le_rfl⟩).union (hqrD hi le_rfl)
        rw [Icc_union_Ici_eq_Ici hlohi.le] at hD
        exact hD.hasDerivAt (Ici_mem_nhds hlohi)
      · exact (hqrD t hgt'.le).hasDerivAt (Ici_mem_nhds hgt')
  have hqLeft : Tendsto q atBot (𝓝 0) :=
    hleft.congr' ((eventually_le_atBot lo).mono fun t ht ↦ (hql t ht).symm)
  have hqRight : Tendsto q atTop (𝓝 uR) :=
    hright.congr' ((eventually_ge_atTop hi).mono fun t ht ↦ (hqr t ht).symm)
  have hfield : ContDiff ℝ ∞ (fun p : ℝ × ℝ^m ↦ f p.2 - μ • p.2) :=
    (hf.comp contDiff_snd).sub (contDiff_snd.const_smul μ)
  have hqSmooth : ContDiff ℝ ∞ q :=
    contDiffOn_univ.mp <| PDE.Analysis.Evolution.contDiffOn_of_hasDerivAt
      (f := fun _ x ↦ f x - μ • x) isOpen_univ hfield.contDiffOn fun t _ ↦ hqODE t
  have hjump : RankineHugoniot f 0 uR μ := by
    change f uR - f 0 = μ • (uR - 0)
    simpa only [hzero, sub_zero] using hendpoint
  exact ⟨q, isViscousProfile_of_first_order (hf.differentiable (by simp))
    (hqSmooth.of_le (by simp)) (fun t ↦ by simpa only [hzero, sub_zero] using hqODE t)
    hqLeft hqRight hjump, fun _ ht ↦ hqu _ ht, fun _ ht ↦ hql _ ht, fun _ ht ↦ hqr _ ht⟩

end PDE.Hyperbolic.ConservationLaw.System
