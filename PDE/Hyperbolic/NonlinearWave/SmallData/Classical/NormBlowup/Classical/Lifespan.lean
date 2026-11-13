/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.Classical.Comparison

/-!
# Equality of quadratic classical and higher Sobolev lifespans

The constructed higher lifetime is the greatest duration of same-data
C² solutions. Every smaller positive duration is realized by restriction, and
the solution at the greatest duration is defined on the open forward interval.
The supremum over classical competitors is therefore exactly the higher
lifespan whose Sobolev norm diverges.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped ENNReal NNReal Sobolev

namespace WaveEquation.SmallData.Classical.NormBlowup

/-- The constructed higher lifetime is attained by a classical wave
before that time, and bounds the duration of every C² competitor. -/
theorem isGreatest_quadratic_existenceTimes
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    IsGreatest (existenceTimes (fun z ↦ -(z ^ 2)) (fun _ ↦ 0)
      (classicalRepresentativeCLM (by norm_num) H)) (quadraticLifespan H).toReal := by
  obtain ⟨u, hu, _⟩ := exists_classical_quadratic_terminal H hs hpositive
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro S ⟨v, hv⟩
  exact classical_duration_le_quadratic_terminalTime H hs hR hpositive hv

/-- The entire set of classical durations is `(0,T]`, where `T` is
the constructed higher lifetime. Membership at `T` imposes no terminal trace. -/
theorem quadratic_existenceTimes_eq
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    existenceTimes (fun z ↦ -(z ^ 2)) (fun _ ↦ 0)
      (classicalRepresentativeCLM (by norm_num) H) =
        Ioc 0 (quadraticLifespan H).toReal := by
  ext S
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨hv.time_pos, classical_duration_le_quadratic_terminalTime H hs hR hpositive hv⟩
  · intro hS
    obtain ⟨u, hu, _⟩ := exists_classical_quadratic_terminal H hs hpositive
    exact ⟨u, hu.mono hS.1 hS.2⟩

/-- The higher Sobolev terminal time equals the supremum over all
same-data C² solution durations, with no higher regularity imposed on competitors. -/
theorem quadratic_terminalTime_eq_csSup
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    (quadraticLifespan H).toReal =
      sSup (existenceTimes (fun z ↦ -(z ^ 2)) (fun _ ↦ 0)
        (classicalRepresentativeCLM (by norm_num) H)) :=
  (isGreatest_quadratic_existenceTimes H hs hR hpositive).csSup_eq.symm

/-- The classical observation of the constructed higher trajectory is
maximal among C² competitors, while retaining both state components. -/
theorem exists_maximal_classical_quadratic_terminal
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    ∃ u : ℝ^4 → ℝ,
      IsMaximalSolutionBefore (fun z ↦ -(z ^ 2)) (fun _ ↦ 0)
        (classicalRepresentativeCLM (by norm_num) H) (quadraticLifespan H).toReal u ∧
      ∀ t ∈ Ico 0 (quadraticLifespan H).toReal, ∀ x,
        u (timeSpaceCons t x) =
          classicalRepresentativeCLM (by norm_num) (quadraticTrajectory H t).1 x ∧
        (∂[0] u) (timeSpaceCons t x) =
          classicalRepresentativeCLM (by norm_num) (quadraticTrajectory H t).2 x := by
  obtain ⟨u, hu, hrep⟩ := exists_classical_quadratic_terminal H hs hpositive
  refine ⟨u, ⟨hu, ?_⟩, hrep⟩
  intro S v hS hv _
  exact (not_lt_of_ge (classical_duration_le_quadratic_terminalTime H hs hR hpositive hv)) hS

end WaveEquation.SmallData.Classical.NormBlowup
