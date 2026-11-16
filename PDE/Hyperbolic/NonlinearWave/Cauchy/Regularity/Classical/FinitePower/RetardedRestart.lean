/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedRestart
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.ConeTrajectory

/-!
# C² restart with the retarded history

For powers above two, the prescribed C² past source gives a C² future
integral trajectory. The lifetime uses only amplitude and elapsed time.
The three statements are the order-two cases of `contDiff_retardedSourceKernel`,
`contDiff_retardedHistory` and `exists_future_of_bounded_history`.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- A C² source gives a jointly C² spherical kernel, including zero age. -/
theorem contDiff_two_retardedSourceKernel {F : ℝ × ℝ^3 → ℝ}
    (hF : ContDiff ℝ 2 F) : ContDiff ℝ 2 (retardedSourceKernel F) :=
  contDiff_retardedSourceKernel (m := 2) hF

/-- The prescribed past becomes a C² free field for the future cone problem. -/
theorem contDiff_two_retardedHistory {F : ℝ × ℝ^3 → ℝ}
    (hF : ContDiff ℝ 2 F) (a : ℝ) : ContDiff ℝ 2 (retardedHistory a F) :=
  contDiff_retardedHistory (m := 2) hF a

/-- Amplitude bounds on the free wave and prescribed past source construct a
future branch on one common time interval for all histories and anchor times.
The integral in the conclusion is the physical Duhamel field. This is
`exists_future_of_bounded_history` at order two, with the cone construction
`exists_c2_signedPower_cone_trajectory`. -/
theorem exists_c2_signedPower_future_of_bounded_history {r : ℝ} (hr : 2 < r)
    {B M L : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ ∀ a ∈ Icc 0 L,
      ∀ H : ℝ × ℝ^3 → ℝ, ContDiff ℝ 2 H →
        (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 (L + 1) → |H p| ≤ B) →
      ∀ F : ℝ × ℝ^3 → ℝ, ContDiff ℝ 2 F →
        (∀ s ∈ Icc 0 a, ∀ x : ℝ^3, |F (s, x)| ≤ M) →
      ∃ v : ℝ × ℝ^3 → ℝ,
        ContDiffOn ℝ 2 v {p | |p.1| < T} ∧
        (∀ x : ℝ^3, v (0, x) = H (a, x) + retardedHistory a F (0, x)) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ v (t, x))
          (deriv (fun t ↦ H (a + t, x) + retardedHistory a F (t, x)) 0) 0) ∧
        (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → |v p| < B + L * (L + 1) * M + 1) ∧
        ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T →
          v p = H (a + p.1, p.2) + retardedHistory a F p +
            oddDuhamelSolution 0
              (fun z : ℝ^4 ↦ -Real.signedPower r (v (timeSpaceContinuousLinearEquiv 3 z)))
              (timeSpaceCons p.1 p.2) :=
  exists_future_of_bounded_history (m := 2) one_le_two (f := fun y ↦ -Real.signedPower r y)
    (fun _ hA ↦ exists_c2_signedPower_cone_trajectory hr hA) hB hM hL

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
