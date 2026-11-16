/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedOverlap
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.RetardedRestart
import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralContinuation

/-!
# Constructed continuation of bounded C² signed-power integral trajectories

A bounded trajectory before a finite terminal time extends past that time.
This is the order-two case of `exists_signedPower_integral_extension`, which
constructs a uniformly long future cone solution at a nearby anchor,
identifies both branches by bounded cone uniqueness, and glues inside the
open overlap. For powers above two the signed power is C² and the C² cone
construction `exists_c2_signedPower_cone_trajectory` is available.

The extension preserves finite C² regularity. The pointwise nonlinear
wave equation is a separate representation statement.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology

open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- A bounded C² signed-power integral trajectory before a finite time has a
bounded C² integral extension beyond it, preserving the entire old trajectory.
The new amplitude bound is supplied by the constructed future branch. The
construction uses no bound on derivatives and no terminal trace. This is
`exists_signedPower_integral_extension` at order two. -/
theorem exists_c2_signedPower_integral_extension_of_bounded {r b L B M : ℝ}
    (hr : 2 < r) (hb : 0 < b) (hL : 0 < L) (hB : 0 ≤ B) (hM : 0 ≤ M)
    {u H : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | -b < p.1 ∧ p.1 < L}) (hH : ContDiff ℝ 2 H)
    (hHB : ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 (L + 1) → |H p| ≤ B)
    (huB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |u p| ≤ M)
    (hue : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L →
      u p = H p + oddDuhamelSolution 0
        (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
        (timeSpaceCons p.1 p.2)) :
    ∃ L' M' : ℝ, L < L' ∧ 0 ≤ M' ∧ ∃ w : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 2 w {p | -b < p.1 ∧ p.1 < L'} ∧
      EqOn w u {p | -b < p.1 ∧ p.1 < L} ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L' → |w p| ≤ M') ∧
      ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L' →
        w p = H p + oddDuhamelSolution 0
          (fun z : ℝ^4 ↦ -Real.signedPower r (w (timeSpaceContinuousLinearEquiv 3 z)))
          (timeSpaceCons p.1 p.2) :=
  exists_signedPower_integral_extension (m := 2) one_le_two (one_le_two.trans hr.le)
    (contDiff_two_signedPower hr) (fun _ hA ↦ exists_c2_signedPower_cone_trajectory hr hA)
    hb hL hB hM hu hH hHB huB hue

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
