/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.FullInterval
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.LocalExistence
import PDE.Analysis.Calculus.LocalExtension.TimeBand

/-!
# Classical representatives on every bounded integral prefix

For a real exponent above two, finite C² persistence upgrades the bounded
C¹ integral trajectory. Extending its C² past to a global source and applying the
Kirchhoff and Duhamel formulas gives a classical representative on any proper
closed prefix. The representative agrees with the original nonlinear trajectory;
the pointwise PDE and both initial traces are derived from the formulas.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open PDE (partialDeriv)
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- Every proper closed prefix of a bounded C¹ integral trajectory has a
jointly C² classical representative for a real signed power above two. This
includes the initial face and assumes no second derivative of the trajectory. -/
theorem exists_classical_representative_on_bounded_integral_prefix {r b L B M T : ℝ} (hr : 2 < r)
    (hb : 0 < b) (hT : 0 < T) (hTL : T < L) {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) {u : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L})
    (hHB : ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 (L + 1) → |cauchyFreeField g h p| ≤ B)
    (huB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |u p| ≤ M)
    (hue : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = cauchyFreeField g h p +
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦
      -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons p.1 p.2)) :
    ∃ v : ℝ^4 → ℝ, ContDiff ℝ 2 v ∧ IsSolutionBefore (Real.signedPower r) g h T v ∧ ∀ p : ℝ × ℝ^3,
      p.1 ∈ Icc 0 T → v (timeSpaceCons p.1 p.2) = u p := by
  have hH := contDiff_two_kirchhoffFormula hg hh
  have hfree : ContDiff ℝ 2 (cauchyFreeField g h) := hH.comp (contDiff_timeSpaceCons_uncurry 3)
  obtain ⟨⟨w, hw, hwu⟩, _⟩ := exists_c2_extension_of_bounded_signedPower_integral_eq
    hr hb (hT.trans hTL) hu hfree hHB huB hue
  obtain ⟨U, hU, hUevent⟩ := hw.exists_contDiff_eventuallyEq_on_band
    (ContinuousLinearMap.fst ℝ ℝ (ℝ^3)) (s := 0) (by norm_num) hTL
  have hUu (p : ℝ × ℝ^3) (hp : p.1 ∈ Icc 0 T) : U p = u p :=
    ((hUevent p hp).self_of_nhds).symm.trans (hwu p ⟨hp.1, hp.2.trans_lt hTL⟩)
  let F : ℝ^4 → ℝ := fun z ↦ -Real.signedPower r (U (timeSpaceContinuousLinearEquiv 3 z))
  have hF : ContDiff ℝ 2 F := ((contDiff_two_signedPower hr).comp
      (hU.comp (timeSpaceContinuousLinearEquiv 3).contDiff)).neg
  have hD := contDiff_two_oddDuhamelSolution 0 hF.contDiffOn
  let v : ℝ^4 → ℝ := fun z ↦ spaceTimeUncurry (kirchhoffFormula g h) z + oddDuhamelSolution 0 F z
  have hv : ContDiff ℝ 2 v := hH.add hD
  have hidentify (p : ℝ × ℝ^3) (hp : p.1 ∈ Icc 0 T) :
      v (timeSpaceCons p.1 p.2) = u p := by
    rw [hue p ⟨hp.1, hp.2.trans_lt hTL⟩]
    change cauchyFreeField g h p + oddDuhamelSolution 0 F (timeSpaceCons p.1 p.2) = _
    congr 1
    apply oddDuhamelSolution_congr_forward (F := fun q ↦ -Real.signedPower r (U q))
      (G := fun q ↦ -Real.signedPower r (u q)) p hp.1
    intro s hs x
    rw [hUu (s, x) ⟨hs.1, hs.2.trans hp.2⟩]
  have hfreeEq (z : ℝ^4) (hz : 0 ≤ z 0) :
      waveOperator (spaceTimeUncurry (kirchhoffFormula g h)) z = 0 := by
    rcases hz.eq_or_lt with hzero | hpos
    · have he := waveResidualAssignedCauchyDataProblem.residual_eq_initial hH
        (kirchhoffFormula_satisfiesResidualAssignedCauchyData hg hh) (spatialPart z)
      have hez : timeSpaceCons 0 (spatialPart z) = z := by
        rw [hzero, timeSpaceCons_spatialPart]
      rwa [hez] at he
    · exact waveOperator_kirchhoffFormula hg hh hpos
  refine ⟨v, hv, ⟨hT, hv.contDiffOn, ?_, ?_, ?_⟩, hidentify⟩
  · intro z hz
    change waveOperator (fun q ↦ spaceTimeUncurry (kirchhoffFormula g h) q +
      oddDuhamelSolution 0 F q) z = -Real.signedPower r (v z)
    rw [waveOperator_add hH.contDiffAt hD.contDiffAt, hfreeEq z hz.1,
      waveOperator_oddDuhamelSolution 0 hF.contDiffOn hz.1, zero_add]
    change -Real.signedPower r (U (z 0, spatialPart z)) = _
    rw [hUu (z 0, spatialPart z) ⟨hz.1, hz.2.le⟩]
    exact congrArg (fun y ↦ -Real.signedPower r y) (by
      simpa only [timeSpaceCons_spatialPart] using
        (hidentify (z 0, spatialPart z) ⟨hz.1, hz.2.le⟩).symm)
  · intro x
    simp only [v, kirchhoffFormula_initial_position, oddDuhamelSolution_initial, add_zero]
  · intro x
    change (∂[0] (fun z ↦ spaceTimeUncurry (kirchhoffFormula g h) z +
      oddDuhamelSolution 0 F z)) (timeSpaceCons 0 x) = _
    rw [partialDeriv_add (hH.differentiable (by norm_num) _)
      (hD.differentiable (by norm_num) _),
      partialDeriv_kirchhoffFormula_initial_velocity (hg.of_le (by norm_num))
        (hh.of_le (by norm_num)), partialDeriv_oddDuhamelSolution_initial 0 hF.contDiffOn, add_zero]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
