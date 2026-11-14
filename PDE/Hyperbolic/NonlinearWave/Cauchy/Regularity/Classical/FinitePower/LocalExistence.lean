/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.ConeTrajectory
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Construction
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Lifespan
import PDE.Hyperbolic.Models.Wave.Kirchhoff.Family

/-!
# Local and maximal classical solutions for a C² reaction in three dimensions

The full Kirchhoff field and the classical Duhamel potential represent the constructed integral
trajectory on a smaller forward strip. Finite C² source regularity suffices.

Let `f : ℝ → ℝ` be `C²`, with no condition on its sign, on its growth or on its value at zero,
and let `g ∈ C³`, `h ∈ C²` be compactly supported Cauchy data on `ℝ³`. For the classical
solutions of `u_tt - Δu + f(u) = 0`, `WaveEquation.SmallData.Classical.IsSolutionBefore f g h T u`:

* `exists_classical_of_compact_data`: there is a solution before some time `T > 0`, and it is
  `C²` on the whole space-time;
* `exists_maximalSolution_of_compact_data`: when the durations of all solutions from `g`, `h` have
  a common bound, there is a maximal solution: it lives up to the supremum of the durations, and
  no solution with the same data extends it.

The first says nothing about the size of `T`, and the second assumes the bound. For signed powers
this gives the range above two (`exists_classical_signedPower_of_compact_data`).

## How it works

`exists_c2_cone_trajectory` is the fixed point behind the first theorem, for every free field
that is `C²` and bounded on the slab `0 ≤ t ≤ 1`. The free field of compactly supported data is
bounded on the slab (`exists_bound_cauchyFreeField_of_compact_data`), and
`exists_classical_representative_of_c2_integral_eq` turns the trajectory into a classical
solution. The maximal solution is the union of all solutions,
`WaveEquation.SmallData.Classical.exists_maximalSolution_of_bounded`.

## Related results

Other local existence theorems for classical solutions of semilinear waves, in other settings:

* smooth compactly supported data and a smooth reaction with `f 0 = 0`:
  `PDE.Hyperbolic.NonlinearWave.Cauchy.exists_unique_smooth_local_of_smoothCompact` and
  `exists_maximal_smooth_wave` in `ℝ³`, `exists_classical_localReaction_of_smoothCompact` in every
  dimension `n ≥ 1`; these are stated for `t ≥ 0`, with a one-sided velocity at `t = 0`;
* zero displacement and a bounded `C²` velocity that need not have compact support, every `C²`
  reaction, `ℝ³`: `exists_solutionBefore_of_contDiff_two` of
  `WaveEquation.SmallData.Classical.LocalPower`;
* one space dimension, every `C¹` reaction, bounded data `g ∈ C²`, `h ∈ C¹` with `g'` bounded:
  `WaveEquation.exists_bounded_classicalWaveBefore`.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open PDE (partialDeriv)
open scoped unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- A C² integral trajectory for the full Cauchy input has a classical
representative agreeing with that same trajectory at all sufficiently short
nonnegative times. The extension is C² across the initial slice. -/
theorem exists_classical_representative_of_c2_integral_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) {T : ℝ} (hT : 0 < T)
    {v a : ℝ × ℝ^3 → ℝ} (hv : ContDiffOn ℝ 2 v {p | |p.1| < T})
    (heq : ∀ p : ℝ × ℝ^3, |p.1| < T → v p = cauchyFreeField g h p + p.1 ^ 2 * a p)
    (hrem : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T → a p = ∫ s : I, (1 - (s : ℝ)) *
      ((∫ θ : Direction, f (v (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (θ : ℝ^3))))
      ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) :
    ∃ S : ℝ, 0 < S ∧ S < T ∧ ∃ u : ℝ^4 → ℝ, ContDiff ℝ 2 u ∧ IsSolutionBefore (fun z ↦ -f z) g h S
      u ∧ ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 S → u (timeSpaceCons p.1 p.2) = v p := by
  obtain ⟨S, hS, hST, V, hV, hVeq⟩ := exists_time_extension hT hv
  let F : ℝ^4 → ℝ := f ∘ V ∘ timeSpaceContinuousLinearEquiv 3
  have hF : ContDiff ℝ 2 F := hf.comp (hV.comp (timeSpaceContinuousLinearEquiv 3).contDiff)
  have hD := contDiff_two_oddDuhamelSolution 0 hF.contDiffOn
  have hH := contDiff_two_kirchhoffFormula hg hh
  let u : ℝ^4 → ℝ := fun z ↦ spaceTimeUncurry (kirchhoffFormula g h) z + oddDuhamelSolution 0 F z
  have hu : ContDiff ℝ 2 u := hH.add hD
  have hidentify (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 S) :
      u (timeSpaceCons p.1 p.2) = v p := by
    rw [heq p (by simpa only [abs_of_nonneg hp.1] using hp.2.trans hST),
      hrem p ⟨hp.1, hp.2.trans hST⟩]
    change spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons p.1 p.2) +
      oddDuhamelSolution 0 F (timeSpaceCons p.1 p.2) = _
    rw [oddDuhamelSolution_zero_eq_normalized F p.2 hp.1]
    congr 2
    congr 1 with s
    congr 3 with θ
    have hs : |p.1 * (s : ℝ)| < S := by
      rw [abs_of_nonneg (mul_nonneg hp.1 s.2.1)]
      exact (mul_le_of_le_one_right hp.1 s.2.2).trans_lt hp.2
    change f (V (timeSpaceContinuousLinearEquiv 3 (timeSpaceCons (p.1 * (s : ℝ))
      (p.2 + p.1 • ((1 - (s : ℝ)) • (θ : ℝ^3)))))) = _
    simp only [timeSpaceContinuousLinearEquiv_apply, PDE.time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons]
    rw [hVeq _ hs]
  have hfree (z : ℝ^4) (hz : 0 ≤ z 0) :
      waveOperator (spaceTimeUncurry (kirchhoffFormula g h)) z = 0 := by
    rcases hz.eq_or_lt with hzero | hpos
    · have he := waveResidualAssignedCauchyDataProblem.residual_eq_initial hH
        (kirchhoffFormula_satisfiesResidualAssignedCauchyData hg hh) (spatialPart z)
      have hez : timeSpaceCons 0 (spatialPart z) = z := by
        rw [hzero, timeSpaceCons_spatialPart]
      rwa [hez] at he
    · exact waveOperator_kirchhoffFormula hg hh hpos
  refine ⟨S, hS, hST, u, hu, ⟨hS, hu.contDiffOn, ?_, ?_, ?_⟩, hidentify⟩
  · intro z hz
    change waveOperator (fun q ↦ spaceTimeUncurry (kirchhoffFormula g h) q +
      oddDuhamelSolution 0 F q) z = - -f (u z)
    rw [waveOperator_add hH.contDiffAt hD.contDiffAt, hfree z hz.1,
      waveOperator_oddDuhamelSolution 0 hF.contDiffOn hz.1, zero_add, neg_neg]
    change f (V (z 0, spatialPart z)) = f (u z)
    rw [hVeq _ (by simpa only [abs_of_nonneg hz.1] using hz.2)]
    exact congrArg f (by
      simpa only [timeSpaceCons_spatialPart] using (hidentify (z 0, spatialPart z) hz).symm)
  · intro x
    simp only [u, kirchhoffFormula_initial_position, oddDuhamelSolution_initial, add_zero]
  · intro x
    change (∂[0] (fun z ↦ spaceTimeUncurry (kirchhoffFormula g h) z +
      oddDuhamelSolution 0 F z)) (timeSpaceCons 0 x) = _
    rw [partialDeriv_add (hH.differentiable (by norm_num) _)
      (hD.differentiable (by norm_num) _),
      partialDeriv_kirchhoffFormula_initial_velocity (hg.of_le (by norm_num))
        (hh.of_le (by norm_num)), partialDeriv_oddDuhamelSolution_initial 0 hF.contDiffOn, add_zero]

/-- **Local existence.** For a `C²` reaction `f` and compactly supported Cauchy data `g ∈ C³`,
`h ∈ C²` on `ℝ³`, the equation `u_tt - Δu + f(u) = 0` has a classical solution before some time
`T > 0`, and the solution is `C²` on the whole space-time. -/
theorem exists_classical_of_compact_data {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, ContDiff ℝ 2 u ∧ IsSolutionBefore f g h T u := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_cauchyFreeField_of_compact_data (hg.of_le (by norm_num))
    (hh.of_le (by norm_num)) hgs hhs 1
  obtain ⟨T, hT, -, htrajectory⟩ := exists_c2_cone_trajectory hf.neg hB
  obtain ⟨v, a, hv, -, heq, -, hrem⟩ := htrajectory (cauchyFreeField g h)
    ((contDiff_two_kirchhoffFormula hg hh).comp (contDiff_timeSpaceCons_uncurry 3)) hbound
  obtain ⟨S, -, -, u, hu, hsol, -⟩ :=
    exists_classical_representative_of_c2_integral_eq hf.neg hg hh hT hv heq hrem
  exact ⟨S, u, hu, by simpa only [neg_neg] using hsol⟩

/-- **A maximal solution.** Let `f` be a `C²` reaction and `g ∈ C³`, `h ∈ C²` compactly supported
Cauchy data on `ℝ³`. When the durations of all classical solutions of `u_tt - Δu + f(u) = 0` from
`g`, `h` have a common bound, there is a solution up to their supremum, and no classical solution
with the same data extends it. -/
theorem exists_maximalSolution_of_compact_data {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) (hbounded : BddAbove (existenceTimes f g h)) :
    ∃ u, IsMaximalSolutionBefore f g h (sSup (existenceTimes f g h)) u := by
  obtain ⟨a, u₀, -, h₀⟩ := exists_classical_of_compact_data hf hg hh hgs hhs
  exact exists_maximalSolution_of_bounded (hf.of_le (by norm_num)).locallyLipschitz hbounded h₀

/-- Every real signed-power exponent above two admits a local classical
solution for arbitrary compact C³ displacement and C² velocity. The solution
has a jointly C² extension across the initial slice. This is the case `f = Real.signedPower r`
of `exists_classical_of_compact_data`. -/
theorem exists_classical_signedPower_of_compact_data {r : ℝ} (hr : 2 < r)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, ContDiff ℝ 2 u ∧ IsSolutionBefore (Real.signedPower r) g h T u :=
  exists_classical_of_compact_data (contDiff_two_signedPower hr) hg hh hgs hhs

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
