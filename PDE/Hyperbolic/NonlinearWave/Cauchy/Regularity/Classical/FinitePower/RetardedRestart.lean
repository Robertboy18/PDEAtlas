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
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- A C² source gives a jointly C² spherical kernel, including zero age. -/
theorem contDiff_two_retardedSourceKernel {F : ℝ × ℝ^3 → ℝ}
    (hF : ContDiff ℝ 2 F) : ContDiff ℝ 2 (retardedSourceKernel F) := by
  have hc : ContDiff ℝ 2 (fun z : ((ℝ × ℝ^3) × ℝ) × ℝ^3 ↦
      F (z.1.2, z.1.1.2 + (z.1.1.1 - z.1.2) • z.2)) := hF.comp (contDiff_fst.snd.prodMk
      (contDiff_fst.fst.snd.add ((contDiff_fst.fst.fst.sub contDiff_fst.snd).smul contDiff_snd)))
  exact (contDiff_fst.fst.sub contDiff_snd).mul ((contDiff_integral_compact_parametrization
      (μ := (volume : Measure (ℝ^3)).toSphere) hc continuous_subtype_val).div_const _)

/-- The prescribed past becomes a C² free field for the future cone problem. -/
theorem contDiff_two_retardedHistory {F : ℝ × ℝ^3 → ℝ}
    (hF : ContDiff ℝ 2 F) (a : ℝ) : ContDiff ℝ 2 (retardedHistory a F) :=
  (contDiff_intervalIntegral (contDiff_two_retardedSourceKernel hF) 0 a).comp
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)

/-- Amplitude bounds on the free wave and prescribed past source construct a
future branch on one common time interval for all histories and anchor times.
The integral in the conclusion is the physical Duhamel field. -/
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
              (timeSpaceCons p.1 p.2) := by
  let A := B + L * (L + 1) * M
  have hA : 0 ≤ A := by positivity
  obtain ⟨T, hT, hT1, hconstruct⟩ := exists_c2_signedPower_cone_trajectory hr hA
  refine ⟨T, hT, hT1, fun a ha H hH hHB F hF hFB ↦ ?_⟩
  let G : ℝ × ℝ^3 → ℝ := fun p ↦ H (a + p.1, p.2) + retardedHistory a F p
  have hG : ContDiff ℝ 2 G := (hH.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)).add
      (contDiff_two_retardedHistory hF a)
  have hGB (p : ℝ × ℝ^3) (hp : p.1 ∈ Icc 0 1) : |G p| ≤ A := by
    have hhistory := norm_retardedHistory_le ha.1 hFB hp
    have hmul : a * (a + 1) * M ≤ L * (L + 1) * M := by
      gcongr <;> linarith [ha.1, ha.2]
    exact (abs_add_le _ _).trans (add_le_add
      (hHB (a + p.1, p.2) ⟨add_nonneg ha.1 hp.1, add_le_add ha.2 hp.2⟩) (hhistory.trans hmul))
  obtain ⟨v, c, hv, hc, heq, hb, hint⟩ := hconstruct G hG hGB
  obtain ⟨hg, hh⟩ := cauchy_traces_of_quadratic_remainder (hG.of_le (by norm_num)) hT
    (hc.of_le (by norm_num)) heq
  refine ⟨v, hv, ?_, hh, hb, ?_⟩
  · intro x
    simpa only [G, add_zero] using hg x
  · intro p hp
    rw [heq p (by simpa only [abs_of_nonneg hp.1] using hp.2), hint p hp,
      oddDuhamelSolution_zero_eq_normalized _ _ hp.1]
    simp only [G, timeSpaceContinuousLinearEquiv_apply]
    rfl

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
