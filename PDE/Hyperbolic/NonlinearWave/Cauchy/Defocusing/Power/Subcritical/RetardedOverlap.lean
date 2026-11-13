/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedSplit
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalUniqueness
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import PDE.Analysis.Calculus.SignedPower.Deriv

/-!
# Comparing a restarted trajectory with its prescribed past

Interior time-band extension supplies a regular representative of each compact
past interval. The physical retarded splitting identity therefore applies
without a terminal trace. Bounded cone uniqueness identifies the old and new
trajectories on their common forward interval.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A C¹ trajectory on an open time band has a global C¹ representative on
any shorter closed past interval. No data at the terminal time are used. -/
theorem exists_contDiff_representative_on_initial_band {b L a : ℝ} (hb : 0 < b) {u : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L}) (ha : a < L) :
    ∃ U : ℝ × ℝ^3 → ℝ, ContDiff ℝ 1 U ∧ ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 a → U p = u p := by
  obtain ⟨U, hU, heq⟩ := hu.exists_contDiff_eventuallyEq_on_band
    (ContinuousLinearMap.fst ℝ ℝ (ℝ^3)) (s := 0) (by linarith) ha
  exact ⟨U, hU, fun p hp ↦ ((heq p hp).self_of_nhds).symm⟩

/-- Splitting the Duhamel field requires regularity only before its evaluation
time. A derivative trace at the maximal lifespan is unnecessary. -/
theorem retarded_eq_history_add_shift_of_contDiffOn {b L : ℝ} (hb : 0 < b)
    {F : ℝ × ℝ^3 → ℝ} (hF : ContDiffOn ℝ 1 F {p | -b < p.1 ∧ p.1 < L})
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hat : a + t < L) (x : ℝ^3) :
    oddDuhamelSolution 0 (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z))
      (timeSpaceCons (a + t) x) = retardedHistory a F (t, x) + oddDuhamelSolution 0
      (fun z : ℝ^4 ↦ F (a + z 0, spatialPartCLM 3 z)) (timeSpaceCons t x) := by
  obtain ⟨U, hU, heq⟩ := exists_contDiff_representative_on_initial_band hb hF hat
  have hfull := oddDuhamelSolution_congr_forward (F := U) (G := F)
    (a + t, x) (add_nonneg ha ht) (fun s hs y ↦ heq (s, y) hs)
  have hpast := retardedHistory_congr (F := U) (G := F) ha
    (fun s hs y ↦ heq (s, y) ⟨hs.1, by linarith [hs.2]⟩) (t, x)
  have hfuture := oddDuhamelSolution_congr_forward
    (F := fun q ↦ U (a + q.1, q.2)) (G := fun q ↦ F (a + q.1, q.2)) (t, x) ht
    (fun s hs y ↦ heq (a + s, y) ⟨add_nonneg ha hs.1, (by change a + s ≤ a + t; linarith [hs.2])⟩)
  calc
    _ = oddDuhamelSolution 0 (fun z : ℝ^4 ↦ U (timeSpaceContinuousLinearEquiv 3 z))
        (timeSpaceCons (a + t) x) := hfull.symm
    _ = retardedHistory a U (t, x) + oddDuhamelSolution 0
        (fun z : ℝ^4 ↦ U (a + z 0, spatialPartCLM 3 z)) (timeSpaceCons t x) :=
      oddDuhamelSolution_eq_history_add_shift hU.continuous ha ht x
    _ = _ := congrArg₂ (· + ·) hpast hfuture

/-- A translated nonlinear integral trajectory has the past contribution as
its free input. The formula concerns the physical Duhamel field. -/
theorem shift_eq_retarded_of_integral_eq {r b L a : ℝ} (hr : 1 ≤ r) (hb : 0 < b) {u H : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L})
    (heq : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = H p + oddDuhamelSolution 0 (fun z : ℝ^4 ↦
      -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons p.1 p.2))
    (ha : 0 ≤ a) {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 (L - a)) :
    u (a + p.1, p.2) = H (a + p.1, p.2) + retardedHistory a (fun q ↦ -Real.signedPower r (u q)) p +
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦ -Real.signedPower r (u (a + z 0, spatialPartCLM 3 z)))
      (timeSpaceCons p.1 p.2) := by
  have hF : ContDiffOn ℝ 1 (fun q ↦ -Real.signedPower r (u q))
      {p | -b < p.1 ∧ p.1 < L} := (Real.contDiff_one_signedPower hr).comp_contDiffOn hu |>.neg
  rw [heq (a + p.1, p.2) ⟨add_nonneg ha hp.1, by linarith [hp.2]⟩,
    retarded_eq_history_add_shift_of_contDiffOn hb hF ha hp.1 (by linarith [hp.2]) p.2, add_assoc]

/-- The constructed future branch agrees with the old bounded trajectory on
every sufficiently short overlap. The hypotheses contain integral equations,
not an assumed continuation or an endpoint derivative trace. -/
theorem eq_on_restart_overlap {r b L a T S M : ℝ} (hr : 1 ≤ r) (hb : 0 < b) (hM : 0 ≤ M)
    (ha : 0 ≤ a) (hSL : S ≤ L - a) (hST : S ≤ T) (hSa : S ≤ a + b) {u v H F : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L}) (hv : ContDiffOn ℝ 1 v {p | |p.1| < T})
    (hH : ContDiff ℝ 1 H) (hF : ContDiff ℝ 1 F)
    (hFpast : ∀ s ∈ Icc 0 a, ∀ x : ℝ^3, F (s, x) = -Real.signedPower r (u (s, x)))
    (huB : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 L → |u q| ≤ M)
    (hvB : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 T → |v q| ≤ M)
    (hue : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 L → u q = H q + oddDuhamelSolution 0 (fun z : ℝ^4 ↦
      -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons q.1 q.2))
    (hve : ∀ q : ℝ × ℝ^3, q.1 ∈ Ico 0 T → v q = H (a + q.1, q.2) + retardedHistory a F q +
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦
      -Real.signedPower r (v (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons q.1 q.2))
    {p : ℝ × ℝ^3} (hp : p.1 ∈ Ico 0 S)
    (hsmall : p.1 ^ 2 * ‖duhamelOperator‖ * ((2 * r) * (2 * M) ^ (r - 1)) < 1) :
    u (a + p.1, p.2) = v p := by
  let G : ℝ × ℝ^3 → ℝ := fun q ↦ H (a + q.1, q.2) + retardedHistory a F q
  have hG : ContDiff ℝ 1 G := (hH.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)).add
      (contDiff_one_retardedHistory hF a)
  have huS : ContinuousOn (fun q : ℝ × ℝ^3 ↦ u (a + q.1, q.2)) {q | |q.1| < S} := by
    apply hu.continuousOn.comp
      ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
    intro q hq
    have habs := abs_lt.mp (show |q.1| < S from hq)
    change -b < a + q.1 ∧ a + q.1 < L
    exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  have hvS : ContinuousOn v {q | |q.1| < S} := hv.continuousOn.mono (fun _ hq ↦ hq.trans_le hST)
  apply eq_of_bounded_signedPower_integral_eq hr hM huS hvS ⟨G, hG.continuous⟩
    (fun q hq ↦ huB (a + q.1, q.2)
      ⟨add_nonneg ha hq.1, by linarith [hq.2]⟩)
    (fun q hq ↦ hvB q ⟨hq.1, hq.2.trans_le hST⟩) hp hsmall
  · intro q hq
    have he := shift_eq_retarded_of_integral_eq hr hb hu hue ha (p := q) ⟨hq.1, hq.2.trans_le hSL⟩
    rw [← retardedHistory_congr ha hFpast q, oddDuhamelSolution_zero_eq_normalized _ _ hq.1] at he
    exact he
  · intro q hq
    have he := hve q ⟨hq.1, hq.2.trans_le hST⟩
    rwa [oddDuhamelSolution_zero_eq_normalized _ _ hq.1] at he

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
