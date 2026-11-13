/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalTrajectory
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedHistory
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Formula

/-!
# Constructing a future branch from a prescribed retarded history

A bounded C¹ past source gives a future signed-power integral trajectory on a
uniform interval. The interval depends on amplitude and elapsed-time bounds,
not bounds on derivatives of the history. The future branch has the same
initial position and velocity as the free field with that history included.

This constructs the future branch.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A C¹ remainder multiplied by time squared leaves both initial traces of
an arbitrary C¹ free field unchanged. -/
theorem cauchy_traces_of_quadratic_remainder {H v c : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H) {T : ℝ}
    (hT : 0 < T) (hc : ContDiffOn ℝ 1 c {p | |p.1| < T})
    (heq : ∀ p : ℝ × ℝ^3, |p.1| < T → v p = H p + p.1 ^ 2 * c p) :
    (∀ x : ℝ^3, v (0, x) = H (0, x)) ∧ ∀ x : ℝ^3,
      HasDerivAt (fun t ↦ v (t, x)) (deriv (fun t ↦ H (t, x)) 0) 0 := by
  constructor
  · intro x
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero]
      using heq (0, x) (by simpa using hT)
  · intro x
    have hnear : {p : ℝ × ℝ^3 | |p.1| < T} ∈ 𝓝 (0, x) :=
      (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (by simpa using hT)
    have hcc : ContDiffAt ℝ 1 (fun t : ℝ ↦ c (t, x)) 0 :=
      (hc.contDiffAt hnear).comp 0 (contDiffAt_id.prodMk contDiffAt_const)
    have hfree : ContDiff ℝ 1 (fun t : ℝ ↦ H (t, x)) := hH.comp (contDiff_id.prodMk contDiff_const)
    have hd := (hfree.differentiable one_ne_zero 0).hasDerivAt.fun_add
      (((hasDerivAt_id (0 : ℝ)).fun_pow 2).fun_mul (hcc.differentiableAt one_ne_zero).hasDerivAt)
    have htrace : HasDerivAt (fun t : ℝ ↦ H (t, x) + t ^ 2 * c (t, x))
        (deriv (fun t ↦ H (t, x)) 0) 0 := by simpa using hd
    apply htrace.congr_of_eventuallyEq
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hnear]
      with t ht using heq (t, x) ht

/-- Amplitude bounds on the free wave and prescribed past source construct a
future branch on one common time interval for all histories and anchor times.
The integral in the conclusion is the physical Duhamel field. -/
theorem exists_signedPower_future_of_bounded_history {r : ℝ} (hr : 1 ≤ r)
    {B M L : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ ∀ a ∈ Icc 0 L,
      ∀ H : ℝ × ℝ^3 → ℝ, ContDiff ℝ 1 H →
        (∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 (L + 1) → |H p| ≤ B) →
      ∀ F : ℝ × ℝ^3 → ℝ, ContDiff ℝ 1 F →
        (∀ s ∈ Icc 0 a, ∀ x : ℝ^3, |F (s, x)| ≤ M) →
      ∃ v : ℝ × ℝ^3 → ℝ,
        ContDiffOn ℝ 1 v {p | |p.1| < T} ∧
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
  obtain ⟨T, hT, hT1, hconstruct⟩ := exists_signedPower_cone_trajectory hr hA
  refine ⟨T, hT, hT1, fun a ha H hH hHB F hF hFB ↦ ?_⟩
  let G : ℝ × ℝ^3 → ℝ := fun p ↦ H (a + p.1, p.2) + retardedHistory a F p
  have hG : ContDiff ℝ 1 G := (hH.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)).add
      (contDiff_one_retardedHistory hF a)
  have hGB (p : ℝ × ℝ^3) (hp : p.1 ∈ Icc 0 1) : |G p| ≤ A := by
    have hhistory := norm_retardedHistory_le ha.1 hFB hp
    have hmul : a * (a + 1) * M ≤ L * (L + 1) * M := by
      gcongr <;> linarith [ha.1, ha.2]
    exact (abs_add_le _ _).trans (add_le_add
      (hHB (a + p.1, p.2) ⟨add_nonneg ha.1 hp.1, add_le_add ha.2 hp.2⟩) (hhistory.trans hmul))
  obtain ⟨v, c, hv, hc, heq, hb, hint⟩ := hconstruct G hG hGB
  obtain ⟨hg, hh⟩ := cauchy_traces_of_quadratic_remainder hG hT hc heq
  refine ⟨v, hv, ?_, hh, hb, ?_⟩
  · intro x
    simpa only [G, add_zero] using hg x
  · intro p hp
    rw [heq p (by simpa only [abs_of_nonneg hp.1] using hp.2), hint p hp,
      oddDuhamelSolution_zero_eq_normalized _ _ hp.1]
    simp only [G, timeSpaceContinuousLinearEquiv_apply]
    rfl

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
