/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.IntegralAgreement
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Persistence

/-!
# Finite classical regularity on the whole bounded integral lifespan

For exponents above two, an arbitrary bounded C¹ integral trajectory agrees
on its entire finite forward interval with a field jointly C² across time
zero. The free field needs only C² regularity and an amplitude bound. The initial C² germ is
constructed and then propagated by retarded continuation and uniqueness.
-/

@[expose] public noncomputable section

open Set Filter PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- The original bounded C¹ integral trajectory for a real exponent above
two is C² throughout its finite positive-time interval and admits a C²
representative across the initial face. -/
theorem exists_c2_extension_of_bounded_signedPower_integral_eq {r b L B M : ℝ} (hr : 2 < r)
    (hb : 0 < b) (hL : 0 < L) {u H : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L}) (hH : ContDiff ℝ 2 H)
    (hHB : ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 (L + 1) → |H p| ≤ B)
    (huB : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → |u p| ≤ M)
    (hue : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = H p + oddDuhamelSolution 0 (fun z : ℝ^4 ↦
      -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons p.1 p.2)) :
    (∃ w : ℝ × ℝ^3 → ℝ, ContDiffOn ℝ 2 w {p | -1 < p.1 ∧ p.1 < L} ∧ ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L →
      w p = u p) ∧ ContDiffOn ℝ 2 u {p | 0 < p.1 ∧ p.1 < L} := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hHB ((0 : ℝ), (0 : ℝ^3)) ⟨le_rfl, by linarith⟩)
  have hM : 0 ≤ M := (abs_nonneg _).trans (huB ((0 : ℝ), (0 : ℝ^3)) ⟨le_rfl, hL⟩)
  obtain ⟨S, hS, hSL, V, hV, hVeq, _⟩ :=
    exists_c2_representative_of_bounded_integral_eq hr hb hL hB hM hH
      (fun p hp ↦ hHB p ⟨hp.1, hp.2.trans (by linarith)⟩) hu.continuousOn huB hue
  let w : ℝ × ℝ^3 → ℝ := fun p ↦ if p.1 < S / 2 then V p else u p
  have hwu (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 L) : w p = u p := by
    dsimp only [w]
    split_ifs with hpS
    · exact hVeq p ⟨hp.1, by linarith⟩
    · rfl
  have hwV (p : ℝ × ℝ^3) (hp : p.1 < S / 2) : w p = V p := ite_eq_left hp
  have hw : ContDiffOn ℝ 1 w {p | -1 < p.1 ∧ p.1 < L} := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    by_cases hpS : p.1 < S / 2
    · apply ((hV.of_le (by norm_num)).contDiffAt).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hpS]
        with q hq using hwV q hq
    · have hp0 : 0 < p.1 := by linarith
      apply (hu.contDiffAt (((isOpen_lt continuous_const continuous_fst).inter
          (isOpen_lt continuous_fst continuous_const)).mem_nhds
            ⟨show -b < p.1 by linarith, hp.2⟩)).congr_of_eventuallyEq
      filter_upwards [((isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_fst continuous_const)).mem_nhds ⟨hp0, hp.2⟩]
        with q hq using hwu q ⟨hq.1.le, hq.2⟩
  have hw₂ : ContDiffOn ℝ 2 w {p | -1 < p.1 ∧ p.1 < S / 2} :=
    hV.contDiffOn.congr fun p hp ↦ hwV p hp.2
  have hwe (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 L) : w p = H p + oddDuhamelSolution 0
        (fun z : ℝ^4 ↦ -Real.signedPower r (w (timeSpaceContinuousLinearEquiv 3 z)))
        (timeSpaceCons p.1 p.2) := by
    rw [hwu p hp, hue p hp]
    congr 1
    apply oddDuhamelSolution_congr_forward (F := fun q ↦ -Real.signedPower r (u q))
      (G := fun q ↦ -Real.signedPower r (w q)) p hp.1
    intro s hs x
    rw [hwu (s, x) ⟨hs.1, hs.2.trans_lt hp.2⟩]
  have hwfull : ContDiffOn ℝ 2 w {p | -1 < p.1 ∧ p.1 < L} :=
    contDiffOn_two_of_initial_signedPower_integral_eq hr (by norm_num)
      (by positivity : 0 < S / 2) hw hw₂ hH hHB
      (fun p hp ↦ by rw [hwu p hp]; exact huB p hp) hwe
  refine ⟨⟨w, hwfull, hwu⟩, ?_⟩
  refine (hwfull.mono (fun p hp ↦ ⟨by linarith [hp.1], hp.2⟩)).congr fun p hp ↦ ?_
  exact (hwu p ⟨hp.1.le, hp.2⟩).symm

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
