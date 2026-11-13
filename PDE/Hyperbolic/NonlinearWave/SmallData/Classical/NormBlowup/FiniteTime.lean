/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.MaximalBridge
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.QuadraticEvolution
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.StraussLifespan

/-!
# Finiteness of the constructed quadratic higher lifetime

An infinite higher lifetime would supply classical solutions on every
finite prefix. Their zero displacement and compact velocity of
positive integral contradict the established strict Strauss obstruction at
power two.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped ENNReal NNReal Sobolev

namespace WaveEquation.SmallData.Classical.NormBlowup

/-- The constructed H⁵ × H⁴ quadratic trajectory has finite lifetime for
zero displacement and compact velocity of positive integral.
The velocity's C² regularity follows from its H⁵ representative. -/
theorem quadraticLifespan_ne_top
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    quadraticLifespan H ≠ ∞ := by
  let h : ℝ^3 → ℝ := classicalRepresentativeCLM (by norm_num) H
  have hh : ContDiff ℝ 2 h :=
    contDiff_classicalRepresentativeCLM (by norm_num) (by norm_num) H
  have hcrit : (2 : ℝ) < 1 + Real.sqrt 2 := by
    have hsq : (1 : ℝ) < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    linarith
  obtain ⟨B, hB⟩ := bddAbove_existenceTimes_three_of_lt_strauss contDiff_const hh
    (fun _ _ ↦ rfl) hs hR (by norm_num : (1 : ℝ) < 2) hcrit (by simp) hpositive
  intro htop
  let a := max B 0 + 1
  have ha : 0 < a := by positivity
  let τ : ℝ≥0 := ⟨a, ha.le⟩
  have hlt : (τ : ℝ≥0∞) < quadraticLifespan H := by
    rw [htop]
    exact ENNReal.coe_lt_top
  obtain ⟨u, hu, _⟩ := exists_classical_prefix_maximal
    (k := 3) (by norm_num) (by norm_num) (by norm_num)
    contDiff_neg_sq (by simp) H (τ := τ) ha hlt
  have hτ : (τ : ℝ) = a := rfl
  rw [hτ] at hu
  have hu' : IsSolutionBefore (fun z ↦ -|z| ^ (2 : ℝ)) (fun _ ↦ 0) h a u := by
    simpa only [h, Real.rpow_two, sq_abs] using hu
  have hab : a ≤ B := hB ⟨u, hu'⟩
  have hBa : B < a := (le_max_left B 0).trans_lt (lt_add_one _)
  exact (not_lt_of_ge hab) hBa

/-- The finite terminal time is strictly positive by constructed local
existence, rather than by a supplied classical solution. -/
theorem quadratic_terminalTime_pos
    (H : W^{5,2}(ℝ^3)) {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → classicalRepresentativeCLM (by norm_num) H x = 0)
    (hR : 0 < R)
    (hpositive : 0 < ∫ x, classicalRepresentativeCLM (by norm_num) H x) :
    0 < (quadraticLifespan H).toReal :=
  ENNReal.toReal_pos (ne_of_gt (quadraticLifespan_pos H))
    (quadraticLifespan_ne_top H hs hR hpositive)

end WaveEquation.SmallData.Classical.NormBlowup
