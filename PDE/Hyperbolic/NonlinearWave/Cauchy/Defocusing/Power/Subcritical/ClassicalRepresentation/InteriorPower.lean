/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ClassicalRepresentation.InteriorRetarded

/-!
# Retarded representation of classical signed-power waves

Subtracting the Kirchhoff free field identifies an interior classical signed-power wave with its
nonlinear Duhamel formula.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData WaveEquation.SmallData.Classical.LocalPower
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The classical signed-power candidate obeys its nonlinear integral identity
with no second regularity at the initial face. -/
theorem eq_free_add_duhamel_of_interior_classical_power {p L : ℝ} (hp : 1 ≤ p) {u : ℝ^4 → ℝ}
    {g h : ℝ^3 → ℝ} (hu : ContDiff ℝ 1 u) (hu₂ : ContDiffOn ℝ 2 u {z | z 0 ∈ Ioo 0 L})
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x, (∂[0] u) (timeSpaceCons 0 x) = h x)
    (hwave : ∀ t ∈ Ioo 0 L, ∀ x,
      waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0)
    {t : ℝ} (ht : t ∈ Ico 0 L) (x : ℝ^3) :
    u (timeSpaceCons t x) = cauchyFreeField g h (t, x) +
      oddDuhamelSolution 0 (fun z ↦ -Real.signedPower p (u z)) (timeSpaceCons t x) := by
  rcases ht.1.eq_or_lt with rfl | hpos
  · simp only [hposition, cauchyFreeField_initial_position,
      oddDuhamelSolution_zero_eq_normalized _ _ le_rfl, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero]
  have hH := contDiff_two_kirchhoffFormula hg hh
  have hF := ((Real.contDiff_one_signedPower hp).comp hu).neg
  have he := eq_oddDuhamel_of_interior_zero_data (hu.sub (hH.of_le (by norm_num)))
    (hu₂.sub hH.contDiffOn) hF hpos ht.2 (fun s hs y ↦ ?_) (fun y ↦ ?_) (fun y ↦ ?_) x
  · exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  · have hopen : IsOpen {z : ℝ^4 | z 0 ∈ Ioo 0 L} :=
      (EuclideanSpace.proj 0).continuous.isOpen_preimage _ isOpen_Ioo
    rw [waveOperator_sub (hu₂.contDiffAt (hopen.mem_nhds
      (show timeSpaceCons s y ∈ {z | z 0 ∈ Ioo 0 L} from hs))) hH.contDiffAt,
      waveOperator_kirchhoffFormula hg hh (by simpa using hs.1), sub_zero]
    exact eq_neg_of_add_eq_zero_left (hwave s hs y)
  · simp only [hposition, kirchhoffFormula_initial_position, sub_self]
  · rw [partialDeriv_sub (hu.differentiable (by norm_num) _)
      (hH.differentiable (by norm_num) _), hinitial, partialDeriv_kirchhoffFormula_initial_velocity
        (hg.of_le (by norm_num)) (hh.of_le (by norm_num)), sub_self]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

end
