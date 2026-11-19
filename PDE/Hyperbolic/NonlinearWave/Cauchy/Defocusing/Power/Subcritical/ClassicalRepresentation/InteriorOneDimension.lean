/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.LocalExtension.TimeBand
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.ClassicalSolution
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ClassicalRepresentation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiniteForwardUniqueness
public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.SphericalReduction

/-!
# One-dimensional forced representation with initial traces

A field with continuous second derivatives at positive time and continuous first derivatives at
the initial face agrees with the zero-data forced representation.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Forward one-dimensional uniqueness represents an interior C² wave using
only C¹ regularity at its initial face. -/
theorem eq_dAlembertDuhamel_of_interior_zero_data {v f : ℝ^2 → ℝ} {L : ℝ} (hv : ContDiff ℝ 1 v)
    (hv₂ : ContDiffOn ℝ 2 v {z | z 0 ∈ Ioo 0 L}) (hf : ContDiff ℝ 1 f)
    (hwave : ∀ t ∈ Ioo 0 L, ∀ x : ℝ^1, waveOperator v (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hzero : ∀ x : ℝ^1, v (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^1, (∂[0] v) (timeSpaceCons 0 x) = 0) {t : ℝ} (ht : t ∈ Ico 0 L) (x : ℝ^1) :
    v (timeSpaceCons t x) = dAlembertDuhamelSolution f (timeSpaceCons t x) := by
  have hd := contDiff_two_dAlembertDuhamelSolution hf.contDiffOn
  have h₁ : ContDiff ℝ 1 (v - dAlembertDuhamelSolution f) :=
    hv.sub (hd.of_le (by norm_num))
  have he := eq_on_finite_forward_strip (f := fun _ ↦ (0 : ℝ))
    (u := v - dAlembertDuhamelSolution f) (v := fun _ ↦ (0 : ℝ))
    (T := L) (LipschitzWith.const (0 : ℝ)).locallyLipschitz
    (hv₂.sub hd.contDiffOn) contDiffOn_const h₁.contDiffOn contDiffOn_const
    (fun s hs y ↦ ?_) (fun _ _ _ ↦ by simp [waveOperator])
    (fun y ↦ by simp [hzero, dAlembertDuhamelSolution_initial]) (fun y ↦ ?_) t ht x
  · exact sub_eq_zero.mp he
  · have hopen : IsOpen {z : ℝ^2 | z 0 ∈ Ioo 0 L} :=
      (EuclideanSpace.proj 0).continuous.isOpen_preimage _ isOpen_Ioo
    change waveOperator (fun z ↦ v z - dAlembertDuhamelSolution f z) _ + 0 = 0
    rw [waveOperator_sub (hv₂.contDiffAt (hopen.mem_nhds
      (show timeSpaceCons s y ∈ {z | z 0 ∈ Ioo 0 L} from hs))) hd.contDiffAt,
      hwave s hs y, waveOperator_dAlembertDuhamelSolution hf.contDiffOn
        (by simpa using hs.1.le), sub_self, add_zero]
  · have ht' := (hasDerivAt_timeSpaceCons _ 0 y
      (h₁.differentiable (by norm_num) _)).hasDerivWithinAt (s := Ici 0)
    rw [ht'.derivWithin (uniqueDiffWithinAt_Ici 0)]
    change (∂[0] (fun z ↦ v z - dAlembertDuhamelSolution f z)) (timeSpaceCons 0 y) = _
    simp only [derivWithin_fun_const, Pi.zero_apply]
    rw [partialDeriv_sub (hv.differentiable (by norm_num) _)
        (hd.differentiable (by norm_num) _), hinitial,
      partialDeriv_dAlembertDuhamelSolution_initial hf.contDiffOn, sub_self]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

end
