/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Compatibility
public import PDE.Hyperbolic.Models.Wave.Equation
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.ClassicalSolution
import CAS.ExactTactic

/-!
# Classical regularity of the nonlinear strip solution

The first Duhamel insertion is C¹ for continuous forcing. Composing it with a C¹
reaction supplies C¹ forcing for the second insertion, which is C². Causality
identifies both insertions with the original integral solution on the closed strip.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set Filter Function
open scoped Topology BoundedContinuousFunction

namespace WaveEquation

/-- On the time strip the clipping projection reconstructs the original spacetime point. -/
theorem stripInclusion_stripProjection_of_mem {T : NNReal} {p : ℝ^2}
    (hp : p 0 ∈ Icc (0 : ℝ) (T : ℝ)) : stripInclusion (stripProjection T p) = p := by
  have ht : (projIcc (0 : ℝ) T T.coe_nonneg (p 0) : ℝ) = p 0 :=
    congrArg Subtype.val (projIcc_of_mem T.coe_nonneg hp)
  ext i
  fin_cases i <;> simp [stripInclusion, stripProjection, timeSpaceCons, ht]

/-- Reinsert the continuous strip solution into the Duhamel representation.
The first smoothing theorem gives this extension one spacetime derivative. -/
def firstStripExtension {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (T : NNReal) (p : ℝ^2) : ℝ :=
  dAlembertFormula g h (p 1) (p 0) -
    dAlembertDuhamelSolution
      (fun q ↦ f (nonlinearStripSolution hf g h T (stripProjection T q))) p

/-- The first extension agrees with the selected integral solution. -/
theorem firstStripExtension_stripInclusion {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (g h : ℝ →ᵇ ℝ) (T : NNReal) (p : ForwardStrip T) :
    firstStripExtension hf g h T (stripInclusion p) = nonlinearStripSolution hf g h T p := by
  simpa [firstStripExtension, stripInclusion, timeSpaceCons] using
    (nonlinearStripSolution_satisfies_integralEquation hf g h T p).symm

/-- The first extension reads the same strip value throughout the forward slab. -/
theorem firstStripExtension_eq_on_strip {L T : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (g h : ℝ →ᵇ ℝ) {p : ℝ^2} (hp : p 0 ∈ Icc (0 : ℝ) (T : ℝ)) :
    firstStripExtension hf g h T p = nonlinearStripSolution hf g h T (stripProjection T p) := by
  have he := firstStripExtension_stripInclusion hf g h T (stripProjection T p)
  rwa [stripInclusion_stripProjection_of_mem hp] at he

/-- Continuous forcing gives the first extension joint `C¹` regularity. -/
theorem contDiff_one_firstStripExtension {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (T : NNReal) :
    ContDiff ℝ 1 (firstStripExtension hf g h T) :=
  ((contDiff_two_dAlembertFormula g h hg hh).of_le (by norm_num)).sub
    (contDiff_one_dAlembertDuhamelSolution
      (hf.continuous.comp ((nonlinearStripSolution hf g h T).continuous.comp
        (continuous_stripProjection T))))

/-- A second insertion uses the `C¹` first extension as forcing and gains a second derivative. -/
def classicalStripExtension {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (T : NNReal) (p : ℝ^2) : ℝ :=
  dAlembertFormula g h (p 1) (p 0) -
    dAlembertDuhamelSolution (fun q ↦ f (firstStripExtension hf g h T q)) p

/-- The second extension is jointly `C²`, including across the initial slice. -/
theorem contDiff_two_classicalStripExtension {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (T : NNReal) :
    ContDiff ℝ 2 (classicalStripExtension hf g h T) :=
  (contDiff_two_dAlembertFormula g h hg hh).sub (contDiff_two_dAlembertDuhamelSolution
      ((hf₁.comp (contDiff_one_firstStripExtension hf hg hh T)).contDiffOn))

/-- Causality makes the two extensions agree on the full closed forward slab. -/
theorem classicalStripExtension_eq_firstStripExtension {L T : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) {p : ℝ^2} (hp : p 0 ∈ Icc (0 : ℝ) (T : ℝ)) :
    classicalStripExtension hf g h T p = firstStripExtension hf g h T p := by
  unfold classicalStripExtension firstStripExtension
  congr 1
  refine dAlembertDuhamelSolution_eq_of_eqOn_past hp.1 fun s hs x ↦ ?_
  congr 1
  exact firstStripExtension_eq_on_strip hf g h
    (by simpa only [timeSpaceCons_zero, mem_Icc] using And.intro hs.1 (hs.2.trans hp.2))

/-- The smooth extension is the fixed-point solution on its strip. -/
theorem classicalStripExtension_eq_on_strip {L T : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (g h : ℝ →ᵇ ℝ) {p : ℝ^2} (hp : p 0 ∈ Icc (0 : ℝ) (T : ℝ)) :
    classicalStripExtension hf g h T p = nonlinearStripSolution hf g h T (stripProjection T p) :=
  (classicalStripExtension_eq_firstStripExtension hf g h hp).trans
    (firstStripExtension_eq_on_strip hf g h hp)

/-- The nonlinear PDE holds throughout the forward slab, also at time zero. -/
theorem waveOperator_classicalStripExtension {L T : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) {p : ℝ^2}
    (hp : p 0 ∈ Icc (0 : ℝ) (T : ℝ)) :
    waveOperator (n := 1) (classicalStripExtension hf g h T) p =
      -f (classicalStripExtension hf g h T p) := by
  have hF : ContDiff ℝ 1 (fun q ↦ f (firstStripExtension hf g h T q)) :=
    hf₁.comp (contDiff_one_firstStripExtension hf hg hh T)
  have hzero : waveOperator (n := 1) (fun p : ℝ^2 ↦ dAlembertFormula g h (p 1) (p 0)) p = 0 :=
    waveOperator_dAlembertFormula g h hg hh p
  unfold classicalStripExtension
  rw [waveOperator_sub (contDiff_two_dAlembertFormula g h hg hh).contDiffAt
    (contDiff_two_dAlembertDuhamelSolution hF.contDiffOn).contDiffAt, hzero,
    waveOperator_dAlembertDuhamelSolution hF.contDiffOn hp.1, zero_sub]
  exact congrArg (fun y ↦ -f y) (classicalStripExtension_eq_firstStripExtension hf g h hp).symm

/-- The smooth extension attains the prescribed displacement. -/
theorem classicalStripExtension_initial_position {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (g h : ℝ →ᵇ ℝ) (T : NNReal) (x : ℝ^1) :
    classicalStripExtension hf g h T (timeSpaceCons 0 x) = g (x 0) := by
  simp only [classicalStripExtension, dAlembertDuhamelSolution_initial, sub_zero]
  suffices (1 / 2 : ℝ) * (g (x 0) + g (x 0)) = g (x 0) by
    simpa [timeSpaceCons, dAlembertFormula] using this
  cas

/-- The second insertion has zero initial first jet, so the prescribed velocity is retained. -/
theorem classicalStripExtension_initial_velocity {L : NNReal} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (T : NNReal)
    (x : ℝ^1) :
    (∂[0] (classicalStripExtension hf g h T)) (timeSpaceCons 0 x) = h (x 0) := by
  have hF : ContDiff ℝ 1 (fun q ↦ f (firstStripExtension hf g h T q)) :=
    hf₁.comp (contDiff_one_firstStripExtension hf hg hh T)
  unfold classicalStripExtension
  rw [PDE.partialDeriv_sub
    ((contDiff_two_dAlembertFormula g h hg hh).differentiable (by norm_num) _)
    ((contDiff_two_dAlembertDuhamelSolution hF.contDiffOn).differentiable (by norm_num) _),
    partialDeriv_dAlembert_time g h hg hh,
    partialDeriv_dAlembertDuhamelSolution_initial hF.contDiffOn]
  simp only [one_div, Fin.isValue, timeSpaceCons_zero,
    add_zero, sub_zero, sub_self, mul_zero, zero_add]
  cas

end WaveEquation
