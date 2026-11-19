/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.FiniteTrajectory
public import PDE.Hyperbolic.Models.Wave.Operator

import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.TraceOperator

/-!
# The canonical classical field of a maximal higher Sobolev wave

The maximal mild trajectory determines one spacetime field, independent
of the finite prefix used to study it. Every prefix strictly below the higher
lifespan gives interior C² regularity and the original pointwise wave equation.
-/

@[expose] public noncomputable section

open Filter PDE.Common Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open WaveEquation

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- Evaluate the displacement of the maximal higher mild trajectory in
canonical Euclidean spacetime. Only preterminal times have a solution meaning. -/
def higherSmoothMaximalField
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) (p : ℝ^(n + 1)) : ℝ :=
  classicalRepresentativeCLM hq
    (((higherLinearSemigroup n (k + 1)).maximalMildSolution
      (F := higherSmoothMap hv hs hf0)
      (locallyLipschitz_higherSmoothSource hv hs hf0) x (p 0)).1) (spatialPart p)

/-- A time slice is the canonical representative of the maximal displacement. -/
@[simp]
theorem higherSmoothMaximalField_timeSpaceCons (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) (t : ℝ) (y : ℝ^n) :
    higherSmoothMaximalField hv hq hs hf0 x (timeSpaceCons t y) =
      classicalRepresentativeCLM hq
        (((higherLinearSemigroup n (k + 1)).maximalMildSolution
          (F := higherSmoothMap hv hs hf0)
          (locallyLipschitz_higherSmoothSource hv hs hf0) x t).1) y := by
  simp only [higherSmoothMaximalField, timeSpaceCons_zero, spatialPart_timeSpaceCons]

/-- Every finite prefix below the higher lifespan gives interior joint
C² regularity of the same canonical maximal field. -/
theorem contDiffOn_two_higherSmoothMaximalField (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) <
      (higherLinearSemigroup n (k + 1)).mildLifespan (higherSmoothMap hv hs hf0) x) :
    ContDiffOn ℝ 2 (higherSmoothMaximalField hv hq hs hf0 x) {p | p 0 ∈ Ioo 0 (τ : ℝ)} := by
  have hF : LocallyLipschitz (higherSmoothMap hv hs hf0) :=
    locallyLipschitz_higherSmoothSource hv hs hf0
  obtain ⟨V, hV, heq⟩ :=
    (higherLinearSemigroup n (k + 1)).exists_mildSolutionOn_eqOn_maximalMildSolution
      (F := higherSmoothMap hv hs hf0) hF x hτ
  have hprod := contDiffOn_two_higherSmooth_trajectory (n := n) (k := k) hk hv hq hs hf0 V hV
  have hcoord : ContDiffOn ℝ 2 (timeSpaceContinuousLinearEquiv n) {p | p 0 ∈ Ioo 0 (τ : ℝ)} :=
    (timeSpaceContinuousLinearEquiv n).contDiff.contDiffOn
  have hmaps : MapsTo (timeSpaceContinuousLinearEquiv n)
      {p | p 0 ∈ Ioo 0 (τ : ℝ)} (Ioo 0 (τ : ℝ) ×ˢ univ) := by
    intro p hp
    simpa only [timeSpaceContinuousLinearEquiv_apply, time_apply, mem_prod,
      mem_univ, and_true, mem_ofPred_eq] using hp
  have hfield := hprod.comp hcoord hmaps
  simp only [Function.comp_def, timeSpaceContinuousLinearEquiv_apply, time_apply] at hfield
  exact hfield.congr fun p hp ↦ congrArg (fun z : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n) ↦
    classicalRepresentativeCLM hq z.1 (spatialPart p)) (heq ⟨hp.1.le, hp.2.le⟩).symm

/-- On each interior finite prefix, the canonical maximal field solves the
original wave equation. -/
theorem higherSmoothMaximalField_wave_equation (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < (higherLinearSemigroup n (k + 1)).mildLifespan (higherSmoothMap hv hs hf0) x)
    {t : ℝ} (ht : t ∈ Ioo 0 (τ : ℝ)) (y : ℝ^n) :
    waveOperator (higherSmoothMaximalField hv hq hs hf0 x) (timeSpaceCons t y) +
      f (higherSmoothMaximalField hv hq hs hf0 x (timeSpaceCons t y)) = 0 := by
  have hF : LocallyLipschitz (higherSmoothMap hv hs hf0) :=
    locallyLipschitz_higherSmoothSource hv hs hf0
  obtain ⟨V, hV, heq⟩ :=
    (higherLinearSemigroup n (k + 1)).exists_mildSolutionOn_eqOn_maximalMildSolution
      (F := higherSmoothMap hv hs hf0) hF x hτ
  let u := higherSmoothMaximalField hv hq hs hf0 x
  let q := fun s z ↦ classicalRepresentativeCLM hq (IccExtend τ.property V s).1 z
  have heval (s : ℝ) (hs' : s ∈ Icc 0 (τ : ℝ)) (z : ℝ^n) :
      u (timeSpaceCons s z) = q s z := by
    dsimp only [u, q]
    rw [higherSmoothMaximalField_timeSpaceCons]
    exact congrArg (fun a : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n) ↦
      classicalRepresentativeCLM hq a.1 z) (heq hs').symm
  have hu := contDiffOn_two_higherSmoothMaximalField hk hv hq hs hf0 x hτ
  have hopen : IsOpen {p : ℝ^(n + 1) | p 0 ∈ Ioo 0 (τ : ℝ)} :=
    isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous
  have hat : ContDiffAt ℝ 2 u (timeSpaceCons t y) := (hu _ ht).contDiffAt (hopen.mem_nhds ht)
  have htime : (fun s ↦ u (timeSpaceCons s y)) =ᶠ[𝓝 t] (fun s ↦ q s y) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs' using heval s ⟨hs'.1.le, hs'.2.le⟩ y
  have hspace : (fun z ↦ u (timeSpaceCons t z)) = q t := funext fun z ↦ heval t ⟨ht.1.le, ht.2.le⟩ z
  change waveOperator u (timeSpaceCons t y) + f (u (timeSpaceCons t y)) = 0
  rw [waveOperator_timeSpaceCons_of_contDiffAt hat, htime.deriv.deriv_eq,
    hspace, heval t ⟨ht.1.le, ht.2.le⟩ y]
  exact higherSmooth_trajectory_wave_equation hk hv hq hs hf0 V hV ht y

end PDE.Hyperbolic.NonlinearWave.Cauchy
