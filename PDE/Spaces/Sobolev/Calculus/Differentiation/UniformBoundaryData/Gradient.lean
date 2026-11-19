/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure
public import PDE.FDeriv.Operators
public import PDE.Analysis.Calculus.UniformClosure

/-!
# The continuous closure gradient of classical data

Uniform continuity completes each first partial derivative to the closure.
The ambient continuation is auxiliary: every continuous continuation agrees
on the closure. In particular this gradient agrees there with the gradient
of any ambient C¹ representative of the original scalar field.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace SobolevSpace.ContDiffUpToBoundary

open Set

variable {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ^n → ℝ}

/-- A continuous ambient continuation of the gradient, obtained by completion
of the uniformly continuous partial derivatives. Its values on the closure
are independent of the auxiliary continuations. -/
def completedGradient (hu : ContDiffUpToBoundary 1 u Ω) : ℝ^n → ℝ^n :=
  fun x ↦ WithLp.toLp 2 fun i ↦
    Classical.choose ((hu.uniformContinuousOn [i] (by simp)).exists_continuous_eqOn) x

/-- The completed gradient is continuous on the ambient space. -/
theorem continuous_completedGradient (hu : ContDiffUpToBoundary 1 u Ω) :
    Continuous hu.completedGradient := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp
  exact continuous_pi fun i ↦
    (Classical.choose_spec
      ((hu.uniformContinuousOn [i] (by simp)).exists_continuous_eqOn)).1

/-- In the open domain the completion is the gradient. -/
theorem completedGradient_eq_gradient (hu : ContDiffUpToBoundary 1 u Ω) :
    EqOn hu.completedGradient (∇ u) Ω := by
  intro x hx
  ext i
  rw [PDE.gradient_apply_eq_partialDeriv]
  exact (Classical.choose_spec
    ((hu.uniformContinuousOn [i] (by simp)).exists_continuous_eqOn)).2 hx

/-- The continuous extension of the gradient is unique on the closure. -/
theorem completedGradient_eqOn (hu : ContDiffUpToBoundary 1 u Ω)
    {G : ℝ^n → ℝ^n} (hG : ContinuousOn G (closure Ω))
    (heq : EqOn G (∇ u) Ω) :
    EqOn hu.completedGradient G (closure Ω) :=
  (hu.completedGradient_eq_gradient.trans heq.symm).of_subset_closure
    hu.continuous_completedGradient.continuousOn hG subset_closure Subset.rfl

/-- Any ambient C¹ representative has the completed gradient on the closure. -/
theorem completedGradient_eq_gradient_extension (hu : ContDiffUpToBoundary 1 u Ω)
    (hopen : IsOpen Ω) {U : ℝ^n → ℝ} (hU : ContDiff ℝ 1 U)
    (heq : EqOn U u Ω) :
    EqOn hu.completedGradient (∇ U) (closure Ω) := by
  apply hu.completedGradient_eqOn
  · exact ((InnerProductSpace.toDual ℝ (ℝ^n)).symm.continuous.comp
      (hU.continuous_fderiv one_ne_zero)).continuousOn
  · intro x hx
    exact (heq.eventuallyEq_of_mem (hopen.mem_nhds hx)).gradient_eq

/-- Completing the first derivatives of C² closure data preserves their
raw first-order closure regularity. -/
theorem contDiffUpToBoundary_completedGradient (hu : ContDiffUpToBoundary 2 u Ω)
    (hopen : IsOpen Ω) (i : Fin n) :
    ContDiffUpToBoundary 1 (fun x ↦ (hu.of_le (by omega)).completedGradient x i) Ω := by
  apply (hu.partialDeriv_of_succ hopen i).congr hopen
  intro x hx
  exact (congrArg (fun z : ℝ^n ↦ z i)
    ((hu.of_le (show 1 ≤ 2 by omega)).completedGradient_eq_gradient hx)).trans
      (PDE.gradient_apply_eq_partialDeriv u x i)

end SobolevSpace.ContDiffUpToBoundary
