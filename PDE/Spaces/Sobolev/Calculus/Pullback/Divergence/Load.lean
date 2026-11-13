/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.GraphOperator
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability

/-!
# The load in a weak equation under change of variables

The scalar load transforms by composition with the inverse chart and
multiplication by its absolute Jacobian determinant. On a bounded chart with
globally C¹ inverse this is a bounded operator on every finite `Lᵖ` space.
In particular, transforming a weak equation does not require a smoother load.
-/

@[expose] public noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory GraphSpace
open scoped ENNReal

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}

/-- The absolute inverse Jacobian is an essentially bounded coefficient
on a bounded chart target. -/
theorem memLp_inverseJacobian
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) :
    MemLp (fun y ↦ |(fderiv ℝ (fun z ↦ E.symm z) y).det|)
      ∞ (domainMeasure n E.target) :=
  memLp_top_on_bounded_of_continuous hTarget
    (ContinuousLinearMap.continuous_det.comp
      (hSymm.continuous_fderiv (by norm_num))).abs

/-- The inverse Jacobian as an `L∞` multiplier. -/
def inverseJacobianLp
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) : DerivLp n ∞ E.target :=
  (memLp_inverseJacobian hSymm hTarget).toLp _

/-- The multiplier represents the absolute determinant almost everywhere. -/
theorem inverseJacobianLp_apply_ae
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) :
    (inverseJacobianLp hSymm hTarget : ℝ^n → ℝ)
      =ᵐ[domainMeasure n E.target]
        fun y ↦ |(fderiv ℝ (fun z ↦ E.symm z) y).det| :=
  MemLp.coeFn_toLp _

/-- The scalar load transformation on a bounded chart. -/
def piolaLoadCLM
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) :
    DerivLp n p E.source →L[ℝ] DerivLp n p E.target :=
  (mulLpLeft (inverseJacobianLp hSymm hTarget)).comp
    (boundedPullbackCLM (E := E.symm) hSymm hE
      (isBounded_source_of_isBounded_target hSymm.continuous hTarget))

/-- The transformed load is exactly `|det D(E⁻¹)| f ∘ E⁻¹` almost everywhere. -/
theorem piolaLoadCLM_apply_ae
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (f : DerivLp n p E.source) :
    (piolaLoadCLM hE hSymm hTarget f : ℝ^n → ℝ)
      =ᵐ[domainMeasure n E.target]
        fun y ↦ |(fderiv ℝ (fun z ↦ E.symm z) y).det| * f (E.symm y) := by
  let g := boundedPullbackCLM (E := E.symm) hSymm hE
    (isBounded_source_of_isBounded_target hSymm.continuous hTarget) f
  have hg : (g : ℝ^n → ℝ) =ᵐ[domainMeasure n E.target] fun y ↦ f (E.symm y) :=
    boundedPullbackLp_apply_ae hSymm hE
      (isBounded_source_of_isBounded_target hSymm.continuous hTarget) f
  filter_upwards [mulLpLeft_apply_ae (inverseJacobianLp hSymm hTarget) g,
    inverseJacobianLp_apply_ae hSymm hTarget, hg] with y hmul hJ hg
  exact hmul.trans (congrArg₂ (· * ·) hJ hg)

end SobolevSpace.WeakChangeOfVariables
