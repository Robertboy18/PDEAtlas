/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.MixedConvection
public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.Derivative

/-!
# Scaling of the convection under dilations

For `(δ_a u)(x) = u(a x)` the chain rule gives `((δ_a U)·∇)(δ_a V) = a δ_a ((U·∇) V)`: the
transport is homogeneous of degree one in the dilation factor
(`mixedConvection_vectorDilation`).
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped BigOperators Sobolev

namespace NavierStokes.SobolevConvection

set_option linter.missingDocs true

variable {m : ℕ}

/-- **Scaling of the transport.** `((δ_a U)·∇)(δ_a V) = a δ_a ((U·∇) V)`. -/
theorem mixedConvection_vectorDilation (hm : (3 : ℝ) < 2 * m) (a : ℝ) (ha : a ≠ 0)
    (U : VectorH 3 m) (V : VectorH 3 (m + 1)) :
    mixedConvection m hm (vectorDilation 3 m a ha U) (vectorDilation 3 (m + 1) a ha V) =
      a • vectorDilation 3 m a ha (mixedConvection m hm U V) := by
  refine PiLp.ext fun j ↦ WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  simp only [domainMeasure, Measure.restrict_univ]
  rw [PiLp.smul_apply, vectorDilation_apply]
  have hsmul := baseRepresentative_smul_ae a
    (dilationWkpCLM (by norm_num) a ha (mixedConvection m hm U V j))
  have hdil := dilationWkpCLM_base_ae (by norm_num) a ha (mixedConvection m hm U V j)
  simp only [domainMeasure, Measure.restrict_univ] at hsmul hdil
  have hcomp := (Measure.quasiMeasurePreserving_smul volume ha).ae_eq_comp
    (mixedConvection_base_ae hm U V j)
  have hdU : ∀ i : Fin 3, baseRepresentative (vectorDilation 3 m a ha U i) =ᵐ[volume]
      fun x ↦ baseRepresentative (U i) (a • x) := fun i ↦ by
    have h := dilationWkpCLM_base_ae (by norm_num) a ha (U i)
    simp only [domainMeasure, Measure.restrict_univ] at h
    rw [vectorDilation_apply]
    exact h
  have hdV : ∀ i : Fin 3, baseRepresentative (partialDerivCLM (k := m) i
      (vectorDilation 3 (m + 1) a ha V j)) =ᵐ[volume]
      fun x ↦ a * baseRepresentative (partialDerivCLM (k := m) i (V j)) (a • x) := fun i ↦ by
    rw [vectorDilation_apply, partialDerivCLM_dilationWkpCLM]
    have h₁ := baseRepresentative_smul_ae a
      (dilationWkpCLM (by norm_num) a ha (partialDerivCLM (k := m) i (V j)))
    have h₂ := dilationWkpCLM_base_ae (by norm_num) a ha (partialDerivCLM (k := m) i (V j))
    simp only [domainMeasure, Measure.restrict_univ] at h₁ h₂
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    rw [hx₁, hx₂, smul_eq_mul]
  filter_upwards [mixedConvection_base_ae hm (vectorDilation 3 m a ha U)
      (vectorDilation 3 (m + 1) a ha V) j, hsmul, hdil, hcomp, ae_all_iff.mpr hdU,
    ae_all_iff.mpr hdV] with x h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, h₃]
  simp only [Function.comp_apply] at h₄
  rw [h₄, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h₅ i, h₆ i]
  ring

end NavierStokes.SobolevConvection
