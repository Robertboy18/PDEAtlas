/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.Sobolev
public import PDE.Spaces.Sobolev.Evolution.VectorL2Triple
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivativeCoordinates

/-!
# Convection at every Sobolev order in three dimensions

For `m ≥ 2` the space `Hᵐ(ℝ³)` is an algebra, so the unprojected transport `(U · ∇) V` is a
bounded bilinear map `mixedConvection m` from vector `Hᵐ × Hᵐ⁺¹` to vector `Hᵐ`. Freezing the
coefficient `U` gives the bounded operator
`V ↦ (U · ∇) V`, which loses one derivative; this is the form in which the convection term of
a nonlinear equation enters a linear smoothing argument, with the coefficient taken from the
regularity already known.

The operators of successive orders agree once the top order is forgotten
(`vectorLower_mixedConvection`), and at the lowest order with a coefficient in `H³` the operator
is the convection `NavierStokes.SobolevConvection.convection` from `H³ × H³` to `H²`
(`convection_eq_mixedConvection`).
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped BigOperators Sobolev

namespace NavierStokes.SobolevConvection

set_option linter.missingDocs true

variable {m : ℕ}

/-- A whole-space Sobolev function is determined by its base representative. -/
private theorem ext_of_baseRepresentative_ae {U V : W^{m,2}(ℝ^3)}
    (h : baseRepresentative U =ᵐ[volume] baseRepresentative V) : U = V :=
  WkpSpaceOn.ext_of_base_ae isOpen_univ U V (by
    simp only [domainMeasure, Measure.restrict_univ]
    exact h)

/-- One component `∑ᵢ Uᵢ ∂ᵢ Vⱼ` of the transport with `U ∈ Hᵐ` and `V ∈ Hᵐ⁺¹`, for `3 < 2m`. -/
def mixedScalarConvection (m : ℕ) (hm : (3 : ℝ) < 2 * m) (j : Fin 3) :
    VectorH 3 m →L[ℝ] VectorH 3 (m + 1) →L[ℝ] W^{m,2}(ℝ^3) :=
  ∑ i : Fin 3, (multiplication hm).bilinearComp (PiLp.proj 2 _ i)
    ((partialDerivCLM (k := m) i).comp (PiLp.proj 2 _ j))

/-- The scalar component is the sum of the coefficient times the weak partial derivative. -/
theorem mixedScalarConvection_apply (hm : (3 : ℝ) < 2 * m) (j : Fin 3) (U : VectorH 3 m)
    (V : VectorH 3 (m + 1)) :
    mixedScalarConvection m hm j U V =
      ∑ i : Fin 3, multiplication hm (U i) (partialDerivCLM (k := m) i (V j)) := by
  simp only [mixedScalarConvection, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply]

/-- The scalar component is `∑ᵢ Uᵢ ∂ᵢ Vⱼ` almost everywhere, with base representatives. -/
theorem mixedScalarConvection_base_ae (hm : (3 : ℝ) < 2 * m) (j : Fin 3) (U : VectorH 3 m)
    (V : VectorH 3 (m + 1)) :
    baseRepresentative (mixedScalarConvection m hm j U V) =ᵐ[volume]
      fun x ↦ ∑ i : Fin 3, baseRepresentative (U i) x *
        baseRepresentative (partialDerivCLM (k := m) i (V j)) x := by
  rw [mixedScalarConvection_apply]
  have hs := baseRepresentative_sum_ae (fun i : Fin 3 ↦
    multiplication hm (U i) (partialDerivCLM (k := m) i (V j)))
  simp only [domainMeasure, Measure.restrict_univ] at hs
  filter_upwards [hs, ae_all_iff.mpr (fun i : Fin 3 ↦
    multiplication_ae hm (U i) (partialDerivCLM (k := m) i (V j)))] with x hsum hprod
  rw [hsum]
  exact Finset.sum_congr rfl fun i _ ↦ hprod i

/-- The transport `(U · ∇) V` from vector `Hᵐ × Hᵐ⁺¹` to vector `Hᵐ`, for `3 < 2m`. -/
def mixedConvection (m : ℕ) (hm : (3 : ℝ) < 2 * m) :
    VectorH 3 m →L[ℝ] VectorH 3 (m + 1) →L[ℝ] VectorH 3 m :=
  let J := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 3 ↦ W^{m,2}(ℝ^3))).symm.toContinuousLinearMap
  ∑ j : Fin 3, (ContinuousLinearMap.compL ℝ (VectorH 3 (m + 1)) (W^{m,2}(ℝ^3)) (VectorH 3 m)
    (J.comp (ContinuousLinearMap.single ℝ (fun _ : Fin 3 ↦ W^{m,2}(ℝ^3)) j))).comp
      (mixedScalarConvection m hm j)

/-- The components of the transport are the scalar components. -/
@[simp]
theorem mixedConvection_apply (hm : (3 : ℝ) < 2 * m) (U : VectorH 3 m) (V : VectorH 3 (m + 1))
    (j : Fin 3) : mixedConvection m hm U V j = mixedScalarConvection m hm j U V := by
  simp [mixedConvection, ContinuousLinearMap.compL_apply]

/-- The components of the transport are `∑ᵢ Uᵢ ∂ᵢ Vⱼ` almost everywhere. -/
theorem mixedConvection_base_ae (hm : (3 : ℝ) < 2 * m) (U : VectorH 3 m)
    (V : VectorH 3 (m + 1)) (j : Fin 3) :
    baseRepresentative (mixedConvection m hm U V j) =ᵐ[volume]
      fun x ↦ ∑ i : Fin 3, baseRepresentative (U i) x *
        baseRepresentative (partialDerivCLM (k := m) i (V j)) x := by
  rw [mixedConvection_apply]
  exact mixedScalarConvection_base_ae hm j U V

/-- The bound `‖(U · ∇) V‖ ≤ ‖mixedConvection m hm‖ ‖U‖ ‖V‖`. -/
theorem norm_mixedConvection_le (hm : (3 : ℝ) < 2 * m) (U : VectorH 3 m)
    (V : VectorH 3 (m + 1)) :
    ‖mixedConvection m hm U V‖ ≤ ‖mixedConvection m hm‖ * ‖U‖ * ‖V‖ :=
  (mixedConvection m hm).le_opNorm₂ U V

/-- Forgetting the top order of the transport of order `m + 1` gives the transport of order `m`
of the fields with their top orders forgotten. -/
theorem vectorLower_mixedConvection (hm : (3 : ℝ) < 2 * m) (hm' : (3 : ℝ) < 2 * (m + 1 : ℕ))
    (U : VectorH 3 (m + 1)) (V : VectorH 3 (m + 2)) :
    vectorLower 3 m (mixedConvection (m + 1) hm' U V) =
      mixedConvection m hm (vectorLower 3 m U) (vectorLower 3 (m + 1) V) := by
  refine PiLp.ext fun j ↦ ext_of_baseRepresentative_ae ?_
  rw [vectorLower_apply, baseRepresentative_lowerOrderCLM]
  filter_upwards [mixedConvection_base_ae hm' U V j,
    mixedConvection_base_ae hm (vectorLower 3 m U) (vectorLower 3 (m + 1) V) j]
    with x h₁ h₂
  rw [h₁, h₂]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [vectorLower_apply, vectorLower_apply, baseRepresentative_lowerOrderCLM,
    ← lowerOrderCLM_partialDerivCLM (Nat.le_succ m), baseRepresentative_lowerOrderCLM]

/-- At the lowest order with a coefficient in `H³`, the transport is the convection from
`H³ × H³` to `H²`. -/
theorem convection_eq_mixedConvection (hm : (3 : ℝ) < 2 * (2 : ℕ)) (U V : VectorH 3 3) :
    convection U V = mixedConvection 2 hm (vectorLower 3 2 U) V := by
  refine PiLp.ext fun j ↦ ?_
  rw [convection_apply, mixedConvection_apply, scalarConvection_apply,
    mixedScalarConvection_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [vectorLower_apply]

/-- A coefficient path continuous on a set gives a family `(s, v) ↦ (U s · ∇) v` that is jointly
continuous on the set times the whole space. -/
theorem continuousOn_mixedConvection (hm : (3 : ℝ) < 2 * m) {U : ℝ → VectorH 3 m} {S : Set ℝ}
    (hU : ContinuousOn U S) :
    ContinuousOn (fun p : ℝ × VectorH 3 (m + 1) ↦ mixedConvection m hm (U p.1) p.2)
      (S ×ˢ univ) :=
  ((mixedConvection m hm).continuous.comp_continuousOn
    (hU.comp continuousOn_fst fun _ hp ↦ hp.1)).clm_apply continuousOn_snd

end NavierStokes.SobolevConvection
