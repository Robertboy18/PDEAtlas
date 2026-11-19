/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Gelfand.VectorField
public import PDE.Analysis.MeasureTheory.StronglyMeasurable.ContinuousLinearMap

/-!
# Measurable finite-dimensional Galerkin coefficients

When the data `B(t) ∈ L(V, V*)` and `ℓ(t) ∈ V*` of a weak evolution equation
are only measurable in time, the Galerkin ODE on a finite-dimensional trial
space `S` becomes a Carathéodory system `u' = -A_S(t) u + f_S(t)`. The
passage from ambient data to coefficients, namely restriction to `S`, Riesz
representation in `S`, and inversion of the pivot mass operator, is given by
continuous linear maps `V* →L S` and `L(V, V*) →L L(S, S)`.  Composition
with a continuous linear map preserves strong measurability and turns uniform
ambient bounds into uniform coefficient bounds, so no coordinate basis of `S`
is ever chosen.

## Main results

* `gelfandGalerkinForcingMap`, `gelfandGalerkinOperatorMap`: the coefficient
  maps, with `_apply` lemmas identifying them with `gelfandGalerkinForcing`
  and `gelfandGalerkinOperator`.
* `aestronglyMeasurable_gelfandGalerkin_coefficients`: measurable ambient
  data give measurable coefficients.
* `neg_gelfandGalerkinOperator_add_forcing`: the affine decomposition of the
  pivot-mass Galerkin vector field.
* `norm_neg_gelfandGalerkinOperator_le`, `norm_gelfandGalerkinForcing_le`:
  uniform ambient bounds transfer to the coefficients through the
  mass-conditioning constant `gelfandGalerkinLipschitzBound`.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

open InnerProductSpace

namespace PDE.Analysis.Evolution

section GalerkinCaratheodory

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
The mass-inverted forcing `ℓ ↦ M_S⁻¹ r_S(ℓ)` as a continuous linear map `V* → S`, where
`r_S(ℓ)` is the Riesz representative in `S` of the restriction of `ℓ` to `S`.
-/
def gelfandGalerkinForcingMap
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S] :
    StrongDual ℝ V →L[ℝ] S :=
  (trialMassEquiv T S).symm.toContinuousLinearMap.comp
    ((toDual ℝ S).symm.toContinuousLinearMap.comp
      (restrictFunctionalMap S))

omit [CompleteSpace V] [CompleteSpace H] in
/-- The forcing map sends `ℓ ∈ V*` to the mass-inverted Riesz representative
of its restriction to the trial space. -/
@[simp]
theorem gelfandGalerkinForcingMap_apply
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (ell : StrongDual ℝ V) :
    gelfandGalerkinForcingMap T S ell =
      (trialMassEquiv T S).symm
        ((toDual ℝ _).symm (restrictFunctional S ell)) :=
  rfl

/--
The mass-inverted stiffness operator `B ↦ M_S⁻¹ A_S(B)` as a continuous linear map
`L(V, V*) → L(S, S)`, with operator norm at most `‖M_S⁻¹‖`.
-/
def gelfandGalerkinOperatorMap
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S] :
    (V →L[ℝ] StrongDual ℝ V) →L[ℝ] (S →L[ℝ] S) :=
  LinearMap.mkContinuous
    { toFun := gelfandGalerkinOperator T S
      map_add' := by
        intro B₁ B₂
        ext u
        simp [gelfandGalerkinOperator, continuousLinearMapOfBilin]
      map_smul' := by
        intro c B
        ext u
        simp [gelfandGalerkinOperator, continuousLinearMapOfBilin] }
    ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖
    (fun B ↦ norm_gelfandGalerkinOperator_le T S B)

omit [CompleteSpace V] [CompleteSpace H] in
/-- The operator map sends a form `B` to the mass-inverted Galerkin stiffness
operator `gelfandGalerkinOperator T S B`. -/
@[simp]
theorem gelfandGalerkinOperatorMap_apply
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V) :
    gelfandGalerkinOperatorMap T S B =
      gelfandGalerkinOperator T S B :=
  rfl

omit [CompleteSpace V] [CompleteSpace H] in
/--
If `t ↦ B(t) v` is almost everywhere strongly measurable on `[a, b]` for every `v ∈ V` and
`ℓ` is almost everywhere strongly measurable there, then so are the Galerkin coefficients
`t ↦ -M_S⁻¹ A_S(t)` and `t ↦ M_S⁻¹ r_S(t)`.
-/
theorem aestronglyMeasurable_gelfandGalerkin_coefficients
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    {a b : ℝ}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V}
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Icc a b)))
    (hell : AEStronglyMeasurable ell (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable
        (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
          (volume.restrict (Set.Icc a b)) ∧
      AEStronglyMeasurable (gelfandGalerkinForcing T S ell)
        (volume.restrict (Set.Icc a b)) := by
  constructor
  · apply ContinuousLinearMap.aestronglyMeasurable_of_forall_apply
    intro v
    exact ((gelfandGalerkinForcingMap T S).continuous.comp_aestronglyMeasurable
      (hB (v : V))).neg
  · apply
      ((gelfandGalerkinForcingMap T S).continuous.comp_aestronglyMeasurable hell).congr
    filter_upwards with t
    rfl

omit [CompleteSpace V] [CompleteSpace H] in
/-- The Galerkin vector field is affine in the state:
`F(t, u) = -M_S⁻¹ A_S(t) u + M_S⁻¹ r_S(t)`. -/
theorem neg_gelfandGalerkinOperator_add_forcing
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) (t : ℝ) (u : S) :
    -(gelfandGalerkinOperator T S (B t)) u +
        gelfandGalerkinForcing T S ell t =
      gelfandGalerkinVectorField T S B ell t u := by
  simp [gelfandGalerkinOperator, gelfandGalerkinForcing,
    gelfandGalerkinVectorField, map_sub]
  abel

omit [CompleteSpace V] [CompleteSpace H] in
/-- If `‖B‖ ≤ M_B`, then `‖-M_S⁻¹ A_S(B)‖ ≤ ‖M_S⁻¹‖ M_B`. -/
theorem norm_neg_gelfandGalerkinOperator_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V) (MB : NNReal)
    (hB : ‖B‖ ≤ MB) :
    ‖-(gelfandGalerkinOperator T S B)‖ ≤
      gelfandGalerkinLipschitzBound T S MB := by
  calc
    ‖-(gelfandGalerkinOperator T S B)‖ =
        ‖gelfandGalerkinOperator T S B‖ :=
      norm_neg (gelfandGalerkinOperator T S B)
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * ‖B‖ :=
      norm_gelfandGalerkinOperator_le T S B
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * (MB : ℝ) := by
      gcongr
    _ = (gelfandGalerkinLipschitzBound T S MB : ℝ) := rfl

omit [CompleteSpace V] [CompleteSpace H] in
/-- If `‖ℓ‖ ≤ M_ℓ`, then `‖M_S⁻¹ r_S(ℓ)‖ ≤ ‖M_S⁻¹‖ M_ℓ`. -/
theorem norm_gelfandGalerkinForcing_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (ell : StrongDual ℝ V) (Mell : NNReal)
    (hell : ‖ell‖ ≤ Mell) :
    ‖(trialMassEquiv T S).symm
        ((toDual ℝ _).symm (restrictFunctional S ell))‖ ≤
      gelfandGalerkinLipschitzBound T S Mell := by
  calc
    ‖(trialMassEquiv T S).symm
        ((toDual ℝ _).symm (restrictFunctional S ell))‖ ≤
        ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
          ‖(toDual ℝ _).symm (restrictFunctional S ell)‖ :=
      (trialMassEquiv T S).symm.toContinuousLinearMap.le_opNorm _
    _ = ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
          ‖restrictFunctional S ell‖ := by
      exact congrArg
        (fun z : ℝ ↦
          ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * z)
        ((toDual ℝ S).symm.norm_map (restrictFunctional S ell))
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * ‖ell‖ := by
      gcongr
      exact norm_restrictFunctional_le S ell
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * (Mell : ℝ) := by
      gcongr
    _ = (gelfandGalerkinLipschitzBound T S Mell : ℝ) := rfl

end GalerkinCaratheodory

end PDE.Analysis.Evolution
