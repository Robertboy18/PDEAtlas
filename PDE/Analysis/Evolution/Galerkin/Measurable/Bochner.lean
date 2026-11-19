/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Approximation

/-!
# Bochner representatives of measurable Galerkin trajectories

A measurable-time Galerkin trajectory and its coefficient derivative define
trial-space and ambient-space Bochner `L²` classes. The coercion lemmas
identify those classes with the original almost-everywhere representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution

namespace AEGelfandGalerkinApproximation

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {T : GelfandTriple (V := V) (H := H)}
  {S : Submodule ℝ V}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : ℝ → StrongDual ℝ V}
  {a b C M : ℝ} {u₀ : S}

/-- The trial-space Bochner class of an absolutely continuous Galerkin
trajectory. -/
def trajectoryLp
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) :
    Lp S 2 (volume.restrict (Set.Ioc a b)) :=
  (G.trajectoryMemLp hab).toLp G.trajectory

/-- The trial-space Bochner class of the almost-everywhere coefficient
derivative. -/
def coefficientDerivativeLp
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀) :
    Lp S 2 (volume.restrict (Set.Ioc a b)) :=
  G.derivative_memLp.toLp G.coefficientDerivative

omit [CompleteSpace V] [CompleteSpace H] in
/-- The trial-space trajectory class agrees almost everywhere with the
stored absolutely continuous representative. -/
theorem trajectoryLp_apply_ae
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) :
    (G.trajectoryLp hab : ℝ → S) =ᵐ[
      volume.restrict (Set.Ioc a b)] G.trajectory :=
  (G.trajectoryMemLp hab).coeFn_toLp

omit [CompleteSpace V] [CompleteSpace H] in
/-- The trial-space derivative class agrees almost everywhere with the
stored coefficient derivative. -/
theorem coefficientDerivativeLp_apply_ae
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀) :
    (G.coefficientDerivativeLp : ℝ → S) =ᵐ[
      volume.restrict (Set.Ioc a b)] G.coefficientDerivative :=
  G.derivative_memLp.coeFn_toLp

/-- The class in `L²(a, b; V)` of the trajectory, included into the energy space. -/
def ambientTrajectoryLp
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) :
    Lp V 2 (volume.restrict (Set.Ioc a b)) :=
  S.subtypeL.compLpL 2 (volume.restrict (Set.Ioc a b))
    (G.trajectoryLp hab)

/-- The class in `L²(a, b; V)` of the coefficient derivative, included into the energy
space. -/
def ambientDerivativeLp
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀) :
    Lp V 2 (volume.restrict (Set.Ioc a b)) :=
  S.subtypeL.compLpL 2 (volume.restrict (Set.Ioc a b))
    G.coefficientDerivativeLp

omit [CompleteSpace V] [CompleteSpace H] in
/-- The ambient trajectory class is represented almost everywhere by the
trial-space trajectory coerced into the energy space. -/
theorem ambientTrajectoryLp_apply_ae
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) :
    (G.ambientTrajectoryLp hab : ℝ → V) =ᵐ[
      volume.restrict (Set.Ioc a b)] fun t ↦ (G.trajectory t : V) := by
  filter_upwards [S.subtypeL.coeFn_compLpL (G.trajectoryLp hab),
    G.trajectoryLp_apply_ae hab] with t hcomp htraj
  change
    ((S.subtypeL.compLpL 2 (volume.restrict (Set.Ioc a b))
      (G.trajectoryLp hab) : Lp V 2 (volume.restrict (Set.Ioc a b))) t) =
      (G.trajectory t : V)
  rw [hcomp, htraj]
  rfl

omit [CompleteSpace V] [CompleteSpace H] in
/-- The ambient derivative class is represented almost everywhere by the
coefficient derivative coerced into the energy space. -/
theorem ambientDerivativeLp_apply_ae
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀) :
    (G.ambientDerivativeLp : ℝ → V) =ᵐ[
      volume.restrict (Set.Ioc a b)]
        fun t ↦ (G.coefficientDerivative t : V) := by
  filter_upwards [S.subtypeL.coeFn_compLpL G.coefficientDerivativeLp,
    G.coefficientDerivativeLp_apply_ae] with t hcomp hderiv
  change
    ((S.subtypeL.compLpL 2 (volume.restrict (Set.Ioc a b))
      G.coefficientDerivativeLp :
        Lp V 2 (volume.restrict (Set.Ioc a b))) t) =
      (G.coefficientDerivative t : V)
  rw [hcomp, hderiv]
  rfl

end AEGelfandGalerkinApproximation

end PDE.Analysis.Evolution
