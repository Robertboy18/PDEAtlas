/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Coefficients
public import PDE.Analysis.Evolution.ODE.Caratheodory.Affine

/-!
# Galerkin trajectories for integrable forcing

Let `B` be a form with `t ↦ B(t) v` measurable for each `v` and `‖B(t)‖ ≤ MB` on `[a, b]`. For
a load `ℓ` integrable on `(a, b]`, the mass-inverted Galerkin system on a finite-dimensional
trial space has an absolutely continuous Carathéodory solution on `[a, b]` for each initial
value, and it is unique. The load need not be bounded. When `ℓ ∈ L²(a, b; V*)`, the
derivative of the solution is square integrable.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- For a load `ℓ` integrable on `(a, b]`, the mass-inverted Galerkin system has a
Carathéodory solution on `[a, b]` with `u(a) = u₀`. -/
theorem exists_gelfandGalerkinCaratheodory_of_integrable
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Icc a b)))
    (hell : Integrable ell (volume.restrict (Ioc a b)))
    (MB : NNReal) (hbound : ∀ t ∈ Icc a b, ‖B t‖ ≤ MB) (u₀ : S) :
    Nonempty (AffineCaratheodorySolutionOn
      (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
      (gelfandGalerkinForcing T S ell) a b u₀) := by
  have hell' : Integrable ell (volume.restrict (Icc a b)) := by
    rwa [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
  have hA := (aestronglyMeasurable_gelfandGalerkin_coefficients
    T S hB hell'.aestronglyMeasurable).1
  exact AffineCaratheodorySolutionOn.exists hab _ _ hA
    ((gelfandGalerkinForcingMap T S).integrable_comp hell')
    (gelfandGalerkinLipschitzBound T S MB)
    (fun t ht ↦ norm_neg_gelfandGalerkinOperator_le T S (B t) MB (hbound t ht)) u₀

/-- If `ℓ ∈ L²(a, b; V*)`, the Galerkin vector field along a Carathéodory trajectory is in
`L²(a, b; S)`. -/
theorem AffineCaratheodorySolutionOn.gelfandGalerkin_derivative_memLp
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    [FiniteDimensional ℝ S] [CompleteSpace S]
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b : ℝ} {u₀ : S} (hab : a ≤ b)
    (U : AffineCaratheodorySolutionOn
      (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
      (gelfandGalerkinForcing T S ell) a b u₀)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Icc a b)))
    (hell : MemLp ell 2 (volume.restrict (Ioc a b)))
    (MB : NNReal) (hbound : ∀ t ∈ Icc a b, ‖B t‖ ≤ MB) :
    MemLp (fun t ↦ gelfandGalerkinVectorField T S B ell t (U.trajectory t))
      2 (volume.restrict (Ioc a b)) := by
  have hell' : AEStronglyMeasurable ell (volume.restrict (Icc a b)) := by
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
    exact hell.aestronglyMeasurable
  have hA := (aestronglyMeasurable_gelfandGalerkin_coefficients T S hB hell').1
  have hrhs := U.rhsMemLp_of_memLp hab
    (hA.mono_measure (volume.restrict_mono_set Ioc_subset_Icc_self))
    ((gelfandGalerkinForcingMap T S).comp_memLp' hell)
    (gelfandGalerkinLipschitzBound T S MB)
    (fun t ht ↦ norm_neg_gelfandGalerkinOperator_le T S (B t) MB (hbound t ht))
  apply (memLp_congr_ae ?_).1 hrhs
  filter_upwards with t
  exact neg_gelfandGalerkinOperator_add_forcing T S B ell t (U.trajectory t)

/-- The stored affine equation is the derivative of the Galerkin trajectory. -/
theorem AffineCaratheodorySolutionOn.gelfandGalerkin_derivative_ae
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    [FiniteDimensional ℝ S] [CompleteSpace S]
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b : ℝ} {u₀ : S}
    (U : AffineCaratheodorySolutionOn
      (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
      (gelfandGalerkinForcing T S ell) a b u₀) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt U.trajectory
      (gelfandGalerkinVectorField T S B ell t (U.trajectory t)) t := by
  filter_upwards [U.equation_ae] with t ht
  exact ht.congr_deriv (neg_gelfandGalerkinOperator_add_forcing T S B ell t (U.trajectory t))

/-- The projected AC solution is unique on the prescribed interval.
Only the form evaluations must be measurable; the load cancels in the difference. -/
theorem AffineCaratheodorySolutionOn.gelfandGalerkin_trajectory_eq
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    [FiniteDimensional ℝ S] [CompleteSpace S]
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b : ℝ} {u₀ : S} (hab : a ≤ b)
    (U W : AffineCaratheodorySolutionOn
      (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
      (gelfandGalerkinForcing T S ell) a b u₀)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Icc a b)))
    (MB : NNReal) (hbound : ∀ t ∈ Icc a b, ‖B t‖ ≤ MB) :
    EqOn U.trajectory W.trajectory (Icc a b) := by
  have hA := (aestronglyMeasurable_gelfandGalerkin_coefficients T S hB
    (ell := fun _ ↦ 0) aestronglyMeasurable_const).1
  exact fun t ht ↦ AffineCaratheodorySolutionOn.trajectory_eq hab hA
    (gelfandGalerkinLipschitzBound T S MB)
    (fun t ht ↦ norm_neg_gelfandGalerkinOperator_le T S (B t) MB (hbound t ht)) U W t ht

end PDE.Analysis.Evolution
