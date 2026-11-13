/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import PDE.Analysis.Evolution.Gelfand.Triple
import PDE.Analysis.Evolution.Compactness.Lp.Basic

/-!
# Measurable-time Galerkin approximations

An almost-everywhere Gelfand Galerkin approximation on a trial space `S` is an absolutely
continuous trajectory `u : [a, b] → S` with `u(a) = u₀` and a square-integrable derivative
existing almost everywhere, such that `⟪ι u'(t), ι v⟫_H + B(t)(u(t), v) = ℓ(t)(v)` for all
`v ∈ S` and almost every `t`, together with the integrated coercive estimate. A Carathéodory
solver produces such trajectories for coefficients measurable in time. The notion is
unchanged when `B` or `ℓ` is modified on a null set.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 1 and its proof (absolutely continuous
  coefficients `d_m^k`). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A finite-dimensional Galerkin trajectory for measurable
coefficients.

The derivative and equation hold almost everywhere on `(a,b]`, as for a Carathéodory
solution. The integrated energy estimate, with constants independent of the trial space, is
part of the data. -/
structure AEGelfandGalerkinApproximation
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    (a b C M : ℝ) (u₀ : S) where
  /-- The finite-dimensional trajectory. -/
  trajectory : ℝ → S
  /-- Its almost-everywhere coefficient derivative. -/
  coefficientDerivative : ℝ → S
  /-- The prescribed initial value. -/
  initial : trajectory a = u₀
  /-- Carathéodory trajectories are absolutely continuous. -/
  trajectory_ac : AbsolutelyContinuousOnInterval trajectory a b
  /-- The chosen coefficient derivative agrees with the classical derivative
  almost everywhere on the time interval. -/
  derivative_ae :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      HasDerivAt trajectory (coefficientDerivative t) t
  /-- The coefficient derivative has the natural square-integrability. -/
  derivative_memLp :
    MemLp coefficientDerivative 2 (volume.restrict (Set.Ioc a b))
  /-- The finite-dimensional weak equation holds almost everywhere. -/
  equation_ae :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ v : S,
      inner ℝ (T.inclusion (coefficientDerivative t : V))
          (T.inclusion (v : V)) +
        B t (trajectory t : V) (v : V) =
      ell t (v : V)
  /-- The dimension-independent integrated coercive estimate. -/
  integrated_energy_bound : ∀ t ∈ Set.Icc a b,
    (1 / 2 : ℝ) * ‖T.inclusion (trajectory t : V)‖ ^ 2 +
        (C / 2) * ∫ s in a..t, ‖(trajectory s : V)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (M ^ 2 / (2 * C)) * (t - a)

namespace AEGelfandGalerkinApproximation

variable
    {T : GelfandTriple (V := V) (H := H)}
    {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}

omit [CompleteSpace V] [CompleteSpace H] in
/-- Replacing the forcing by an almost-everywhere equal representative
preserves an absolutely continuous Galerkin approximation. -/
def congrForcingAE
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    {ell' : ℝ → StrongDual ℝ V}
    (hEll : ell =ᵐ[volume.restrict (Set.Ioc a b)] ell') :
    AEGelfandGalerkinApproximation T S B ell' a b C M u₀ where
  trajectory := G.trajectory
  coefficientDerivative := G.coefficientDerivative
  initial := G.initial
  trajectory_ac := G.trajectory_ac
  derivative_ae := G.derivative_ae
  derivative_memLp := G.derivative_memLp
  equation_ae := by
    filter_upwards [G.equation_ae, hEll] with t heq ht
    intro v
    rw [← ht]
    exact heq v
  integrated_energy_bound := G.integrated_energy_bound

omit [CompleteSpace V] [CompleteSpace H] in
/-- Replacing the time-dependent operator by an almost-everywhere equal
representative preserves an absolutely continuous Galerkin approximation. -/
def congrOperatorAE
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    {B' : ℝ → V →L[ℝ] StrongDual ℝ V}
    (hB : B =ᵐ[volume.restrict (Set.Ioc a b)] B') :
    AEGelfandGalerkinApproximation T S B' ell a b C M u₀ where
  trajectory := G.trajectory
  coefficientDerivative := G.coefficientDerivative
  initial := G.initial
  trajectory_ac := G.trajectory_ac
  derivative_ae := G.derivative_ae
  derivative_memLp := G.derivative_memLp
  equation_ae := by
    filter_upwards [G.equation_ae, hB] with t heq ht
    intro v
    rw [← ht]
    exact heq v
  integrated_energy_bound := G.integrated_energy_bound

omit [CompleteSpace V] [CompleteSpace H] in
/-- An absolutely continuous trial trajectory is Bochner `L²` on a finite
interval. -/
theorem trajectoryMemLp
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) :
    MemLp G.trajectory 2 (volume.restrict (Set.Ioc a b)) := by
  apply memLp_restrict_Ioc_of_continuousOn
  simpa only [Set.uIcc_of_le hab] using G.trajectory_ac.continuousOn

end AEGelfandGalerkinApproximation

end PDE.Analysis.Evolution
