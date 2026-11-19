/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Bochner
import PDE.Analysis.Evolution.Galerkin.Measurable.Energy
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Uniform bounds for measurable Galerkin trajectories

An absolutely continuous Gelfand–Galerkin approximation
(`AEGelfandGalerkinApproximation`) stores the integrated energy estimate
`½ ‖u(t)‖²_H + (C/2) ∫_a^t ‖u‖²_V ≤ ½ ‖u₀‖²_H + M² (t - a) / (2C)`. We
turn it into a bound on the Bochner norm `‖u‖_{L²(a,b;V)}`, uniform
in the trial space, which is the input to weak compactness in `L²(V)`, and
prove the sharper coercive bound when the forcing is controlled by its
Bochner norm `‖ℓ‖_{L²(a,b;V*)}` rather than pointwise: the energy identity
for the absolutely continuous pivot trajectory, Young's inequality and
coercivity give `(C/2) ‖u‖²_{L²(V)} ≤ ½ ‖u₀‖²_H + ‖ℓ‖²_{L²(V*)} / (2C)`.

## Main results

* `AEGelfandGalerkinApproximation.integralNormSqLe`,
  `AEGelfandGalerkinApproximation.norm_ambientTrajectoryLp_sq_le`: the
  stored estimate as an `L²(V)` bound.
* `AEGelfandGalerkinApproximation.norm_ambientTrajectoryLp_sq_le_of_forcing_memLp`:
  the coercive bound in terms of `‖ℓ‖_{L²(V*)}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 2 (energy estimates for the Galerkin
  approximations). <https://doi.org/10.1090/gsm/019>
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

omit [CompleteSpace V] [CompleteSpace H] in
/-- For `C > 0`, `∫_a^b ‖u‖²_V ≤ (2/C) (½ ‖ι u₀‖²_H + M² (b - a) / (2C))`. -/
theorem integralNormSqLe
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) (hC : 0 < C) :
    ∫ s in a..b, ‖(G.trajectory s : V)‖ ^ 2 ≤
      (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (M ^ 2 / (2 * C)) * (b - a)) := by
  have henergy := G.integrated_energy_bound b ⟨hab, le_rfl⟩
  have hnonneg :
      0 ≤ (1 / 2 : ℝ) *
        ‖T.inclusion (G.trajectory b : V)‖ ^ 2 := by
    positivity
  have hbase :
      (C / 2) * ∫ s in a..b, ‖(G.trajectory s : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (b - a) := by
    nlinarith
  calc
    ∫ s in a..b, ‖(G.trajectory s : V)‖ ^ 2 =
        (2 / C) *
          ((C / 2) * ∫ s in a..b, ‖(G.trajectory s : V)‖ ^ 2) := by
      field_simp
    _ ≤ (2 / C) *
        ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (b - a)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)

omit [CompleteSpace V] [CompleteSpace H] in
/-- Explicit dimension-independent squared `L²(V)` bound for an absolutely
continuous Galerkin trajectory. -/
theorem norm_ambientTrajectoryLp_sq_le
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) (hC : 0 < C) :
    ‖G.ambientTrajectoryLp hab‖ ^ 2 ≤
      (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (M ^ 2 / (2 * C)) * (b - a)) := by
  rw [MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
  have hae :
      (fun t ↦ ‖G.ambientTrajectoryLp hab t‖ ^ 2) =ᵐ[
        volume.restrict (Set.Ioc a b)]
        fun t ↦ ‖(G.trajectory t : V)‖ ^ 2 :=
    (G.ambientTrajectoryLp_apply_ae hab).fun_comp
      (fun z : V ↦ ‖z‖ ^ 2)
  rw [integral_congr_ae hae, ← intervalIntegral.integral_of_le hab]
  exact G.integralNormSqLe hab hC

omit [CompleteSpace V] [CompleteSpace H] in
/-- The Galerkin state has the natural coercive bound for Bochner `L²`
forcing, independently of the pointwise forcing bound stored in `G`. -/
theorem norm_ambientTrajectoryLp_sq_le_of_forcing_memLp
    (G : AEGelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) (hC : 0 < C)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (hell : MemLp ell 2 (volume.restrict (Set.Ioc a b))) :
    ‖G.ambientTrajectoryLp hab‖ ^ 2 ≤
      (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (1 / (2 * C)) * ‖hell.toLp ell‖ ^ 2) := by
  have henergy := gelfandGalerkin_integrated_energy_bound_of_forcing_memLp T S
    B ell G.trajectory G.coefficientDerivative hab hC
    G.trajectory_ac G.derivative_ae G.derivative_memLp hcoercive hell G.equation_ae
  rw [G.initial] at henergy
  have hstateNorm : ‖G.ambientTrajectoryLp hab‖ ^ 2 =
      ∫ t in Set.Ioc a b, ‖(G.trajectory t : V)‖ ^ 2 := by
    rw [MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
    exact integral_congr_ae
      ((G.ambientTrajectoryLp_apply_ae hab).fun_comp (fun z : V ↦ ‖z‖ ^ 2))
  have hforcingNorm : ‖hell.toLp ell‖ ^ 2 =
      ∫ t in Set.Ioc a b, ‖ell t‖ ^ 2 := by
    rw [MeasureTheory.Lp.norm_sq_eq_integral_norm_sq]
    exact integral_congr_ae
      (hell.coeFn_toLp.fun_comp (fun z : StrongDual ℝ V ↦ ‖z‖ ^ 2))
  rw [hstateNorm, hforcingNorm]
  have hbase : (C / 2) * ∫ t in Set.Ioc a b, ‖(G.trajectory t : V)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (1 / (2 * C)) * ∫ t in Set.Ioc a b, ‖ell t‖ ^ 2 := by
    linarith [sq_nonneg ‖T.inclusion (G.trajectory b : V)‖]
  calc
    (∫ t in Set.Ioc a b, ‖(G.trajectory t : V)‖ ^ 2) =
        (2 / C) * ((C / 2) * ∫ t in Set.Ioc a b, ‖(G.trajectory t : V)‖ ^ 2) := by
      field_simp
    _ ≤ (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (1 / (2 * C)) * ∫ t in Set.Ioc a b, ‖ell t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)

end AEGelfandGalerkinApproximation

end PDE.Analysis.Evolution
