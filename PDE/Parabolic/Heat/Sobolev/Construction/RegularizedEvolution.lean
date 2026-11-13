/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Energy.Regularized
public import PDE.Analysis.Evolution.ODE.Caratheodory.Affine
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Core.Dissipation

/-!
# Constructed regularized heat trajectories

Affine Carathéodory existence constructs trajectories for `u' = ε Jδ Δ Jδ u + Jδ F`
on every finite interval. The spatial energy estimates give bounds independent
of `δ`, although the operator norm used for existence can depend on `δ`.
The initial datum belongs to H¹ and the forcing only to Bochner L²(L²).
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ} {ε δ a b : ℝ}
  {F : ℝ → DerivLp n 2 univ} {q : W^{1,2}(ℝ^n)}

/-- Every regularized heat trajectory satisfies a closed-interval H¹
bound depending on the L² forcing budget, uniformly in the smoothing scale. -/
theorem regularized_heat_norm_sq_le (hε : 0 < ε) (hδ : 0 < δ) (hab : a ≤ b)
    (hf : MemLp F 2 (volume.restrict (Ioc a b)))
    (U : AffineCaratheodorySolutionOn (fun _ ↦ ε • regularizedLaplacianCLM 1 hδ)
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t)) a b q) :
    ∀ t ∈ Icc a b,
      ‖U.trajectory t‖ ^ 2 ≤
        (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) *
          Real.exp (t - a) := by
  have hfsq : IntervalIntegrable (fun t ↦ ‖F t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hf.integrable_norm_pow (by norm_num)
  have hc : 0 ≤ 1 + (n : ℝ) / ε := by positivity
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      deriv (fun s ↦ ‖U.trajectory s‖ ^ 2) t ≤
        1 * ‖U.trajectory t‖ ^ 2 + (1 + (n : ℝ) / ε) * ‖F t‖ ^ 2 := by
    filter_upwards [U.equation_ae] with t ht
    rw [ht.norm_sq.deriv]
    simpa only [smul_apply, one_mul] using
      two_inner_regularized_heat_le hε hδ (U.trajectory t) (F t)
  have hbound := le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le hab
    (absolutelyContinuousOnInterval_norm_sq U.absolutely_continuous)
    (hfsq.const_mul (1 + (n : ℝ) / ε))
    (Filter.Eventually.of_forall fun t ↦ mul_nonneg hc (sq_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1) hderiv
  simpa only [one_mul, intervalIntegral.integral_const_mul, U.initial_value] using hbound

/-- The total diffusion dissipation has a bound independent of the smoothing
scale. The estimate keeps the initial energy and the L² forcing norm explicit. -/
theorem regularized_heat_integral_dissipation_le
    (hε : 0 < ε) (hδ : 0 < δ) (hab : a ≤ b)
    (hf : MemLp F 2 (volume.restrict (Ioc a b)))
    (U : AffineCaratheodorySolutionOn (fun _ ↦ ε • regularizedLaplacianCLM 1 hδ)
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t)) a b q) :
    ε * (∫ t in a..b,
      -⟪U.trajectory t, regularizedLaplacianCLM 1 hδ (U.trajectory t)⟫_ℝ) ≤
        (1 + (b - a) * Real.exp (b - a)) *
          (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) := by
  have hU : ContinuousOn U.trajectory (Icc a b) := by
    simpa only [uIcc_of_le hab] using U.absolutely_continuous.continuousOn
  have hd : IntervalIntegrable
      (fun t ↦ ε * -⟪U.trajectory t,
        regularizedLaplacianCLM 1 hδ (U.trajectory t)⟫_ℝ) volume a b :=
    ((hU.inner (𝕜 := ℝ)
      ((regularizedLaplacianCLM 1 hδ).continuous.comp_continuousOn hU)).neg.const_mul ε)
      |>.intervalIntegrable_of_Icc hab
  have hfsq : IntervalIntegrable (fun t ↦ ‖F t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hf.integrable_norm_pow (by norm_num)
  have hc : 0 ≤ 1 + (n : ℝ) / ε := by positivity
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioc a b),
      deriv (fun s ↦ ‖U.trajectory s‖ ^ 2) t +
        ε * -⟪U.trajectory t, regularizedLaplacianCLM 1 hδ (U.trajectory t)⟫_ℝ ≤
      ‖U.trajectory t‖ ^ 2 + (1 + (n : ℝ) / ε) * ‖F t‖ ^ 2 := by
    filter_upwards [U.equation_ae] with t ht
    rw [ht.norm_sq.deriv]
    simpa only [smul_apply, mul_neg, sub_eq_add_neg] using
      regularized_heat_energy_le hε hδ (U.trajectory t) (F t)
  have hbound := integral_dissipation_le_of_deriv_add_le hab (by norm_num : (0 : ℝ) ≤ 1)
    (absolutelyContinuousOnInterval_norm_sq U.absolutely_continuous)
    (fun _ _ ↦ sq_nonneg _) hd (hfsq.const_mul (1 + (n : ℝ) / ε))
    (Filter.Eventually.of_forall fun t ↦ mul_nonneg hε.le
      (neg_nonneg.mpr (inner_regularizedLaplacianCLM_one_nonpos hδ _)))
    (Filter.Eventually.of_forall fun t ↦ mul_nonneg hc (sq_nonneg _))
    (by simpa only [one_mul] using hdiff)
  simpa only [one_mul, intervalIntegral.integral_const_mul, U.initial_value] using hbound

/-- H¹ regularized heat evolution exists on every finite interval.
The returned trajectory has a smoothing-scale-independent energy bound. -/
theorem exists_regularized_heat_solution
    (hε : 0 < ε) (hδ : 0 < δ) (hab : a ≤ b)
    (F : ℝ → DerivLp n 2 univ)
    (hf : MemLp F 2 (volume.restrict (Ioc a b))) (q : W^{1,2}(ℝ^n)) :
    ∃ U : AffineCaratheodorySolutionOn (fun _ ↦ ε • regularizedLaplacianCLM 1 hδ)
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t)) a b q,
      ∀ t ∈ Icc a b,
        ‖U.trajectory t‖ ^ 2 ≤
          (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) *
            Real.exp (t - a) := by
  let A : W^{1,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) :=
    ε • regularizedLaplacianCLM 1 hδ
  have hfcc : MemLp F 2 (volume.restrict (Icc a b)) := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using hf
  have hJf := (mollifierSmoothingCLM 1 (standardMollifier n) hδ).comp_memLp' hfcc
  obtain ⟨U⟩ := AffineCaratheodorySolutionOn.exists hab (fun _ ↦ A)
    (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t))
    aestronglyMeasurable_const (hJf.integrable (by norm_num)) ‖A‖₊
    (fun _ _ ↦ le_rfl) q
  exact ⟨U, regularized_heat_norm_sq_le hε hδ hab hf U⟩

end PDE.Parabolic.Heat
