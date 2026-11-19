/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Regular
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Heaviside distribution

The Heaviside step function is a regular distribution on the real line, and its distributional
derivative is the Dirac mass at the origin.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open TopologicalSpace
open scoped Distributions

namespace Distribution

/-- The Heaviside step function, with value one at the origin. -/
def heaviside (x : ℝ) : ℝ :=
  (Set.Ici (0 : ℝ)).indicator (fun _ ↦ 1) x

/-- The Heaviside step function is locally integrable. -/
theorem heaviside_locallyIntegrable :
    LocallyIntegrable heaviside volume := by
  exact (locallyIntegrable_const (μ := volume) (1 : ℝ)).indicator measurableSet_Ici

/-- The regular distribution associated with the Heaviside step function. -/
def heavisideDistribution :
    𝓓'((⊤ : Opens ℝ), ℝ) :=
  ofFun ⊤ heaviside volume ⊤

/-- The Heaviside distribution acts by integration over the nonnegative half-line. -/
@[simp]
theorem heavisideDistribution_apply
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    heavisideDistribution φ = ∫ x in Set.Ici (0 : ℝ), φ x := by
  have hf : LocallyIntegrableOn heaviside (⊤ : Opens ℝ) volume := by
    simpa using heaviside_locallyIntegrable.locallyIntegrableOn (Set.univ : Set ℝ)
  rw [heavisideDistribution, ofFun_apply hf]
  simp only [smul_eq_mul]
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards with x
  simp [heaviside, Set.indicator]

/-- The distributional derivative of the Heaviside step function is the Dirac mass at zero. -/
theorem heavisideDistribution_lineDerivCLM :
    lineDerivCLM (1 : ℝ) heavisideDistribution =
      (delta (0 : ℝ) : 𝓓'((⊤ : Opens ℝ), ℝ)) := by
  ext φ
  rw [lineDerivCLM_apply, heavisideDistribution_apply, delta_apply]
  have hline :
      ∀ x : ℝ,
        (TestFunction.lineDerivCLM ℝ (1 : ℝ) φ :
          𝓓((⊤ : Opens ℝ), ℝ)) x =
          deriv (fun y : ℝ ↦ φ y) x := by
    intro x
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    simp [fderiv_eq_smul_deriv]
  simp_rw [hline]
  rw [integral_Ici_eq_integral_Ioi]
  rw [φ.hasCompactSupport.integral_Ioi_deriv_eq
    (φ.contDiff.of_le (by simp)) (0 : ℝ)]
  ring

end Distribution
