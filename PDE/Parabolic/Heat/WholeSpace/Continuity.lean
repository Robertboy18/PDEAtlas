/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Fourier
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Strong continuity of whole-space heat evolution

The Gaussian symbols converge pointwise and stay bounded by one. Dominated
convergence of squared Fourier differences proves continuity on L² even at
time zero, where convergence in the L∞ symbol norm fails.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter
open scoped ENNReal NNReal Topology Real

namespace HeatEquation.WholeSpace

variable {n : ℕ}

/-- Pointwise Gaussian multiplication is strongly continuous on Fourier L². -/
theorem continuous_heatSymbolLinf_smul (f : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    Continuous (fun t : ℝ≥0 ↦ (heatSymbolLinf n t • f : Lp ℂ 2 volume)) := by
  apply continuous_iff_continuousAt.2
  intro t₀
  let G : ℝ≥0 → ℝ^n → ℂ := fun t ξ ↦ (heatSymbol n t ξ - heatSymbol n t₀ ξ) * f ξ
  have hbound : ∀ t ξ, ‖G t ξ‖ ^ 2 ≤ 4 * ‖f ξ‖ ^ 2 := by
    intro t ξ
    have hm : ‖heatSymbol n t ξ - heatSymbol n t₀ ξ‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by
        have h₁ := norm_heatSymbol_le_one t ξ
        have h₂ := norm_heatSymbol_le_one t₀ ξ
        linarith)
    have hG : ‖G t ξ‖ ≤ 2 * ‖f ξ‖ := by
      dsimp [G]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    nlinarith [norm_nonneg (G t ξ), norm_nonneg (f ξ)]
  have hcont : ∀ ξ, Continuous (fun t : ℝ≥0 ↦ ‖G t ξ‖ ^ 2) := by
    intro ξ
    dsimp [G, heatSymbol]
    fun_prop
  have hmeas : ∀ t, AEStronglyMeasurable (fun ξ ↦ ‖G t ξ‖ ^ 2) volume := by
    intro t
    exact (((by unfold heatSymbol; fun_prop : Continuous
      (fun ξ : ℝ^n ↦ heatSymbol n t ξ - heatSymbol n t₀ ξ)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f)).norm.pow 2)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun ξ ↦ 4 * ‖f ξ‖ ^ 2) (.of_forall hmeas)
    (.of_forall fun t ↦ .of_forall fun ξ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound t ξ)
    (((Lp.memLp f).integrable_norm_pow (by norm_num)).const_mul 4)
    (.of_forall fun ξ ↦ (hcont ξ).tendsto t₀)
  have hzero : ∫ ξ, ‖G t₀ ξ‖ ^ 2 = 0 := by simp [G]
  rw [hzero] at hlim
  have hrep (t : ℝ≥0) :
      ‖(heatSymbolLinf n t • f : Lp ℂ 2 volume) - heatSymbolLinf n t₀ • f‖ ^ 2 =
        ∫ ξ, ‖G t ξ‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    have htAE : ⇑(heatSymbolLinf n t) =ᵐ[volume] heatSymbol n t :=
      (memLp_top_heatSymbol (n := n) t).coeFn_toLp
    have ht₀AE : ⇑(heatSymbolLinf n t₀) =ᵐ[volume] heatSymbol n t₀ :=
      (memLp_top_heatSymbol (n := n) t₀).coeFn_toLp
    filter_upwards [Lp.coeFn_sub (heatSymbolLinf n t • f) (heatSymbolLinf n t₀ • f),
      Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t) f,
      Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t₀) f, htAE, ht₀AE]
      with ξ hsub ht ht₀ htAE ht₀AE
    simp only [hsub, Pi.sub_apply, ht, ht₀, Pi.smul_apply', smul_eq_mul, htAE, ht₀AE]
    simp only [G, sub_mul]
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hlim
  simpa only [Function.comp_def, ← hrep, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero]
    using hsqrt

/-- The actual Fourier heat evolution has continuous L² orbits at every nonnegative time. -/
theorem continuous_heatL2 (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    Continuous (fun t : ℝ≥0 ↦ heatL2 n t u) := by
  simp only [heatL2, PDE.Analysis.Fourier.fourierMultiplierL2_apply]
  exact continuous_fourierInv.comp (continuous_heatSymbolLinf_smul (𝓕 u))

end HeatEquation.WholeSpace
