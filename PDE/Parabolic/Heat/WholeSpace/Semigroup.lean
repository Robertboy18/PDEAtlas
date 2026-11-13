/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Continuity
public import PDE.Analysis.Evolution.Semigroup.Basic

/-!
# The actual whole-space Fourier heat semigroup

The Gaussian multipliers multiply by adding time. Together with the proved
strong continuity, this bundles the actual L² evolution as a semigroup.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open PDE.Analysis.Evolution
open scoped ENNReal NNReal Topology Real

namespace HeatEquation.WholeSpace

variable {n : ℕ}

@[simp]
theorem heatSymbol_zero (ξ : ℝ^n) : heatSymbol n 0 ξ = 1 := by simp [heatSymbol]

theorem heatSymbol_add (s t : ℝ≥0) (ξ : ℝ^n) :
    heatSymbol n (s + t) ξ = heatSymbol n s ξ * heatSymbol n t ξ := by
  simp only [heatSymbol, NNReal.coe_add, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.exp_add]
  congr 1
  ring

/-- The Fourier transform of actual heat evolution is its Gaussian multiplier. -/
theorem fourier_heatL2 (t : ℝ≥0) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    𝓕 (heatL2 n t u) = (heatSymbolLinf n t • 𝓕 u : Lp ℂ 2 volume) := by
  rw [heatL2, PDE.Analysis.Fourier.fourierMultiplierL2_apply, fourier_fourierInv_eq]

@[simp]
theorem heatL2_zero (u : Lp ℂ 2 (volume : Measure (ℝ^n))) : heatL2 n 0 u = u := by
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (heatL2 n 0 u) = 𝓕 u
  rw [fourier_heatL2]
  apply Lp.ext
  have hAE : ⇑(heatSymbolLinf n 0) =ᵐ[volume] heatSymbol n 0 :=
    (memLp_top_heatSymbol (n := n) 0).coeFn_toLp
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n 0) (𝓕 u), hAE]
    with ξ hmul hsymbol
  simp only [hmul, Pi.smul_apply', smul_eq_mul, hsymbol, heatSymbol_zero, one_mul]

theorem heatL2_add (s t : ℝ≥0) (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    heatL2 n (s + t) u = heatL2 n s (heatL2 n t u) := by
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (heatL2 n (s + t) u) = 𝓕 (heatL2 n s (heatL2 n t u))
  rw [fourier_heatL2, fourier_heatL2, fourier_heatL2]
  apply Lp.ext
  have hAE (r : ℝ≥0) : ⇑(heatSymbolLinf n r) =ᵐ[volume] heatSymbol n r :=
    (memLp_top_heatSymbol (n := n) r).coeFn_toLp
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n (s + t)) (𝓕 u),
    Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n s) (heatSymbolLinf n t • 𝓕 u),
    Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t) (𝓕 u), hAE (s + t), hAE s, hAE t]
    with ξ hsum hs ht hsumAE hsAE htAE
  simp only [hsum, hs, ht, Pi.smul_apply', smul_eq_mul, hsumAE, hsAE, htAE,
    heatSymbol_add, mul_assoc]

/-- The actual Fourier heat evolution, regarded as a real strongly continuous semigroup. -/
def heatL2Semigroup (n : ℕ) : StronglyContinuousSemigroup
    (Lp ℂ 2 (volume : Measure (ℝ^n))) where
  toMonoidHom :=
    { toFun := fun t ↦ (heatL2 n t.toAdd).restrictScalars ℝ
      map_one' := by
        apply ContinuousLinearMap.ext
        intro u
        exact heatL2_zero u
      map_mul' := by
        intro s t
        apply ContinuousLinearMap.ext
        intro u
        exact heatL2_add s.toAdd t.toAdd u }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro u
    exact continuous_heatL2 u

end HeatEquation.WholeSpace
