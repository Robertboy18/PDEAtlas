/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.GaussianFlow
public import PDE.Parabolic.Heat.WholeSpace.Convolution
public import PDE.Parabolic.Heat.WholeSpace.Selfsimilar

/-!
# The Gaussian heat flow of L² data

For real `f ∈ L²(ℝ^n)` and `t > 0` the pointwise heat flow `gaussianFlow t f` represents the
Gaussian convolution operator on `L²`, and for every `t ≥ 0` it represents the Fourier heat
operator `heatL2` on the complexification. On the integer Sobolev spaces `W^{k,2}(ℝ^n)` the
base representative of the heat semigroup `heatSobolev` is the heat flow of the base
representative, and the free self-similar evolution is `e^{τ/2} (G_{e^τ - 1} * u)(e^{τ/2} x)`.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional PDE.Analysis
open scoped ENNReal NNReal Convolution Sobolev

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- The heat flow of real `L²` data represents the Gaussian convolution operator on `L²`. -/
theorem gaussianFlow_ae_eq_heatConvolutionRealL2 {t : ℝ} (ht : 0 < t) {f : ℝ^n → ℝ}
    (hf : MemLp f 2 volume) :
    gaussianFlow t f =ᵐ[volume] heatConvolutionRealL2 n t ht (hf.toLp f) := by
  have h := convolutionL2CLM_ae_eq (fun x ↦ fundamentalSolutionHeat (n := n) x t)
    (fundamentalSolutionHeat_integrable t ht) (hf.toLp f)
  have hc : (fun x ↦ fundamentalSolutionHeat (n := n) x t) ⋆ (hf.toLp f : ℝ^n → ℝ) =
      (fun x ↦ fundamentalSolutionHeat (n := n) x t) ⋆ f :=
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl hf.coeFn_toLp
  have hflow : gaussianFlow t f = (fun x ↦ fundamentalSolutionHeat (n := n) x t) ⋆ f := by
    simp only [gaussianFlow, ht, ↓reduceIte]
  rw [hflow, ← hc]
  exact h.symm

/-- The heat flow of real `L²` data is the Fourier heat evolution of its complexification. -/
theorem gaussianFlow_eq_heatL2 (t : ℝ≥0) {f : ℝ^n → ℝ} (hf : MemLp f 2 volume) :
    (fun x ↦ ((gaussianFlow (t : ℝ) f x : ℝ) : ℂ)) =ᵐ[volume]
      heatL2 n t (complexifyRealL2 n (hf.toLp f)) := by
  rcases eq_zero_or_pos t with rfl | ht
  · rw [heatL2_zero, NNReal.coe_zero, gaussianFlow_of_nonpos le_rfl]
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL (μ := volume) (p := 2) (hf.toLp f),
      hf.coeFn_toLp] with x h1 h2
    change _ = (Complex.ofRealCLM.compLpL 2 volume (hf.toLp f)) x
    rw [h1]
    simp [h2]
  have ht' : 0 < (t : ℝ) := ht
  rw [heatL2_complexify_eq_convolution t ht']
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (heatConvolutionRealL2 n (t : ℝ) ht'
      (hf.toLp f)), gaussianFlow_ae_eq_heatConvolutionRealL2 ht' hf] with x h1 h2
  change ((gaussianFlow (t : ℝ) f x : ℝ) : ℂ) = (Complex.ofRealCLM.compLpL 2 volume
    (heatConvolutionRealL2 n (t : ℝ) ht' (hf.toLp f))) x
  rw [h1, h2]
  rfl

/-- The base representative of a whole-space `W^{k,2}` element lies in `L²`. -/
theorem memLp_baseRepresentative (u : W^{k,2}(ℝ^n)) :
    MemLp (baseRepresentative u) 2 volume := by
  have h := Lp.memLp ((u : WkpAmbientOn n k 2 Set.univ) (baseIndex n k))
  simp only [domainMeasure, Measure.restrict_univ] at h
  exact h

/-- The complexified base coordinate is the complexification of the base representative. -/
theorem baseL2_eq_complexifyRealL2 (u : W^{k,2}(ℝ^n)) :
    baseL2 u = complexifyRealL2 n ((memLp_baseRepresentative u).toLp _) := by
  apply Lp.ext
  rw [← complexifyL2CLM_base]
  filter_upwards [complexifyL2CLM_ae (wkpBaseCoordinateCLM u),
    Complex.ofRealCLM.coeFn_compLpL ((memLp_baseRepresentative u).toLp _),
    (memLp_baseRepresentative u).coeFn_toLp] with x h1 h2 h3
  change _ = (Complex.ofRealCLM.compLpL 2 volume ((memLp_baseRepresentative u).toLp _)) x
  rw [h1, h2, h3]
  rfl

/-- The base representative of the heat semigroup on `W^{k,2}(ℝ^n)` is the heat flow of the base
representative. -/
theorem baseRepresentative_heatSobolev (t : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    baseRepresentative (heatSobolev n k t u) =ᵐ[volume]
      gaussianFlow t (baseRepresentative u) := by
  have h1 := complexifyL2CLM_ae (wkpBaseCoordinateCLM (heatSobolev n k t u))
  rw [complexifyL2CLM_base, baseL2_heatSobolev, baseL2_eq_complexifyRealL2] at h1
  have h2 := gaussianFlow_eq_heatL2 t (memLp_baseRepresentative u)
  filter_upwards [h1, h2] with x hx1 hx2
  exact Complex.ofReal_injective (hx1.symm.trans hx2.symm)

/-- The base representative of the free self-similar evolution on `W^{k,2}(ℝ^n)` is
`e^{τ/2} (G_{e^τ - 1} * u)(e^{τ/2} x)`. -/
theorem baseRepresentative_selfsimilarHeatSobolev (τ : ℝ≥0) (u : W^{k,2}(ℝ^n)) :
    baseRepresentative (selfsimilarHeatSobolev n k τ u) =ᵐ[volume] fun x ↦
      selfsimilarFactor τ •
        gaussianFlow (selfsimilarHeatTime τ) (baseRepresentative u) (selfsimilarFactor τ • x) := by
  rw [selfsimilarHeatSobolev_apply]
  have h1 := baseRepresentative_smul_ae (selfsimilarFactor τ)
    (dilationWkpCLM (by norm_num) (selfsimilarFactor τ) (selfsimilarFactor_pos τ).ne'
      (heatSobolev n k (selfsimilarHeatTime τ) u))
  have h2 := dilationWkpCLM_base_ae (by norm_num) (selfsimilarFactor τ)
    (selfsimilarFactor_pos τ).ne' (heatSobolev n k (selfsimilarHeatTime τ) u)
  have h3 := (Measure.quasiMeasurePreserving_smul volume (selfsimilarFactor_pos τ).ne').ae_eq_comp
    (baseRepresentative_heatSobolev (selfsimilarHeatTime τ) u)
  simp only [domainMeasure, Measure.restrict_univ] at h1 h2
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [hx1, hx2]
  simp only [Function.comp_apply] at hx3
  rw [hx3]

end HeatEquation.WholeSpace
