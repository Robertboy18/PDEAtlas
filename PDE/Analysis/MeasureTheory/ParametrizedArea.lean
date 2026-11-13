/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.MeasureTheory.Function.Jacobian
import PDE.Common.Euclidean
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Hausdorff transport and reparametrization of area integrals

Mathlib's Lipschitz estimate for Hausdorff measure transfers to the normalized
Euclidean Hausdorff measure. Together with Mathlib's change of variables in equal
dimension and the multiplicativity of `LinearMap.normDet`, this compares surface
null sets and surface integrals written in different boundary charts.
-/

@[expose] public section

noncomputable section

open Set
open scoped ENNReal NNReal

namespace LipschitzOnWith

open MeasureTheory

variable {X Y : Type*}
variable [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A Lipschitz map increases normalized Euclidean Hausdorff measure by at
most the usual power of its Lipschitz constant. -/
theorem euclideanHausdorffMeasure_image_le
    {K : ℝ≥0} {f : X → Y} {s : Set X} (h : LipschitzOnWith K f s)
    (d : ℕ) :
    Measure.euclideanHausdorffMeasure d (f '' s) ≤
      (K : ℝ≥0∞) ^ (d : ℝ) *
        Measure.euclideanHausdorffMeasure d s := by
  have hraw := h.hausdorffMeasure_image_le
    (d := (d : ℝ)) (by positivity)
  let a : ℝ≥0∞ := Measure.addHaarScalarFactor
    (volume : Measure (ℝ^d))
    (Measure.hausdorffMeasure (d : ℝ))
  simp only [Measure.euclideanHausdorffMeasure_def,
    Measure.smul_apply, ENNReal.smul_def]
  calc
    a * Measure.hausdorffMeasure (d : ℝ) (f '' s) ≤
        a * ((K : ℝ≥0∞) ^ (d : ℝ) *
          Measure.hausdorffMeasure (d : ℝ) s) := by
      gcongr
    _ = (K : ℝ≥0∞) ^ (d : ℝ) *
        (a * Measure.hausdorffMeasure (d : ℝ) s) := by
      ac_rfl

end LipschitzOnWith

namespace MeasureTheory

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A Jacobian-weighted area integral is invariant under a differentiable
injective reparametrization of its parameter domain. -/
theorem lintegral_image_eq_lintegral_normDet_fderiv_comp
    {s : Set E} {ψ : E → E} {φ : E → F}
    (hs : MeasurableSet s) (hψ : Differentiable ℝ ψ)
    (hψinj : Set.InjOn ψ s) (hφ : Differentiable ℝ φ)
    (g : F → ENNReal) :
    ∫⁻ y in ψ '' s,
        ENNReal.ofReal (fderiv ℝ φ y).toLinearMap.normDet * g (φ y) ∂volume =
      ∫⁻ x in s,
        ENNReal.ofReal (fderiv ℝ (φ ∘ ψ) x).toLinearMap.normDet *
          g ((φ ∘ ψ) x) ∂volume := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := volume) hs
    (fun x _ ↦ (hψ x).hasFDerivAt.hasFDerivWithinAt) hψinj]
  apply setLIntegral_congr_fun hs
  intro x _
  simp only [Function.comp_apply]
  rw [fderiv_comp x (hφ (ψ x)) (hψ x)]
  rw [ContinuousLinearMap.toLinearMap_comp]
  rw [LinearMap.normDet_comp_of_finrank_eq]
  · rw [LinearMap.normDet_eq_abs_det]
    rw [ENNReal.ofReal_mul]
    · ac_rfl
    · exact LinearMap.normDet_nonneg _
  · rfl

end MeasureTheory
