/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convolution.ParameterApproximation
public import PDE.Common.Euclidean.Cylinder
public import PDE.FDeriv.PartialDeriv

/-!
# First derivatives of spatially smoothed waves

Parameter convolution approximates all first derivatives. The continuous
linear change of coordinates carries this convergence to Euclidean spacetime.
-/

public section

open Filter Set MeasureTheory PDE PDE.Common
open scoped Topology Convolution

namespace ContDiffBump

/-- Spatial smoothing approximates each coordinate derivative after identifying
product spacetime with canonical Euclidean spacetime. -/
theorem tendstoLocallyUniformlyOn_partialDeriv_convolution_timeSpace {n : ℕ} {u : ℝ × ℝ^n → ℝ}
    {I : Set ℝ} {K : Set (ℝ^n)} (hI : IsOpen I) (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (I ×ˢ univ)) (hs : ∀ t ∈ I, ∀ x ∉ K, u (t, x) = 0) {ι : Type*}
    {φ : ι → ContDiffBump (0 : ℝ^n)} {l : Filter ι} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (j : Fin (n + 1)) :
    let e := timeSpaceContinuousLinearEquiv n
    let U := fun i (p : ℝ^(n + 1)) ↦
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y ↦ u ((e p).1, y))) (e p).2
    TendstoLocallyUniformlyOn (fun i ↦ ∂[j] (U i)) (∂[j] (fun p ↦ u (e p)))
      l (spaceTimeCylinder univ I) := by
  dsimp only
  let e := timeSpaceContinuousLinearEquiv n
  have he (f : ℝ × ℝ^n → ℝ) (p : ℝ^(n + 1)) : (∂[j] (fun q ↦ f (e q))) p =
        fderiv ℝ f (e p) (e (EuclideanSpace.single j (1 : ℝ))) := by
    change (fderiv ℝ (f ∘ e) p) (EuclideanSpace.single j (1 : ℝ)) = _
    rw [e.comp_right_fderiv]
    rfl
  have hd := tendstoLocallyUniformlyOn_fderiv_convolution_parameter_apply
    (μ := volume) hI hK hu hs hφ (e (EuclideanSpace.single j (1 : ℝ)))
  have hc := hd.comp e (mapsTo_preimage e _) e.continuous.continuousOn
  refine (hc.congr (fun i p _ ↦ (he _ p).symm)).congr_right ?_
  exact fun p _ ↦ (he u p).symm

end ContDiffBump
