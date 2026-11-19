/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.AbsoluteContinuity
public import PDE.Analysis.Evolution.Time.FundamentalTheorem
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Local C¹ tests along absolutely continuous curves

A real-valued C¹ function is Lipschitz on the compact image of an absolutely
continuous curve. A Lipschitz extension therefore proves absolute continuity
of the composition, even when the test is defined smoothly only near the curve.

An integrable velocity then gives the chain rule in integral form. The curve
need have the specified derivative only almost everywhere; the state space
can be infinite dimensional.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real C¹ test preserves absolute continuity when an open set on which it
is C¹ contains the whole trajectory. Compactness is required only of the
trajectory image, which follows from continuity on the closed time interval. -/
theorem AbsolutelyContinuousOnInterval.comp_contDiffOn
    {u : ℝ → E} {a b : ℝ} {φ : E → ℝ} {U : Set E}
    (hu : AbsolutelyContinuousOnInterval u a b) (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 1 φ U) (himage : MapsTo u (uIcc a b) U) :
    AbsolutelyContinuousOnInterval (φ ∘ u) a b := by
  let S := u '' uIcc a b
  have hS : IsCompact S := isCompact_uIcc.image_of_continuousOn hu.continuousOn
  have hlocal : LocallyLipschitzOn S φ := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨K, V, hV, hK⟩ :=
      (hφ.contDiffAt (hU.mem_nhds (himage ht))).exists_lipschitzOnWith
    exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hK⟩
  obtain ⟨K, hK⟩ := hlocal.exists_lipschitzOnWith_of_compact hS
  exact hK.comp_absolutelyContinuousOnInterval (mapsTo_image u (uIcc a b)) hu

/-- Applying the derivative of a local C¹ test to an integrable velocity is
integrable along a continuous curve. The derivative is bounded on the compact
trajectory image; this does not require a global derivative bound. -/
theorem integrableOn_fderiv_comp_apply
    {u v : ℝ → E} {a b : ℝ} {φ : E → ℝ} {U : Set E}
    (hu : ContinuousOn u (Icc a b)) (hv : IntegrableOn v (Icc a b) volume)
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U)
    (himage : MapsTo u (Icc a b) U) :
    IntegrableOn (fun t ↦ fderiv ℝ φ (u t) (v t)) (Icc a b) volume := by
  have hD : ContinuousOn (fun t ↦ fderiv ℝ φ (u t)) (Icc a b) :=
    (hφ.continuousOn_fderiv_of_isOpen hU le_rfl).comp hu himage
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hm := (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
    (hD.aestronglyMeasurable measurableSet_Icc) hv.aestronglyMeasurable
  apply (hv.norm.const_mul C).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (fderiv ℝ φ (u t)).le_opNorm (v t) |>.trans
    (mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg (v t)))

/-- The chain rule integrated along an absolutely continuous curve.
The velocity is specified only almost everywhere, and the test need be C¹
only on an open neighborhood of the curve. -/
theorem AbsolutelyContinuousOnInterval.intervalIntegral_fderiv_comp_apply
    {u v : ℝ → E} {a b : ℝ} {φ : E → ℝ} {U : Set E}
    (hab : a ≤ b) (hu : AbsolutelyContinuousOnInterval u a b)
    (hv : IntegrableOn v (Icc a b) volume)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (v t) t)
    (hU : IsOpen U) (hφ : ContDiffOn ℝ 1 φ U)
    (himage : MapsTo u (Icc a b) U) :
    ∫ t in a..b, fderiv ℝ φ (u t) (v t) = φ (u b) - φ (u a) := by
  have huC : ContinuousOn u (Icc a b) := by
    simpa only [uIcc_of_le hab] using hu.continuousOn
  have huφ :=
    PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.comp_contDiffOn hu hU hφ (by
      simpa only [uIcc_of_le hab] using himage)
  apply AbsolutelyContinuousOnInterval.intervalIntegral_eq_sub_of_ae_hasDerivAt_normedSpace
    hab huφ
    (integrableOn_fderiv_comp_apply huC hv hU hφ himage)
  filter_upwards [hderiv, ae_restrict_mem measurableSet_Ioc] with t ht htI
  exact (hφ.contDiffAt (hU.mem_nhds (himage ⟨htI.1.le, htI.2⟩))).differentiableAt_one
    |>.hasFDerivAt.comp_hasDerivAt t ht

end PDE.Analysis.Evolution
