/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.Mixed
public import PDE.Hyperbolic.Models.Wave.Strichartz.SpacetimeOperator

/-!
# The exterior Newtonian spacetime operator on mixed Lp spaces

The spatial Young inequality and the temporal fractional-integral estimate give
an operator from L^(4/3) time/L^(12/11) space to L⁴ time/L¹² space. Joint measurable
representatives and explicit almost-everywhere transport define a continuous
linear map on the nested quotient spaces. Its values represent the
iterated exterior-kernel integral.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveEquation.Strichartz

/-- The product of the spatial Young and temporal fractional-integral constants. -/
noncomputable def spacetimeNewtonBound : ℝ≥0∞ :=
  (((volume : Measure (ℝ^3)).toSphere univ * ENNReal.ofReal (1 / 3 : ℝ)) ^ (1 / 6 : ℝ)) *
    (((2 * (2 : ℝ≥0∞) ^ (1 / 4 : ℝ) + 2) ^ (4 : ℝ) *
      ((2 : ℝ≥0∞) ^ (4 / 3 : ℝ) * 16)) ^ (1 / 4 : ℝ))

/-- The explicit operator bound is finite. -/
theorem spacetimeNewtonBound_lt_top : spacetimeNewtonBound < ∞ :=
  spacetime_newton_constant_lt_top

variable (u v : Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3)))
  (4 / 3) (volume : Measure ℝ))

/-- The mixed Lp class representing the exterior Newtonian spacetime integral. -/
noncomputable def spacetimeNewtonLp :
    Lp (Lp ℝ 12 (volume : Measure (ℝ^3))) 4 (volume : Measure ℝ) :=
  (exists_spacetimeNewtonLp (Lp.measurable_jointRepresentative u)
    (Lp.memLp_eLpNorm_jointRepresentative u)).choose

/-- Almost every spatial section represents the kernel integral. -/
theorem spacetimeNewtonLp_section :
    ∀ᵐ t ∂volume, spacetimeNewtonIntegral (Lp.jointRepresentative u) t =ᵐ[volume]
      (spacetimeNewtonLp u t : ℝ^3 → ℝ) :=
  (exists_spacetimeNewtonLp (Lp.measurable_jointRepresentative u)
    (Lp.memLp_eLpNorm_jointRepresentative u)).choose_spec.1

/-- The chosen class satisfies the spatial Young and temporal fractional-integral bound. -/
theorem enorm_spacetimeNewtonLp_le :
    ‖spacetimeNewtonLp u‖ₑ ≤ spacetimeNewtonBound * ‖u‖ₑ := by
  have h := (exists_spacetimeNewtonLp (Lp.measurable_jointRepresentative u)
    (Lp.memLp_eLpNorm_jointRepresentative u)).choose_spec.2
  simpa only [spacetimeNewtonLp, spacetimeNewtonBound, Lp.eLpNorm_jointRepresentative] using h

/-- The mixed Lp class is additive, independently of the chosen representatives. -/
theorem spacetimeNewtonLp_add :
    spacetimeNewtonLp (u + v) = spacetimeNewtonLp u + spacetimeNewtonLp v := by
  have heq := spacetimeNewtonIntegral_congr_ae (Lp.jointRepresentative_add u v)
  have hadd := spacetimeNewtonIntegral_add_ae
    (Lp.measurable_jointRepresentative u) (Lp.measurable_jointRepresentative v)
    (Lp.memLp_eLpNorm_jointRepresentative u) (Lp.memLp_eLpNorm_jointRepresentative v)
  apply Lp.ext
  filter_upwards [spacetimeNewtonLp_section (u + v), spacetimeNewtonLp_section u,
    spacetimeNewtonLp_section v, Lp.coeFn_add (spacetimeNewtonLp u) (spacetimeNewtonLp v),
    hadd] with t huv hu hv hout hsum
  apply Lp.ext
  filter_upwards [huv, hu, hv, hsum,
    Lp.coeFn_add (spacetimeNewtonLp u t) (spacetimeNewtonLp v t)] with x huvx hux hvx hsumx hinner
  simp only [Pi.add_apply] at hout hinner
  rw [hout, hinner, ← huvx, heq, hsumx, hux, hvx]

/-- Scalar multiplication commutes with the mixed Lp kernel integral. -/
theorem spacetimeNewtonLp_smul (c : ℝ) :
    spacetimeNewtonLp (c • u) = c • spacetimeNewtonLp u := by
  have heq := spacetimeNewtonIntegral_congr_ae (Lp.jointRepresentative_smul c u)
  apply Lp.ext
  filter_upwards [spacetimeNewtonLp_section (c • u), spacetimeNewtonLp_section u,
    Lp.coeFn_smul c (spacetimeNewtonLp u)] with t hcu hu hout
  simp only [Pi.smul_apply] at hout
  rw [hout]
  apply Lp.ext
  filter_upwards [hcu, hu, Lp.coeFn_smul c (spacetimeNewtonLp u t)] with x hcux hux hinner
  simp only [Pi.smul_apply] at hinner
  calc
    (spacetimeNewtonLp (c • u) t : ℝ^3 → ℝ) x =
        spacetimeNewtonIntegral (Lp.jointRepresentative (c • u)) t x := hcux.symm
    _ = spacetimeNewtonIntegral (c • Lp.jointRepresentative u) t x := congrFun (congrFun heq t) x
    _ = c • spacetimeNewtonIntegral (Lp.jointRepresentative u) t x :=
      congrFun (congrFun (spacetimeNewtonIntegral_smul c (Lp.jointRepresentative u)) t) x
    _ = c • (spacetimeNewtonLp u t : ℝ^3 → ℝ) x := congrArg (c • ·) hux
    _ = (c • spacetimeNewtonLp u t : Lp ℝ 12 volume) x := hinner.symm

/-- Integration against the exterior Newtonian spacetime kernel defines a continuous
linear map from L^(4/3) time/L^(12/11) space to L⁴ time/L¹² space. Representatives
are constructed and transported explicitly through both quotient spaces. -/
noncomputable def spacetimeNewtonOperator :
    Lp (Lp ℝ (12 / 11) (volume : Measure (ℝ^3))) (4 / 3) (volume : Measure ℝ) →L[ℝ]
      Lp (Lp ℝ 12 (volume : Measure (ℝ^3))) 4 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := spacetimeNewtonLp
      map_add' := spacetimeNewtonLp_add
      map_smul' := fun c u ↦ spacetimeNewtonLp_smul u c }
    spacetimeNewtonBound.toReal fun u ↦ by
      change ‖spacetimeNewtonLp u‖ ≤ spacetimeNewtonBound.toReal * ‖u‖
      have h := ENNReal.toReal_mono
        (ENNReal.mul_ne_top spacetimeNewtonBound_lt_top.ne enorm_ne_top)
        (enorm_spacetimeNewtonLp_le u)
      simpa only [ENNReal.toReal_mul, toReal_enorm] using h

/-- The quotient-space operator is represented by the iterated kernel integral. -/
theorem spacetimeNewtonOperator_section :
    ∀ᵐ t ∂volume, spacetimeNewtonIntegral (Lp.jointRepresentative u) t =ᵐ[volume]
      (spacetimeNewtonOperator u t : ℝ^3 → ℝ) :=
  spacetimeNewtonLp_section u

/-- The quotient-space operator satisfies the explicit mixed-norm estimate. -/
theorem enorm_spacetimeNewtonOperator_le :
    ‖spacetimeNewtonOperator u‖ₑ ≤ spacetimeNewtonBound * ‖u‖ₑ :=
  enorm_spacetimeNewtonLp_le u

end WaveEquation.Strichartz
