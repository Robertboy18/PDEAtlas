/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Polar.Profile
public import PDE.Common.Euclidean.CoordinateReflection

/-!
# Continuity of separated polar profiles

The angular branch cut disappears from a separated profile `a(r) f(β)`
when the angular endpoint values agree. The radius-zero singularity disappears
when the radial factor vanishes on a neighborhood of zero. These two conditions
give a continuous Cartesian reconstruction without assuming its continuity.
Reflection in the vertical axis sends an upper-half-plane chart angle `β` to `π - β`,
so an angular factor antisymmetric under this substitution gives an odd profile.
-/

@[expose] public section

noncomputable section

namespace PDE.FDeriv

open PDE.CoordinateSystems (meridianR meridianZ)
open scoped Topology

/-- Matching angular endpoint values make a separated polar profile continuous
away from the origin, including on the negative horizontal axis. -/
theorem continuousAt_profileFromPolar_mul
    {a f : ℝ → ℝ} (ha : Continuous a)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hend : f (-Real.pi) = f Real.pi)
    {x : ℝ^2} (hx : x ≠ 0) :
    ContinuousAt (profileFromPolar (fun r β ↦ a r * f β)) x := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let angular : Real.Angle → ℝ := AddCircle.liftIoc (2 * Real.pi) (-Real.pi) f
  have hangular : Continuous angular := by
    apply AddCircle.liftIoc_continuous
    · simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hend
    · simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hf
  let z : ℝ^2 → ℂ := fun y ↦ Complex.equivRealProd.symm (pointPair y)
  have hz : Continuous z := by
    exact Complex.equivRealProdCLM.symm.continuous.comp pointPairLinearMap.continuous
  have hxz : z x ≠ 0 := by
    intro hzero
    apply hx
    apply point_eq_of_pointPair_eq
    have hpair := congrArg Complex.equivRealProd hzero
    simpa [z, pointPair, meridianR, meridianZ] using hpair
  have hangle : ContinuousAt (fun y ↦ (Complex.arg (z y) : Real.Angle)) x :=
    (Complex.continuousAt_arg_coe_angle hxz).comp hz.continuousAt
  have hvalue (y : ℝ^2) : angular (Complex.arg (z y) : Real.Angle) =
      f (Complex.arg (z y)) := by
    apply AddCircle.liftIoc_coe_apply
    constructor
    · exact Complex.neg_pi_lt_arg _
    · simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using
        Complex.arg_le_pi (z y)
  have heq : profileFromPolar (fun r β ↦ a r * f β) =
      fun y ↦ a ‖y‖ * angular (Complex.arg (z y) : Real.Angle) := by
    funext y
    rw [hvalue]
    simp only [profileFromPolar, polarCoord_pointPair_fst]
    rfl
  rw [heq]
  exact (ha.continuousAt.comp continuous_norm.continuousAt).mul
    (hangular.continuousAt.comp hangle)

/-- A radial factor zero near the origin and an angular factor with matching
endpoint values give a globally continuous Cartesian profile. -/
theorem continuous_profileFromPolar_mul_of_zero_near_zero
    {a f : ℝ → ℝ} (ha : Continuous a)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hend : f (-Real.pi) = f Real.pi)
    (hzero : a =ᶠ[𝓝 0] fun _ ↦ 0) :
    Continuous (profileFromPolar (fun r β ↦ a r * f β)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hnorm : Filter.Tendsto (fun y : ℝ^2 ↦ ‖y‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using continuous_norm.tendsto (0 : ℝ^2)
    have hradial : ∀ᶠ y : ℝ^2 in 𝓝 0, a ‖y‖ = 0 :=
      hnorm.eventually hzero
    have hprofile : profileFromPolar (fun r β ↦ a r * f β) =ᶠ[𝓝 0] fun _ ↦ 0 := by
      filter_upwards [hradial] with y hy
      simp only [profileFromPolar, polarCoord_pointPair_fst, hy, zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq hprofile
  · exact continuousAt_profileFromPolar_mul ha hf hend hx

/-- Cutting off the homogeneous field near the origin gives global continuity
for every real exponent when the angular branch endpoints match. -/
theorem continuous_profileFromPolar_cutoff_rpow_mul
    {χ f : ℝ → ℝ} (hχ : Continuous χ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hend : f (-Real.pi) = f Real.pi)
    (hflat : χ =ᶠ[𝓝 0] fun _ ↦ 0) (m : ℝ) :
    Continuous (profileFromPolar (fun r β ↦ χ r * (r ^ m * f β))) := by
  let a : ℝ → ℝ := fun r ↦ χ r * r ^ m
  have hazero : a =ᶠ[𝓝 0] fun _ ↦ 0 := by
    filter_upwards [hflat] with r hr
    simp [a, hr]
  have ha : Continuous a := by
    apply continuous_iff_continuousAt.mpr
    intro r
    by_cases hr : r = 0
    · subst r
      exact continuousAt_const.congr_of_eventuallyEq hazero
    · exact hχ.continuousAt.mul (Real.continuousAt_rpow_const r m (Or.inl hr))
  simpa only [a, mul_assoc] using
    continuous_profileFromPolar_mul_of_zero_near_zero ha hf hend hazero

/-- An angular formula on nonnegative angles can be extended evenly for the
purpose of reconstructing a continuous Cartesian source. -/
def evenAngularExtension (f : ℝ → ℝ) (β : ℝ) : ℝ := f |β|

/-- The even extension is continuous whenever the original angular function is. -/
theorem continuous_evenAngularExtension {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (evenAngularExtension f) := hf.comp continuous_abs

/-- Even angular extension matches the two branch-cut endpoints automatically. -/
theorem evenAngularExtension_neg_pi (f : ℝ → ℝ) :
    evenAngularExtension f (-Real.pi) = evenAngularExtension f Real.pi := by
  simp only [evenAngularExtension, abs_neg]

/-- At a positive angle, even extension preserves the entire local formula. -/
theorem evenAngularExtension_eventuallyEq {f : ℝ → ℝ} {β : ℝ} (hβ : 0 < β) :
    evenAngularExtension f =ᶠ[𝓝 β] f := by
  filter_upwards [eventually_gt_nhds hβ] with θ hθ
  simp only [evenAngularExtension, abs_of_pos hθ]

/-- Every point of the physical upper half-plane has a strictly positive chart angle. -/
theorem polarCoord_pointPair_snd_pos {x : ℝ^2} (hx : 0 < x 1) :
    0 < (polarCoord (pointPair x)).2 := by
  let z : ℂ := Complex.equivRealProd.symm (pointPair x)
  have him : 0 < z.im := by
    simpa [z, Complex.equivRealProd_symm_apply, pointPair, meridianR, meridianZ] using hx
  change 0 < z.arg
  apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le)
  intro hzero
  exact him.ne' (Complex.arg_eq_zero_iff.mp hzero.symm).2

/-- Vertical-axis reflection sends every physical interior angle to `π - β`. -/
theorem polarCoord_pointPair_snd_coordinateReflection_zero
    {x : ℝ^2} (hx : 0 < x 1) :
    (polarCoord (pointPair (PDE.Common.coordinateReflection 0 x))).2 =
      Real.pi - (polarCoord (pointPair x)).2 := by
  let z : ℂ := Complex.equivRealProd.symm (pointPair x)
  have him : 0 < z.im := by
    simpa [z, Complex.equivRealProd_symm_apply, pointPair, meridianR, meridianZ] using hx
  have hrepr : Complex.equivRealProd.symm (pointPair (PDE.Common.coordinateReflection 0 x)) =
      -star z := by
    apply Complex.ext <;>
      simp [z, Complex.equivRealProd_symm_apply, pointPair, meridianR, meridianZ,
        PDE.Common.coordinateReflection_apply_of_ne]
  change Complex.arg (Complex.equivRealProd.symm
    (pointPair (PDE.Common.coordinateReflection 0 x))) = Real.pi - z.arg
  rw [hrepr, Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using neg_neg_of_pos him)]
  change Complex.arg ((starRingEnd ℂ) z) + Real.pi = Real.pi - z.arg
  rw [Complex.arg_conj, ite_eq_right (ne_of_lt (Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')))]
  ring

/-- A separated polar profile with an antisymmetric physical angular factor is
odd in the tangential coordinate at every upper-half-plane point. -/
theorem profileFromPolar_coordinateReflection_zero_of_odd
    (a f : ℝ → ℝ)
    (hodd : ∀ β ∈ Set.Ioo 0 Real.pi, f (Real.pi - β) = -f β)
    {x : ℝ^2} (hx : 0 < x 1) :
    profileFromPolar (fun r β ↦ a r * f β) (PDE.Common.coordinateReflection 0 x) =
      -profileFromPolar (fun r β ↦ a r * f β) x := by
  have hsource : pointPair x ∈ polarCoord.source := by
    right
    exact ne_of_gt hx
  have hβ : (polarCoord (pointPair x)).2 ∈ Set.Ioo 0 Real.pi :=
    ⟨polarCoord_pointPair_snd_pos hx, (polarCoord.map_source hsource).2.2⟩
  simp only [profileFromPolar, polarCoord_pointPair_fst, PDE.Common.norm_coordinateReflection,
    polarCoord_pointPair_snd_coordinateReflection_zero hx, hodd _ hβ, mul_neg]

end PDE.FDeriv
