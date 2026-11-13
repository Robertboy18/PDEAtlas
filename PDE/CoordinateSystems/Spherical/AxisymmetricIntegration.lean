/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.AngularMeasure
public import PDE.CoordinateSystems.Axisymmetric.Isometry
public import PDE.CoordinateSystems.Spherical.Inverse
import PDE.CoordinateSystems.Spherical.Axisymmetric
import PDE.Analysis.Integration.Polar

/-!
# Integrals of axisymmetric functions in spherical coordinates

A function `g` on `ℝ^3` invariant under every rotation about the symmetry axis takes the same
value at `radialFrame θ φ` for every azimuth `φ`. Its integral over the unit sphere is therefore
`2π ∫₀^π g (θ, 0) sin θ dθ`. If moreover `g` is even under the equatorial reflection
`(x, y, z) ↦ (x, y, -z)`, which takes the polar angle `θ` to `π - θ`, the polar integral folds
onto `(0, π/2)` and the sphere integral is `4π ∫₀^{π/2} g (θ, 0) sin θ dθ`. Functions of the
polar angle alone are the main example.

The sphere formulas hold without integrability or measurability hypotheses: the azimuthal
integral of a function of `θ` alone is a constant multiple of the polar integral for every
function, and a function symmetric about `π/2` has half its integral on each half interval,
both sides vanishing when the function is not integrable. For volume integrals the polar
formula of Euclidean space adds the radial factor `r²`. The Bochner formulas are stated for
vector-valued functions with the weight acting by scalar multiplication, and for real-valued
functions with the weight as a factor on the right.

## Main results

* `integral_sphere_of_axisymmetric`, `lintegral_sphere_of_axisymmetric`.
* `integral_sphere_of_axisymmetric_even`, `lintegral_sphere_of_axisymmetric_even`.
* `polarAngle_axisRotation`, `polarAngle_equatorialReflection`,
  `integral_sphere_comp_polarAngle_of_symm`, `lintegral_sphere_comp_polarAngle_of_symm`.
* `integral_volume_of_axisymmetric`, `lintegral_volume_of_axisymmetric`,
  `setIntegral_ball_of_axisymmetric`.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open MeasureTheory Set Metric Real
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The lower integral over a product of a function of the first coordinate, for every function
and a finite second factor. -/
private theorem lintegral_fun_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure ν] (h : α → ℝ≥0∞) :
    ∫⁻ z, h z.1 ∂(μ.prod ν) = ν univ * ∫⁻ x, h x ∂μ := by
  apply le_antisymm
  · obtain ⟨k, hkm, hkle, hkeq⟩ :=
      exists_measurable_le_lintegral_eq (μ.prod ν) (fun z ↦ h z.1)
    rw [hkeq, lintegral_prod _ hkm.aemeasurable,
      ← lintegral_const_mul' _ _ (measure_ne_top ν univ)]
    refine lintegral_mono fun x ↦ ?_
    calc ∫⁻ y, k (x, y) ∂ν ≤ ∫⁻ _, h x ∂ν := lintegral_mono fun y ↦ hkle (x, y)
      _ = ν univ * h x := by rw [lintegral_const, mul_comm]
  · obtain ⟨k, hkm, hkle, hkeq⟩ := exists_measurable_le_lintegral_eq μ h
    calc ν univ * ∫⁻ x, h x ∂μ = ∫⁻ z, k z.1 ∂(μ.prod ν) := by
          rw [hkeq, lintegral_prod (fun z ↦ k z.1) (hkm.comp measurable_fst).aemeasurable,
            ← lintegral_const_mul' _ _ (measure_ne_top ν univ)]
          refine lintegral_congr fun x ↦ ?_
          dsimp only
          rw [lintegral_const, mul_comm]
      _ ≤ ∫⁻ z, h z.1 ∂(μ.prod ν) := lintegral_mono fun z ↦ hkle z.1

/-- A function symmetric about `a / 2` has equal lower integrals over the two halves of
`(0, a)`. -/
private theorem setLIntegral_Ioo_eq_two_mul_of_symm {k : ℝ → ℝ≥0∞} {a : ℝ} (ha : 0 < a)
    (hk : ∀ x, k (a - x) = k x) :
    ∫⁻ x in Ioo 0 a, k x = 2 * ∫⁻ x in Ioo 0 (a / 2), k x := by
  have hunion : Ioc 0 (a / 2) ∪ Ioo (a / 2) a = Ioo 0 a :=
    Ioc_union_Ioo_eq_Ioo (by linarith) (by linarith)
  have hdisj : Disjoint (Ioc 0 (a / 2)) (Ioo (a / 2) a) :=
    disjoint_left.2 fun _ hx hx' ↦ (not_lt.2 hx.2) hx'.1
  have hrefl : ∫⁻ x in Ioo (a / 2) a, k x = ∫⁻ x in Ioo 0 (a / 2), k x := by
    have hmp := Measure.measurePreserving_sub_left (volume : Measure ℝ) a
    have hemb : MeasurableEmbedding fun x : ℝ ↦ a - x :=
      (MeasurableEquiv.subLeft a).measurableEmbedding
    rw [← hmp.setLIntegral_comp_preimage_emb hemb, preimage_const_sub_Ioo, sub_self,
      show a - a / 2 = a / 2 by ring]
    exact setLIntegral_congr_fun measurableSet_Ioo fun x _ ↦ hk x
  rw [← hunion, lintegral_union measurableSet_Ioo hdisj, hrefl,
    setLIntegral_congr (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := a / 2)).symm, two_mul]

/-- A function symmetric about `a / 2` has twice its integral over `(0, a / 2)` on `(0, a)`;
both sides vanish when the function is not integrable. -/
private theorem intervalIntegral_eq_two_smul_of_symm {h : ℝ → E} {a : ℝ} (ha : 0 ≤ a)
    (hh : ∀ x, h (a - x) = h x) :
    ∫ x in (0 : ℝ)..a, h x = (2 : ℝ) • ∫ x in (0 : ℝ)..(a / 2), h x := by
  by_cases hi : IntervalIntegrable h volume 0 (a / 2)
  · have hi' : IntervalIntegrable h volume (a / 2) a := by
      have h' := hi.comp_sub_left a
      simp only [hh, sub_zero, show a - a / 2 = a / 2 by ring] at h'
      exact h'.symm
    rw [← intervalIntegral.integral_add_adjacent_intervals hi hi', two_smul]
    congr 1
    calc ∫ x in (a / 2)..a, h x = ∫ x in (a / 2)..a, h (a - x) := by simp only [hh]
      _ = ∫ x in (0 : ℝ)..(a / 2), h x := by
        rw [intervalIntegral.integral_comp_sub_left, sub_self, show a - a / 2 = a / 2 by ring]
  · have hi0 : ¬ IntervalIntegrable h volume 0 a := fun hint ↦ hi (hint.mono_set
      (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc.2 (Or.inl ⟨by linarith, by linarith⟩))))
    rw [intervalIntegral.integral_undef hi, intervalIntegral.integral_undef hi0, smul_zero]

/-- An axisymmetric function takes the same value at every azimuth. -/
private theorem apply_radialFrame_of_axisymmetric {F : Type*} {g : ℝ^3 → F}
    (hrot : IsInvariantUnderAxisRotation g) (θ φ : ℝ) :
    g (radialFrame θ φ) = g (radialFrame θ 0) :=
  (congrArg g (axisRotation_frame φ θ 0)).symm.trans (hrot φ _)

/-- A function even under the equatorial reflection takes the same value at the polar angles
`θ` and `π - θ`. -/
private theorem apply_radialFrame_pi_sub_of_even {F : Type*} {g : ℝ^3 → F}
    (hrefl : ∀ x, g (equatorialReflection x) = g x) (θ : ℝ) :
    g (radialFrame (π - θ) 0) = g (radialFrame θ 0) := by
  rw [radialFrame_pi_sub, ← coe_equatorialReflection, hrefl]

/-! ### Axisymmetric functions on the unit sphere -/

/-- The nonnegative integral of an axisymmetric function over the unit sphere. No measurability
hypothesis is needed. -/
theorem lintegral_sphere_of_axisymmetric {g : ℝ^3 → ℝ≥0∞}
    (hrot : IsInvariantUnderAxisRotation g) :
    ∫⁻ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (sin θ) * g (radialFrame θ 0) := by
  calc ∫⁻ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere
      = ∫⁻ p in angleDomain, ENNReal.ofReal (sin p.1) * g (radialFrame p.1 0) := by
        rw [lintegral_sphere_eq_setLIntegral]
        exact lintegral_congr fun p ↦ by
          rw [apply_radialFrame_of_axisymmetric hrot p.1 p.2]
    _ = _ := by
        rw [angleDomain, Measure.volume_eq_prod, ← Measure.prod_restrict,
          lintegral_fun_fst (fun θ ↦ ENNReal.ofReal (sin θ) * g (radialFrame θ 0)),
          Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]

/-- The integral of an axisymmetric vector-valued function over the unit sphere:
`∫_{S²} g dσ = 2π • ∫₀^π sin θ • g (θ, 0) dθ`. No integrability hypothesis is needed. -/
theorem integral_sphere_of_axisymmetric_smul {g : ℝ^3 → E}
    (hrot : IsInvariantUnderAxisRotation g) :
    ∫ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      (2 * π) • ∫ θ in (0 : ℝ)..π, sin θ • g (radialFrame θ 0) := by
  calc ∫ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere
      = ∫ p in angleDomain, sin p.1 • g (radialFrame p.1 0) := by
        rw [integral_sphere_eq_setIntegral]
        exact integral_congr_ae (Filter.Eventually.of_forall fun p ↦ by
          simp only [apply_radialFrame_of_axisymmetric hrot p.1 p.2])
    _ = _ := by
        rw [angleDomain, Measure.volume_eq_prod, ← Measure.prod_restrict,
          integral_fun_fst (fun θ ↦ sin θ • g (radialFrame θ 0)),
          measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le two_pi_pos.le, sub_zero,
          intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo]

/-- The integral of an axisymmetric function over the unit sphere:
`∫_{S²} g dσ = 2π ∫₀^π g (θ, 0) sin θ dθ`. No integrability hypothesis is needed. -/
theorem integral_sphere_of_axisymmetric {g : ℝ^3 → ℝ}
    (hrot : IsInvariantUnderAxisRotation g) :
    ∫ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      2 * π * ∫ θ in (0 : ℝ)..π, g (radialFrame θ 0) * sin θ := by
  rw [integral_sphere_of_axisymmetric_smul hrot]
  simp only [smul_eq_mul, mul_comm (sin _)]

/-- The nonnegative integral over the unit sphere of an axisymmetric function that is even under
the equatorial reflection. No measurability hypothesis is needed. -/
theorem lintegral_sphere_of_axisymmetric_even {g : ℝ^3 → ℝ≥0∞}
    (hrot : IsInvariantUnderAxisRotation g)
    (hrefl : ∀ x, g (equatorialReflection x) = g x) :
    ∫⁻ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      ENNReal.ofReal (4 * π) *
        ∫⁻ θ in Ioo 0 (π / 2), ENNReal.ofReal (sin θ) * g (radialFrame θ 0) := by
  have hsym : ∀ θ, ENNReal.ofReal (sin (π - θ)) * g (radialFrame (π - θ) 0) =
      ENNReal.ofReal (sin θ) * g (radialFrame θ 0) := fun θ ↦ by
    rw [sin_pi_sub, apply_radialFrame_pi_sub_of_even hrefl]
  rw [lintegral_sphere_of_axisymmetric hrot, setLIntegral_Ioo_eq_two_mul_of_symm pi_pos hsym,
    ← mul_assoc, show (4 : ℝ) * π = 2 * π * 2 by ring, ENNReal.ofReal_mul two_pi_pos.le,
    ENNReal.ofReal_ofNat]

/-- The integral over the unit sphere of an axisymmetric vector-valued function that is even
under the equatorial reflection: `∫_{S²} g dσ = 4π • ∫₀^{π/2} sin θ • g (θ, 0) dθ`. No
integrability hypothesis is needed. -/
theorem integral_sphere_of_axisymmetric_even_smul {g : ℝ^3 → E}
    (hrot : IsInvariantUnderAxisRotation g)
    (hrefl : ∀ x, g (equatorialReflection x) = g x) :
    ∫ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      (4 * π) • ∫ θ in (0 : ℝ)..(π / 2), sin θ • g (radialFrame θ 0) := by
  have hsym : ∀ θ, sin (π - θ) • g (radialFrame (π - θ) 0) = sin θ • g (radialFrame θ 0) :=
    fun θ ↦ by rw [sin_pi_sub, apply_radialFrame_pi_sub_of_even hrefl]
  rw [integral_sphere_of_axisymmetric_smul hrot,
    intervalIntegral_eq_two_smul_of_symm pi_pos.le hsym, smul_smul]
  congr 1
  ring

/-- The integral over the unit sphere of an axisymmetric function that is even under the
equatorial reflection: `∫_{S²} g dσ = 4π ∫₀^{π/2} g (θ, 0) sin θ dθ`. No integrability
hypothesis is needed. -/
theorem integral_sphere_of_axisymmetric_even {g : ℝ^3 → ℝ}
    (hrot : IsInvariantUnderAxisRotation g)
    (hrefl : ∀ x, g (equatorialReflection x) = g x) :
    ∫ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      4 * π * ∫ θ in (0 : ℝ)..(π / 2), g (radialFrame θ 0) * sin θ := by
  rw [integral_sphere_of_axisymmetric_even_smul hrot hrefl]
  simp only [smul_eq_mul, mul_comm (sin _)]

/-! ### Functions of the polar angle -/

/-- Rotation about the symmetry axis keeps the polar angle. -/
theorem polarAngle_axisRotation (φ : ℝ) (x : ℝ^3) :
    polarAngle (axisRotation φ x) = polarAngle x := by
  rw [polarAngle, polarAngle, ← axialRotation_apply, axialRotation_apply_two,
    LinearIsometryEquiv.norm_map]

/-- The equatorial reflection takes the polar angle `θ` to `π - θ`. -/
theorem polarAngle_equatorialReflection (x : ℝ^3) :
    polarAngle (equatorialReflection x) = π - polarAngle x := by
  rw [polarAngle, polarAngle, equatorialReflection_apply_two, LinearIsometryEquiv.norm_map,
    neg_div, arccos_neg]

/-- A function of the polar angle alone integrates over the unit sphere as
`∫_{S²} h (θ) dσ = 2π ∫₀^π h θ sin θ dθ`. -/
theorem integral_sphere_comp_polarAngle (h : ℝ → ℝ) :
    ∫ ω : sphere (0 : ℝ^3) 1, h (polarAngle ω) ∂(volume : Measure (ℝ^3)).toSphere =
      2 * π * ∫ θ in (0 : ℝ)..π, h θ * sin θ := by
  rw [integral_sphere_of_axisymmetric (g := fun x ↦ h (polarAngle x))
    (by intro φ x; simp only [polarAngle_axisRotation])]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ ↦ ?_
  rw [uIcc_of_le pi_pos.le] at hθ
  simp only [polarAngle_radialFrame hθ]

/-- A function of the polar angle symmetric about `π / 2` integrates over the unit sphere as
`∫_{S²} h (θ) dσ = 4π ∫₀^{π/2} h θ sin θ dθ`. -/
theorem integral_sphere_comp_polarAngle_of_symm (h : ℝ → ℝ) (hsym : ∀ θ, h (π - θ) = h θ) :
    ∫ ω : sphere (0 : ℝ^3) 1, h (polarAngle ω) ∂(volume : Measure (ℝ^3)).toSphere =
      4 * π * ∫ θ in (0 : ℝ)..(π / 2), h θ * sin θ := by
  rw [integral_sphere_of_axisymmetric_even (g := fun x ↦ h (polarAngle x))
    (by intro φ x; simp only [polarAngle_axisRotation])
    (fun x ↦ by simp only [polarAngle_equatorialReflection, hsym])]
  congr 1
  refine intervalIntegral.integral_congr fun θ hθ ↦ ?_
  rw [uIcc_of_le (by positivity)] at hθ
  simp only [polarAngle_radialFrame ⟨hθ.1, hθ.2.trans (by linarith [pi_pos])⟩]

/-- The nonnegative integral over the unit sphere of a function of the polar angle. -/
theorem lintegral_sphere_comp_polarAngle (h : ℝ → ℝ≥0∞) :
    ∫⁻ ω : sphere (0 : ℝ^3) 1, h (polarAngle ω) ∂(volume : Measure (ℝ^3)).toSphere =
      ENNReal.ofReal (2 * π) * ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (sin θ) * h θ := by
  rw [lintegral_sphere_of_axisymmetric (g := fun x ↦ h (polarAngle x))
    (by intro φ x; simp only [polarAngle_axisRotation])]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ?_
  simp only [polarAngle_radialFrame (Ioo_subset_Icc_self hθ)]

/-- The nonnegative integral over the unit sphere of a function of the polar angle symmetric
about `π / 2`. -/
theorem lintegral_sphere_comp_polarAngle_of_symm (h : ℝ → ℝ≥0∞)
    (hsym : ∀ θ, h (π - θ) = h θ) :
    ∫⁻ ω : sphere (0 : ℝ^3) 1, h (polarAngle ω) ∂(volume : Measure (ℝ^3)).toSphere =
      ENNReal.ofReal (4 * π) * ∫⁻ θ in Ioo 0 (π / 2), ENNReal.ofReal (sin θ) * h θ := by
  rw [lintegral_sphere_of_axisymmetric_even (g := fun x ↦ h (polarAngle x))
    (by intro φ x; simp only [polarAngle_axisRotation])
    (fun x ↦ by simp only [polarAngle_equatorialReflection, hsym])]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ?_
  simp only [polarAngle_radialFrame ⟨hθ.1.le, hθ.2.le.trans (by linarith [pi_pos])⟩]

/-! ### Axisymmetric functions on `ℝ^3` -/

/-- The ball about the origin is invariant under the rotations about the axis. -/
theorem axisRotation_mem_ball_iff (R φ : ℝ) (x : ℝ^3) :
    axisRotation φ x ∈ ball (0 : ℝ^3) R ↔ x ∈ ball (0 : ℝ^3) R := by
  simp only [mem_ball, dist_zero_right]
  rw [show ‖axisRotation φ x‖ = ‖x‖ from (axialRotation φ).norm_map x]

/-- Restricting a rotation-invariant function to a ball about the origin keeps it invariant. -/
theorem _root_.PDE.CoordinateSystems.IsInvariantUnderAxisRotation.indicator_ball {E : Type*}
    [Zero E] {f : ℝ^3 → E} (hf : IsInvariantUnderAxisRotation f) (R : ℝ) :
    IsInvariantUnderAxisRotation ((ball (0 : ℝ^3) R).indicator f) := by
  intro φ x
  by_cases hx : x ∈ ball (0 : ℝ^3) R
  · rw [Set.indicator_of_mem ((axisRotation_mem_ball_iff R φ x).mpr hx),
      Set.indicator_of_mem hx, hf]
  · rw [Set.indicator_of_notMem (fun h ↦ hx ((axisRotation_mem_ball_iff R φ x).mp h)),
      Set.indicator_of_notMem hx]

/-- A function of the distance `‖u x - v x‖` of two equivariant fields is invariant. -/
theorem isInvariantUnderAxisRotation_comp_norm_sub {E : Type*} {u v : ℝ^3 → ℝ^3}
    (hu : IsEquivariantUnderAxisRotation u) (hv : IsEquivariantUnderAxisRotation v)
    (g : ℝ → E) : IsInvariantUnderAxisRotation fun x ↦ g ‖u x - v x‖ := by
  intro φ x
  simp only [hu φ x, hv φ x]
  rw [← axialRotation_apply, ← axialRotation_apply, ← map_sub, LinearIsometryEquiv.norm_map]

/-- A function of the norm of an equivariant field is invariant. -/
theorem isInvariantUnderAxisRotation_comp_norm {E : Type*} {u : ℝ^3 → ℝ^3}
    (hu : IsEquivariantUnderAxisRotation u) (g : ℝ → E) :
    IsInvariantUnderAxisRotation fun x ↦ g ‖u x‖ := by
  intro φ x
  simp only [hu φ x]
  rw [← axialRotation_apply, LinearIsometryEquiv.norm_map]

/-- The points of the meridian of azimuth zero depend continuously on the radius and the polar
angle. -/
theorem continuous_point_meridian : Continuous fun p : ℝ × ℝ ↦ point p.1 p.2 0 :=
  continuous_fst.smul (continuous_radialFrame.comp (continuous_snd.prodMk continuous_const))

/-- At a fixed radius the meridian points depend continuously on the polar angle. -/
theorem continuous_point_meridian_angle (r : ℝ) : Continuous fun θ : ℝ ↦ point r θ 0 :=
  continuous_point_meridian.comp (continuous_const.prodMk continuous_id)

/-- The nonnegative integral of a measurable axisymmetric function over `ℝ^3` in the radius and
the polar angle. -/
theorem lintegral_volume_of_axisymmetric {f : ℝ^3 → ℝ≥0∞}
    (hrot : IsInvariantUnderAxisRotation f) (hf : Measurable f) :
    ∫⁻ x, f x = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π,
      ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) := by
  rw [lintegral_eq_lintegral_point hf, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun r ↦ ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun θ ↦ ?_
  have hφ : ∀ φ, f (point r θ φ) = f (point r θ 0) := fun φ ↦ by
    rw [← axisRotation_point, hrot]
  rw [lintegral_congr fun φ ↦ by rw [hφ φ], setLIntegral_const, Real.volume_Ioo, sub_zero,
    mul_comm]

/-- The integral of an integrable axisymmetric vector-valued function over `ℝ^3` in the radius
and the polar angle: `∫ f = 2π • ∫₀^∞ ∫₀^π (r² sin θ) • f (r, θ, 0) dθ dr`. Integrability
cannot be dropped: without it the left side is `0` while the right side can be nonzero. -/
theorem integral_volume_of_axisymmetric_smul {f : ℝ^3 → E}
    (hrot : IsInvariantUnderAxisRotation f) (hf : Integrable f) :
    ∫ x, f x =
      (2 * π) • ∫ r in Ioi 0, ∫ θ in (0 : ℝ)..π, (r ^ 2 * sin θ) • f (point r θ 0) := by
  rw [PDE.Analysis.integral_polar_addHaar_iterated volume f hf, finrank_euclideanSpace_fin,
    ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r ↦ ?_)
  have hr : IsInvariantUnderAxisRotation fun x ↦ f (r • x) := fun φ x ↦ by
    simp only
    rw [← axisRotation_smul, hrot]
  have hθ : ∫ θ in (0 : ℝ)..π, (r ^ 2 * sin θ) • f (point r θ 0) =
      r ^ 2 • ∫ θ in (0 : ℝ)..π, sin θ • f (r • radialFrame θ 0) := by
    rw [← intervalIntegral.integral_smul]
    congr 1
    funext θ
    rw [point, mul_smul]
  dsimp only
  rw [integral_sphere_of_axisymmetric_smul hr, hθ, smul_comm]

/-- The integral of an integrable axisymmetric function over `ℝ^3` in the radius and the polar
angle: `∫ f = 2π ∫₀^∞ ∫₀^π f (r, θ, 0) r² sin θ dθ dr`. Integrability cannot be dropped:
without it the left side is `0` while the right side can be nonzero. -/
theorem integral_volume_of_axisymmetric {f : ℝ^3 → ℝ}
    (hrot : IsInvariantUnderAxisRotation f) (hf : Integrable f) :
    ∫ x, f x = 2 * π * ∫ r in Ioi 0, ∫ θ in (0 : ℝ)..π, f (point r θ 0) * r ^ 2 * sin θ := by
  rw [integral_volume_of_axisymmetric_smul hrot hf, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun r ↦
    intervalIntegral.integral_congr fun θ _ ↦ ?_)
  simp only [smul_eq_mul]
  ring

/-- The integral over the ball of radius `R` of an axisymmetric vector-valued function integrable
on it: `∫_{B_R} f = 2π • ∫₀^R ∫₀^π (r² sin θ) • f (r, θ, 0) dθ dr`. -/
theorem setIntegral_ball_of_axisymmetric_smul {f : ℝ^3 → E} {R : ℝ}
    (hrot : IsInvariantUnderAxisRotation f) (hf : IntegrableOn f (ball 0 R)) :
    ∫ x in ball (0 : ℝ^3) R, f x =
      (2 * π) • ∫ r in Ioo 0 R, ∫ θ in (0 : ℝ)..π, (r ^ 2 * sin θ) • f (point r θ 0) := by
  have hball : ∀ φ x, axisRotation φ x ∈ ball (0 : ℝ^3) R ↔ x ∈ ball (0 : ℝ^3) R :=
    fun φ x ↦ by
      rw [mem_ball_zero_iff, mem_ball_zero_iff, ← axialRotation_apply,
        LinearIsometryEquiv.norm_map]
  have hrot' : IsInvariantUnderAxisRotation ((ball (0 : ℝ^3) R).indicator f) := fun φ x ↦ by
    by_cases h : x ∈ ball (0 : ℝ^3) R
    · rw [indicator_of_mem ((hball φ x).2 h), indicator_of_mem h, hrot]
    · rw [indicator_of_notMem (fun h' ↦ h ((hball φ x).1 h')), indicator_of_notMem h]
  rw [← integral_indicator measurableSet_ball,
    integral_volume_of_axisymmetric_smul hrot' (hf.integrable_indicator measurableSet_ball),
    ← Ioi_inter_Iio, ← setIntegral_indicator measurableSet_Iio]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
  have hmem : ∀ θ, point r θ 0 ∈ ball (0 : ℝ^3) R ↔ r < R := fun θ ↦ by
    rw [mem_ball_zero_iff, norm_point hr]
  by_cases hrR : r < R
  · rw [indicator_of_mem (show r ∈ Iio R from hrR)]
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    simp only [indicator_of_mem ((hmem θ).2 hrR)]
  · rw [indicator_of_notMem (show r ∉ Iio R from hrR)]
    simp only [indicator_of_notMem (fun h ↦ hrR ((hmem _).1 h)), smul_zero,
      intervalIntegral.integral_zero]

/-- The integral over the ball of radius `R` of an axisymmetric function integrable on it:
`∫_{B_R} f = 2π ∫₀^R ∫₀^π f (r, θ, 0) r² sin θ dθ dr`. -/
theorem setIntegral_ball_of_axisymmetric {f : ℝ^3 → ℝ} {R : ℝ}
    (hrot : IsInvariantUnderAxisRotation f) (hf : IntegrableOn f (ball 0 R)) :
    ∫ x in ball (0 : ℝ^3) R, f x =
      2 * π * ∫ r in Ioo 0 R, ∫ θ in (0 : ℝ)..π, f (point r θ 0) * r ^ 2 * sin θ := by
  rw [setIntegral_ball_of_axisymmetric_smul hrot hf, smul_eq_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun r _ ↦
    intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp only [smul_eq_mul]
  ring

end PDE.CoordinateSystems.Spherical
