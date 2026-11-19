/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityHolder
import PDE.Fluid.Incompressible.HalfPlane.WeightedStreamBounds
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# The velocity gradient of a vorticity vanishing near the point

Let `ω` be a continuous compactly supported vorticity, Hölder on the closed upper half-plane, that
vanishes on the closed upper half-plane inside the disc `B(x, δ)` around a point `x` of the open
upper half-plane. Its odd extension `W` then vanishes on all of `B(x, δ)`, since the reflection
`y* ` of a point `y` below the boundary is closer to `x` than `y`. The principal value defining the
velocity gradient is therefore an absolutely convergent integral.

The integrals are stated as bounds `B` on lower Lebesgue integrals, so no integrability of the
weighted vorticity is assumed. These are the bounds of the part of a vorticity away from the point
in the scale-adapted estimates of the velocity gradient.

## Main results

* `norm_sub_le_norm_sub_reflect`: for `x, y` in the open upper half-plane the image `y*` is
  farther from `x` than `y`.
* `IsSingularKernel.singularIntegral_eq_integral_of_eq_zero`: a singular integral of a source
  vanishing on `B(x, δ)` is the absolutely convergent integral.
* `abs_partialDeriv_halfPlaneVelocity_le_of_eq_zero`:
  `|∂ᵢuₖ(x)| ≤ (10/π) ∫_{ℝ²₊} |ω(y)|/|x - y|² dy`.
* `abs_partialDeriv_halfPlaneVelocity_sub_le_of_eq_zero`: for `z` in the open upper half-plane with
  `2|x - z| ≤ δ`, `|∂ᵢuₖ(x) - ∂ᵢuₖ(z)| ≤ (10/π) |x - z| ∫_{ℝ²₊} |ω(y)|/|x - y|³ dy`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open GreenFunction PotentialTheory.Planar SobolevSpace
open PDE.Analysis (evenReflection halfPlaneFold_mem norm_sub_halfPlaneFold_le)

namespace IncompressibleFlow

variable {ω : ℝ^2 → ℝ} {x : ℝ^2} {δ : ℝ}

/-- For `x, y` in the open upper half-plane the image `y*` is farther from `x` than `y`. -/
theorem norm_sub_le_norm_sub_reflect {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    ‖x - y‖ ≤ ‖x - HalfSpace.reflect 2 y‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_fin_two,
      EuclideanSpace.norm_sq_fin_two]
  simp only [PiLp.sub_apply, reflect_two_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith

/-- A singular integral of a source vanishing on `B(x, δ)` is the absolutely convergent
integral. -/
theorem _root_.PotentialTheory.Planar.IsSingularKernel.singularIntegral_eq_integral_of_eq_zero
    {K : ℝ^2 → ℝ} {A : ℝ} (hK : IsSingularKernel K A) {f : ℝ^2 → ℝ} (hf : Integrable f) (hδ : 0 < δ)
    (h0 : ∀ y ∈ ball x δ, f y = 0) :
    Integrable (fun y ↦ K (x - y) * f y) ∧ singularIntegral K f x = ∫ y, K (x - y) * f y := by
  have hball : IntegrableOn (fun y ↦ K (x - y) * f y) (ball x δ) :=
    (integrableOn_zero).congr_fun (fun y hy ↦ by simp [h0 y hy]) measurableSet_ball
  have hcompl : IntegrableOn (fun y ↦ K (x - y) * f y) (ball x δ)ᶜ :=
    hK.integrableOn_mul_of_le hf x measurableSet_ball.compl hδ fun y hy ↦
      le_norm_sub_of_mem_compl_ball hy
  have hint : Integrable (fun y ↦ K (x - y) * f y) := by
    have := hball.union hcompl
    rwa [union_compl_self, integrableOn_univ] at this
  refine ⟨hint, ?_⟩
  have hx0 : f x = 0 := h0 x (mem_ball_self hδ)
  unfold singularIntegral
  simp only [hx0, sub_zero]
  exact integral_add_compl measurableSet_ball hint

/-- Where `ω` vanishes on the closed upper half-plane inside `B(x, δ)`, so does its even
extension on the whole disc. -/
private theorem evenReflection_eq_zero_of_mem_ball (hx : 0 ≤ x 1)
    (h0 : ∀ y, 0 ≤ y 1 → ‖x - y‖ < δ → ω y = 0) : ∀ y ∈ ball x δ, evenReflection ω y = 0 :=
  fun y hy ↦ h0 _ (halfPlaneFold_mem y)
    ((norm_sub_halfPlaneFold_le hx y).trans_lt (by rwa [mem_ball, dist_comm, dist_eq_norm] at hy))

/-- The odd extension of a vorticity vanishing near `x` vanishes on `B(x, δ)`. -/
private theorem oddHalfSpaceExtension_eq_zero (hx : 0 ≤ x 1)
    (h0 : ∀ y, 0 ≤ y 1 → ‖x - y‖ < δ → ω y = 0) {y : ℝ^2} (hy : ‖x - y‖ < δ) :
    oddHalfSpaceExtension ω y = 0 := by
  unfold oddHalfSpaceExtension
  by_cases hyu : y ∈ HalfSpace.upper 2
  · have hyl : y ∉ HalfSpace.lower 2 := fun h ↦ by
      have h1 : 0 < y 1 := hyu
      have h2 : y 1 < 0 := h
      linarith
    simp [hyu, hyl, h0 y (le_of_lt hyu) hy]
  · by_cases hyl : y ∈ HalfSpace.lower 2
    · have hr : 0 ≤ (HalfSpace.reflect 2 y) 1 := by
        have h2 : y 1 < 0 := hyl
        rw [reflect_two_eq]
        simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        linarith
      have hd : ‖x - HalfSpace.reflect 2 y‖ ≤ ‖x - y‖ := by
        have := norm_sub_le_norm_sub_reflect hx hr
        rwa [HalfSpace.reflect_involutive] at this
      simp [hyu, hyl, h0 _ hr (hd.trans_lt hy)]
    · simp [hyu, hyl]

/-- `∫⁻ c F ≤ c (2 B)` from `∫⁻ F ≤ 2 B` for `c ≥ 0`. -/
private theorem lintegral_const_mul_le {c : ℝ} (hc : 0 ≤ c) {F : ℝ^2 → ℝ} {B : ℝ}
    (h : ∫⁻ y, ENNReal.ofReal (F y) ≤ 2 * ENNReal.ofReal B) :
    ∫⁻ y, ENNReal.ofReal (c * F y) ≤ ENNReal.ofReal (c * (2 * B)) := by
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  by_cases hB : 0 ≤ B
  · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
  · have hB' : ENNReal.ofReal B = 0 := ENNReal.ofReal_of_nonpos (le_of_not_ge hB)
    rw [hB', mul_zero, nonpos_iff_eq_zero] at h
    rw [h, mul_zero]
    exact bot_le

variable (hω : Continuous ω) (hc : HasCompactSupport ω)
include hω hc

/-- The half-plane singular integral of a vorticity vanishing near `x` is the absolutely
convergent integral against the odd extension. -/
private theorem halfPlaneSingularIntegral_eq_integral {K : ℝ^2 → ℝ} {A : ℝ}
    (hK : IsSingularKernel K A) (hx : 0 < x 1) (hδ : 0 < δ)
    (h0 : ∀ y, 0 ≤ y 1 → ‖x - y‖ < δ → ω y = 0) :
    Integrable (fun y ↦ K (x - y) * oddHalfSpaceExtension ω y) ∧
      halfPlaneSingularIntegral K ω x = ∫ y, K (x - y) * oddHalfSpaceExtension ω y := by
  have hE := integrable_evenReflection hω hc
  obtain ⟨hint, heq⟩ := hK.singularIntegral_eq_integral_of_eq_zero hE hδ
    (evenReflection_eq_zero_of_mem_ball hx.le h0)
  have hae : (fun y ↦ K (x - y) * oddHalfSpaceExtension ω y) =ᵐ[volume]
      fun y ↦ K (x - y) * evenReflection ω y -
        2 * {y : ℝ^2 | y 1 < 0}.indicator (fun y ↦ K (x - y) * evenReflection ω y) y := by
    filter_upwards [oddHalfSpaceExtension_ae_eq ω] with y hy
    rw [hy]
    by_cases hyl : y ∈ {y : ℝ^2 | y 1 < 0}
    · simp only [indicator_of_mem hyl]; ring
    · simp only [indicator_of_notMem hyl]; ring
  have hint2 : Integrable fun y ↦
      2 * {y : ℝ^2 | y 1 < 0}.indicator (fun y ↦ K (x - y) * evenReflection ω y) y :=
    (hint.indicator measurableSet_lower).const_mul 2
  refine ⟨(hint.sub hint2).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub hint hint2, integral_const_mul,
    integral_indicator measurableSet_lower, halfPlaneSingularIntegral, heq]

omit hc in
/-- The weighted mass of the odd extension is at most twice that of the vorticity on the upper
half-plane, for any power of the distance to a point near which the vorticity vanishes. -/
private theorem lintegral_oddHalfSpaceExtension_le (hx : 0 < x 1) (hδ : 0 < δ)
    (h0 : ∀ y, 0 ≤ y 1 → ‖x - y‖ < δ → ω y = 0) (p : ℕ) :
    ∫⁻ y, ENNReal.ofReal (|oddHalfSpaceExtension ω y| / ‖x - y‖ ^ p) ≤
      2 * ∫⁻ y in HalfSpace.upper 2, ENNReal.ofReal (|ω y| / ‖x - y‖ ^ p) := by
  set G := fun y ↦ ENNReal.ofReal (|ω y| / ‖x - y‖ ^ p)
  have hωm : Measurable ω := hω.measurable
  have hGm : Measurable G := by fun_prop
  have hsplit : ∀ y, ENNReal.ofReal (|oddHalfSpaceExtension ω y| / ‖x - y‖ ^ p) ≤
      (HalfSpace.upper 2).indicator G y +
        (HalfSpace.lower 2).indicator
          (fun y ↦ ENNReal.ofReal (|ω (HalfSpace.reflect 2 y)| / ‖x - y‖ ^ p)) y := by
    intro y
    unfold oddHalfSpaceExtension
    by_cases hyu : y ∈ HalfSpace.upper 2
    · have hyl : y ∉ HalfSpace.lower 2 := fun h ↦ by
        have h1 : 0 < y 1 := hyu
        have h2 : y 1 < 0 := h
        linarith
      simp [hyu, hyl, G]
    · by_cases hyl : y ∈ HalfSpace.lower 2
      · simp [hyu, hyl]
      · simp [hyu, hyl]
  have hlow : ∫⁻ y, (HalfSpace.lower 2).indicator
        (fun y ↦ ENNReal.ofReal (|ω (HalfSpace.reflect 2 y)| / ‖x - y‖ ^ p)) y ≤
      ∫⁻ y in HalfSpace.upper 2, G y := by
    rw [lintegral_indicator (HalfSpace.measurableSet_lower 2)]
    have hmp := HalfSpace.measurePreserving_reflect_restrict_lower (n := 2)
    have hemb : MeasurableEmbedding (HalfSpace.reflect 2) :=
      (HalfSpace.reflectLinearIsometryEquiv 2).toMeasurableEquiv.measurableEmbedding
    have hcomp := hmp.lintegral_comp_emb hemb
      (fun y ↦ ENNReal.ofReal (|ω y| / ‖x - HalfSpace.reflect 2 y‖ ^ p))
    simp only [HalfSpace.reflect_involutive 2 _] at hcomp
    rw [hcomp]
    refine setLIntegral_mono' (HalfSpace.measurableSet_upper 2) fun y hy ↦ ?_
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hyx : ‖x - y‖ < δ
    · simp [h0 y (le_of_lt hy) hyx]
    · have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le hδ (not_lt.mp hyx)
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
        (pow_le_pow_left₀ hpos.le (norm_sub_le_norm_sub_reflect hx.le (le_of_lt hy)) p)
  calc ∫⁻ y, ENNReal.ofReal (|oddHalfSpaceExtension ω y| / ‖x - y‖ ^ p)
      ≤ ∫⁻ y, ((HalfSpace.upper 2).indicator G y + (HalfSpace.lower 2).indicator
          (fun y ↦ ENNReal.ofReal (|ω (HalfSpace.reflect 2 y)| / ‖x - y‖ ^ p)) y) :=
        lintegral_mono hsplit
    _ = (∫⁻ y, (HalfSpace.upper 2).indicator G y) + ∫⁻ y, (HalfSpace.lower 2).indicator
          (fun y ↦ ENNReal.ofReal (|ω (HalfSpace.reflect 2 y)| / ‖x - y‖ ^ p)) y :=
        lintegral_add_left (hGm.indicator (HalfSpace.measurableSet_upper 2)) _
    _ ≤ (∫⁻ y in HalfSpace.upper 2, G y) + ∫⁻ y in HalfSpace.upper 2, G y := by
        rw [lintegral_indicator (HalfSpace.measurableSet_upper 2)]
        exact add_le_add le_rfl hlow
    _ = 2 * ∫⁻ y in HalfSpace.upper 2, G y := by rw [two_mul]

variable {M α : ℝ}

/-- **The velocity gradient of a vorticity vanishing near the point.** If `ω` vanishes on the
closed upper half-plane inside `B(x, δ)` and `∫⁻_{ℝ²₊} |ω(y)|/|x - y|² ≤ B`, then
`|∂ᵢuₖ(x)| ≤ (10/π) B`. -/
theorem abs_partialDeriv_halfPlaneVelocity_le_of_eq_zero (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) (hx : 0 < x 1)
    (hδ : 0 < δ) (h0 : ∀ y, 0 ≤ y 1 → ‖x - y‖ < δ → ω y = 0) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∫⁻ y in HalfSpace.upper 2, ENNReal.ofReal (|ω y| / ‖x - y‖ ^ 2) ≤ ENNReal.ofReal B)
    (i k : Fin 2) :
    |(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x| ≤ 10 / Real.pi * B := by
  obtain ⟨j, a, b, ha, -, hab⟩ := halfPlaneVelocityGradient_eq_combination i k
  have hK := isSingularKernel_hessianKernel 0 j
  obtain ⟨-, heq⟩ := halfPlaneSingularIntegral_eq_integral hω hc hK hx hδ h0
  have hωx : ω x = 0 := h0 x hx.le (by simpa using hδ)
  rw [partialDeriv_halfPlaneVelocity hω hc hα hα1 hM i k hx, hab, hωx, mul_zero, add_zero, heq]
  have hlin := lintegral_oddHalfSpaceExtension_le hω hx hδ h0 2
  have hI : |∫ y, hessianKernel 0 j (x - y) * oddHalfSpaceExtension ω y| ≤ 10 * B := by
    have h := abs_setIntegral_le_of_lintegral_le (S := univ) (T := univ) MeasurableSet.univ
      subset_rfl (F := fun y ↦ hessianKernel 0 j (x - y) * oddHalfSpaceExtension ω y)
      (g := fun y ↦ 5 * (|oddHalfSpaceExtension ω y| / ‖x - y‖ ^ 2)) (B := 10 * B)
      (by positivity) ?_ ?_
    · rwa [setIntegral_univ] at h
    · intro y _
      by_cases hy : ‖x - y‖ < δ
      · simp [oddHalfSpaceExtension_eq_zero hx.le h0 hy]
      · have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le hδ (not_lt.mp hy)
        rw [abs_mul]
        have hk := hK.abs_le_of_le hpos (le_refl ‖x - y‖)
        calc |hessianKernel 0 j (x - y)| * |oddHalfSpaceExtension ω y|
            ≤ 5 / ‖x - y‖ ^ 2 * |oddHalfSpaceExtension ω y| := by gcongr
          _ = 5 * (|oddHalfSpaceExtension ω y| / ‖x - y‖ ^ 2) := by ring
    · simp only [Measure.restrict_univ]
      rw [show (10 : ℝ) * B = 5 * (2 * B) by ring]
      exact lintegral_const_mul_le (by norm_num) (hlin.trans (by gcongr))
  calc |a * ∫ y, hessianKernel 0 j (x - y) * oddHalfSpaceExtension ω y|
      = |a| * |∫ y, hessianKernel 0 j (x - y) * oddHalfSpaceExtension ω y| := abs_mul _ _
    _ ≤ 1 / Real.pi * (10 * B) := by gcongr
    _ = 10 / Real.pi * B := by ring

/-- **Lipschitz bound of the velocity gradient of a vorticity vanishing near the point.** If `ω`
vanishes on the closed upper half-plane inside `B(x, δ)`, `z` lies in the open upper half-plane with
`2|x - z| ≤ δ` and `∫⁻_{ℝ²₊} |ω(y)|/|x - y|³ ≤ B`, then `|∂ᵢuₖ(x) - ∂ᵢuₖ(z)| ≤ (10/π) |x - z| B`. -/
theorem abs_partialDeriv_halfPlaneVelocity_sub_le_of_eq_zero (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α) (hx : 0 < x 1)
    (hδ : 0 < δ) (h0 : ∀ y, 0 ≤ y 1 → ‖x - y‖ < δ → ω y = 0) {z : ℝ^2} (hz : 0 < z 1)
    (hxz : 2 * ‖x - z‖ ≤ δ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∫⁻ y in HalfSpace.upper 2, ENNReal.ofReal (|ω y| / ‖x - y‖ ^ 3) ≤ ENNReal.ofReal B)
    (i k : Fin 2) :
    |(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x - (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) z| ≤
      10 / Real.pi * ‖x - z‖ * B := by
  by_cases hxz0 : x = z
  · subst hxz0; simp only [sub_self, abs_zero, norm_zero]; positivity
  have hd : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz0)
  have hδ2 : 0 < δ / 2 := by linarith
  have h0z : ∀ y, 0 ≤ y 1 → ‖z - y‖ < δ / 2 → ω y = 0 := fun y hy hzy ↦
    h0 y hy (by
      calc ‖x - y‖ ≤ ‖x - z‖ + ‖z - y‖ := norm_sub_le_norm_sub_add_norm_sub x z y
        _ < δ := by linarith)
  obtain ⟨j, a, b, ha, -, hab⟩ := halfPlaneVelocityGradient_eq_combination i k
  have hK := isSingularKernel_hessianKernel 0 j
  obtain ⟨hintx, heqx⟩ := halfPlaneSingularIntegral_eq_integral hω hc hK hx hδ h0
  obtain ⟨hintz, heqz⟩ := halfPlaneSingularIntegral_eq_integral hω hc hK hz hδ2 h0z
  have hωx : ω x = 0 := h0 x hx.le (by simpa using hδ)
  have hωz : ω z = 0 := h0z z hz.le (by simpa using hδ2)
  rw [partialDeriv_halfPlaneVelocity hω hc hα hα1 hM i k hx,
    partialDeriv_halfPlaneVelocity hω hc hα hα1 hM i k hz, hab, hab, hωx, hωz, mul_zero,
    add_zero, add_zero, heqx, heqz, ← mul_sub, ← integral_sub hintx hintz]
  have hlin := lintegral_oddHalfSpaceExtension_le hω hx hδ h0 3
  have hI : |∫ y, (hessianKernel 0 j (x - y) * oddHalfSpaceExtension ω y -
      hessianKernel 0 j (z - y) * oddHalfSpaceExtension ω y)| ≤ ‖x - z‖ * (10 * B) := by
    have h := abs_setIntegral_le_of_lintegral_le (S := univ) (T := univ) MeasurableSet.univ
      subset_rfl (F := fun y ↦ hessianKernel 0 j (x - y) * oddHalfSpaceExtension ω y -
        hessianKernel 0 j (z - y) * oddHalfSpaceExtension ω y)
      (g := fun y ↦ 5 * ‖x - z‖ * (|oddHalfSpaceExtension ω y| / ‖x - y‖ ^ 3))
      (B := ‖x - z‖ * (10 * B)) (by positivity) ?_ ?_
    · rwa [setIntegral_univ] at h
    · intro y _
      by_cases hy : ‖x - y‖ < δ
      · simp [oddHalfSpaceExtension_eq_zero hx.le h0 hy]
      · have hle : δ ≤ ‖x - y‖ := not_lt.mp hy
        have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le hδ hle
        rw [← sub_mul, abs_mul]
        have hk := hK.abs_sub_sub_le x z y (hxz.trans hle)
        calc |hessianKernel 0 j (x - y) - hessianKernel 0 j (z - y)| *
              |oddHalfSpaceExtension ω y|
            ≤ 5 * ‖x - z‖ / ‖x - y‖ ^ 3 * |oddHalfSpaceExtension ω y| := by gcongr
          _ = 5 * ‖x - z‖ * (|oddHalfSpaceExtension ω y| / ‖x - y‖ ^ 3) := by ring
    · simp only [Measure.restrict_univ]
      rw [show ‖x - z‖ * (10 * B) = 5 * ‖x - z‖ * (2 * B) by ring]
      exact lintegral_const_mul_le (by positivity) (hlin.trans (by gcongr))
  calc |a * ∫ y, (hessianKernel 0 j (x - y) * oddHalfSpaceExtension ω y -
        hessianKernel 0 j (z - y) * oddHalfSpaceExtension ω y)|
      = |a| * |∫ y, (hessianKernel 0 j (x - y) * oddHalfSpaceExtension ω y -
        hessianKernel 0 j (z - y) * oddHalfSpaceExtension ω y)| := abs_mul _ _
    _ ≤ 1 / Real.pi * (‖x - z‖ * (10 * B)) := by gcongr
    _ = 10 / Real.pi * ‖x - z‖ * B := by ring

end IncompressibleFlow
