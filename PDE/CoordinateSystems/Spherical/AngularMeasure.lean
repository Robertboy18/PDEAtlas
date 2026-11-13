/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical
public import PDE.CoordinateSystems.Spherical.Integration
import PDE.Analysis.Integration.Polar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Lebesgue measure and the sphere measure in spherical angles

The spherical point of radius `r`, polar angle `θ` and azimuthal angle `φ` is
`point r θ φ = r • radialFrame θ φ`. Lebesgue measure on `ℝ^3` is `r² sin θ dr dθ dφ` on
`(0, ∞) × (0, π) × (0, 2π)`, and the sphere measure induced by volume is the image of
`sin θ dθ dφ` on the open rectangle `(0, π) × (0, 2π)` under `(θ, φ) ↦ radialFrame θ φ`.

The volume formula composes planar polar coordinates in the first two coordinates with polar
coordinates in the meridian half-plane. Testing it against functions of the form
`1_{‖x‖ < 1} g (x / ‖x‖)` and comparing with the disintegration of volume into sphere measure
and `r² dr` identifies the sphere measure. Since the angle map is a measurable embedding of the
rectangle, the integral formulas over the sphere need no measurability hypothesis in their
rectangle form; the iterated forms need integrability or measurability for Fubini's theorem.

## Main results

* `lintegral_eq_lintegral_point`: `∫⁻ x, f x = ∫⁻ r θ φ, r² sin θ f (point r θ φ)`.
* `toSphere_eq_map_anglePoint`: the sphere measure is the image of `angleMeasure`.
* `lintegral_sphere_eq_setLIntegral`, `integral_sphere_eq_setIntegral`,
  `integrable_sphere_iff`: integrals over the sphere as integrals over the angle rectangle.
* `integral_sphere_eq_polar`, `integral_sphere_eq_polar_smul`, `lintegral_sphere_eq_polar`:
  the iterated angular formulas.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open MeasureTheory Set Metric Real
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Lebesgue measure in spherical coordinates -/

/-- The point `!₂[a, b, c]` of `ℝ^3` depends continuously on its coordinates. -/
private theorem continuous_cartesianPoint :
    Continuous fun v : ℝ × ℝ × ℝ ↦ !₂[v.1, v.2.1, v.2.2] := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp <;> fun_prop

private theorem cartesianPoint_eq_point (r θ φ : ℝ) :
    !₂[r * sin θ * cos φ, r * sin θ * sin φ, r * cos θ] = point r θ φ := by
  ext i
  fin_cases i <;> simp [point, radialFrame] <;> ring

/-- Lebesgue measure on `ℝ^3` is the product of Lebesgue measures in the coordinates
`(x₂, (x₀, x₁))`. -/
private theorem lintegral_eq_lintegral_cartesian (f : ℝ^3 → ℝ≥0∞) :
    ∫⁻ x, f x = ∫⁻ p : ℝ × (ℝ × ℝ), f !₂[p.2.1, p.2.2, p.1] := by
  let e : ℝ × (ℝ × ℝ) ≃ᵐ ℝ^3 :=
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow.symm).trans
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) (Fin.last 2)).symm.trans
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))
  have he : MeasurePreserving e volume volume :=
    ((MeasurePreserving.id volume).prod ((volume_preserving_finTwoArrow ℝ).symm _)).trans
      (((measurePreserving_piFinSuccAbove (fun _ : Fin 3 ↦ (volume : Measure ℝ))
        (Fin.last 2)).symm _).trans (PiLp.volume_preserving_toLp (Fin 3)))
  rw [← he.lintegral_comp_emb e.measurableEmbedding]
  congr 1
  funext p
  congr 1
  ext i
  fin_cases i <;> rfl

/-- A `2π`-periodic function has the same integral over `(-π, π)` and `(0, 2π)`. -/
private theorem setLIntegral_Ioo_neg_pi_pi {G : ℝ → ℝ≥0∞} (hG : Function.Periodic G (2 * π)) :
    ∫⁻ φ in Ioo (-π) π, G φ = ∫⁻ φ in Ioo 0 (2 * π), G φ := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  have h₁ := AddCircle.lintegral_preimage (2 * π) (-π) hG.lift
  have h₂ := AddCircle.lintegral_preimage (2 * π) 0 hG.lift
  simp only [Function.Periodic.lift_coe] at h₁ h₂
  rw [show -π + 2 * π = π by ring] at h₁
  rw [zero_add] at h₂
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, setLIntegral_congr Ioo_ae_eq_Ioc, h₁, h₂]

/-- Polar coordinates in the plane, with the angle in `(0, 2π)`. -/
private theorem lintegral_plane_polar {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ q, F q = ∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ *
      ∫⁻ φ in Ioo 0 (2 * π), F (ρ * cos φ, ρ * sin φ) := by
  rw [← lintegral_comp_polarCoord_symm F, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod]
  · refine lintegral_congr fun ρ ↦ ?_
    simp only [polarCoord_symm_apply, smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    apply setLIntegral_Ioo_neg_pi_pi
    intro φ
    simp only [cos_add_two_pi, sin_add_two_pi]
  · apply Measurable.aemeasurable
    apply Measurable.smul measurable_fst.ennreal_ofReal
    exact hF.comp continuous_polarCoord_symm.measurable

/-- Polar coordinates `(c, ρ) = (r cos θ, r sin θ)` in the half-plane `ρ > 0`, iterated. -/
private theorem lintegral_halfPlane_polar_iterated {K : ℝ × ℝ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ c, ∫⁻ ρ in Ioi 0, K (c, ρ) = ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π,
      ENNReal.ofReal r * K (r * cos θ, r * sin θ) := by
  have hU : MeasurableSet {q : ℝ × ℝ | 0 < q.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hpolar : Measurable fun p : ℝ × ℝ ↦ (p.1 * cos p.2, p.1 * sin p.2) := by
    apply Continuous.measurable
    fun_prop
  calc ∫⁻ c, ∫⁻ ρ in Ioi 0, K (c, ρ)
      = ∫⁻ q in {q : ℝ × ℝ | 0 < q.2}, K q := by
        rw [← lintegral_indicator hU, Measure.volume_eq_prod,
          lintegral_prod _ (hK.indicator hU).aemeasurable]
        refine lintegral_congr fun c ↦ ?_
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr fun ρ ↦ ?_
        by_cases hρ : 0 < ρ <;> simp [indicator, hρ]
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo 0 π,
          ENNReal.ofReal p.1 * K (p.1 * cos p.2, p.1 * sin p.2) :=
        PDE.Analysis.lintegral_upperHalfPlane_polar K
    _ = _ := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
        exact (measurable_fst.ennreal_ofReal.mul (hK.comp hpolar)).aemeasurable

/-- Lebesgue measure on `ℝ^3` in spherical coordinates: the density is `r² sin θ` on
`(0, ∞) × (0, π) × (0, 2π)`. -/
theorem lintegral_eq_lintegral_point {f : ℝ^3 → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π, ∫⁻ φ in Ioo 0 (2 * π),
      ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ φ) := by
  have hfc : Measurable fun v : ℝ × ℝ × ℝ ↦ f !₂[v.1, v.2.1, v.2.2] :=
    hf.comp continuous_cartesianPoint.measurable
  let H : ℝ × ℝ → ℝ≥0∞ := fun q ↦
    ∫⁻ φ in Ioo 0 (2 * π), f !₂[q.2 * cos φ, q.2 * sin φ, q.1]
  have hH : Measurable H := by
    apply Measurable.lintegral_prod_right'
      (f := fun z : (ℝ × ℝ) × ℝ ↦ f !₂[z.1.2 * cos z.2, z.1.2 * sin z.2, z.1.1])
    exact hfc.comp (f := fun z : (ℝ × ℝ) × ℝ ↦ (z.1.2 * cos z.2, z.1.2 * sin z.2, z.1.1))
      (by apply Continuous.measurable; fun_prop)
  calc ∫⁻ x, f x = ∫⁻ c, ∫⁻ q : ℝ × ℝ, f !₂[q.1, q.2, c] := by
        rw [lintegral_eq_lintegral_cartesian, Measure.volume_eq_prod, lintegral_prod]
        exact (hfc.comp (f := fun p : ℝ × ℝ × ℝ ↦ (p.2.1, p.2.2, p.1))
          (by apply Continuous.measurable; fun_prop)).aemeasurable
    _ = ∫⁻ c, ∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * H (c, ρ) := by
        refine lintegral_congr fun c ↦ ?_
        exact lintegral_plane_polar (F := fun q ↦ f !₂[q.1, q.2, c])
          (hfc.comp (f := fun q : ℝ × ℝ ↦ (q.1, q.2, c))
            (by apply Continuous.measurable; fun_prop))
    _ = ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π, ENNReal.ofReal r *
          (ENNReal.ofReal (r * sin θ) * H (r * cos θ, r * sin θ)) :=
        lintegral_halfPlane_polar_iterated (K := fun q ↦ ENNReal.ofReal q.2 * H q)
          (measurable_snd.ennreal_ofReal.mul hH)
    _ = _ := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
        refine lintegral_congr fun θ ↦ ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hr),
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun φ ↦ ?_
        rw [← cartesianPoint_eq_point]
        congr 2
        ring

/-! ### The sphere measure in spherical angles -/

/-- For measurable `g`, the sphere measure is `sin θ dθ dφ` in iterated form. -/
private theorem lintegral_sphere_eq_polar_of_measurable {g : ℝ^3 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω : sphere (0 : ℝ^3) 1, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      ∫⁻ θ in Ioo 0 π, ∫⁻ φ in Ioo 0 (2 * π),
        ENNReal.ofReal (sin θ) * g (radialFrame θ φ) := by
  set I := ∫⁻ θ in Ioo 0 π, ∫⁻ φ in Ioo 0 (2 * π), ENNReal.ofReal (sin θ) * g (radialFrame θ φ)
  let w : ℝ → ℝ≥0∞ := (Iio (1 : ℝ)).indicator 1
  have hw : Measurable w := measurable_one.indicator measurableSet_Iio
  have hwtop : ∀ r, w r ≠ ⊤ := fun r ↦ by
    by_cases h : r < 1 <;> simp [w, h]
  let F : ℝ^3 → ℝ≥0∞ := fun x ↦ w ‖x‖ * g (‖x‖⁻¹ • x)
  have hF : Measurable F :=
    (hw.comp measurable_norm).mul (hg.comp (measurable_norm.inv.smul measurable_id))
  set c₀ := ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * w r
  have hc₀ : c₀ = ENNReal.ofReal (1 / 3) := by
    have hind : ∀ r : ℝ, ENNReal.ofReal (r ^ 2) * w r =
        (Iio (1 : ℝ)).indicator (fun r ↦ ENNReal.ofReal (r ^ 2)) r := fun r ↦ by
      by_cases h : r < 1 <;> simp [w, indicator, h]
    simp_rw [c₀, hind]
    rw [setLIntegral_indicator measurableSet_Iio, inter_comm, Ioi_inter_Iio,
      ← ofReal_integral_eq_lintegral_ofReal, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
    · norm_num
    · exact (continuous_pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    · exact Filter.Eventually.of_forall fun r ↦ sq_nonneg r
  have hc₀0 : c₀ ≠ 0 := by rw [hc₀]; norm_num
  have hc₀top : c₀ ≠ ⊤ := by rw [hc₀]; exact ENNReal.ofReal_ne_top
  have hsphere : ∫⁻ x, F x = c₀ * ∫⁻ ω : sphere (0 : ℝ^3) 1, g ω
      ∂(volume : Measure (ℝ^3)).toSphere := by
    rw [lintegral_spherical hF.aemeasurable, ← lintegral_const_mul' _ _ hc₀top]
    refine lintegral_congr fun ω ↦ ?_
    have hω : ‖(ω : ℝ^3)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
    calc ∫⁻ r in Ioi 0, ENNReal.ofReal (r ^ 2) * F (r • (ω : ℝ^3))
        = ∫⁻ r in Ioi 0, ENNReal.ofReal (r ^ 2) * w r * g ω := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
          have hr' : ‖r • (ω : ℝ^3)‖ = r := by
            rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hr]
          simp only [F, hr', inv_smul_smul₀ (ne_of_gt hr), mul_assoc]
      _ = c₀ * g ω := lintegral_mul_const _ ((measurable_id.pow_const 2).ennreal_ofReal.mul hw)
  have hvolume : ∫⁻ x, F x = c₀ * I := by
    rw [lintegral_eq_lintegral_point hF]
    calc ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π, ∫⁻ φ in Ioo 0 (2 * π),
          ENNReal.ofReal (r ^ 2 * sin θ) * F (point r θ φ)
        = ∫⁻ r in Ioi 0, ENNReal.ofReal (r ^ 2) * w r * I := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
          have hc : ENNReal.ofReal (r ^ 2) * w r ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hwtop r)
          have hFp : ∀ θ φ, F (point r θ φ) = w r * g (radialFrame θ φ) := fun θ φ ↦ by
            simp only [F, norm_point hr]
            rw [point, inv_smul_smul₀ (ne_of_gt hr)]
          simp only [I, hFp]
          rw [← lintegral_const_mul' _ _ hc]
          refine lintegral_congr fun θ ↦ ?_
          rw [← lintegral_const_mul' _ _ hc]
          refine lintegral_congr fun φ ↦ ?_
          rw [ENNReal.ofReal_mul (sq_nonneg r)]
          ring
      _ = c₀ * I := lintegral_mul_const _ ((measurable_id.pow_const 2).ennreal_ofReal.mul hw)
  exact (ENNReal.mul_right_inj hc₀0 hc₀top).1 (hsphere.symm.trans hvolume)

/-- The open rectangle `(0, π) × (0, 2π)` of polar and azimuthal angles. -/
def angleDomain : Set (ℝ × ℝ) := Ioo 0 π ×ˢ Ioo 0 (2 * π)

/-- The rectangle of angles is measurable. -/
theorem measurableSet_angleDomain : MeasurableSet angleDomain :=
  measurableSet_Ioo.prod measurableSet_Ioo

/-- The point of the unit sphere with polar angle `p.1` and azimuthal angle `p.2`. -/
def anglePoint (p : angleDomain) : sphere (0 : ℝ^3) 1 :=
  ⟨radialFrame p.1.1 p.1.2, mem_sphere_zero_iff_norm.2 (norm_radialFrame _ _)⟩

/-- The measure `sin θ dθ dφ` on the rectangle of angles. -/
def angleMeasure : Measure angleDomain :=
  Measure.comap Subtype.val
    ((volume : Measure (ℝ × ℝ)).withDensity fun p ↦ ENNReal.ofReal (sin p.1))

/-- The angle map into the sphere is continuous. -/
theorem continuous_anglePoint : Continuous anglePoint :=
  (continuous_radialFrame.comp continuous_subtype_val).subtype_mk _

/-- Distinct angles in the open rectangle give distinct points of the sphere. -/
theorem anglePoint_injective : Function.Injective anglePoint := by
  rintro ⟨⟨θ, φ⟩, ⟨hθ, hφ⟩⟩ ⟨⟨θ', φ'⟩, ⟨hθ', hφ'⟩⟩ h
  have h' : radialFrame θ φ = radialFrame θ' φ' := congrArg Subtype.val h
  have h0 := congrArg (fun v : ℝ^3 ↦ v 0) h'
  have h1 := congrArg (fun v : ℝ^3 ↦ v 1) h'
  have h2 := congrArg (fun v : ℝ^3 ↦ v 2) h'
  simp only [radialFrame] at h0 h1 h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hθθ : θ = θ' := injOn_cos ⟨hθ.1.le, hθ.2.le⟩ ⟨hθ'.1.le, hθ'.2.le⟩ h2
  subst hθθ
  have hs : sin θ ≠ 0 := (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hc : cos φ = cos φ' := mul_left_cancel₀ hs h0
  have hs' : sin φ = sin φ' := mul_left_cancel₀ hs h1
  have hmem : ∀ ψ ∈ Ioo (0 : ℝ) (2 * π), ((1 : ℝ), ψ - π) ∈ polarCoord.target := by
    intro ψ hψ
    exact ⟨one_pos, by linarith [hψ.1], by linarith [hψ.2]⟩
  have hpolar : polarCoord.symm (1, φ - π) = polarCoord.symm (1, φ' - π) := by
    simp [polarCoord_symm_apply, cos_sub_pi, sin_sub_pi, hc, hs']
  have hφφ : φ - π = φ' - π := congrArg Prod.snd (polarCoord.symm.injOn
    (by simpa using hmem φ hφ) (by simpa using hmem φ' hφ') hpolar)
  have : φ = φ' := by linarith
  subst this
  rfl

/-- The angle map is a measurable embedding of the open rectangle into the sphere. -/
theorem measurableEmbedding_anglePoint : MeasurableEmbedding anglePoint := by
  have : PolishSpace angleDomain := (isOpen_Ioo.prod isOpen_Ioo).polishSpace
  exact continuous_anglePoint.measurableEmbedding anglePoint_injective

/-- Integration against `angleMeasure` is integration against `sin θ dθ dφ` on the rectangle.
No measurability hypothesis is needed. -/
theorem lintegral_angleMeasure (k : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ q, k q ∂angleMeasure = ∫⁻ p in angleDomain, ENNReal.ofReal (sin p.1) * k p := by
  rw [angleMeasure, lintegral_subtype_comap measurableSet_angleDomain,
    restrict_withDensity measurableSet_angleDomain,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (measurable_fst.sin.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  rfl

/-- Bochner integration against `angleMeasure` is integration against `sin θ dθ dφ` on the
rectangle. No integrability hypothesis is needed. -/
theorem integral_angleMeasure (k : ℝ × ℝ → E) :
    ∫ q, k q ∂angleMeasure = ∫ p in angleDomain, sin p.1 • k p := by
  rw [angleMeasure, integral_subtype_comap measurableSet_angleDomain,
    restrict_withDensity measurableSet_angleDomain]
  have h : (fun p : ℝ × ℝ ↦ ENNReal.ofReal (sin p.1)) =
      fun p ↦ ((Real.toNNReal (sin p.1) : NNReal) : ℝ≥0∞) := rfl
  rw [h, integral_withDensity_eq_integral_smul measurable_fst.sin.real_toNNReal]
  refine setIntegral_congr_fun measurableSet_angleDomain fun p hp ↦ ?_
  have hs : 0 ≤ sin p.1 := (sin_pos_of_pos_of_lt_pi hp.1.1 hp.1.2).le
  simp [NNReal.smul_def, Real.coe_toNNReal _ hs]

/-- Integrability for `angleMeasure` is integrability against `sin θ dθ dφ` on the rectangle. -/
theorem integrable_angleMeasure_iff (k : ℝ × ℝ → E) :
    Integrable (fun q : angleDomain ↦ k q) angleMeasure ↔
      IntegrableOn (fun p ↦ sin p.1 • k p) angleDomain := by
  refine (integrableOn_iff_comap_subtypeVal measurableSet_angleDomain).symm.trans ?_
  rw [IntegrableOn, restrict_withDensity measurableSet_angleDomain]
  have h : (fun p : ℝ × ℝ ↦ ENNReal.ofReal (sin p.1)) =
      fun p ↦ ((Real.toNNReal (sin p.1) : NNReal) : ℝ≥0∞) := rfl
  rw [h, integrable_withDensity_iff_integrable_smul measurable_fst.sin.real_toNNReal]
  refine integrableOn_congr_fun (fun p hp ↦ ?_) measurableSet_angleDomain
  have hs : 0 ≤ sin p.1 := (sin_pos_of_pos_of_lt_pi hp.1.1 hp.1.2).le
  simp [NNReal.smul_def, Real.coe_toNNReal _ hs]

private theorem setLIntegral_angleDomain {k : ℝ × ℝ → ℝ≥0∞}
    (hk : AEMeasurable k (volume.restrict angleDomain)) :
    ∫⁻ p in angleDomain, k p = ∫⁻ θ in Ioo 0 π, ∫⁻ φ in Ioo 0 (2 * π), k (θ, φ) := by
  rw [angleDomain, Measure.volume_eq_prod, ← Measure.prod_restrict] at hk ⊢
  exact lintegral_prod _ hk

private theorem setIntegral_angleDomain {k : ℝ × ℝ → E} (hk : IntegrableOn k angleDomain) :
    ∫ p in angleDomain, k p = ∫ θ in Ioo 0 π, ∫ φ in Ioo 0 (2 * π), k (θ, φ) := by
  rw [IntegrableOn, angleDomain, Measure.volume_eq_prod, ← Measure.prod_restrict] at hk
  rw [angleDomain, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod _ hk

/-- The sphere measure induced by volume is the image of `sin θ dθ dφ` on the rectangle
`(0, π) × (0, 2π)` under `(θ, φ) ↦ radialFrame θ φ`. -/
theorem toSphere_eq_map_anglePoint :
    (volume : Measure (ℝ^3)).toSphere = angleMeasure.map anglePoint := by
  ext A hA
  have hAimg : MeasurableSet ((↑) '' A : Set (ℝ^3)) :=
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).measurableSet_image.2 hA
  let g : ℝ^3 → ℝ≥0∞ := ((↑) '' A : Set (ℝ^3)).indicator 1
  have hg : Measurable g := measurable_one.indicator hAimg
  have hgA : ∀ ω : sphere (0 : ℝ^3) 1, A.indicator 1 ω = g ω := fun ω ↦ by
    simp only [g]
    by_cases h : ω ∈ A
    · rw [indicator_of_mem h, indicator_of_mem (mem_image_of_mem _ h)]
      rfl
    · rw [indicator_of_notMem h, indicator_of_notMem]
      exact fun ⟨ω', hω', hωω'⟩ ↦ h (Subtype.val_injective hωω' ▸ hω')
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA]
  simp_rw [hgA]
  rw [measurableEmbedding_anglePoint.lintegral_map,
    lintegral_sphere_eq_polar_of_measurable hg]
  simp only [anglePoint]
  rw [lintegral_angleMeasure (fun p ↦ g (radialFrame p.1 p.2)),
    setLIntegral_angleDomain]
  exact (measurable_fst.sin.ennreal_ofReal.mul
    (hg.comp continuous_radialFrame.measurable)).aemeasurable

/-! ### Integrals over the sphere in spherical angles -/

/-- A nonnegative integral over the unit sphere is the integral of `sin θ g (θ, φ)` over the
rectangle `(0, π) × (0, 2π)`. No measurability hypothesis is needed. -/
theorem lintegral_sphere_eq_setLIntegral (g : ℝ^3 → ℝ≥0∞) :
    ∫⁻ ω : sphere (0 : ℝ^3) 1, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      ∫⁻ p in angleDomain, ENNReal.ofReal (sin p.1) * g (radialFrame p.1 p.2) := by
  rw [toSphere_eq_map_anglePoint, measurableEmbedding_anglePoint.lintegral_map]
  exact lintegral_angleMeasure (fun p ↦ g (radialFrame p.1 p.2))

/-- An integral over the unit sphere is the integral of `sin θ • g (θ, φ)` over the rectangle
`(0, π) × (0, 2π)`. No integrability hypothesis is needed. -/
theorem integral_sphere_eq_setIntegral (g : ℝ^3 → E) :
    ∫ ω : sphere (0 : ℝ^3) 1, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      ∫ p in angleDomain, sin p.1 • g (radialFrame p.1 p.2) := by
  rw [toSphere_eq_map_anglePoint, measurableEmbedding_anglePoint.integral_map]
  exact integral_angleMeasure (fun p ↦ g (radialFrame p.1 p.2))

/-- A function on the unit sphere is integrable exactly when `sin θ • g (θ, φ)` is integrable
on the rectangle `(0, π) × (0, 2π)`. -/
theorem integrable_sphere_iff (g : ℝ^3 → E) :
    Integrable (fun ω : sphere (0 : ℝ^3) 1 ↦ g ω) (volume : Measure (ℝ^3)).toSphere ↔
      IntegrableOn (fun p ↦ sin p.1 • g (radialFrame p.1 p.2)) angleDomain := by
  rw [toSphere_eq_map_anglePoint, measurableEmbedding_anglePoint.integrable_map_iff]
  exact integrable_angleMeasure_iff (fun p ↦ g (radialFrame p.1 p.2))

/-- The integral of an integrable vector-valued function over the unit sphere in polar and
azimuthal angles: `∫_{S²} g dσ = ∫₀^π ∫₀^{2π} sin θ • g (θ, φ) dφ dθ`. -/
theorem integral_sphere_eq_polar_smul {g : ℝ^3 → E}
    (hg : Integrable (fun ω : sphere (0 : ℝ^3) 1 ↦ g ω) (volume : Measure (ℝ^3)).toSphere) :
    ∫ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π), sin θ • g (radialFrame θ φ) := by
  rw [integral_sphere_eq_setIntegral, setIntegral_angleDomain ((integrable_sphere_iff g).1 hg),
    intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ ↦ ?_)
  dsimp only
  rw [intervalIntegral.integral_of_le two_pi_pos.le, integral_Ioc_eq_integral_Ioo]

/-- The integral of an integrable function over the unit sphere in polar and azimuthal angles:
`∫_{S²} g dσ = ∫₀^π ∫₀^{2π} g (θ, φ) sin θ dφ dθ`. -/
theorem integral_sphere_eq_polar {g : ℝ^3 → ℝ}
    (hg : Integrable (fun ω : sphere (0 : ℝ^3) 1 ↦ g ω) (volume : Measure (ℝ^3)).toSphere) :
    ∫ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π), g (radialFrame θ φ) * sin θ := by
  rw [integral_sphere_eq_polar_smul hg]
  simp only [smul_eq_mul, mul_comm (sin _)]

/-- The nonnegative integral of an almost everywhere measurable function over the unit sphere in
polar and azimuthal angles. -/
theorem lintegral_sphere_eq_polar {g : ℝ^3 → ℝ≥0∞}
    (hg : AEMeasurable (fun ω : sphere (0 : ℝ^3) 1 ↦ g ω) (volume : Measure (ℝ^3)).toSphere) :
    ∫⁻ ω, g ω ∂(volume : Measure (ℝ^3)).toSphere =
      ∫⁻ θ in Ioo 0 π, ∫⁻ φ in Ioo 0 (2 * π), ENNReal.ofReal (sin θ) * g (radialFrame θ φ) := by
  rw [lintegral_sphere_eq_setLIntegral, setLIntegral_angleDomain]
  rw [toSphere_eq_map_anglePoint] at hg
  have h₁ := hg.comp_measurable measurableEmbedding_anglePoint.measurable
  have h₂ : AEMeasurable (fun p : ℝ × ℝ ↦ g (radialFrame p.1 p.2))
      (((volume : Measure (ℝ × ℝ)).restrict angleDomain).withDensity
        fun p ↦ ENNReal.ofReal (sin p.1)) := by
    rw [← restrict_withDensity measurableSet_angleDomain,
      ← map_comap_subtype_coe measurableSet_angleDomain,
      (MeasurableEmbedding.subtype_coe measurableSet_angleDomain).aemeasurable_map_iff]
    exact h₁
  exact (aemeasurable_withDensity_ennreal_iff measurable_fst.sin.real_toNNReal).1 h₂

end PDE.CoordinateSystems.Spherical
