/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Axisymmetric.Isometry
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Equivariant representatives of almost everywhere equivariant fields

A field `u` with `u (R_θ x) = R_θ (u x)` for almost every `x`, for each rotation `R_θ` about
the symmetry axis separately, agrees almost everywhere with the field
`axisAverage u x = (2π)⁻¹ ∫₀^{2π} R_{-θ} u (R_θ x) dθ`, which commutes with every rotation at
every point: for almost every `x` the identity holds for almost every `θ` (Fubini), and the
average of a field that commutes with the rotations is the field itself. Averaging once more
over the equatorial reflection `σ` gives a representative that is also pointwise of parity
`ε`. Point values of such a representative along meridians are meaningful, which the
separation of variables on balls needs.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real
open scoped RealInnerProductSpace

namespace PDE.CoordinateSystems

/-- The rotation average `(2π)⁻¹ ∫₀^{2π} R_{-θ} u (R_θ x) dθ` of a vector field. -/
def axisAverage (u : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ^3 :=
  (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, axisRotation (-θ) (u (axisRotation θ x))

/-- Rotations through angles differing by `2π` agree. -/
theorem axisRotation_add_two_pi (θ : ℝ) (x : ℝ^3) :
    axisRotation (θ + 2 * π) x = axisRotation θ x := by
  rw [← axialRotation_apply, axialRotation_add_two_pi, axialRotation_apply]

/-- The rotation average commutes with every rotation about the axis, for every field. -/
theorem axisAverage_axisRotation (u : ℝ^3 → ℝ^3) (φ : ℝ) (x : ℝ^3) :
    axisAverage u (axisRotation φ x) = axisRotation φ (axisAverage u x) := by
  set g : ℝ → ℝ^3 := fun θ ↦ axisRotation (-θ) (u (axisRotation θ x)) with hg
  have hper : Function.Periodic g (2 * π) := by
    intro θ
    simp only [hg, axisRotation_add_two_pi, neg_add]
    rw [show -θ + -(2 * π) = (-θ - 2 * π) by ring, ← axisRotation_add_two_pi (-θ - 2 * π),
      show -θ - 2 * π + 2 * π = -θ by ring]
  have hint : ∀ θ, axisRotation (-θ) (u (axisRotation θ (axisRotation φ x))) =
      axisRotation φ (g (θ + φ)) := by
    intro θ
    simp only [hg]
    rw [← axisRotation_add, ← axisRotation_add, show φ + -(θ + φ) = -θ by ring]
  have hcomm : ∫ θ in (0 : ℝ)..2 * π, axisRotation φ (g (θ + φ)) =
      axisRotation φ (∫ θ in (0 : ℝ)..2 * π, g (θ + φ)) := by
    rw [intervalIntegral.integral_of_le (by positivity),
      intervalIntegral.integral_of_le (by positivity)]
    exact (axialRotation φ).toContinuousLinearEquiv.integral_comp_comm _
  have hshift : ∫ θ in (0 : ℝ)..2 * π, g (θ + φ) = ∫ θ in (0 : ℝ)..2 * π, g θ := by
    rw [intervalIntegral.integral_comp_add_right, zero_add,
      show 2 * π + φ = φ + 2 * π by ring, hper.intervalIntegral_add_eq φ 0, zero_add]
  simp only [axisAverage]
  rw [intervalIntegral.integral_congr fun θ _ ↦ hint θ, hcomm, hshift, ← axialRotation_apply,
    ← axialRotation_apply, map_smul]

/-- The rotation average of an equivariant field is the field. -/
theorem axisAverage_eq_of_forall {u : ℝ^3 → ℝ^3} {x : ℝ^3}
    (h : ∀ᵐ θ ∂(volume.restrict (Ioc 0 (2 * π))), u (axisRotation θ x) =
      axisRotation θ (u x)) :
    axisAverage u x = u x := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  rw [axisAverage, intervalIntegral.integral_of_le h2π]
  have hc : ∫ θ in Ioc 0 (2 * π), axisRotation (-θ) (u (axisRotation θ x)) =
      ∫ _θ in Ioc 0 (2 * π), u x := by
    refine integral_congr_ae ?_
    filter_upwards [h] with θ hθ
    rw [hθ, axisRotation_neg_apply]
  rw [hc, setIntegral_const, Real.volume_real_Ioc_of_le h2π, sub_zero, smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]

/-- The rotation of `v` splits as `cos θ` times its projection to the plane, `sin θ` times the
quarter turn of that projection, and its axial part. -/
theorem axisRotation_eq_add (θ : ℝ) (v : ℝ^3) :
    axisRotation θ v = Real.cos θ • (WithLp.toLp 2 ![v 0, v 1, 0] : ℝ^3) +
      Real.sin θ • (WithLp.toLp 2 ![-v 1, v 0, 0] : ℝ^3) + (WithLp.toLp 2 ![0, 0, v 2] : ℝ^3) := by
  ext i
  fin_cases i <;> simp [axisRotation] <;> ring

/-- Rotating a strongly measurable field through a measurable angle gives a strongly measurable
field. -/
theorem stronglyMeasurable_axisRotation_comp {X : Type*} [MeasurableSpace X] {a : X → ℝ}
    {F : X → ℝ^3} (ha : Measurable a) (hF : StronglyMeasurable F) :
    StronglyMeasurable fun p ↦ axisRotation (a p) (F p) := by
  have h1 : Continuous fun v : ℝ^3 ↦ (WithLp.toLp 2 ![v 0, v 1, 0] : ℝ^3) := by fun_prop
  have h2 : Continuous fun v : ℝ^3 ↦ (WithLp.toLp 2 ![-v 1, v 0, 0] : ℝ^3) := by fun_prop
  have h3 : Continuous fun v : ℝ^3 ↦ (WithLp.toLp 2 ![0, 0, v 2] : ℝ^3) := by fun_prop
  simp only [axisRotation_eq_add]
  exact (((Real.continuous_cos.measurable.comp ha).stronglyMeasurable.smul
    (h1.comp_stronglyMeasurable hF)).add
    ((Real.continuous_sin.measurable.comp ha).stronglyMeasurable.smul
    (h2.comp_stronglyMeasurable hF))).add (h3.comp_stronglyMeasurable hF)

/-- The rotated point depends measurably on the point and the angle. -/
theorem measurable_axisRotation_swap : Measurable fun p : ℝ^3 × ℝ ↦ axisRotation p.2 p.1 := by
  have h : Continuous fun p : ℝ^3 × ℝ ↦ axisRotation p.2 p.1 := by
    unfold axisRotation
    fun_prop
  exact h.measurable

/-- The rotation average of a strongly measurable field is strongly measurable. -/
theorem stronglyMeasurable_axisAverage {u : ℝ^3 → ℝ^3} (hu : StronglyMeasurable u) :
    StronglyMeasurable (axisAverage u) := by
  have hf : StronglyMeasurable fun p : ℝ^3 × ℝ ↦ axisRotation (-p.2) (u (axisRotation p.2 p.1)) :=
    stronglyMeasurable_axisRotation_comp measurable_snd.neg
      (hu.comp_measurable measurable_axisRotation_swap)
  have := (hf.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * π)))).const_smul
    (2 * π)⁻¹
  have heq : axisAverage u = fun x ↦ (2 * π)⁻¹ • ∫ θ in Ioc 0 (2 * π),
      axisRotation (-θ) (u (axisRotation θ x)) := by
    funext x
    simp only [axisAverage, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [heq]
  exact this

/-- A strongly measurable field that commutes almost everywhere with each rotation equals its
rotation average almost everywhere. -/
theorem axisAverage_ae_eq {u : ℝ^3 → ℝ^3} (hu : StronglyMeasurable u)
    (h : ∀ θ, ∀ᵐ x, u (axisRotation θ x) = axisRotation θ (u x)) :
    axisAverage u =ᵐ[volume] u := by
  have hmeas : MeasurableSet {p : ℝ^3 × ℝ | u (axisRotation p.2 p.1) =
      axisRotation p.2 (u p.1)} :=
    (hu.comp_measurable measurable_axisRotation_swap).measurableSet_eq_fun
      (stronglyMeasurable_axisRotation_comp measurable_snd (hu.comp_measurable measurable_fst))
  have hswap := (Measure.ae_ae_comm (μ := volume) (ν := volume.restrict (Ioc 0 (2 * π)))
    (p := fun x θ ↦ u (axisRotation θ x) = axisRotation θ (u x)) hmeas).mpr
    (ae_of_all _ fun θ ↦ h θ)
  filter_upwards [hswap] with x hx
  exact axisAverage_eq_of_forall hx

/-- Rotations about the axis preserve the measure of a centred ball. -/
theorem measurePreserving_axisRotation_ball (R θ : ℝ) :
    MeasurePreserving (axisRotation θ) (volume.restrict (Metric.ball (0 : ℝ^3) R))
      (volume.restrict (Metric.ball (0 : ℝ^3) R)) := by
  have h := (measurePreserving_axialRotation θ).restrict_preimage
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : ℝ^3) R))
  have hpre : (axialRotation θ) ⁻¹' Metric.ball (0 : ℝ^3) R = Metric.ball (0 : ℝ^3) R := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  rw [hpre] at h
  exact h

/-- The equatorial reflection preserves Lebesgue measure on the ball `B(0, R)`. -/
theorem measurePreserving_equatorialReflection_ball (R : ℝ) :
    MeasurePreserving equatorialReflection (volume.restrict (Metric.ball (0 : ℝ^3) R))
      (volume.restrict (Metric.ball (0 : ℝ^3) R)) := by
  have h := measurePreserving_equatorialReflection.restrict_preimage
    (measurableSet_ball : MeasurableSet (Metric.ball (0 : ℝ^3) R))
  have hpre : equatorialReflection ⁻¹' Metric.ball (0 : ℝ^3) R = Metric.ball (0 : ℝ^3) R := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  rw [hpre] at h
  exact h

/-- **Equivariant representatives on a ball.** Let `u` be almost everywhere strongly
measurable on the ball `B(0, R)`, commute almost everywhere with each rotation about the axis
and have parity `ε` (`ε² = 1`) under the equatorial reflection almost everywhere. Then `u` agrees
almost everywhere on the ball with a strongly measurable field that commutes with every rotation
and has parity `ε` at every point. -/
theorem exists_equivariant_representative_ball {R ε : ℝ} (hε : ε ^ 2 = 1) {u : ℝ^3 → ℝ^3}
    (hu : AEStronglyMeasurable u (volume.restrict (Metric.ball (0 : ℝ^3) R)))
    (hrot : ∀ θ, ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      u (axisRotation θ x) = axisRotation θ (u x))
    (hrefl : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      u (equatorialReflection x) = ε • equatorialReflection (u x)) :
    ∃ w : ℝ^3 → ℝ^3, StronglyMeasurable w ∧ IsEquivariantUnderAxisRotation w ∧
      (∀ x, w (equatorialReflection x) = ε • equatorialReflection (w x)) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w := by
  set B := Metric.ball (0 : ℝ^3) R with hBdef
  have hBrot (θ : ℝ) (x : ℝ^3) : axisRotation θ x ∈ B ↔ x ∈ B := by
    simp only [hBdef, Metric.mem_ball, dist_zero_right]
    rw [← axialRotation_apply, LinearIsometryEquiv.norm_map]
  have hmpR (θ : ℝ) : MeasurePreserving (axisRotation θ) (volume.restrict B)
      (volume.restrict B) := measurePreserving_axisRotation_ball R θ
  have hmpσ : MeasurePreserving equatorialReflection (volume.restrict B) (volume.restrict B) :=
    measurePreserving_equatorialReflection_ball R
  set u₀ := hu.mk u with hu₀def
  have hu₀ : StronglyMeasurable u₀ := hu.stronglyMeasurable_mk
  have hae : u =ᵐ[volume.restrict B] u₀ := hu.ae_eq_mk
  set u₁ := B.indicator u₀ with hu₁def
  have hu₁ : StronglyMeasurable u₁ := hu₀.indicator Metric.isOpen_ball.measurableSet
  have hu₁B : u₁ =ᵐ[volume.restrict B] u₀ := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact indicator_of_mem hx u₀
  have hu₁rot (θ : ℝ) : ∀ᵐ x, u₁ (axisRotation θ x) = axisRotation θ (u₁ x) := by
    have hcomp : (fun x ↦ u (axisRotation θ x)) =ᵐ[volume.restrict B]
        fun x ↦ u₀ (axisRotation θ x) := (hmpR θ).quasiMeasurePreserving.ae_eq_comp hae
    have h1 : ∀ᵐ x ∂(volume.restrict B), u₀ (axisRotation θ x) = axisRotation θ (u₀ x) := by
      filter_upwards [hrot θ, hae, hcomp] with x h1 h2 h3
      rw [← h3, h1, h2]
    rw [ae_restrict_iff' Metric.isOpen_ball.measurableSet] at h1
    filter_upwards [h1] with x hx
    by_cases hxB : x ∈ B
    · rw [hu₁def, indicator_of_mem ((hBrot θ x).mpr hxB), indicator_of_mem hxB, hx hxB]
    · rw [hu₁def, indicator_of_notMem (fun h ↦ hxB ((hBrot θ x).mp h)),
        indicator_of_notMem hxB, ← axialRotation_apply, map_zero]
  set w₁ := axisAverage u₁ with hw₁def
  have hw₁m : StronglyMeasurable w₁ := stronglyMeasurable_axisAverage hu₁
  have hw₁eq : w₁ =ᵐ[volume] u₁ := axisAverage_ae_eq hu₁ hu₁rot
  set w : ℝ^3 → ℝ^3 := fun x ↦ (1 / 2 : ℝ) •
    (w₁ x + ε • equatorialReflection (w₁ (equatorialReflection x))) with hw
  have hσc : Continuous (equatorialReflection : ℝ^3 → ℝ^3) := equatorialReflection.continuous
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · exact (hw₁m.add ((hσc.comp_stronglyMeasurable
      (hw₁m.comp_measurable hσc.measurable)).const_smul ε)).const_smul (1 / 2 : ℝ)
  · intro φ x
    have hσR (y : ℝ^3) : equatorialReflection (axisRotation φ y) =
        axisRotation φ (equatorialReflection y) := by
      rw [← axialRotation_apply, ← axialRotation_apply, equatorialReflection_axialRotation]
    simp only [hw, hw₁def]
    rw [hσR, axisAverage_axisRotation, axisAverage_axisRotation, hσR]
    simp only [← axialRotation_apply, map_smul, map_add]
  · intro x
    simp only [hw, equatorialReflection_equatorialReflection, map_smul, map_add, smul_add,
      smul_smul]
    rw [show ε * (1 / 2 * ε) = (1 / 2 : ℝ) by linear_combination (1 / 2) * hε,
      show (1 / 2 * ε) = ε * (1 / 2) by ring, add_comm]
  · have e1 : w₁ =ᵐ[volume.restrict B] u := by
      filter_upwards [ae_restrict_of_ae hw₁eq, hu₁B, hae] with x h1 h2 h3
      rw [h1, h2, h3]
    have e2 : (fun x ↦ w₁ (equatorialReflection x)) =ᵐ[volume.restrict B]
        fun x ↦ u (equatorialReflection x) := hmpσ.quasiMeasurePreserving.ae_eq_comp e1
    filter_upwards [e1, e2, hrefl] with x h1 h2 h3
    simp only [hw]
    rw [h1, h2, h3, map_smul, equatorialReflection_equatorialReflection, smul_smul,
      show ε * ε = ε ^ 2 by ring, hε, one_smul, ← two_smul ℝ (u x), smul_smul]
    norm_num

/-- The rotations about the axis are measurable embeddings. -/
theorem measurableEmbedding_axisRotation (θ : ℝ) : MeasurableEmbedding (axisRotation θ) :=
  (axialRotation θ).toHomeomorph.measurableEmbedding

/-- An integrable function on a centred ball, composed with the rotations, is integrable on
the product of the ball and `(0, 2π]`. -/
theorem integrable_comp_axisRotation_prod {R : ℝ} {E : Type*} [NormedAddCommGroup E]
    {g : ℝ^3 → E} (hg : StronglyMeasurable g)
    (hgint : IntegrableOn g (Metric.ball (0 : ℝ^3) R)) :
    Integrable (fun p : ℝ^3 × ℝ ↦ g (axisRotation p.2 p.1))
      ((volume.restrict (Metric.ball (0 : ℝ^3) R)).prod (volume.restrict (Ioc 0 (2 * π)))) := by
  have hm : StronglyMeasurable fun p : ℝ^3 × ℝ ↦ g (axisRotation p.2 p.1) :=
    hg.comp_measurable measurable_axisRotation_swap
  refine (integrable_prod_iff' hm.aestronglyMeasurable).mpr ⟨ae_of_all _ fun θ ↦ ?_, ?_⟩
  · exact ((measurePreserving_axisRotation_ball R θ).integrable_comp_emb
      (measurableEmbedding_axisRotation θ)).mpr hgint
  · have hc : (fun θ : ℝ ↦ ∫ x in Metric.ball (0 : ℝ^3) R, ‖g (axisRotation θ x)‖) =
        fun _ ↦ ∫ x in Metric.ball (0 : ℝ^3) R, ‖g x‖ := by
      funext θ
      exact (measurePreserving_axisRotation_ball R θ).integral_comp
        (measurableEmbedding_axisRotation θ) (fun x ↦ ‖g x‖)
    simp only [hc]
    exact integrable_const _

/-- The rotation average of a strongly measurable field integrable on a centred ball is
integrable on it. -/
theorem integrableOn_axisAverage {R : ℝ} {f : ℝ^3 → ℝ^3} (hf : StronglyMeasurable f)
    (hfint : IntegrableOn f (Metric.ball (0 : ℝ^3) R)) :
    IntegrableOn (axisAverage f) (Metric.ball (0 : ℝ^3) R) := by
  have hprod := integrable_comp_axisRotation_prod hf.norm hfint.norm
  have hdom := hprod.integral_prod_left
  refine Integrable.mono' (hdom.const_mul (2 * π)⁻¹)
    (stronglyMeasurable_axisAverage hf).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [axisAverage, norm_smul, Real.norm_of_nonneg (by positivity),
    intervalIntegral.integral_of_le (by positivity)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans
    (le_of_eq (integral_congr_ae (ae_of_all _ fun θ ↦ ?_)))) (by positivity)
  simp only
  rw [← axialRotation_apply, LinearIsometryEquiv.norm_map]

/-- **Averaging against equivariant fields.** For a strongly measurable field `f` integrable on
a centred ball and a continuous equivariant field `Φ`, the rotation average of `f` has the same
pairing with `Φ` as `f`. -/
theorem setIntegral_inner_axisAverage {R : ℝ} {f Φ : ℝ^3 → ℝ^3} (hf : StronglyMeasurable f)
    (hfint : IntegrableOn f (Metric.ball (0 : ℝ^3) R)) (hΦ : Continuous Φ)
    (hΦeq : IsEquivariantUnderAxisRotation Φ) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪axisAverage f x, Φ x⟫ =
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪f x, Φ x⟫ := by
  set B := Metric.ball (0 : ℝ^3) R with hB
  set ν : Measure ℝ := volume.restrict (Ioc 0 (2 * π)) with hν
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ^3) R).exists_bound_of_continuousOn
    hΦ.continuousOn
  have hh : StronglyMeasurable fun x ↦ ⟪f x, Φ x⟫ := hf.inner hΦ.stronglyMeasurable
  have hhint : IntegrableOn (fun x ↦ ⟪f x, Φ x⟫) B := by
    refine Integrable.mono' (hfint.norm.mul_const M) hh.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    calc ‖⟪f x, Φ x⟫‖ ≤ ‖f x‖ * ‖Φ x‖ := norm_inner_le_norm _ _
      _ ≤ ‖f x‖ * M := mul_le_mul_of_nonneg_left (hM x (Metric.ball_subset_closedBall hx))
          (norm_nonneg _)
  set F : ℝ^3 × ℝ → ℝ^3 := fun p ↦ axisRotation (-p.2) (f (axisRotation p.2 p.1)) with hF
  have hFint : Integrable F ((volume.restrict B).prod ν) := by
    have hm : StronglyMeasurable F := stronglyMeasurable_axisRotation_comp measurable_snd.neg
      (hf.comp_measurable measurable_axisRotation_swap)
    refine (integrable_comp_axisRotation_prod hf.norm hfint.norm).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun p ↦ ?_)
    simp only [hF]
    rw [← axialRotation_apply, LinearIsometryEquiv.norm_map]
  have hHint := integrable_comp_axisRotation_prod hh hhint
  have hsec := hFint.prod_right_ae
  have hpt (x : ℝ^3) (θ : ℝ) : ⟪axisRotation (-θ) (f (axisRotation θ x)), Φ x⟫ =
      ⟪f (axisRotation θ x), Φ (axisRotation θ x)⟫ := by
    have hback : axisRotation θ (axisRotation (-θ) (f (axisRotation θ x))) =
        f (axisRotation θ x) := by
      rw [← axisRotation_add, add_neg_cancel, axisRotation_zero]
    rw [hΦeq, ← (axialRotation θ).inner_map_map, axialRotation_apply, axialRotation_apply,
      hback]
  calc ∫ x in B, ⟪axisAverage f x, Φ x⟫
      = ∫ x in B, (2 * π)⁻¹ * ∫ θ, ⟪f (axisRotation θ x), Φ (axisRotation θ x)⟫ ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hsec] with x hx
        rw [axisAverage, intervalIntegral.integral_of_le h2π, real_inner_smul_left,
          real_inner_comm, ← integral_inner hx]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
        simp only [hF]
        rw [real_inner_comm, hpt]
    _ = (2 * π)⁻¹ * ∫ θ, (∫ x in B, ⟪f (axisRotation θ x), Φ (axisRotation θ x)⟫) ∂ν := by
        rw [integral_const_mul]
        congr 1
        exact integral_integral_swap (f := fun x θ ↦ ⟪f (axisRotation θ x),
          Φ (axisRotation θ x)⟫) hHint
    _ = ∫ x in B, ⟪f x, Φ x⟫ := by
        have hc : ∀ θ, ∫ x in B, ⟪f (axisRotation θ x), Φ (axisRotation θ x)⟫ =
            ∫ x in B, ⟪f x, Φ x⟫ := fun θ ↦
          (measurePreserving_axisRotation_ball R θ).integral_comp
            (measurableEmbedding_axisRotation θ) (fun x ↦ ⟪f x, Φ x⟫)
        simp only [hc, integral_const, hν, measureReal_restrict_apply_univ,
          Real.volume_real_Ioc_of_le h2π, sub_zero, smul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end PDE.CoordinateSystems
