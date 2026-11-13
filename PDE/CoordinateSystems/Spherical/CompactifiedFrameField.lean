/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Spherical.CompactifiedEnergy
public import PDE.CoordinateSystems.Spherical.CompactifiedField
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Axisymmetric fields with prescribed compactified frame components

For a scale `s > 0` and functions `T k β θ`, `compactifiedFrameField s T` is the axisymmetric
field whose frame components at radius `s tan β` and polar angle `θ` are
`cos² β / sin β · T k β θ`, so that the compactified frame components of the energy lemma
`lintegral_sq_norm_eq_quadrant` are exactly `T` (`inner_frame_compactifiedFrameField`). When the
polar and azimuthal components vanish at `θ = 0` and `θ = π` the field is continuous off the
origin (`continuousAt_compactifiedFrameField`); its energy is then `s³ · 4π` times the quadrant
integral of `∑ₖ T k²` (`lintegral_sq_compactifiedFrameField`), and it is square integrable
(`memLp_two_compactifiedFrameField`).
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems.Spherical

open MeasureTheory Set Real Filter
open scoped ENNReal RealInnerProductSpace BigOperators Topology

/-- The axisymmetric field with frame components `cos² β / sin β · T k β θ` at the radius
`s tan β` and the polar angle `θ`. -/
def compactifiedFrameField (s : ℝ) (T : Fin 3 → ℝ → ℝ → ℝ) : ℝ^3 → ℝ^3 :=
  axisymmetricField (compactifiedProfile s fun β θ k ↦ cos β ^ 2 / sin β * T k β θ)

variable {s : ℝ} {T : Fin 3 → ℝ → ℝ → ℝ}

theorem compactifiedFrameField_point (hs : 0 < s) {β : ℝ} (hβ : β ∈ Ioo 0 (π / 2)) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) (φ : ℝ) :
    compactifiedFrameField s T (point (s * tan β) θ φ) =
      frameVector θ φ (fun k ↦ cos β ^ 2 / sin β * T k β θ) := by
  unfold compactifiedFrameField
  rw [axisymmetricField_point _ (mul_pos hs (tan_pos_of_pos_of_lt_pi_div_two hβ.1 hβ.2)) hθ,
    compactifiedProfile_mul_tan _ hs.ne' ⟨by linarith [hβ.1, pi_pos], hβ.2⟩]

/-- The compactified frame components of the field are `T`. -/
theorem inner_frame_compactifiedFrameField (hs : 0 < s) {β : ℝ} (hβ : β ∈ Ioo 0 (π / 2))
    {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (φ : ℝ) (k : Fin 3) :
    sin β / cos β ^ 2 * ⟪frame θ φ k, compactifiedFrameField s T (point (s * tan β) θ φ)⟫ =
      T k β θ := by
  have hsn : sin β ≠ 0 := (sin_pos_of_pos_of_lt_pi hβ.1 (by linarith [hβ.2, pi_pos])).ne'
  have hcs : cos β ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [hβ.1, pi_pos], hβ.2⟩).ne'
  rw [compactifiedFrameField_point hs hβ hθ, inner_frame_frameVector]
  field_simp

private theorem continuousAt_profile (hs : 0 < s)
    (hT : ∀ k, Continuous (Function.uncurry (T k))) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ContinuousAt (Function.uncurry (compactifiedProfile s
      (fun β θ k ↦ cos β ^ 2 / sin β * T k β θ))) (r, θ) := by
  have hn : ContinuousAt (fun p : ℝ × ℝ ↦ arctan (p.1 / s)) (r, θ) :=
    (continuous_arctan.comp (continuous_fst.div_const s)).continuousAt
  have hpos : 0 < arctan (r / s) := arctan_pos.mpr (div_pos hr hs)
  have hsin : sin (arctan (r / s)) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi hpos (by linarith [arctan_lt_pi_div_two (r / s), pi_pos])).ne'
  refine continuousAt_pi.mpr fun k ↦ ?_
  have hc : ContinuousAt (Function.uncurry (T k)) (arctan (r / s), θ) := (hT k).continuousAt
  have hT' : ContinuousAt (Function.uncurry (T k) ∘ fun p : ℝ × ℝ ↦ (arctan (p.1 / s), p.2))
      (r, θ) := ContinuousAt.comp (f := fun p : ℝ × ℝ ↦ (arctan (p.1 / s), p.2)) (x := (r, θ))
        hc (hn.prodMk continuousAt_snd)
  exact (((continuous_cos.continuousAt.comp hn).pow 2).div
    (continuous_sin.continuousAt.comp hn) hsin).mul hT'

/-- **Continuity off the origin**, when the polar and azimuthal components vanish on the axis. -/
theorem continuousAt_compactifiedFrameField (hs : 0 < s)
    (hT : ∀ k, Continuous (Function.uncurry (T k)))
    (haxis : ∀ k, k ≠ 0 → ∀ β, T k β 0 = 0 ∧ T k β π = 0) {x : ℝ^3} (hx : x ≠ 0) :
    ContinuousAt (compactifiedFrameField s T) x := by
  set f := compactifiedProfile s (fun β θ k ↦ cos β ^ 2 / sin β * T k β θ) with hfdef
  have hfc : ∀ y : ℝ^3, y ≠ 0 → ContinuousAt (fun z : ℝ^3 ↦ f ‖z‖ (polarAngle z)) y :=
    fun y hy ↦ (continuousAt_profile hs hT (norm_pos_iff.mpr hy) _).comp
      (f := fun z : ℝ^3 ↦ (‖z‖, polarAngle z))
      (continuous_norm.continuousAt.prodMk (continuousAt_polarAngle hy))
  by_cases hax : x ∈ symmetryAxis
  · -- on the axis: the radial part is continuous, the other parts tend to zero
    have hsin : sin (polarAngle x) = 0 := by
      rw [sin_polarAngle hx, (cylindricalRadius_eq_zero_iff x).mpr
        ((mem_symmetryAxis_iff x).mp hax), zero_div]
    have hθ : polarAngle x = 0 ∨ polarAngle x = π := by
      have h0 : 0 ≤ arccos (x 2 / ‖x‖) := arccos_nonneg _
      rcases eq_or_lt_of_le (arccos_le_pi (x 2 / ‖x‖)) with h | h
      · exact Or.inr h
      · exact Or.inl ((sin_eq_zero_iff_of_lt_of_lt (by linarith [pi_pos]) h).mp hsin)
    have hz : ∀ k, k ≠ 0 → f ‖x‖ (polarAngle x) k = 0 := by
      intro k hk
      simp only [hfdef, compactifiedProfile]
      rcases hθ with h | h <;> rw [h]
      · rw [(haxis k hk _).1, mul_zero]
      · rw [(haxis k hk _).2, mul_zero]
    have hrad : ∀ y : ℝ^3, y ≠ 0 →
        radialFrame (polarAngle y) (azimuthalAngle y) = ‖y‖⁻¹ • y := by
      intro y hy
      have h := point_norm_polarAngle_azimuthalAngle hy
      rw [point] at h
      have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
      calc radialFrame (polarAngle y) (azimuthalAngle y) =
            ‖y‖⁻¹ • (‖y‖ • radialFrame (polarAngle y) (azimuthalAngle y)) := by
            rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
        _ = ‖y‖⁻¹ • y := by rw [h]
    set A : ℝ^3 → ℝ^3 := fun y ↦ f ‖y‖ (polarAngle y) 0 • (‖y‖⁻¹ • y)
    set R : ℝ^3 → ℝ^3 := fun y ↦ f ‖y‖ (polarAngle y) 1 • polarFrame (polarAngle y)
      (azimuthalAngle y) + f ‖y‖ (polarAngle y) 2 • azimuthalFrame (azimuthalAngle y)
    have hdec : ∀ y : ℝ^3, y ≠ 0 → compactifiedFrameField s T y = A y + R y := by
      intro y hy
      simp only [compactifiedFrameField, axisymmetricField, frameVector_apply, A, R, hrad y hy]
      rw [← hfdef]
      abel
    have hA : ContinuousAt A x := by
      have hk := continuousAt_pi.mp (hfc x hx) 0
      exact hk.smul ((continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul
        continuousAt_id)
    have hpf : ∀ θ φ : ℝ, ‖polarFrame θ φ‖ = 1 := fun θ φ ↦ (orthonormal_frame θ φ).1 1
    have haf : ∀ θ φ : ℝ, ‖azimuthalFrame φ‖ = 1 := fun θ φ ↦ (orthonormal_frame θ φ).1 2
    have hR0 : R x = 0 := by
      simp only [R, hz 1 (by decide), hz 2 (by decide), zero_smul, add_zero]
    have hR : ContinuousAt R x := by
      have h1 := continuousAt_pi.mp (hfc x hx) 1
      have h2 := continuousAt_pi.mp (hfc x hx) 2
      have hb : Tendsto (fun y : ℝ^3 ↦ |f ‖y‖ (polarAngle y) 1| + |f ‖y‖ (polarAngle y) 2|)
          (𝓝 x) (𝓝 0) := by
        have h := Tendsto.add h1.abs.tendsto h2.abs.tendsto
        have e : |f ‖x‖ (polarAngle x) 1| + |f ‖x‖ (polarAngle x) 2| = 0 := by
          rw [hz 1 (by decide), hz 2 (by decide), abs_zero, add_zero]
        rw [e] at h
        exact h
      refine ContinuousAt.congr_of_eventuallyEq (f := R) ?_ (Eventually.of_forall fun _ ↦ rfl)
      change Tendsto R (𝓝 x) (𝓝 (R x))
      rw [hR0]
      refine squeeze_zero_norm (fun y ↦ ?_) hb
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_smul, norm_smul, hpf, haf 0, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one]
    have hev : (fun y ↦ A y + R y) =ᶠ[𝓝 x] compactifiedFrameField s T :=
      Filter.eventually_of_mem (isOpen_ne.mem_nhds hx) fun y hy ↦ (hdec y hy).symm
    exact (hA.add hR).congr hev
  · refine (contDiffAt_axisymmetricField (n := 0) hax ?_).continuousAt
    rw [contDiffAt_zero]
    exact ⟨{p : ℝ × ℝ | 0 < p.1}, (isOpen_lt continuous_const continuous_fst).mem_nhds
      (norm_pos_iff.mpr hx), fun p hp ↦ (continuousAt_profile hs hT hp p.2).continuousWithinAt⟩

theorem aestronglyMeasurable_compactifiedFrameField (hs : 0 < s)
    (hT : ∀ k, Continuous (Function.uncurry (T k)))
    (haxis : ∀ k, k ≠ 0 → ∀ β, T k β 0 = 0 ∧ T k β π = 0) :
    AEStronglyMeasurable (compactifiedFrameField s T) volume := by
  have hc : ContinuousOn (compactifiedFrameField s T) {(0 : ℝ^3)}ᶜ := fun x hx ↦
    (continuousAt_compactifiedFrameField hs hT haxis hx).continuousWithinAt
  have h := hc.aestronglyMeasurable (μ := volume) (measurableSet_singleton _).compl
  rwa [restrict_compl_singleton] at h

/-- **The energy outside a ball** of a field whose compactified frame components are continuous
functions `T` with summed squares symmetric about the equator: `s³ · 4π` times the integral of
`∑ₖ T k²` against `sin θ` over `β ∈ [arctan (R/s), π/2]`, `θ ∈ [0, π/2]`. -/
theorem setLIntegral_compl_ball_sq_norm_eq_quadrant {f : ℝ^3 → ℝ^3} (hs : 0 < s)
    (hf : AEStronglyMeasurable f volume) (hc : ∀ x, x ≠ 0 → ContinuousAt f x)
    (T : Fin 3 → ℝ → ℝ → ℝ) (hT : ∀ k, Continuous (Function.uncurry (T k)))
    (hframe : ∀ β ∈ Ioo 0 (π / 2), ∀ θ ∈ Ioo 0 π, ∀ φ k,
      sin β / cos β ^ 2 * ⟪frame θ φ k, f (point (s * tan β) θ φ)⟫ = T k β θ)
    (hsym : ∀ β θ, ∑ k, T k β (π - θ) ^ 2 = ∑ k, T k β θ ^ 2) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in (Metric.ball (0 : ℝ^3) R)ᶜ, ENNReal.ofReal (‖f x‖ ^ 2) =
      ENNReal.ofReal (s ^ 3 * (4 * π * ∫ β in arctan (R / s)..(π / 2),
        ∫ θ in (0 : ℝ)..(π / 2), (∑ k, T k β θ ^ 2) * sin θ)) := by
  set β₁ := arctan (R / s)
  have hβ₁ : 0 < β₁ := arctan_pos.mpr (div_pos hR hs)
  have hβ₁' : β₁ < π / 2 := arctan_lt_pi_div_two _
  set B := (Metric.ball (0 : ℝ^3) R)ᶜ
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet.compl
  set g := B.indicator f
  have hFc : Continuous fun p : ℝ × ℝ ↦ ∑ k, T k p.1 p.2 ^ 2 :=
    continuous_finsetSum _ fun k _ ↦ (hT k).pow 2
  have hF0 : ∀ β θ, 0 ≤ ∑ k, T k β θ ^ 2 := fun β θ ↦ Finset.sum_nonneg fun k _ ↦ sq_nonneg _
  have e1 : ∫⁻ x in B, ENNReal.ofReal (‖f x‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := by
    rw [← lintegral_indicator hB]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ B <;> simp [g, hx]
  have hmem : ∀ β ∈ Ioo 0 (π / 2), ∀ ω : Metric.sphere (0 : ℝ^3) 1,
      (s * tan β) • (ω : ℝ^3) ∈ B ↔ β₁ ≤ β := by
    intro β hβ ω
    have ht : 0 < tan β := tan_pos_of_pos_of_lt_pi_div_two hβ.1 hβ.2
    have hn : ‖(s * tan β) • (ω : ℝ^3)‖ = s * tan β := by
      rw [norm_smul, norm_eq_of_mem_sphere ω, mul_one, Real.norm_eq_abs,
        abs_of_pos (mul_pos hs ht)]
    have h1 : R ≤ s * tan β ↔ β₁ ≤ β := by
      rw [← arctan_tan (by linarith [hβ.1, pi_pos] : -(π / 2) < β) hβ.2,
        arctan_le_arctan_iff, arctan_tan (by linarith [hβ.1, pi_pos]) hβ.2, div_le_iff₀ hs,
        mul_comm]
    simp only [B, mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt, hn, h1]
  set H : ℝ → ℝ≥0∞ := fun θ ↦ ∫⁻ β in Ioo β₁ (π / 2), ENNReal.ofReal (∑ k, T k β θ ^ 2)
  have h1 : ∀ ω : Metric.sphere (0 : ℝ^3) 1,
      ∫⁻ β in Ioo 0 (π / 2),
        ENNReal.ofReal (‖(sin β / cos β ^ 2) • g ((s * tan β) • (ω : ℝ^3))‖ ^ 2) =
        H (polarAngle ω) := by
    intro ω
    have hpt : ∀ β ∈ Ioo 0 (π / 2),
        ENNReal.ofReal (‖(sin β / cos β ^ 2) • g ((s * tan β) • (ω : ℝ^3))‖ ^ 2) =
          (Ici β₁).indicator (fun β ↦ ENNReal.ofReal (∑ k, T k β (polarAngle ω) ^ 2)) β := by
      intro β hβ
      by_cases h : β₁ ≤ β
      · rw [indicator_of_mem (mem_Ici.mpr h), show g ((s * tan β) • (ω : ℝ^3)) =
          f ((s * tan β) • (ω : ℝ^3)) from indicator_of_mem ((hmem β hβ ω).mpr h) f,
          norm_sq_compactified_eq_sum_sq hs hc T hT hframe hβ ω]
      · rw [indicator_of_notMem (by simpa using h), show g ((s * tan β) • (ω : ℝ^3)) = 0 from
          indicator_of_notMem (fun hm ↦ h ((hmem β hβ ω).mp hm)) f]
        simp
    have hset : Ioo 0 (π / 2) ∩ Ici β₁ = Ico β₁ (π / 2) := by
      ext β
      simp only [mem_inter_iff, mem_Ioo, mem_Ici, mem_Ico]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨hβ₁.trans_le h1, h2⟩, h1⟩
    rw [setLIntegral_congr_fun measurableSet_Ioo hpt, lintegral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici, inter_comm, hset]
    exact setLIntegral_congr Ioo_ae_eq_Ico.symm
  have hsymH : ∀ θ, H (π - θ) = H θ := fun θ ↦ by simp only [H, hsym]
  have h2 : ∫⁻ θ in Ioo 0 (π / 2), ENNReal.ofReal (sin θ) * H θ =
      ∫⁻ θ in Ioo 0 (π / 2), ∫⁻ β in Ioo β₁ (π / 2),
        ENNReal.ofReal ((∑ k, T k β θ ^ 2) * sin θ) :=
    setLIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ by
      have hsn : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos])
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun β ↦ ?_
      rw [← ENNReal.ofReal_mul hsn, mul_comm]
  have hmeas : AEMeasurable (Function.uncurry fun θ β ↦
      ENNReal.ofReal ((∑ k, T k β θ ^ 2) * sin θ))
      ((volume.restrict (Ioo 0 (π / 2))).prod (volume.restrict (Ioo β₁ (π / 2)))) :=
    ((hFc.comp continuous_swap).mul (continuous_sin.comp continuous_fst)).measurable
      |>.ennreal_ofReal.aemeasurable
  have h3 : ∀ β, ∫⁻ θ in Ioo 0 (π / 2), ENNReal.ofReal ((∑ k, T k β θ ^ 2) * sin θ) =
      ENNReal.ofReal (∫ θ in (0 : ℝ)..(π / 2), (∑ k, T k β θ ^ 2) * sin θ) := fun β ↦
    setLIntegral_Ioo_ofReal_eq_ofReal_intervalIntegral (by linarith [pi_pos])
      ((hFc.comp (Continuous.prodMk_right β)).mul continuous_sin).continuousOn
      fun θ hθ ↦ mul_nonneg (hF0 β θ)
        (sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos]))
  have hG : Continuous fun β ↦ ∫ θ in (0 : ℝ)..(π / 2), (∑ k, T k β θ ^ 2) * sin θ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β θ ↦ (∑ k, T k β θ ^ 2) * sin θ)
      (hFc.mul (continuous_sin.comp continuous_snd)) _ _
  rw [e1, lintegral_sq_norm_comp_scaled_tan hs (hf.indicator hB), lintegral_congr h1,
    lintegral_sphere_comp_polarAngle_of_symm H hsymH, h2, lintegral_lintegral_swap hmeas,
    lintegral_congr h3,
    setLIntegral_Ioo_ofReal_eq_ofReal_intervalIntegral hβ₁'.le
      hG.continuousOn fun β _ ↦
      intervalIntegral.integral_nonneg (by linarith [pi_pos]) fun θ hθ ↦
        mul_nonneg (hF0 β θ) (sin_nonneg_of_nonneg_of_le_pi hθ.1
          (by linarith [hθ.2, pi_pos])),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]

/-- **The energy of the field** as `s³ · 4π` times the quadrant integral of `∑ₖ T k²`. -/
theorem lintegral_sq_compactifiedFrameField (hs : 0 < s)
    (hT : ∀ k, Continuous (Function.uncurry (T k)))
    (haxis : ∀ k, k ≠ 0 → ∀ β, T k β 0 = 0 ∧ T k β π = 0)
    (hsym : ∀ β θ, ∑ k, T k β (π - θ) ^ 2 = ∑ k, T k β θ ^ 2) :
    ∫⁻ x, ENNReal.ofReal (‖compactifiedFrameField s T x‖ ^ 2) = ENNReal.ofReal (s ^ 3 *
      (4 * π * ∫ β in (0 : ℝ)..(π / 2), ∫ θ in (0 : ℝ)..(π / 2), (∑ k, T k β θ ^ 2) * sin θ)) :=
  lintegral_sq_norm_eq_quadrant hs (aestronglyMeasurable_compactifiedFrameField hs hT haxis)
    (fun _ hx ↦ continuousAt_compactifiedFrameField hs hT haxis hx) T hT
    (fun _ hβ _ hθ φ k ↦ inner_frame_compactifiedFrameField hs hβ hθ φ k) hsym

/-- The field is square integrable. -/
theorem memLp_two_compactifiedFrameField (hs : 0 < s)
    (hT : ∀ k, Continuous (Function.uncurry (T k)))
    (haxis : ∀ k, k ≠ 0 → ∀ β, T k β 0 = 0 ∧ T k β π = 0)
    (hsym : ∀ β θ, ∑ k, T k β (π - θ) ^ 2 = ∑ k, T k β θ ^ 2) :
    MemLp (compactifiedFrameField s T) 2 volume := by
  have hm := aestronglyMeasurable_compactifiedFrameField hs hT haxis
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ⟨hm.norm.pow 2, ?_⟩
  have e : ∀ x, ‖‖compactifiedFrameField s T x‖ ^ 2‖ₑ =
      ENNReal.ofReal (‖compactifiedFrameField s T x‖ ^ 2) := fun x ↦
    Real.enorm_of_nonneg (sq_nonneg _)
  rw [HasFiniteIntegral, lintegral_congr e, lintegral_sq_compactifiedFrameField hs hT haxis hsym]
  exact ENNReal.ofReal_lt_top

/-- **The energy of the field outside `B(0, R)`** as `s³ · 4π` times the integral of `∑ₖ T k²`
over `β ∈ [arctan (R/s), π/2]`. -/
theorem setLIntegral_compl_ball_sq_compactifiedFrameField (hs : 0 < s)
    (hT : ∀ k, Continuous (Function.uncurry (T k)))
    (haxis : ∀ k, k ≠ 0 → ∀ β, T k β 0 = 0 ∧ T k β π = 0)
    (hsym : ∀ β θ, ∑ k, T k β (π - θ) ^ 2 = ∑ k, T k β θ ^ 2) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in (Metric.ball (0 : ℝ^3) R)ᶜ, ENNReal.ofReal (‖compactifiedFrameField s T x‖ ^ 2) =
      ENNReal.ofReal (s ^ 3 * (4 * π * ∫ β in arctan (R / s)..(π / 2),
        ∫ θ in (0 : ℝ)..(π / 2), (∑ k, T k β θ ^ 2) * sin θ)) :=
  setLIntegral_compl_ball_sq_norm_eq_quadrant hs
    (aestronglyMeasurable_compactifiedFrameField hs hT haxis)
    (fun _ hx ↦ continuousAt_compactifiedFrameField hs hT haxis hx) T hT
    (fun _ hβ _ hθ φ k ↦ inner_frame_compactifiedFrameField hs hβ hθ φ k) hsym hR

end PDE.CoordinateSystems.Spherical
