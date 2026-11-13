/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.SphericalForm
public import PDE.Analysis.SpecialFunctions.SphericalBessel.WeakSolution
public import PDE.CoordinateSystems.Spherical.AxisymmetricIntegration
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Radial coefficients of axisymmetric fields on the ball

For a field `W` on `ℝ³` and a vector harmonic `Y_{l,k}` (`Y_l, X_l, Z_l` for `k = 0, 1, 2`), the
meridian coefficient `c(r) = ∫₀^π ⟪W(point r θ 0), Y_{l,k}(θ)⟫ sin θ dθ` is the moment of the
profile of `W` at radius `r`. For an equivariant `W` the ball integral of `W` against an
azimuthal field `K(‖x‖²) ψ(x)`, with `ψ` an azimuthal mode, is `2π ∫₀^R K(r²) Z(r) r² c(r) dr`,
where `Z` is the radial profile of `ψ` and `c` the azimuthal coefficient of `W`. Testing a
field with `Δ + μ` against `F(‖x‖²) ψ₀`, where `ψ₀ = (x × ∇h_l) / (2l + 1)!!` is the mode of
root zero and `Δ(F(‖x‖²) ψ₀) = (4 ‖x‖² F'' + (4l + 6) F')(‖x‖²) ψ₀`, therefore gives the
one-dimensional equation of `ae_eq_smul_radialSolution_of_weak` for its azimuthal
coefficient, which is then a multiple of the regular solution `r^l G_l(μ r²)`. For a
measurable equivariant `W` integrable on the ball the coefficients are integrable on every
`[a, b] ⊆ (0, R)`, since `sin θ ≤ a⁻² r² sin θ` there, and `r² c` is integrable on `(0, R)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real MvPolynomial
open PDE (laplacian)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff

namespace PDE.Fluid.Stokes.Ball

/-- The meridian coefficient `∫₀^π ⟪W(point r θ 0), Y_{l,k}(θ)⟫ sin θ dθ` of a field `W` at
radius `r` on the vector harmonic `Y_{l,k}`. -/
def meridianCoefficient (W : ℝ^3 → ℝ^3) (l : ℕ) (k : Fin 3) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..π, ⟪W (point r θ 0), vectorHarmonic l k θ⟫ * sin θ

/-- The ball integral of an equivariant field against an azimuthal field `K(‖x‖²) ψ(x)` in terms
of the azimuthal meridian coefficient. -/
theorem setIntegral_inner_azimuthal {R : ℝ} {W : ℝ^3 → ℝ^3}
    (hW : IsEquivariantUnderAxisRotation W) (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R))
    {K : ℝ → ℝ} (hK : Continuous K) (l : ℕ) (α : ℝ) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪W x, K (‖x‖ ^ 2) • mode R .azimuthal l α x⟫ =
      2 * π * ∫ r in Ioo 0 R, K (r ^ 2) * azimuthalProfile R l α r * r ^ 2 *
        meridianCoefficient W l 2 r := by
  set f : ℝ^3 → ℝ := fun x ↦ ⟪W x, K (‖x‖ ^ 2) • mode R .azimuthal l α x⟫ with hf
  have hrot : IsInvariantUnderAxisRotation f := by
    intro φ x
    have hn : ‖axisRotation φ x‖ = ‖x‖ := (axialRotation φ).norm_map x
    simp only [hf, mode_axisRotation, hn, ← axisRotation_smul]
    rw [hW, inner_axisRotation_axisRotation]
  have hcont : Continuous fun x : ℝ^3 ↦ K (‖x‖ ^ 2) • mode R .azimuthal l α x :=
    (hK.comp (continuous_norm.pow 2)).smul (mode_contDiff R .azimuthal l α).continuous
  have hint : IntegrableOn f (Metric.ball (0 : ℝ^3) R) := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℝ^3) R).exists_bound_of_continuousOn
      hcont.continuousOn
    refine Integrable.mono' (hWint.norm.mul_const M)
      (hWint.aestronglyMeasurable.inner hcont.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    calc ‖f x‖ ≤ ‖W x‖ * ‖K (‖x‖ ^ 2) • mode R .azimuthal l α x‖ := norm_inner_le_norm _ _
      _ ≤ ‖W x‖ * M := mul_le_mul_of_nonneg_left (hM x (Metric.ball_subset_closedBall hx))
          (norm_nonneg _)
  rw [setIntegral_ball_of_axisymmetric hrot hint]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun r _ ↦ ?_
  rw [meridianCoefficient, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp only [hf, norm_point_sq, mode_azimuthal_point, vectorHarmonic, vectorHarmonicProfile,
    frame, real_inner_smul_right]
  simp
  ring

/-- The ball integral of `‖W‖` in polar form is finite: with `f` the extension of `‖W‖ₑ` by
zero outside the ball, `∫⁻_{r > 0} ∫⁻_{0 < θ < π} r² sin θ f(point r θ 0) < ∞`. -/
private theorem lintegral_meridian_lt_top {R : ℝ} {W : ℝ^3 → ℝ^3} (hWm : Measurable W)
    (hW : IsEquivariantUnderAxisRotation W) (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R)) :
    ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) *
      (Metric.ball (0 : ℝ^3) R).indicator (fun x ↦ ‖W x‖ₑ) (point r θ 0) < ⊤ := by
  set f : ℝ^3 → ENNReal := (Metric.ball (0 : ℝ^3) R).indicator fun x ↦ ‖W x‖ₑ with hf
  have hfm : Measurable f := (hWm.enorm).indicator Metric.isOpen_ball.measurableSet
  have hfinv : IsInvariantUnderAxisRotation f := by
    have h := (isInvariantUnderAxisRotation_comp_norm hW fun t ↦ ENNReal.ofReal t).indicator_ball R
    simp only [ofReal_norm] at h
    exact h
  have hfin : ∫⁻ x, f x < ⊤ := by
    rw [hf, MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet]
    exact hWint.hasFiniteIntegral
  rw [lintegral_volume_of_axisymmetric hfinv hfm] at hfin
  rcases ENNReal.mul_lt_top_iff.mp hfin with h | h | h
  · exact h.2
  · exact absurd h (by simp [pi_pos])
  · rw [h]
    exact ENNReal.zero_lt_top

/-- The meridian coefficients of a measurable equivariant field integrable on the ball are
integrable on every interval `[a, b] ⊆ (0, R)`: on it `sin θ ≤ a⁻² r² sin θ`, and the ball
integral of `‖W‖` is `2π ∫ r² sin θ ‖W(point r θ 0)‖`. -/
theorem integrableOn_meridianCoefficient {R a b : ℝ} (ha : 0 < a) (hbR : b < R)
    {W : ℝ^3 → ℝ^3} (hWm : Measurable W) (hW : IsEquivariantUnderAxisRotation W)
    (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R)) (l : ℕ) (k : Fin 3) :
    IntegrableOn (meridianCoefficient W l k) (Icc a b) := by
  set G : ℝ → ℝ → ℝ := fun r θ ↦ ⟪W (point r θ 0), vectorHarmonic l k θ⟫ * sin θ with hG
  have hpt : Continuous fun p : ℝ × ℝ ↦ point p.1 p.2 0 := continuous_point_meridian
  have hGm : StronglyMeasurable (Function.uncurry G) :=
    (((hWm.comp hpt.measurable).inner
      ((continuous_vectorHarmonic l k).measurable.comp measurable_snd)).mul
      (continuous_sin.measurable.comp measurable_snd)).stronglyMeasurable
  have hceq : meridianCoefficient W l k = fun r ↦ ∫ θ in Ioc 0 π, G r θ := by
    funext r
    rw [meridianCoefficient, intervalIntegral.integral_of_le pi_pos.le]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_vectorHarmonic l k).continuousOn (s := Icc 0 π)
  set f : ℝ^3 → ENNReal := (Metric.ball (0 : ℝ^3) R).indicator fun x ↦ ‖W x‖ₑ with hf
  have hX : ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0)
      < ⊤ := lintegral_meridian_lt_top hWm hW hWint
  refine ⟨hceq ▸ hGm.integral_prod_right.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  set M : ENNReal := ENNReal.ofReal (max C 0) * ENNReal.ofReal (a ^ 2)⁻¹ with hM
  have hMtop : M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hbound : ∀ r ∈ Icc a b, ‖meridianCoefficient W l k r‖ₑ ≤
      M * ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) := by
    intro r hr
    have hr0 : 0 < r := ha.trans_le hr.1
    have hpball (θ : ℝ) : point r θ 0 ∈ Metric.ball (0 : ℝ^3) R := by
      rw [Metric.mem_ball, dist_zero_right, norm_point hr0]
      exact hr.2.trans_lt hbR
    rw [hceq]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm,
      ← MeasureTheory.lintegral_const_mul' _ _ hMtop]
    refine setLIntegral_mono' measurableSet_Ioo fun θ hθ ↦ ?_
    have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le
    rw [hf, Set.indicator_of_mem (hpball θ)]
    simp only [hG]
    rw [enorm_mul, Real.enorm_eq_ofReal hsin]
    calc ‖⟪W (point r θ 0), vectorHarmonic l k θ⟫‖ₑ * ENNReal.ofReal (sin θ)
        ≤ (‖W (point r θ 0)‖ₑ * ENNReal.ofReal (max C 0)) * ENNReal.ofReal (sin θ) := by
          gcongr
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans ?_)
          exact mul_le_mul_of_nonneg_left ((hC θ (Ioo_subset_Icc_self hθ)).trans (le_max_left _ _))
            (norm_nonneg _)
      _ ≤ M * (ENNReal.ofReal (r ^ 2 * sin θ) * ‖W (point r θ 0)‖ₑ) := by
          rw [hM]
          have hle : ENNReal.ofReal (sin θ) ≤
              ENNReal.ofReal (a ^ 2)⁻¹ * ENNReal.ofReal (r ^ 2 * sin θ) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have ha2 : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha.le hr.1 2
            rw [← mul_assoc]
            have : 1 ≤ (a ^ 2)⁻¹ * r ^ 2 := by
              rw [inv_mul_eq_div, one_le_div (by positivity)]
              exact ha2
            nlinarith
          calc ‖W (point r θ 0)‖ₑ * ENNReal.ofReal (max C 0) * ENNReal.ofReal (sin θ)
              ≤ ‖W (point r θ 0)‖ₑ * ENNReal.ofReal (max C 0) *
                (ENNReal.ofReal (a ^ 2)⁻¹ * ENNReal.ofReal (r ^ 2 * sin θ)) := by gcongr
            _ = _ := by ring
  calc ∫⁻ r in Icc a b, ‖meridianCoefficient W l k r‖ₑ
      ≤ ∫⁻ r in Icc a b, M * ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) :=
        setLIntegral_mono' measurableSet_Icc hbound
    _ ≤ ∫⁻ r in Ioi 0, M * ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) :=
        lintegral_mono_set fun r hr ↦ ha.trans_le hr.1
    _ = M * ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) :=
        MeasureTheory.lintegral_const_mul' _ _ hMtop
    _ < ⊤ := ENNReal.mul_lt_top hMtop.lt_top hX

/-- The meridian coefficients of a measurable equivariant field integrable on the ball, weighted
by `r²`, are integrable on `(0, R)`: the ball integral of `‖W‖` is
`2π ∫ r² sin θ ‖W(point r θ 0)‖`. -/
theorem integrableOn_sq_mul_meridianCoefficient {R : ℝ} {W : ℝ^3 → ℝ^3} (hWm : Measurable W)
    (hW : IsEquivariantUnderAxisRotation W) (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R))
    (l : ℕ) (k : Fin 3) :
    IntegrableOn (fun r ↦ r ^ 2 * meridianCoefficient W l k r) (Ioo 0 R) := by
  set G : ℝ → ℝ → ℝ := fun r θ ↦ ⟪W (point r θ 0), vectorHarmonic l k θ⟫ * sin θ with hG
  have hpt : Continuous fun p : ℝ × ℝ ↦ point p.1 p.2 0 := continuous_point_meridian
  have hGm : StronglyMeasurable (Function.uncurry G) :=
    (((hWm.comp hpt.measurable).inner
      ((continuous_vectorHarmonic l k).measurable.comp measurable_snd)).mul
      (continuous_sin.measurable.comp measurable_snd)).stronglyMeasurable
  have hceq : meridianCoefficient W l k = fun r ↦ ∫ θ in Ioc 0 π, G r θ := by
    funext r
    rw [meridianCoefficient, intervalIntegral.integral_of_le pi_pos.le]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_vectorHarmonic l k).continuousOn (s := Icc 0 π)
  set f : ℝ^3 → ENNReal := (Metric.ball (0 : ℝ^3) R).indicator fun x ↦ ‖W x‖ₑ with hf
  have hX : ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0)
      < ⊤ := lintegral_meridian_lt_top hWm hW hWint
  refine ⟨(continuous_pow 2).aestronglyMeasurable.mul
    (hceq ▸ hGm.integral_prod_right.aestronglyMeasurable), ?_⟩
  rw [HasFiniteIntegral]
  set M : ENNReal := ENNReal.ofReal (max C 0) with hM
  have hMtop : M ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbound : ∀ r ∈ Ioo 0 R, ‖r ^ 2 * meridianCoefficient W l k r‖ₑ ≤
      M * ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hpball (θ : ℝ) : point r θ 0 ∈ Metric.ball (0 : ℝ^3) R := by
      rw [Metric.mem_ball, dist_zero_right, norm_point hr0]
      exact hr.2
    rw [hceq, ← integral_const_mul]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm,
      ← MeasureTheory.lintegral_const_mul' _ _ hMtop]
    refine setLIntegral_mono' measurableSet_Ioo fun θ hθ ↦ ?_
    have hsin : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le
    rw [hf, Set.indicator_of_mem (hpball θ)]
    simp only [hG]
    rw [enorm_mul, enorm_mul, Real.enorm_eq_ofReal hsin, Real.enorm_eq_ofReal (by positivity)]
    calc ENNReal.ofReal (r ^ 2) * (‖⟪W (point r θ 0), vectorHarmonic l k θ⟫‖ₑ *
          ENNReal.ofReal (sin θ))
        ≤ ENNReal.ofReal (r ^ 2) * ((‖W (point r θ 0)‖ₑ * ENNReal.ofReal (max C 0)) *
          ENNReal.ofReal (sin θ)) := by
          gcongr
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans ?_)
          exact mul_le_mul_of_nonneg_left ((hC θ (Ioo_subset_Icc_self hθ)).trans (le_max_left _ _))
            (norm_nonneg _)
      _ = M * (ENNReal.ofReal (r ^ 2 * sin θ) * ‖W (point r θ 0)‖ₑ) := by
          rw [hM, ENNReal.ofReal_mul (by positivity)]
          ring
  calc ∫⁻ r in Ioo 0 R, ‖r ^ 2 * meridianCoefficient W l k r‖ₑ
      ≤ ∫⁻ r in Ioo 0 R, M * ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) :=
        setLIntegral_mono' measurableSet_Ioo hbound
    _ ≤ ∫⁻ r in Ioi 0, M * ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) :=
        lintegral_mono_set fun r hr ↦ hr.1
    _ = M * ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) :=
        MeasureTheory.lintegral_const_mul' _ _ hMtop
    _ < ⊤ := ENNReal.mul_lt_top hMtop.lt_top hX

/-- For almost every radius `r ∈ (0, R)`, the meridian pairings of a measurable equivariant
field integrable on the ball are integrable on `(0, π)`. -/
theorem ae_integrableOn_meridian {R : ℝ} {W : ℝ^3 → ℝ^3} (hWm : Measurable W)
    (hW : IsEquivariantUnderAxisRotation W) (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R))
    (l : ℕ) (k : Fin 3) :
    ∀ᵐ r ∂(volume.restrict (Ioo 0 R)),
      IntegrableOn (fun θ ↦ ⟪W (point r θ 0), vectorHarmonic l k θ⟫ * sin θ) (Ioo 0 π) := by
  set f : ℝ^3 → ENNReal := (Metric.ball (0 : ℝ^3) R).indicator fun x ↦ ‖W x‖ₑ with hf
  have hX := lintegral_meridian_lt_top hWm hW hWint
  have hpt : Continuous fun p : ℝ × ℝ ↦ point p.1 p.2 0 := continuous_point_meridian
  have hfm : Measurable f := (hWm.enorm).indicator Metric.isOpen_ball.measurableSet
  have hmeas : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.1 ^ 2 * sin p.2) *
      f (point p.1 p.2 0) := by
    refine Measurable.mul ?_ (hfm.comp hpt.measurable)
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hinner := hmeas.lintegral_prod_right' (ν := volume.restrict (Ioo 0 π))
  have hae := ae_lt_top' hinner.aemeasurable hX.ne
  have hae' : ∀ᵐ r ∂(volume.restrict (Ioo 0 R)), ∫⁻ θ in Ioo 0 π,
      ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) < ⊤ :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hae
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_vectorHarmonic l k).continuousOn (s := Icc 0 π)
  filter_upwards [hae', ae_restrict_mem measurableSet_Ioo] with r hr hrI
  have hball (θ : ℝ) : point r θ 0 ∈ Metric.ball (0 : ℝ^3) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_point hrI.1]
    exact hrI.2
  have hr2 : (0 : ℝ) < r ^ 2 := by have := hrI.1; positivity
  have hfin : ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (sin θ) * ‖W (point r θ 0)‖ₑ < ⊤ := by
    have heq : ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) =
        ENNReal.ofReal (r ^ 2) * ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (sin θ) * ‖W (point r θ 0)‖ₑ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ?_
      rw [hf, Set.indicator_of_mem (hball θ),
        ENNReal.ofReal_mul hr2.le, mul_assoc]
    rw [heq] at hr
    rcases ENNReal.mul_lt_top_iff.mp hr with h | h | h
    · exact h.2
    · exact absurd h (by simp [hrI.1.ne'])
    · rw [h]
      exact ENNReal.zero_lt_top
  have hWr : IntegrableOn (fun θ ↦ ‖W (point r θ 0)‖ * sin θ) (Ioo 0 π) := by
    refine ⟨((hWm.comp (hpt.measurable.comp measurable_prodMk_left)).norm.mul
      continuous_sin.measurable).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ ↦ ?_
    rw [enorm_mul, enorm_norm, Real.enorm_eq_ofReal (sin_nonneg_of_nonneg_of_le_pi hθ.1.le
      hθ.2.le), mul_comm]
  refine Integrable.mono' (hWr.mul_const (max C 0)) ?_ ?_
  · exact (((hWm.comp (hpt.measurable.comp measurable_prodMk_left)).inner
      (continuous_vectorHarmonic l k).measurable).mul
      continuous_sin.measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hsin := sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le
    rw [norm_mul, Real.norm_of_nonneg hsin]
    calc ‖⟪W (point r θ 0), vectorHarmonic l k θ⟫‖ * sin θ
        ≤ ‖W (point r θ 0)‖ * ‖vectorHarmonic l k θ‖ * sin θ :=
          mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) hsin
      _ ≤ ‖W (point r θ 0)‖ * max C 0 * sin θ := by
          gcongr
          exact (hC θ (Ioo_subset_Icc_self hθ)).trans (le_max_left _ _)
      _ = ‖W (point r θ 0)‖ * sin θ * max C 0 := by ring

/-- The meridian coefficients of a measurable equivariant field integrable on the ball are
locally integrable on `(0, R)`. -/
theorem locallyIntegrableOn_meridianCoefficient {R : ℝ} {W : ℝ^3 → ℝ^3} (hWm : Measurable W)
    (hW : IsEquivariantUnderAxisRotation W) (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R))
    (l : ℕ) (k : Fin 3) : LocallyIntegrableOn (meridianCoefficient W l k) (Ioo 0 R) := by
  refine (locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed).mpr fun K hK hKc ↦ ?_
  rcases K.eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  obtain ⟨x, hx⟩ := hne
  obtain ⟨a, b, ha, hb, -, hKab⟩ := exists_Icc_subset_Ioo_of_isCompact hKc hK (hK hx)
  exact (integrableOn_meridianCoefficient ha hb hWm hW hWint l k).mono_set hKab

/-- The radial profile of the azimuthal mode of root zero is `g_l(0) r^l`. -/
theorem azimuthalProfile_zero (R : ℝ) (l : ℕ) (r : ℝ) :
    azimuthalProfile R l 0 r = reducedSphericalBesselJ l 0 * r ^ l := by
  rw [azimuthalProfile, besselRadial, besselFactor, zero_div, reducedSphericalBesselJ_eq_sq]
  simp

/-- The Laplacian of the azimuthal test fields: for `F` of class `C²`,
`Δ(F(‖x‖²) ψ₀) = (4 ‖x‖² F''(‖x‖²) + (4l + 6) F'(‖x‖²)) ψ₀` componentwise, where
`ψ₀ = mode R .azimuthal l 0` is `g_l(0)` times the harmonic polynomial field `x × ∇h_l`,
homogeneous of degree `l`. -/
theorem laplacian_mul_mode_azimuthal_zero {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (R : ℝ) (l : ℕ)
    (x : ℝ^3) (i : Fin 3) :
    laplacian (fun y ↦ F (‖y‖ ^ 2) * mode R .azimuthal l 0 y i) x =
      (4 * ‖x‖ ^ 2 * deriv (deriv F) (‖x‖ ^ 2) + (4 * l + 6) * deriv F (‖x‖ ^ 2)) *
        mode R .azimuthal l 0 x i := by
  set g := reducedSphericalBesselJSq l 0 with hg
  have hE : ∑ j, X j * pderiv j (zonalSolidHarmonicPolynomial l) =
      C (l : ℝ) * zonalSolidHarmonicPolynomial l := by
    rw [sum_X_mul_pderiv_zonalSolidHarmonicPolynomial, map_natCast]
  have hmode (y : ℝ^3) : mode R .azimuthal l 0 y i =
      g * eval y.ofLp (swirlPolynomial (zonalSolidHarmonicPolynomial l) i) := by
    simp [mode, azimuthalModeField_apply, besselRadial, besselFactor, hg]
  have hfun : (fun y ↦ F (‖y‖ ^ 2) * mode R .azimuthal l 0 y i) = fun y ↦
      (fun s ↦ F s * g) (‖y‖ ^ 2) *
        eval y.ofLp (swirlPolynomial (zonalSolidHarmonicPolynomial l) i) := by
    funext y
    rw [hmode]
    ring
  have hd1 : deriv (fun s ↦ F s * g) = fun s ↦ deriv F s * g := by
    funext s
    exact ((hF.differentiable (by norm_num) s).hasDerivAt.mul_const g).deriv
  have hd2 : deriv (fun s ↦ deriv F s * g) = fun s ↦ deriv (deriv F) s * g := by
    funext s
    exact ((hF.differentiable_deriv_two s).hasDerivAt.mul_const g).deriv
  rw [hfun, laplacian_radial_mul_eval (hF.mul contDiff_const)
    (sum_X_mul_pderiv_swirlPolynomial hE i),
    polynomialLaplacian_swirlPolynomial (polynomialLaplacian_zonalSolidHarmonicPolynomial l) i,
    hmode, hd1, hd2]
  simp only [map_zero, mul_zero, add_zero]
  ring

/-- **Azimuthal coefficients of fields tested with `Δ + μ`.** Let `W` be measurable,
equivariant and integrable on the ball `B(0, R)`, with azimuthal coefficient
`c = meridianCoefficient W l 2`. If `∫_B ⟪W, (Δ + μ) v⟫ = 0` for the azimuthal test fields
`v = F(‖x‖²) ψ₀(x)`, written through `Δ(F(‖x‖²) ψ₀) = (4 ‖x‖² F'' + (4l + 6) F')(‖x‖²) ψ₀`, for
every smooth `F` with compact support in `(-∞, R²)` whose radial operator vanishes near `0`, then
`c` is almost everywhere a multiple of the regular solution `r^l G_l(μ r²)` on `(0, R)`. -/
theorem meridianCoefficient_azimuthal_ae_eq {l : ℕ} {μ R : ℝ} (hR : 0 < R)
    {W : ℝ^3 → ℝ^3} (hWm : Measurable W) (hW : IsEquivariantUnderAxisRotation W)
    (hWint : IntegrableOn W (Metric.ball (0 : ℝ^3) R))
    (hHelm : ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F → tsupport F ⊆ Iio (R ^ 2) →
      (∃ δ > 0, ∀ s ∈ Ioo 0 δ,
        4 * s * deriv (deriv F) s + (4 * l + 6) * deriv F s + μ * F s = 0) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪W x, (4 * ‖x‖ ^ 2 * deriv (deriv F) (‖x‖ ^ 2) +
        (4 * l + 6) * deriv F (‖x‖ ^ 2) + μ * F (‖x‖ ^ 2)) • mode R .azimuthal l 0 x⟫ = 0) :
    ∃ A : ℝ, meridianCoefficient W l 2 =ᵐ[volume.restrict (Ioo 0 R)]
      fun r ↦ A * radialSolution l μ r := by
  refine ae_eq_smul_radialSolution_of_weak hR
    (locallyIntegrableOn_meridianCoefficient hWm hW hWint l 2) fun F hF hcs hsupp hK0 ↦ ?_
  set K : ℝ → ℝ := fun s ↦ 4 * s * deriv (deriv F) s + (4 * l + 6) * deriv F s + μ * F s
    with hKdef
  have hK : Continuous K := by
    have h2 := (hF.iterate_deriv 2).continuous
    have h1 := (hF.iterate_deriv 1).continuous
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
      Function.id_comp] at h1 h2
    simp only [hKdef]
    exact (((continuous_const.mul continuous_id).mul h2).add (continuous_const.mul h1)).add
      (continuous_const.mul hF.continuous)
  have h := hHelm F hF hcs hsupp hK0
  have h' : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪W x, K (‖x‖ ^ 2) • mode R .azimuthal l 0 x⟫ = 0 :=
    h
  rw [setIntegral_inner_azimuthal hW hWint hK l 0] at h'
  have hg : reducedSphericalBesselJ l 0 ≠ 0 := (reducedSphericalBesselJ_zero_pos l).ne'
  have hI : ∫ r in Ioo 0 R, K (r ^ 2) * azimuthalProfile R l 0 r * r ^ 2 *
      meridianCoefficient W l 2 r = reducedSphericalBesselJ l 0 *
        ∫ r in Ioo 0 R, r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv F) (r ^ 2) +
          (4 * l + 6) * deriv F (r ^ 2) + μ * F (r ^ 2)) * meridianCoefficient W l 2 r := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun r _ ↦ ?_
    simp only [hKdef, azimuthalProfile_zero]
    ring
  rw [hI] at h'
  have h2π : 2 * π ≠ 0 := by positivity
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h').resolve_left h2π)).resolve_left hg

/-- **Parity selection for meridian coefficients.** If `W(σ x) = ε σ W(x)` at every point, where
`σ` is the equatorial reflection, the meridian coefficient of `W` on a vector harmonic of
parity different from `ε` vanishes at every radius. -/
theorem meridianCoefficient_eq_zero_of_parity {W : ℝ^3 → ℝ^3} {ε : ℝ}
    (hW : ∀ x, W (equatorialReflection x) = ε • equatorialReflection (W x)) {l : ℕ}
    {k : Fin 3} (hne : ε ≠ vectorHarmonicParity l k) (r : ℝ) :
    meridianCoefficient W l k r = 0 := by
  set c := meridianCoefficient W l k r with hc
  have hsym : c = ε * vectorHarmonicParity l k * c := by
    set f : ℝ → ℝ := fun θ ↦ ⟪W (point r θ 0), vectorHarmonic l k θ⟫ * sin θ with hf
    have h := intervalIntegral.integral_comp_sub_left f π (a := 0) (b := π)
    simp only [sub_zero, sub_self] at h
    have hpt : ∀ θ, f (π - θ) = ε * vectorHarmonicParity l k * f θ := by
      intro θ
      simp only [hf]
      rw [point_pi_sub, vectorHarmonic_pi_sub, sin_pi_sub, ← coe_equatorialReflection, hW,
        real_inner_smul_left, real_inner_smul_right, LinearIsometryEquiv.inner_map_map]
      ring
    calc c = ∫ θ in (0 : ℝ)..π, f θ := rfl
      _ = ∫ θ in (0 : ℝ)..π, f (π - θ) := h.symm
      _ = ∫ θ in (0 : ℝ)..π, ε * vectorHarmonicParity l k * f θ :=
          intervalIntegral.integral_congr fun θ _ ↦ hpt θ
      _ = ε * vectorHarmonicParity l k * c := by
          rw [intervalIntegral.integral_const_mul]
          rfl
  have hp := vectorHarmonicParity_sq l k
  have hεp : ε * vectorHarmonicParity l k ≠ 1 := by
    intro h
    apply hne
    have : ε * vectorHarmonicParity l k * vectorHarmonicParity l k = vectorHarmonicParity l k := by
      rw [h, one_mul]
    rw [mul_assoc, ← sq, hp, mul_one] at this
    exact this
  have h1 : (1 - ε * vectorHarmonicParity l k) * c = 0 := by linear_combination hsym
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hεp.symm)

end PDE.Fluid.Stokes.Ball
