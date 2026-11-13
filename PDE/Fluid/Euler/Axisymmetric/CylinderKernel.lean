/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cylindrical
public import PDE.Elliptic.PotentialTheory.FundamentalSolution
public import Mathlib.Analysis.SpecialFunctions.Arsinh
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# The angular kernel of the Newtonian potential

For an axisymmetric density `h(y) = H(r(y), z(y))` on `ℝ^3` the Newtonian potential at the point
`x = (r, 0, z)` reduces to the meridian plane:

```text
∫ Φ(x - y) h(y) dy = ∫_z₁ ∫_{r₁ > 0} r₁ H(r₁, z₁) K(r, z, r₁, z₁) dr₁ dz₁,
K(r, z, r₁, z₁) = ∫_{-π}^{π} Φ((r, 0, z) - R_θ (r₁, 0, z₁)) dθ,
```

with `Φ(v) = 1 / (4π |v|)` and `R_θ` the rotation about the axis
(`lintegral_fundamentalSolution_mul_meridianLift`, for nonnegative measurable `H`). When
`r r₁ ≥ 1/8` the angular kernel has only a logarithmic singularity on the diagonal,
`K ≤ 2 (1 + |log((r - r₁)² + (z - z₁)²)|)` (`angularKernel_le`). For densities supported in
`1/2 ≤ r₁ ≤ 1` this gives the logarithmic bound of the Newtonian potential used for the stream
function in the cylinder (`integral_fundamentalSolution_mul_meridianLift_le`); this is the kernel
estimate behind Chen and Hou, Part I, Lemma 6.1.

## Main definitions

* `angularKernel`: the angular integral `K` of the Newtonian kernel.

## Main results

* `angularKernel_eq`, `angularKernel_nonneg`, `angularKernel_le`: closed form, sign and the
  logarithmic bound of the angular kernel.
* `lintegral_eq_lintegral_cylindrical`: cylindrical coordinates for nonnegative functions on
  `ℝ^3`.
* `lintegral_fundamentalSolution_mul_meridianLift`: the meridian form of the Newtonian potential
  of an axisymmetric density.
* `integral_fundamentalSolution_mul_meridianLift_le`: the logarithmic bound of the potential.
* `integral_closedBall_inv_one_add_rpow_le`: for `β < 1` the weight `(1 + (‖v‖/c)^β)⁻¹` has integral
  at most `2π c^β R^{2-β} / (2 - β)` over a disc of radius `R` in the plane.

## How it works

The squared distance between `(r, 0, z)` and `R_θ (r₁, 0, z₁)` is
`(r - r₁)² + (z - z₁)² + 2 r r₁ (1 - cos θ)` (`norm_sq_meridianPoint_sub_axisRotation`), which gives
the closed form `angularKernel_eq`. Jordan's inequality for `sin(θ/2)` (`Real.mul_le_sin` in
Mathlib) gives `1 - cos θ ≥ 2θ²/π²` on `[-π, π]` (`two_mul_sq_div_le_one_sub_cos`), so for
`r r₁ ≥ 1/8` the integrand is at most `√2 / (4 √(k² + θ²))`, where `k² = 2π² d²` and
`d² = (r - r₁)² + (z - z₁)²`. This majorant integrates to `(√2/2) arsinh(π/k)`, and
`arsinh_le_log_one_add_two_mul` and `log_one_add_le_of_sq_eq` bound `arsinh(π/k)` by
`2 + |log d²|/2`. The meridian form comes from cylindrical coordinates
(`lintegral_eq_lintegral_cylindrical`, built on the polar coordinates of Mathlib) and Tonelli's
theorem. The lifted density is constant on circles about the axis, so for every `r₁ ≠ r`, hence for
almost every `r₁`, the angular integral of the Newtonian kernel is the angular kernel
(`lintegral_angularIntegrand`). In `integral_fundamentalSolution_mul_meridianLift_le` the hypotheses
`r ≥ 1/4` and `r₁ ≥ 1/2` give `r r₁ ≥ 1/8`, and the right side is finite because `log |(r, z) - p|`
is integrable on discs (`integrableOn_log_norm_sub_closedBall`). Chen and Hou state Lemma 6.1 up to
a constant; the constant `2` comes from this computation.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6, Lemma 6.1, p. 95.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace Euler.Cylinder

open MeasureTheory PotentialTheory
open scoped Real ENNReal

set_option linter.missingDocs true

noncomputable section

/-- The angular kernel: the integral over the angle of the Newtonian kernel between the point
`(r, 0, z)` and the circle of radius `r₁` at height `z₁` around the axis. -/
def angularKernel (r z r₁ z₁ : ℝ) : ℝ :=
  ∫ θ in (-π)..π, fundamentalSolution 3
    (PDE.CoordinateSystems.meridianPoint r z -
      PDE.CoordinateSystems.axisRotation θ (PDE.CoordinateSystems.meridianPoint r₁ z₁))

/-- The Newtonian kernel in three dimensions is `1 / (4π |v|)`. -/
theorem fundamentalSolution_three_eq (v : ℝ^3) :
    fundamentalSolution 3 v = 1 / (4 * π * ‖v‖) := by
  rw [fundamentalSolution_of_three_le (by norm_num), PDE.Analysis.unitBallVolume_three]
  norm_num

/-- The squared distance between `(r, 0, z)` and the rotated point `R_θ (r₁, 0, z₁)`. -/
theorem norm_sq_meridianPoint_sub_axisRotation (r z r₁ z₁ θ : ℝ) :
    ‖PDE.CoordinateSystems.meridianPoint r z -
        PDE.CoordinateSystems.axisRotation θ (PDE.CoordinateSystems.meridianPoint r₁ z₁)‖ ^ 2 =
      (r - r₁) ^ 2 + (z - z₁) ^ 2 + 2 * r * r₁ * (1 - Real.cos θ) := by
  set v := PDE.CoordinateSystems.meridianPoint r z -
    PDE.CoordinateSystems.axisRotation θ (PDE.CoordinateSystems.meridianPoint r₁ z₁)
  have h0 : v 0 = r - Real.cos θ * r₁ := by
    simp [v, PDE.CoordinateSystems.meridianPoint, PDE.CoordinateSystems.axisRotation]
  have h1 : v 1 = -(Real.sin θ * r₁) := by
    simp [v, PDE.CoordinateSystems.meridianPoint, PDE.CoordinateSystems.axisRotation]
  have h2 : v 2 = z - z₁ := by
    simp [v, PDE.CoordinateSystems.meridianPoint, PDE.CoordinateSystems.axisRotation]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, sq_abs, h0, h1, h2]
  linear_combination r₁ ^ 2 * Real.sin_sq_add_cos_sq θ

/-- The angular kernel as an explicit integral over the angle. -/
theorem angularKernel_eq (r z r₁ z₁ : ℝ) :
    angularKernel r z r₁ z₁ = ∫ θ in (-π)..π,
      1 / (4 * π * √((r - r₁) ^ 2 + (z - z₁) ^ 2 + 2 * r * r₁ * (1 - Real.cos θ))) := by
  unfold angularKernel
  congr 1
  funext θ
  rw [fundamentalSolution_three_eq, ← norm_sq_meridianPoint_sub_axisRotation,
    Real.sqrt_sq (norm_nonneg _)]

/-- On `[-π, π]`, `1 - cos θ ≥ 2 θ² / π²`. -/
theorem two_mul_sq_div_le_one_sub_cos {θ : ℝ} (hθ : |θ| ≤ π) :
    2 * θ ^ 2 / π ^ 2 ≤ 1 - Real.cos θ := by
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hsq : Real.sin (θ / 2) ^ 2 = Real.sin (|θ| / 2) ^ 2 := by
    rcases abs_cases θ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_div, Real.sin_neg, neg_sq]
  have h0 : 0 ≤ |θ| / 2 := by positivity
  have h1 : |θ| / 2 ≤ π / 2 := by linarith
  have hjordan := Real.mul_le_sin h0 h1
  have hlow : 0 ≤ 2 / π * (|θ| / 2) := by positivity
  have hsin : (2 / π * (|θ| / 2)) ^ 2 ≤ Real.sin (|θ| / 2) ^ 2 :=
    pow_le_pow_left₀ hlow hjordan 2
  have hval : (2 / π * (|θ| / 2)) ^ 2 = θ ^ 2 / π ^ 2 := by
    rw [mul_pow, div_pow, div_pow, sq_abs]
    field_simp
  rw [hcos, hsq]
  rw [hval] at hsin
  have h2 : 2 * θ ^ 2 / π ^ 2 = 2 * (θ ^ 2 / π ^ 2) := by ring
  linarith

/-- `arsinh t ≤ log (1 + 2 t)` for `t ≥ 0`. -/
theorem arsinh_le_log_one_add_two_mul {t : ℝ} (ht : 0 ≤ t) :
    Real.arsinh t ≤ Real.log (1 + 2 * t) := by
  rw [Real.arsinh]
  have hs : √(1 + t ^ 2) ≤ 1 + t := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hpos : 0 < t + √(1 + t ^ 2) := by positivity
  exact Real.log_le_log hpos (by linarith)

/-- The logarithmic bound behind the angular kernel: with `k² = 2π² D`,
`log (1 + 2π / k) ≤ 2 + |log D| / 2`. -/
theorem log_one_add_le_of_sq_eq {D k : ℝ} (hD : 0 < D) (hk : 0 < k)
    (hk2 : k ^ 2 = 2 * π ^ 2 * D) :
    Real.log (1 + 2 * (π / k)) ≤ 2 + |Real.log D| / 2 := by
  have hpos : 0 < 1 + 2 * (π / k) := by positivity
  have hsq : (2 * (π / k)) ^ 2 = 2 / D := by
    rw [mul_pow, div_pow, hk2]
    field_simp
  rcases le_or_gt 1 D with h1 | h1
  · have hle : 2 * (π / k) ≤ 2 := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 ?_
      rw [hsq, div_le_iff₀ hD]
      nlinarith
    linarith [Real.log_le_sub_one_of_pos hpos, abs_nonneg (Real.log D)]
  · have hsD : 0 < √D := Real.sqrt_pos.2 hD
    have h2 : 2 * (π / k) ≤ 2 / √D := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
      rw [hsq, div_pow, Real.sq_sqrt hD.le]
      gcongr
      norm_num
    have h3 : 1 ≤ 1 / √D := by
      rw [le_div_iff₀ hsD, one_mul, Real.sqrt_le_one]
      exact h1.le
    have hlog : Real.log (1 + 2 * (π / k)) ≤ Real.log 3 - Real.log D / 2 := by
      calc Real.log (1 + 2 * (π / k)) ≤ Real.log (3 / √D) :=
            Real.log_le_log hpos (by linarith [show 3 / √D = 1 / √D + 2 / √D by ring])
        _ = Real.log 3 - Real.log D / 2 := by
          rw [Real.log_div (by norm_num) hsD.ne', Real.log_sqrt hD.le]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num), neg_abs_le (Real.log D)]

/-- **The angular kernel bound.** If `r r₁ ≥ 1/8` and `d² = (r - r₁)² + (z - z₁)² > 0`, then
the angular kernel is at most `2 (1 + |log d²|)`. -/
theorem angularKernel_le {r z r₁ z₁ : ℝ} (hrr : 1 / 8 ≤ r * r₁)
    (hD : 0 < (r - r₁) ^ 2 + (z - z₁) ^ 2) :
    angularKernel r z r₁ z₁ ≤ 2 * (1 + |Real.log ((r - r₁) ^ 2 + (z - z₁) ^ 2)|) := by
  set D := (r - r₁) ^ 2 + (z - z₁) ^ 2 with hDdef
  set k := √(2 * π ^ 2 * D) with hkdef
  have hk : 0 < k := Real.sqrt_pos.2 (by positivity)
  have hk2 : k ^ 2 = 2 * π ^ 2 * D := Real.sq_sqrt (by positivity)
  set f : ℝ → ℝ := fun θ ↦ 1 / (4 * π * √(D + 2 * r * r₁ * (1 - Real.cos θ))) with hf
  set g : ℝ → ℝ := fun θ ↦ √2 / 4 * ((√(1 + (θ / k) ^ 2))⁻¹ * (1 / k)) with hg
  have hQ (θ : ℝ) : D ≤ D + 2 * r * r₁ * (1 - Real.cos θ) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ r * r₁) (sub_nonneg.2 (Real.cos_le_one θ))]
  have hfc : Continuous f := by
    refine continuous_const.div (by fun_prop) fun θ ↦ ?_
    have : 0 < √(D + 2 * r * r₁ * (1 - Real.cos θ)) :=
      Real.sqrt_pos.2 (hD.trans_le (hQ θ))
    positivity
  have hgc : Continuous g := by
    refine continuous_const.mul (Continuous.mul ?_ continuous_const)
    refine Continuous.inv₀ (by fun_prop) fun θ ↦ ?_
    exact (Real.sqrt_pos.2 (by positivity)).ne'
  have hderiv : ∀ θ, HasDerivAt (fun θ ↦ √2 / 4 * Real.arsinh (θ / k)) (g θ) θ := by
    intro θ
    have h := (Real.hasDerivAt_arsinh (θ / k)).comp θ ((hasDerivAt_id θ).div_const k)
    simpa [hg, Function.comp_def] using h.const_mul (√2 / 4)
  have hpt : ∀ θ ∈ Set.Icc (-π) π, f θ ≤ g θ := by
    intro θ hθ
    have habs : |θ| ≤ π := abs_le.2 ⟨hθ.1, hθ.2⟩
    have h1 := two_mul_sq_div_le_one_sub_cos habs
    have h2 : 1 / 8 * (2 * θ ^ 2 / π ^ 2) ≤ r * r₁ * (1 - Real.cos θ) :=
      mul_le_mul hrr h1 (by positivity) (by positivity)
    have h4 : θ ^ 2 ≤ 4 * π ^ 2 * (r * r₁ * (1 - Real.cos θ)) :=
      calc θ ^ 2 = 4 * π ^ 2 * (1 / 8 * (2 * θ ^ 2 / π ^ 2)) := by field_simp; ring
        _ ≤ _ := by gcongr
    set Q := D + 2 * r * r₁ * (1 - Real.cos θ)
    have hQpos : 0 < Q := hD.trans_le (hQ θ)
    set m := k * √(1 + (θ / k) ^ 2)
    have hm : 0 < m := by positivity
    have hm2 : m ^ 2 = k ^ 2 + θ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (θ / k) ^ 2 by positivity)]
      field_simp
    have hb2 : (√2 * π * √Q) ^ 2 = 2 * π ^ 2 * Q := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hQpos.le]
    have hmle : m ≤ √2 * π * √Q := by
      refine (pow_le_pow_iff_left₀ hm.le (by positivity) two_ne_zero).1 ?_
      rw [hm2, hb2, hk2]
      nlinarith
    have hgeq : g θ = √2 / (4 * m) := by
      simp only [hg, m]
      field_simp
    rw [hgeq, hf]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < √(2 : ℝ) := by positivity
    nlinarith [Real.pi_pos]
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  calc angularKernel r z r₁ z₁ = ∫ θ in (-π)..π, f θ := by
        rw [angularKernel_eq]
    _ ≤ ∫ θ in (-π)..π, g θ :=
        intervalIntegral.integral_mono_on hpi (hfc.intervalIntegrable _ _)
          (hgc.intervalIntegrable _ _) hpt
    _ = √2 / 4 * Real.arsinh (π / k) - √2 / 4 * Real.arsinh (-π / k) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hderiv θ)
          (hgc.intervalIntegrable _ _)
    _ = √2 / 2 * Real.arsinh (π / k) := by
        rw [neg_div, Real.arsinh_neg]
        ring
    _ ≤ √2 / 2 * (2 + |Real.log D| / 2) := by
        gcongr
        exact (arsinh_le_log_one_add_two_mul (by positivity)).trans
          (log_one_add_le_of_sq_eq (by positivity) hk hk2)
    _ ≤ 2 * (1 + |Real.log D|) := by
        have hs2 : √(2 : ℝ) ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]
          norm_num
        have := abs_nonneg (Real.log D)
        nlinarith

/-- The angular kernel is nonnegative. -/
theorem angularKernel_nonneg (r z r₁ z₁ : ℝ) : 0 ≤ angularKernel r z r₁ z₁ := by
  rw [angularKernel_eq]
  exact intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ ↦ by positivity

/-- The rotated meridian point in coordinates. -/
theorem axisRotation_meridianPoint (θ r z : ℝ) :
    PDE.CoordinateSystems.axisRotation θ (PDE.CoordinateSystems.meridianPoint r z) =
      WithLp.toLp 2 ![r * Real.cos θ, r * Real.sin θ, z] := by
  ext i
  fin_cases i <;>
    simp [PDE.CoordinateSystems.axisRotation, PDE.CoordinateSystems.meridianPoint, mul_comm]

/-- **Cylindrical coordinates for nonnegative functions.** Every measurable `G : ℝ^3 → [0, ∞]`
satisfies `∫ G = ∫_z ∫_{r > 0, -π < θ < π} r G(R_θ (r, 0, z))`. -/
theorem lintegral_eq_lintegral_cylindrical (G : ℝ^3 → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y, G y = ∫⁻ z₁, ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π,
      ENNReal.ofReal q.1 * G (PDE.CoordinateSystems.axisRotation q.2
        (PDE.CoordinateSystems.meridianPoint q.1 z₁)) := by
  let E : ℝ^2 ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have hE : MeasurePreserving (E : ℝ^2 → ℝ × ℝ) volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hsplit := PDE.Analysis.lastCoordinateSplit_measurePreserving (n := 2)
  have hpt : ∀ (a b z₁ : ℝ), PDE.Analysis.lastCoordinateSplit.symm (E.symm (a, b), z₁) =
      (WithLp.toLp 2 ![a, b, z₁] : ℝ^3) := by
    intro a b z₁
    have hEs : E.symm (a, b) = WithLp.toLp 2 ![a, b] := by
      apply E.injective
      rw [MeasurableEquiv.apply_symm_apply]
      rfl
    refine PiLp.ext fun i ↦ Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [PDE.Analysis.lastCoordinateSplit_symm_last]
      rfl
    · rw [PDE.Analysis.lastCoordinateSplit_symm_castSucc, hEs]
      fin_cases j <;> rfl
  have hGs : Measurable (fun p : ℝ^2 × ℝ ↦ G (PDE.Analysis.lastCoordinateSplit.symm p)) :=
    hG.comp PDE.Analysis.lastCoordinateSplit.symm.measurable
  calc ∫⁻ y, G y = ∫⁻ p : ℝ^2 × ℝ, G (PDE.Analysis.lastCoordinateSplit.symm p) :=
        ((hsplit.symm _).lintegral_comp_emb
          PDE.Analysis.lastCoordinateSplit.symm.measurableEmbedding G).symm
    _ = ∫⁻ z₁, ∫⁻ v : ℝ^2, G (PDE.Analysis.lastCoordinateSplit.symm (v, z₁)) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_symm _ hGs.aemeasurable
    _ = ∫⁻ z₁, ∫⁻ w : ℝ × ℝ, G (PDE.Analysis.lastCoordinateSplit.symm (E.symm w, z₁)) := by
        refine lintegral_congr fun z₁ ↦ ?_
        exact ((hE.symm E).lintegral_comp_emb E.symm.measurableEmbedding
          (fun v ↦ G (PDE.Analysis.lastCoordinateSplit.symm (v, z₁)))).symm
    _ = _ := by
        refine lintegral_congr fun z₁ ↦ ?_
        rw [← lintegral_comp_polarCoord_symm, polarCoord_target]
        refine lintegral_congr fun q ↦ ?_
        rw [polarCoord_symm_apply, hpt, axisRotation_meridianPoint, smul_eq_mul]

/-- The three-dimensional Newtonian kernel is measurable. -/
theorem measurable_fundamentalSolution_three : Measurable (fundamentalSolution 3) := by
  have h : fundamentalSolution 3 = fun v : ℝ^3 ↦ 1 / (4 * π * ‖v‖) :=
    funext fundamentalSolution_three_eq
  rw [h]
  exact measurable_const.div (measurable_const.mul measurable_norm)

/-- The meridian coordinates depend continuously on the point. -/
theorem continuous_meridianCoordinates :
    Continuous PDE.CoordinateSystems.meridianCoordinates := by
  unfold PDE.CoordinateSystems.meridianCoordinates PDE.CoordinateSystems.cylindricalRadius
    PDE.CoordinateSystems.cylindricalRadiusSq PDE.CoordinateSystems.axialCoordinate
  fun_prop

/-- The angular integrand in closed form, a continuous function of the angle off the diagonal. -/
theorem continuous_angularIntegrand {r z r₁ z₁ : ℝ} (hrr : 0 ≤ r * r₁)
    (hD : 0 < (r - r₁) ^ 2 + (z - z₁) ^ 2) :
    Continuous fun θ ↦ fundamentalSolution 3
      (PDE.CoordinateSystems.meridianPoint r z -
        PDE.CoordinateSystems.axisRotation θ (PDE.CoordinateSystems.meridianPoint r₁ z₁)) := by
  have h : (fun θ ↦ fundamentalSolution 3
      (PDE.CoordinateSystems.meridianPoint r z -
        PDE.CoordinateSystems.axisRotation θ (PDE.CoordinateSystems.meridianPoint r₁ z₁))) =
      fun θ ↦ 1 / (4 * π * √((r - r₁) ^ 2 + (z - z₁) ^ 2 + 2 * r * r₁ * (1 - Real.cos θ))) := by
    funext θ
    rw [fundamentalSolution_three_eq, ← norm_sq_meridianPoint_sub_axisRotation,
      Real.sqrt_sq (norm_nonneg _)]
  rw [h]
  refine continuous_const.div (by fun_prop) fun θ ↦ ?_
  have hc := Real.cos_le_one θ
  have : 0 < √((r - r₁) ^ 2 + (z - z₁) ^ 2 + 2 * r * r₁ * (1 - Real.cos θ)) :=
    Real.sqrt_pos.2 (by nlinarith)
  positivity

/-- Off the diagonal, the angular lintegral of the Newtonian kernel is the angular kernel. -/
theorem lintegral_angularIntegrand {r z r₁ z₁ : ℝ} (hrr : 0 ≤ r * r₁)
    (hD : 0 < (r - r₁) ^ 2 + (z - z₁) ^ 2) :
    ∫⁻ θ in Set.Ioo (-π) π, ENNReal.ofReal (fundamentalSolution 3
      (PDE.CoordinateSystems.meridianPoint r z -
        PDE.CoordinateSystems.axisRotation θ (PDE.CoordinateSystems.meridianPoint r₁ z₁))) =
      ENNReal.ofReal (angularKernel r z r₁ z₁) := by
  have hc := continuous_angularIntegrand hrr hD
  have hpi : -π ≤ π := by linarith [Real.pi_pos]
  rw [angularKernel, intervalIntegral.integral_of_le hpi,
    ofReal_integral_eq_lintegral_ofReal
      ((hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall fun θ ↦ by
        simp only [Pi.zero_apply]
        rw [fundamentalSolution_three_eq]; positivity)]
  exact setLIntegral_congr Ioo_ae_eq_Ioc

/-- **The Newtonian potential of an axisymmetric density in meridian form.** For a measurable
`H ≥ 0` on the meridian plane and `x = (r, 0, z)` with `r ≥ 0`,
`∫ Φ(x - y) H(r(y), z(y)) dy = ∫_z₁ ∫_{r₁ > 0} r₁ H(r₁, z₁) K(r, z, r₁, z₁)`, with `K` the angular
kernel. -/
theorem lintegral_fundamentalSolution_mul_meridianLift (H : ℝ^2 → ℝ) (hH : Measurable H)
    (hH0 : ∀ p, 0 ≤ H p) {r : ℝ} (hr : 0 ≤ r) (z : ℝ) :
    ∫⁻ y, ENNReal.ofReal (fundamentalSolution 3 (PDE.CoordinateSystems.meridianPoint r z - y) *
        PDE.CoordinateSystems.meridianLift H y) =
      ∫⁻ z₁, ∫⁻ r₁ in Set.Ioi 0,
        ENNReal.ofReal (r₁ * H (WithLp.toLp 2 ![r₁, z₁]) * angularKernel r z r₁ z₁) := by
  set x := PDE.CoordinateSystems.meridianPoint r z
  have hΦ0 : ∀ v, 0 ≤ fundamentalSolution 3 v := fun v ↦ by
    rw [fundamentalSolution_three_eq]; positivity
  have hlift : Measurable (PDE.CoordinateSystems.meridianLift H) :=
    hH.comp continuous_meridianCoordinates.measurable
  have hmeas : Measurable fun y ↦ ENNReal.ofReal (fundamentalSolution 3 (x - y) *
      PDE.CoordinateSystems.meridianLift H y) :=
    ENNReal.measurable_ofReal.comp ((measurable_fundamentalSolution_three.comp
      (measurable_const.sub measurable_id)).mul hlift)
  rw [lintegral_eq_lintegral_cylindrical _ hmeas]
  refine lintegral_congr fun z₁ ↦ ?_
  have hrot : Measurable fun q : ℝ × ℝ ↦ PDE.CoordinateSystems.axisRotation q.2
      (PDE.CoordinateSystems.meridianPoint q.1 z₁) := by
    simp_rw [axisRotation_meridianPoint]
    fun_prop
  have hprod : Measurable fun q : ℝ × ℝ ↦ ENNReal.ofReal q.1 *
      ENNReal.ofReal (fundamentalSolution 3 (x - PDE.CoordinateSystems.axisRotation q.2
        (PDE.CoordinateSystems.meridianPoint q.1 z₁)) *
        PDE.CoordinateSystems.meridianLift H (PDE.CoordinateSystems.axisRotation q.2
          (PDE.CoordinateSystems.meridianPoint q.1 z₁))) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (hmeas.comp hrot)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hprod.aemeasurable]
  refine setLIntegral_congr_fun_ae measurableSet_Ioi ?_
  filter_upwards [Measure.ae_ne volume r] with r₁ hr₁ hr₁pos
  have hr₁0 : 0 ≤ r₁ := le_of_lt hr₁pos
  have hval : ∀ θ, PDE.CoordinateSystems.meridianLift H
      (PDE.CoordinateSystems.axisRotation θ (PDE.CoordinateSystems.meridianPoint r₁ z₁)) =
      H (WithLp.toLp 2 ![r₁, z₁]) := fun θ ↦ by
    rw [PDE.CoordinateSystems.isInvariantUnderAxisRotation_meridianLift,
      PDE.CoordinateSystems.meridianLift_meridianPoint _ _ _ hr₁0]
  have hD : 0 < (r - r₁) ^ 2 + (z - z₁) ^ 2 := by
    have : r - r₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hr₁)
    positivity
  have hθmeas : Measurable fun θ : ℝ ↦ ENNReal.ofReal (fundamentalSolution 3
      (x - PDE.CoordinateSystems.axisRotation θ (PDE.CoordinateSystems.meridianPoint r₁ z₁))) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularIntegrand (mul_nonneg hr hr₁0) hD).measurable
  calc ∫⁻ θ in Set.Ioo (-π) π, ENNReal.ofReal (r₁, θ).1 *
        ENNReal.ofReal (fundamentalSolution 3 (x - PDE.CoordinateSystems.axisRotation (r₁, θ).2
          (PDE.CoordinateSystems.meridianPoint (r₁, θ).1 z₁)) *
          PDE.CoordinateSystems.meridianLift H (PDE.CoordinateSystems.axisRotation (r₁, θ).2
            (PDE.CoordinateSystems.meridianPoint (r₁, θ).1 z₁)))
      = ∫⁻ θ in Set.Ioo (-π) π, ENNReal.ofReal (r₁ * H (WithLp.toLp 2 ![r₁, z₁])) *
          ENNReal.ofReal (fundamentalSolution 3 (x - PDE.CoordinateSystems.axisRotation θ
            (PDE.CoordinateSystems.meridianPoint r₁ z₁))) := by
        refine lintegral_congr fun θ ↦ ?_
        simp only [hval]
        rw [ENNReal.ofReal_mul (hΦ0 _), ENNReal.ofReal_mul hr₁0]
        ring
    _ = ENNReal.ofReal (r₁ * H (WithLp.toLp 2 ![r₁, z₁])) *
          ENNReal.ofReal (angularKernel r z r₁ z₁) := by
        rw [lintegral_const_mul _ hθmeas, lintegral_angularIntegrand (by positivity) hD]
    _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hr₁0 (hH0 _))]

/-- Lebesgue integrals over the Euclidean plane are integrals over `ℝ × ℝ` in coordinates. -/
theorem lintegral_euclideanPlane (g : ℝ^2 → ℝ≥0∞) :
    ∫⁻ p, g p = ∫⁻ q : ℝ × ℝ, g (WithLp.toLp 2 ![q.1, q.2]) := by
  let E : ℝ^2 ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have hE : MeasurePreserving (E : ℝ^2 → ℝ × ℝ) volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hEs : ∀ q : ℝ × ℝ, E.symm q = WithLp.toLp 2 ![q.1, q.2] := fun q ↦ by
    apply E.injective
    rw [MeasurableEquiv.apply_symm_apply]
    rfl
  simp_rw [← hEs]
  exact ((hE.symm E).lintegral_comp_emb E.symm.measurableEmbedding g).symm

/-- The planar logarithm `p ↦ log |P - p|` is integrable on every closed ball. -/
theorem integrableOn_log_norm_sub_closedBall (P : ℝ^2) (R : ℝ) :
    IntegrableOn (fun p ↦ Real.log ‖P - p‖) (Metric.closedBall P R) := by
  have : Fact (0 < 2) := ⟨by norm_num⟩
  have h0 : IntegrableOn (fundamentalSolution 2) (Metric.closedBall 0 R) :=
    (locallyIntegrable_fundamentalSolution 2).integrableOn_isCompact (isCompact_closedBall _ _)
  have hpre : (fun p : ℝ^2 ↦ p - P) ⁻¹' Metric.closedBall 0 R = Metric.closedBall P R := by
    ext p
    simp [dist_eq_norm]
  have h1 : IntegrableOn (fun p ↦ fundamentalSolution 2 (p - P)) (Metric.closedBall P R) := by
    rw [← hpre]
    exact ((measurePreserving_sub_right volume P).integrableOn_comp_preimage
      (Homeomorph.subRight P).measurableEmbedding).2 h0
  have h2 : IntegrableOn (fun p ↦ -(2 * π) * fundamentalSolution 2 (p - P))
      (Metric.closedBall P R) := h1.const_mul (-(2 * π))
  refine IntegrableOn.congr_fun h2 (fun p _ ↦ ?_) measurableSet_closedBall
  rw [fundamentalSolution_two, norm_sub_rev]
  field_simp

/-- **The log-kernel bound for the Newtonian potential of a meridian density.** Let `H ≥ 0` be
measurable and bounded on the meridian plane, vanishing unless `1/2 ≤ r₁ ≤ 1` and
`a ≤ z₁ ≤ b`. For `x = (r, 0, z)` with `r ≥ 1/4`,
`∫ Φ(x - y) H(r(y), z(y)) dy ≤ 2 ∫ H(r₁, z₁) (1 + |log((r - r₁)² + (z - z₁)²)|) r₁`, the last
integral over the rectangle `[0, 1] × [a, b]` of the meridian plane. -/
theorem integral_fundamentalSolution_mul_meridianLift_le {a b M r z : ℝ} (H : ℝ^2 → ℝ)
    (hH : Measurable H) (hH0 : ∀ p, 0 ≤ H p) (hHM : ∀ p, H p ≤ M)
    (hsupp : ∀ p, H p ≠ 0 → 1 / 2 ≤ p 0 ∧ p 0 ≤ 1 ∧ a ≤ p 1 ∧ p 1 ≤ b) (hr : 1 / 4 ≤ r) :
    ∫ y, fundamentalSolution 3 (PDE.CoordinateSystems.meridianPoint r z - y) *
        PDE.CoordinateSystems.meridianLift H y ≤
      2 * ∫ p in {p : ℝ^2 | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ a ≤ p 1 ∧ p 1 ≤ b},
        H p * (1 + |Real.log ((r - p 0) ^ 2 + (z - p 1) ^ 2)|) * p 0 := by
  set S : Set (ℝ^2) := {p : ℝ^2 | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ a ≤ p 1 ∧ p 1 ≤ b} with hSdef
  set x := PDE.CoordinateSystems.meridianPoint r z
  set B : ℝ^2 → ℝ := fun p ↦ H p * (1 + |Real.log ((r - p 0) ^ 2 + (z - p 1) ^ 2)|) * p 0
    with hBdef
  have hr0 : 0 ≤ r := by linarith
  have hΦ0 : ∀ v, 0 ≤ fundamentalSolution 3 v := fun v ↦ by
    rw [fundamentalSolution_three_eq]; positivity
  have hB0 (p : ℝ^2) : 0 ≤ B p := by
    rcases eq_or_ne (H p) 0 with hp | hp
    · simp [hBdef, hp]
    · exact mul_nonneg (mul_nonneg (hH0 p) (by positivity)) (by linarith [(hsupp p hp).1])
  have hBsupp (p : ℝ^2) (hp : B p ≠ 0) : p ∈ S := by
    obtain ⟨h1, h2, h3, h4⟩ := hsupp p fun h ↦ hp (by simp [hBdef, h])
    exact ⟨by linarith, h2, h3, h4⟩
  have hBmeas : Measurable B := by
    simp only [hBdef]
    fun_prop
  have hlift : Measurable (PDE.CoordinateSystems.meridianLift H) :=
    hH.comp continuous_meridianCoordinates.measurable
  have hFmeas : Measurable fun y ↦ fundamentalSolution 3 (x - y) *
      PDE.CoordinateSystems.meridianLift H y :=
    (measurable_fundamentalSolution_three.comp (measurable_const.sub measurable_id)).mul hlift
  -- the left side as a lintegral
  have hL : ∫ y, fundamentalSolution 3 (x - y) * PDE.CoordinateSystems.meridianLift H y =
      (∫⁻ y, ENNReal.ofReal (fundamentalSolution 3 (x - y) *
        PDE.CoordinateSystems.meridianLift H y)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun y ↦ mul_nonneg (hΦ0 _) (hH0 _))
      hFmeas.aestronglyMeasurable
  have hR : ∫ p in S, B p = (∫⁻ p in S, ENNReal.ofReal (B p)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hB0)
      hBmeas.aestronglyMeasurable
  -- finiteness of the right side
  set P : ℝ^2 := WithLp.toLp 2 ![r, z]
  have hdist : ∀ p : ℝ^2, (r - p 0) ^ 2 + (z - p 1) ^ 2 = ‖P - p‖ ^ 2 := by
    intro p
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    simp [P]
  set R : ℝ := ‖P‖ + 1 + |a| + |b|
  have hSball : S ⊆ Metric.closedBall P R := by
    rintro p ⟨h1, h2, h3, h4⟩
    have hpn : ‖p‖ ≤ 1 + |a| + |b| := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity), Fin.sum_univ_two,
        Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
      nlinarith [abs_nonneg a, abs_nonneg b, mul_le_mul h2 h2 h1 zero_le_one,
        mul_nonneg (by linarith [le_abs_self b, abs_nonneg a] : 0 ≤ |a| + |b| - p 1)
          (by linarith [neg_abs_le a, abs_nonneg b] : 0 ≤ |a| + |b| + p 1)]
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith [norm_sub_le p P]
  have hlogint : IntegrableOn (fun p ↦ Real.log ‖P - p‖) S :=
    (integrableOn_log_norm_sub_closedBall P R).mono_set hSball
  have hSfin : volume S < ⊤ :=
    (measure_mono hSball).trans_lt measure_closedBall_lt_top
  have hgint : IntegrableOn (fun p ↦ M * (1 + 2 * |Real.log ‖P - p‖|)) S :=
    ((integrableOn_const hSfin.ne).add (hlogint.abs.const_mul 2)).const_mul M
  have hM0 : 0 ≤ M := (hH0 0).trans (hHM 0)
  have hBle (p : ℝ^2) : B p ≤ M * (1 + 2 * |Real.log ‖P - p‖|) := by
    have hlog : |Real.log ((r - p 0) ^ 2 + (z - p 1) ^ 2)| = 2 * |Real.log ‖P - p‖| := by
      rw [hdist, Real.log_pow, abs_mul]
      norm_num
    rcases eq_or_ne (H p) 0 with hp | hp
    · simp only [hBdef, hp, zero_mul]
      positivity
    · obtain ⟨h1, h2, -, -⟩ := hsupp p hp
      simp only [hBdef, hlog]
      calc _ ≤ H p * (1 + 2 * |Real.log ‖P - p‖|) * 1 := by
            gcongr
            exact mul_nonneg (hH0 p) (by positivity)
        _ ≤ M * (1 + 2 * |Real.log ‖P - p‖|) := by rw [mul_one]; gcongr; exact hHM p
  have hRfin : ∫⁻ p in S, ENNReal.ofReal (B p) ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono fun p ↦ ENNReal.ofReal_le_ofReal (hBle p))
      hgint.lintegral_lt_top).ne
  -- the pointwise kernel comparison
  have hK (z₁ : ℝ) : ∀ᵐ r₁ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal (r₁ * H (WithLp.toLp 2 ![r₁, z₁]) * angularKernel r z r₁ z₁) ≤
        ENNReal.ofReal 2 * ENNReal.ofReal (B (WithLp.toLp 2 ![r₁, z₁])) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume r)] with r₁ hr₁
    rcases eq_or_ne (H (WithLp.toLp 2 ![r₁, z₁])) 0 with hp | hp
    · simp [hp]
    obtain ⟨h1, h2, -, -⟩ := hsupp _ hp
    simp only [Matrix.cons_val_zero] at h1 h2
    have hD : 0 < (r - r₁) ^ 2 + (z - z₁) ^ 2 := by
      have : r - r₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hr₁)
      positivity
    have hk := angularKernel_le (z := z) (z₁ := z₁) (by nlinarith) hD
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hBdef, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc _ ≤ r₁ * H (WithLp.toLp 2 ![r₁, z₁]) *
          (2 * (1 + |Real.log ((r - r₁) ^ 2 + (z - z₁) ^ 2)|)) := by
          gcongr
          exact mul_nonneg (by linarith) (hH0 _)
      _ = _ := by ring
  have hBmeasq : Measurable fun q : ℝ × ℝ ↦ ENNReal.ofReal 2 *
      ENNReal.ofReal (B (WithLp.toLp 2 ![q.1, q.2])) := by
    fun_prop
  have hsuppS : Function.support (fun p ↦ ENNReal.ofReal (B p)) ⊆ S :=
    fun p hp ↦ hBsupp p fun h ↦ hp (by simp [h])
  have hchain : ∫⁻ y, ENNReal.ofReal (fundamentalSolution 3 (x - y) *
      PDE.CoordinateSystems.meridianLift H y) ≤
        ENNReal.ofReal 2 * ∫⁻ p in S, ENNReal.ofReal (B p) := by
    calc ∫⁻ y, ENNReal.ofReal (fundamentalSolution 3 (x - y) *
          PDE.CoordinateSystems.meridianLift H y)
        = ∫⁻ z₁, ∫⁻ r₁ in Set.Ioi 0,
            ENNReal.ofReal (r₁ * H (WithLp.toLp 2 ![r₁, z₁]) * angularKernel r z r₁ z₁) :=
          lintegral_fundamentalSolution_mul_meridianLift H hH hH0 hr0 z
      _ ≤ ∫⁻ z₁, ∫⁻ r₁ in Set.Ioi 0,
            ENNReal.ofReal 2 * ENNReal.ofReal (B (WithLp.toLp 2 ![r₁, z₁])) :=
          lintegral_mono fun z₁ ↦ lintegral_mono_ae (hK z₁)
      _ ≤ ∫⁻ z₁, ∫⁻ r₁,
            ENNReal.ofReal 2 * ENNReal.ofReal (B (WithLp.toLp 2 ![r₁, z₁])) :=
          lintegral_mono fun z₁ ↦ setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (B (WithLp.toLp 2 ![q.1, q.2])) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.volume_eq_prod,
            lintegral_prod_symm _ hBmeasq.aemeasurable]
      _ = ENNReal.ofReal 2 * ∫⁻ p : ℝ^2, ENNReal.ofReal (B p) := by
          rw [lintegral_euclideanPlane]
      _ = ENNReal.ofReal 2 * ∫⁻ p in S, ENNReal.ofReal (B p) := by
          rw [setLIntegral_eq_of_support_subset hsuppS]
  rw [hL, hR]
  calc (∫⁻ y, ENNReal.ofReal (fundamentalSolution 3 (x - y) *
        PDE.CoordinateSystems.meridianLift H y)).toReal
      ≤ (ENNReal.ofReal 2 * ∫⁻ p in S, ENNReal.ofReal (B p)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRfin) hchain
    _ = 2 * (∫⁻ p in S, ENNReal.ofReal (B p)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]

/-- The radial weight `(1 + (ρ/c)^β)⁻¹` integrated against `ρ dρ` over `(0, R]` is at most
`c^β R^{2-β} / (2 - β)`. -/
theorem integral_Ioc_mul_inv_one_add_rpow_le {c R β : ℝ} (hc : 0 < c) (hR : 0 ≤ R)
    (hβ1 : β < 1) :
    ∫ ρ in Set.Ioc 0 R, ρ * (1 + (ρ / c) ^ β)⁻¹ ≤ c ^ β * R ^ (2 - β) / (2 - β) := by
  have hpt : ∀ ρ ∈ Set.Ioc (0 : ℝ) R, ρ * (1 + (ρ / c) ^ β)⁻¹ ≤ c ^ β * ρ ^ (1 - β) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ.1
    have hpow : 0 < (ρ / c) ^ β := Real.rpow_pos_of_pos (div_pos hρ0 hc) β
    calc ρ * (1 + (ρ / c) ^ β)⁻¹ ≤ ρ * ((ρ / c) ^ β)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ hρ0.le
          exact inv_anti₀ hpow (by linarith)
      _ = c ^ β * ρ ^ (1 - β) := by
          rw [Real.div_rpow hρ0.le hc.le, inv_div, Real.rpow_sub hρ0, Real.rpow_one]
          field_simp
  have hint1 : IntegrableOn (fun ρ : ℝ ↦ c ^ β * ρ ^ (1 - β)) (Set.Ioc 0 R) := by
    refine (Continuous.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuous_const.mul (Real.continuous_rpow_const (by linarith))
  have hint0 : IntegrableOn (fun ρ : ℝ ↦ ρ * (1 + (ρ / c) ^ β)⁻¹) (Set.Ioc 0 R) := by
    refine hint1.mono' ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
      intro ρ hρ
      have hpos : 0 ≤ (1 + (ρ / c) ^ β)⁻¹ :=
        inv_nonneg.2 (by linarith [Real.rpow_nonneg (div_nonneg hρ.1.le hc.le) β])
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hρ.1.le hpos)]
      exact hpt ρ hρ
  calc ∫ ρ in Set.Ioc 0 R, ρ * (1 + (ρ / c) ^ β)⁻¹
      ≤ ∫ ρ in Set.Ioc 0 R, c ^ β * ρ ^ (1 - β) :=
        setIntegral_mono_on hint0 hint1 measurableSet_Ioc hpt
    _ = c ^ β * (R ^ (2 - β) / (2 - β)) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le hR,
          integral_rpow (Or.inl (by linarith))]
        rw [show 1 - β + 1 = 2 - β by ring, Real.zero_rpow (by linarith), sub_zero]
    _ = c ^ β * R ^ (2 - β) / (2 - β) := by ring

/-- **The weighted area of a disc.** For `β < 1`, the integral of `(1 + (‖v‖/c)^β)⁻¹` over
the disc of radius `R` in the plane is at most `2π c^β R^{2-β} / (2 - β)`. -/
theorem integral_closedBall_inv_one_add_rpow_le {c R β : ℝ} (hc : 0 < c) (hR : 0 ≤ R)
    (hβ1 : β < 1) :
    ∫ v : ℝ^2, (Metric.closedBall (0 : ℝ^2) R).indicator (fun v ↦ (1 + (‖v‖ / c) ^ β)⁻¹) v ≤
      2 * π * (c ^ β * R ^ (2 - β) / (2 - β)) := by
  have hrad : (fun v : ℝ^2 ↦ (Metric.closedBall (0 : ℝ^2) R).indicator
      (fun v ↦ (1 + (‖v‖ / c) ^ β)⁻¹) v) =
      fun v ↦ (Set.Iic R).indicator (fun ρ : ℝ ↦ (1 + (ρ / c) ^ β)⁻¹) ‖v‖ := by
    funext v
    by_cases hv : ‖v‖ ≤ R
    · rw [Set.indicator_of_mem (by simpa using hv), Set.indicator_of_mem (by simpa using hv)]
    · rw [Set.indicator_of_notMem (by simpa using hv), Set.indicator_of_notMem (by simpa using hv)]
  rw [hrad, PDE.Analysis.integral_radialPlane]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hset : (∫ ρ in Set.Ioi (0 : ℝ), ρ * (Set.Iic R).indicator
      (fun ρ : ℝ ↦ (1 + (ρ / c) ^ β)⁻¹) ρ) = ∫ ρ in Set.Ioc 0 R, ρ * (1 + (ρ / c) ^ β)⁻¹ := by
    have h : (fun ρ : ℝ ↦ ρ * (Set.Iic R).indicator (fun ρ : ℝ ↦ (1 + (ρ / c) ^ β)⁻¹) ρ) =
        (Set.Iic R).indicator (fun ρ : ℝ ↦ ρ * (1 + (ρ / c) ^ β)⁻¹) := by
      funext ρ
      by_cases hρ : ρ ∈ Set.Iic R
      · simp [Set.indicator_of_mem hρ]
      · simp [Set.indicator_of_notMem hρ]
    rw [h, setIntegral_indicator measurableSet_Iic, Set.Ioi_inter_Iic]
  rw [hset]
  exact integral_Ioc_mul_inv_one_add_rpow_le hc hR hβ1

end

end Euler.Cylinder
