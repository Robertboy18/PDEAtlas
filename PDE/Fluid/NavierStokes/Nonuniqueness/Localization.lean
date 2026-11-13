/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import PDE.Fluid.Incompressible.DistributionalDivergence
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import PDE.Analysis.Calculus.Divergence.Locality
import PDE.Analysis.Calculus.DivergenceTrace
import PDE.Analysis.Calculus.Homogeneous
import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation
import PDE.Analysis.MeasureTheory.Lp.RadialPower

/-!
# Localization of a homogeneous datum of degree `-1`

Let `u` be a vector field on `ℝ^3` that is homogeneous of degree `-1`, `u(c x) = c⁻¹ u(x)` for
`c > 0`, smooth away from the origin and distributionally divergence free. The scale-invariant datum
`‖x‖⁻¹ A(x)` of a self-similar solution, with `A` homogeneous of degree zero, is such a field. For
every radius `R > 0` it splits as `u = u_loc + w`: the localized datum `u_loc` is compactly
supported, distributionally divergence free, smooth away from the origin, equal to `u` on the ball
of radius `R` and in `Lᵠ` for `q < 3`; the remainder `w` is smooth and divergence free, vanishes on
the ball of radius `R`, equals `u` outside the ball of radius `2R`, and
`‖w‖_{Lᵖ} = R^{3/p - 1} ‖w₁‖_{Lᵖ}` for `p > 3`. This is the decomposition `u_in = u_loc + w` of Hou,
Wang and Yang (Section 2.2, construction of the cutoff), where `‖w‖_{L⁴} ≲ R^{-1/4}` is the case
`p = 4`. The theorem `exists_localization` states it for `u = ‖x‖⁻¹ A`, with
`u_loc = localizedDatum u R`, `w = localizationRemainder u R` and `‖w‖_{L⁴} ≤ C R^{-1/4}` for
`C = localizationConstant u`.

## How it works

Hou, Wang and Yang obtain the decomposition from the Bogovskii operator, as Jia and Šverák do; we
need no Bogovskii operator and write the correction explicitly. With the radial cutoff
`χ_R(x) = θ(‖x‖² / R²)` (`localizationCutoff`) and the factor `k_R` defined by `∇χ_R(x) = k_R(x) x`
(`localizationCutoffSlope`) we set

`u_loc = χ_R u + k_R (‖x‖² u - ⟪u, x⟫ x)`,  `w = (1 - χ_R) u - k_R (‖x‖² u - ⟪u, x⟫ x)`.

The correction is orthogonal to `x`, so the derivative of the radial factor `k_R` does not enter its
divergence. Away from the origin `div u = 0`, and `⟪u, x⟫` is homogeneous of degree zero, so Euler's
relation (`fderiv_inner_apply_self_of_homogeneous`) gives
`div (‖x‖² u - ⟪u, x⟫ x) = 2 ⟪x, u⟫ - 3 ⟪u, x⟫ = -⟪u, x⟫`, which cancels `⟪∇χ_R, u⟫ = k_R ⟪x, u⟫`
(`divergence_localizedDatum`). The remainder `w = u - u_loc` vanishes near the origin, so it is
smooth with zero divergence everywhere (`divergence_localizationRemainder`), hence distributionally
divergence free, and `u_loc` inherits this (`distributionallyDivergenceFree_localizedDatum`).
Integrability comes from `‖u(x)‖ ≤ M ‖x‖⁻¹`: near the origin `‖x‖⁻¹` is in `Lᵠ` for `q < 3`
(`memLp_localizedDatum`), and away from it `(1 + ‖x‖)⁻¹` is in `Lᵖ` for `p > 3`
(`memLp_localizationRemainder`). Finally `w_R(x) = R⁻¹ w₁(x/R)` (`localizationRemainder_eq_smul`),
so the `Lᵖ` norms of the remainders scale exactly (`eLpNorm_localizationRemainder`,
`eLpNorm_localizationRemainder_four`).

## Implementation notes

For `u = ‖x‖⁻¹ A` the correction is `∇χ_R × (A × x/‖x‖)`; away from the origin `A × x/‖x‖` is a
vector potential of the datum, homogeneous of degree zero, and `u_loc` is the curl of
`χ_R (A × x/‖x‖)`. Neither axisymmetry nor spherical coordinates are used.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.2, construction of the
  cutoff, p. 12.
  <https://arxiv.org/abs/2509.25116v2>
* H. Jia and V. Šverák, "Are the incompressible 3d Navier–Stokes equations locally ill-posed in the
  natural energy space?", *J. Funct. Anal.* 268 (2015), no. 12, 3734-3766.
  <https://doi.org/10.1016/j.jfa.2015.04.006>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace ENNReal

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-! ### The radial cutoff -/

/-- The transition function `θ` of the localization cutoff in the variable `‖x‖² / R²`: smooth,
equal to one up to one and to zero from four on. -/
def localizationTransition (t : ℝ) : ℝ :=
  Real.smoothTransition ((4 - t) / 3)

/-- The cutoff transition function is smooth. -/
theorem contDiff_localizationTransition : ContDiff ℝ (⊤ : ℕ∞) localizationTransition :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const 3)

/-- The cutoff transition function equals one up to one. -/
theorem localizationTransition_of_le_one {t : ℝ} (ht : t ≤ 1) : localizationTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by norm_num)]; linarith)

/-- The cutoff transition function vanishes from four on. -/
theorem localizationTransition_of_four_le {t : ℝ} (ht : 4 ≤ t) : localizationTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num))

/-- The derivative of the cutoff transition function is smooth. -/
theorem contDiff_deriv_localizationTransition :
    ContDiff ℝ (⊤ : ℕ∞) (deriv localizationTransition) :=
  (contDiff_infty_iff_deriv.mp contDiff_localizationTransition).2

/-- The derivative of the cutoff transition function vanishes below one. -/
theorem deriv_localizationTransition_of_lt_one {t : ℝ} (ht : t < 1) :
    deriv localizationTransition t = 0 := by
  have h : localizationTransition =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact localizationTransition_of_le_one hs.le
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the cutoff transition function vanishes above four. -/
theorem deriv_localizationTransition_of_four_lt {t : ℝ} (ht : 4 < t) :
    deriv localizationTransition t = 0 := by
  have h : localizationTransition =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact localizationTransition_of_four_le hs.le
  rw [h.deriv_eq, deriv_const]

/-- The localization cutoff `χ_R(x) = θ(‖x‖² / R²)`: one on the closed ball of radius `R`, zero
outside the open ball of radius `2R`. -/
def localizationCutoff (R : ℝ) (x : ℝ^3) : ℝ :=
  localizationTransition (‖x‖ ^ 2 / R ^ 2)

/-- The radial factor `k_R(x) = (2 / R²) θ'(‖x‖² / R²)` of the cutoff gradient,
`∇χ_R(x) = k_R(x) x`. -/
def localizationCutoffSlope (R : ℝ) (x : ℝ^3) : ℝ :=
  2 / R ^ 2 * deriv localizationTransition (‖x‖ ^ 2 / R ^ 2)

/-- The localization cutoff is smooth. -/
theorem contDiff_localizationCutoff (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (localizationCutoff R) :=
  contDiff_localizationTransition.comp ((contDiff_norm_sq ℝ).div_const _)

/-- The radial factor of the cutoff gradient is smooth. -/
theorem contDiff_localizationCutoffSlope (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (localizationCutoffSlope R) :=
  contDiff_const.mul
    (contDiff_deriv_localizationTransition.comp ((contDiff_norm_sq ℝ).div_const _))

/-- The chain rule for a function of `‖x‖² / R²`. -/
private theorem hasFDerivAt_comp_normSq_div {g : ℝ → ℝ} (R : ℝ) (x : ℝ^3)
    (hg : DifferentiableAt ℝ g (‖x‖ ^ 2 / R ^ 2)) :
    HasFDerivAt (fun y : ℝ^3 ↦ g (‖y‖ ^ 2 / R ^ 2))
      ((deriv g (‖x‖ ^ 2 / R ^ 2) * (2 / R ^ 2)) • innerSL ℝ x) x := by
  have hq : HasFDerivAt (fun y : ℝ^3 ↦ ‖y‖ ^ 2 / R ^ 2)
      ((R ^ 2)⁻¹ • (2 • innerSL ℝ x)) x := by
    convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (R ^ 2)⁻¹ using 1
    funext y
    simp [div_eq_inv_mul]
  refine (hg.hasDerivAt.comp_hasFDerivAt x hq).congr_fderiv ?_
  ext v
  simp only [smul_apply, coe_innerSL_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The cutoff gradient is `k_R(x) x`. -/
theorem hasFDerivAt_localizationCutoff (R : ℝ) (x : ℝ^3) :
    HasFDerivAt (localizationCutoff R) (localizationCutoffSlope R x • innerSL ℝ x) x := by
  refine (hasFDerivAt_comp_normSq_div R x (contDiff_localizationTransition.differentiable
    (by simp) _)).congr_fderiv ?_
  rw [localizationCutoffSlope, mul_comm]

/-- The directional derivative of the cutoff is `k_R(x) ⟪x, v⟫`. -/
theorem fderiv_localizationCutoff_apply (R : ℝ) (x v : ℝ^3) :
    fderiv ℝ (localizationCutoff R) x v = localizationCutoffSlope R x * ⟪x, v⟫ := by
  rw [(hasFDerivAt_localizationCutoff R x).fderiv]
  simp

/-- The directional derivative of the radial factor is a multiple of `⟪x, v⟫`. -/
theorem fderiv_localizationCutoffSlope_apply (R : ℝ) (x v : ℝ^3) :
    fderiv ℝ (localizationCutoffSlope R) x v =
      deriv (fun t ↦ 2 / R ^ 2 * deriv localizationTransition t) (‖x‖ ^ 2 / R ^ 2) *
        (2 / R ^ 2) * ⟪x, v⟫ := by
  have hg : DifferentiableAt ℝ (fun t ↦ 2 / R ^ 2 * deriv localizationTransition t)
      (‖x‖ ^ 2 / R ^ 2) :=
    (contDiff_const.mul contDiff_deriv_localizationTransition).differentiable (by simp) _
  have h : HasFDerivAt (localizationCutoffSlope R) _ x := hasFDerivAt_comp_normSq_div R x hg
  rw [h.fderiv]
  simp

/-- The radial factor of the cutoff gradient has no derivative orthogonal to the position. -/
theorem fderiv_localizationCutoffSlope_apply_eq_zero (R : ℝ) {x v : ℝ^3} (hv : ⟪x, v⟫ = 0) :
    fderiv ℝ (localizationCutoffSlope R) x v = 0 := by
  rw [fderiv_localizationCutoffSlope_apply, hv, mul_zero]

/-- The cutoff equals one on the closed ball of radius `R`. -/
theorem localizationCutoff_of_norm_le {R : ℝ} (hR : 0 < R) {x : ℝ^3} (hx : ‖x‖ ≤ R) :
    localizationCutoff R x = 1 := by
  apply localizationTransition_of_le_one
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

/-- The cutoff vanishes outside the open ball of radius `2R`. -/
theorem localizationCutoff_of_two_mul_le {R : ℝ} (hR : 0 < R) {x : ℝ^3} (hx : 2 * R ≤ ‖x‖) :
    localizationCutoff R x = 0 := by
  apply localizationTransition_of_four_le
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The radial factor of the cutoff gradient vanishes on the open ball of radius `R`. -/
theorem localizationCutoffSlope_of_norm_lt {R : ℝ} (hR : 0 < R) {x : ℝ^3} (hx : ‖x‖ < R) :
    localizationCutoffSlope R x = 0 := by
  rw [localizationCutoffSlope, deriv_localizationTransition_of_lt_one, mul_zero]
  rw [div_lt_one (by positivity)]
  exact pow_lt_pow_left₀ hx (norm_nonneg _) two_ne_zero

/-- The radial factor of the cutoff gradient vanishes outside the closed ball of radius `2R`. -/
theorem localizationCutoffSlope_of_two_mul_lt {R : ℝ} (hR : 0 < R) {x : ℝ^3}
    (hx : 2 * R < ‖x‖) : localizationCutoffSlope R x = 0 := by
  rw [localizationCutoffSlope, deriv_localizationTransition_of_four_lt, mul_zero]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- The cutoff is nonnegative. -/
theorem localizationCutoff_nonneg (R : ℝ) (x : ℝ^3) : 0 ≤ localizationCutoff R x :=
  Real.smoothTransition.nonneg _

/-- The cutoff is at most one. -/
theorem localizationCutoff_le_one (R : ℝ) (x : ℝ^3) : localizationCutoff R x ≤ 1 :=
  Real.smoothTransition.le_one _

/-! ### Homogeneous fields of degree `-1` -/

section Homogeneous

variable {u : ℝ^3 → ℝ^3}

/-- Euler's relation for the radial component: `⟪u(x), x⟫` is homogeneous of degree zero, so
its derivative vanishes in the radial direction. -/
theorem fderiv_inner_apply_self_of_homogeneous
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x) {x : ℝ^3}
    (hd : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y ↦ ⟪u y, y⟫) x x = 0 := by
  have hf := (hd.inner ℝ differentiableAt_id).hasFDerivAt
  have h := HasFDerivAt.apply_self_eq_smul_of_eventuallyEq hf (w := fun _ ↦ (1 : ℝ))
    (hasDerivAt_const 1 1) ?_
  · simpa using h
  · filter_upwards [Ioi_mem_nhds one_pos] with t ht
    simp only [id, hhom x t ht, inner_smul_left, inner_smul_right, one_smul,
      RCLike.conj_to_real]
    field_simp [(ht : (0 : ℝ) < t).ne']

end Homogeneous

/-! ### The localized datum and the remainder -/

section Localization

variable {u : ℝ^3 → ℝ^3} {R : ℝ}

/-- The divergence correction `k_R(x) (‖x‖² u(x) - ⟪u(x), x⟫ x)` of the cut-off field
`χ_R u`. It is orthogonal to `x` and supported in the closed annulus `R ≤ ‖x‖ ≤ 2R`. -/
def localizationCorrection (u : ℝ^3 → ℝ^3) (R : ℝ) (x : ℝ^3) : ℝ^3 :=
  localizationCutoffSlope R x • (‖x‖ ^ 2 • u x - ⟪u x, x⟫ • x)

/-- The localized datum `u_loc = χ_R u + k_R (‖x‖² u - ⟪u, x⟫ x)`. -/
def localizedDatum (u : ℝ^3 → ℝ^3) (R : ℝ) (x : ℝ^3) : ℝ^3 :=
  localizationCutoff R x • u x + localizationCorrection u R x

/-- The localization remainder `w = (1 - χ_R) u - k_R (‖x‖² u - ⟪u, x⟫ x)`. -/
def localizationRemainder (u : ℝ^3 → ℝ^3) (R : ℝ) (x : ℝ^3) : ℝ^3 :=
  (1 - localizationCutoff R x) • u x - localizationCorrection u R x

/-- The datum is the sum of its localization and the remainder. -/
theorem localizedDatum_add_localizationRemainder (u : ℝ^3 → ℝ^3) (R : ℝ) (x : ℝ^3) :
    localizedDatum u R x + localizationRemainder u R x = u x := by
  simp only [localizedDatum, localizationRemainder, sub_smul, one_smul]
  abel

/-- The remainder depends on the radius only through its square. -/
theorem localizationRemainder_abs (u : ℝ^3 → ℝ^3) (R : ℝ) :
    localizationRemainder u |R| = localizationRemainder u R := by
  funext x
  simp only [localizationRemainder, localizationCorrection, localizationCutoff,
    localizationCutoffSlope, sq_abs]

/-- At radius zero the cutoff is one and the remainder vanishes. This relies on Lean's
convention `‖x‖² / 0 = 0`, so that `χ_0 = θ(0) = 1` and `k_0 = 0`. -/
theorem localizationRemainder_radius_zero (u : ℝ^3 → ℝ^3) : localizationRemainder u 0 = 0 := by
  funext x
  simp [localizationRemainder, localizationCorrection, localizationCutoff,
    localizationCutoffSlope, localizationTransition_of_le_one]

/-- The correction vanishes on the open ball of radius `R`. -/
theorem localizationCorrection_of_norm_lt (hR : 0 < R) {x : ℝ^3} (hx : ‖x‖ < R) :
    localizationCorrection u R x = 0 := by
  simp [localizationCorrection, localizationCutoffSlope_of_norm_lt hR hx]

/-- The correction vanishes outside the closed ball of radius `2R`. -/
theorem localizationCorrection_of_two_mul_lt (hR : 0 < R) {x : ℝ^3} (hx : 2 * R < ‖x‖) :
    localizationCorrection u R x = 0 := by
  simp [localizationCorrection, localizationCutoffSlope_of_two_mul_lt hR hx]

/-- The remainder vanishes on the open ball of radius `R`. -/
theorem localizationRemainder_of_norm_lt (hR : 0 < R) {x : ℝ^3} (hx : ‖x‖ < R) :
    localizationRemainder u R x = 0 := by
  simp [localizationRemainder, localizationCorrection_of_norm_lt hR hx,
    localizationCutoff_of_norm_le hR hx.le]

/-- The remainder equals the datum outside the closed ball of radius `2R`. -/
theorem localizationRemainder_of_two_mul_lt (hR : 0 < R) {x : ℝ^3} (hx : 2 * R < ‖x‖) :
    localizationRemainder u R x = u x := by
  simp [localizationRemainder, localizationCorrection_of_two_mul_lt hR hx,
    localizationCutoff_of_two_mul_le hR hx.le]

/-- The localized datum equals the datum on the open ball of radius `R`. -/
theorem localizedDatum_of_norm_lt (hR : 0 < R) {x : ℝ^3} (hx : ‖x‖ < R) :
    localizedDatum u R x = u x := by
  simp [localizedDatum, localizationCorrection_of_norm_lt hR hx,
    localizationCutoff_of_norm_le hR hx.le]

/-- The localized datum vanishes outside the closed ball of radius `2R`. -/
theorem localizedDatum_of_two_mul_lt (hR : 0 < R) {x : ℝ^3} (hx : 2 * R < ‖x‖) :
    localizedDatum u R x = 0 := by
  simp [localizedDatum, localizationCorrection_of_two_mul_lt hR hx,
    localizationCutoff_of_two_mul_le hR hx.le]

/-- The correction vanishes near the origin. -/
theorem localizationCorrection_eventuallyEq_zero (hR : 0 < R) :
    localizationCorrection u R =ᶠ[𝓝 0] 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ^3) hR] with y hy
  exact localizationCorrection_of_norm_lt hR (by simpa using hy)

/-- The remainder vanishes near the origin. -/
theorem localizationRemainder_eventuallyEq_zero (hR : 0 < R) :
    localizationRemainder u R =ᶠ[𝓝 0] 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ^3) hR] with y hy
  exact localizationRemainder_of_norm_lt hR (by simpa using hy)

/-- The correction is smooth wherever the datum is. -/
theorem contDiffAt_localizationCorrection {x : ℝ^3} (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (localizationCorrection u R) x :=
  (contDiff_localizationCutoffSlope R).contDiffAt.smul
    (((contDiff_norm_sq ℝ).contDiffAt.smul hu).sub
      ((hu.inner ℝ contDiffAt_id).smul contDiffAt_id))

/-- The localized datum is smooth wherever the datum is. -/
theorem contDiffAt_localizedDatum {x : ℝ^3} (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (localizedDatum u R) x :=
  ((contDiff_localizationCutoff R).contDiffAt.smul hu).add
    (contDiffAt_localizationCorrection hu)

/-- The remainder is smooth wherever the datum is. -/
theorem contDiffAt_localizationRemainder {x : ℝ^3} (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (localizationRemainder u R) x :=
  ((contDiff_const.sub (contDiff_localizationCutoff R)).contDiffAt.smul hu).sub
    (contDiffAt_localizationCorrection hu)

/-- For a datum smooth away from the origin, the correction is smooth. -/
theorem contDiff_localizationCorrection (hR : 0 < R)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x) :
    ContDiff ℝ (⊤ : ℕ∞) (localizationCorrection u R) := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · exact contDiffAt_const.congr_of_eventuallyEq (localizationCorrection_eventuallyEq_zero hR)
  · exact contDiffAt_localizationCorrection (hu x hx)

/-- For a datum smooth away from the origin, the remainder is smooth. -/
theorem contDiff_localizationRemainder (hR : 0 < R)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x) :
    ContDiff ℝ (⊤ : ℕ∞) (localizationRemainder u R) := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · exact contDiffAt_const.congr_of_eventuallyEq (localizationRemainder_eventuallyEq_zero hR)
  · exact contDiffAt_localizationRemainder (hu x hx)

/-- The correction is orthogonal to the position vector. -/
private theorem inner_localizationFlux (u : ℝ^3 → ℝ^3) (x : ℝ^3) :
    ⟪x, ‖x‖ ^ 2 • u x - ⟪u x, x⟫ • x⟫ = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_comm]
  ring

/-- At a point where a field homogeneous of degree `-1` is differentiable with zero divergence,
its localization has zero divergence. -/
theorem divergence_localizedDatum (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x)
    {x : ℝ^3} (hud : DifferentiableAt ℝ u x) (hdivu : PDE.divergence u x = 0) :
    PDE.divergence (localizedDatum u R) x = 0 := by
  have hχ : DifferentiableAt ℝ (localizationCutoff R) x :=
    (contDiff_localizationCutoff R).differentiable (by simp) x
  have hk : DifferentiableAt ℝ (localizationCutoffSlope R) x :=
    (contDiff_localizationCutoffSlope R).differentiable (by simp) x
  have hn : DifferentiableAt ℝ (fun y : ℝ^3 ↦ ‖y‖ ^ 2) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt
  have hs : DifferentiableAt ℝ (fun y ↦ ⟪u y, y⟫) x := hud.inner ℝ differentiableAt_fun_id
  have hF1 : DifferentiableAt ℝ (fun y ↦ ‖y‖ ^ 2 • u y) x := hn.smul hud
  have hF2 : DifferentiableAt ℝ (fun y ↦ ⟪u y, y⟫ • y) x := hs.smul differentiableAt_fun_id
  have hF : DifferentiableAt ℝ (fun y ↦ ‖y‖ ^ 2 • u y - ⟪u y, y⟫ • y) x := hF1.sub hF2
  have hdn : fderiv ℝ (fun y : ℝ^3 ↦ ‖y‖ ^ 2) x (u x) = 2 * ⟪x, u x⟫ := by
    rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
    simp
  have hid : PDE.divergence (fun y : ℝ^3 ↦ y) x = 3 := by
    rw [PDE.Analysis.divergence_eq_trace_fderiv (F := fun y ↦ y) differentiableAt_id,
      fderiv_fun_id, ContinuousLinearMap.coe_id, LinearMap.trace_id, finrank_euclideanSpace,
      Fintype.card_fin]
    norm_num
  have hdivF : PDE.divergence (fun y ↦ ‖y‖ ^ 2 • u y - ⟪u y, y⟫ • y) x = -⟪u x, x⟫ := by
    rw [PDE.divergence_sub (F := fun y ↦ ‖y‖ ^ 2 • u y) (G := fun y ↦ ⟪u y, y⟫ • y)
      (differentiableAt_euclidean.mp hF1) (differentiableAt_euclidean.mp hF2),
      PDE.Analysis.divergence_smul hn hud,
      PDE.Analysis.divergence_smul hs differentiableAt_fun_id, hdivu, hid, hdn,
      fderiv_inner_apply_self_of_homogeneous hhom hud, real_inner_comm]
    ring
  have hkF : fderiv ℝ (localizationCutoffSlope R) x (‖x‖ ^ 2 • u x - ⟪u x, x⟫ • x) = 0 := by
    rw [fderiv_localizationCutoffSlope_apply, inner_localizationFlux, mul_zero]
  have hsplit : localizedDatum u R = fun y ↦ localizationCutoff R y • u y +
      localizationCutoffSlope R y • (‖y‖ ^ 2 • u y - ⟪u y, y⟫ • y) := rfl
  rw [hsplit, PDE.divergence_add (F := fun y ↦ localizationCutoff R y • u y)
    (G := fun y ↦ localizationCutoffSlope R y • (‖y‖ ^ 2 • u y - ⟪u y, y⟫ • y))
    (differentiableAt_euclidean.mp (hχ.smul hud)) (differentiableAt_euclidean.mp (hk.smul hF)),
    PDE.Analysis.divergence_smul hχ hud, PDE.Analysis.divergence_smul hk hF, hdivF, hkF,
    fderiv_localizationCutoff_apply, hdivu, real_inner_comm]
  ring

/-- A distributionally divergence-free field smooth away from the origin has zero classical
divergence away from the origin. -/
private theorem divergence_eq_zero_of_ne_zero (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (hdiv : IncompressibleFlow.DistributionallyDivergenceFree u) {x : ℝ^3} (hx : x ≠ 0) :
    PDE.divergence u x = 0 :=
  hdiv.divergence_eq_zero_of_contDiffOn isOpen_compl_singleton
    (fun y hy ↦ ((hu y hy).of_le (by simp)).contDiffWithinAt) hx

/-- The remainder of a divergence-free datum homogeneous of degree `-1` and smooth away from
the origin has zero classical divergence everywhere. -/
theorem divergence_localizationRemainder (hR : 0 < R)
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (hdiv : IncompressibleFlow.DistributionallyDivergenceFree u) (x : ℝ^3) :
    PDE.divergence (localizationRemainder u R) x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact (localizationRemainder_eventuallyEq_zero hR).divergence_eq_zero
  · have hud : DifferentiableAt ℝ u x := (hu x hx).differentiableAt (by simp)
    have hrem : localizationRemainder u R = fun y ↦ u y - localizedDatum u R y := by
      funext y
      rw [← localizedDatum_add_localizationRemainder u R y]
      abel
    rw [hrem, PDE.divergence_sub (differentiableAt_euclidean.mp hud)
      (differentiableAt_euclidean.mp
        ((contDiffAt_localizedDatum (hu x hx)).differentiableAt (by simp))),
      divergence_eq_zero_of_ne_zero hu hdiv hx,
      divergence_localizedDatum hhom hud (divergence_eq_zero_of_ne_zero hu hdiv hx), sub_zero]

/-- The remainder is distributionally divergence free. -/
theorem distributionallyDivergenceFree_localizationRemainder (hR : 0 < R)
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (hdiv : IncompressibleFlow.DistributionallyDivergenceFree u) :
    IncompressibleFlow.DistributionallyDivergenceFree (localizationRemainder u R) :=
  IncompressibleFlow.SpatialFieldDivergenceFree.distributionallyDivergenceFree
    (divergence_localizationRemainder hR hhom hu hdiv)
    ((contDiff_localizationRemainder hR hu).of_le (by simp))

/-- The localized datum is distributionally divergence free. -/
theorem distributionallyDivergenceFree_localizedDatum (hR : 0 < R)
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (hdiv : IncompressibleFlow.DistributionallyDivergenceFree u) :
    IncompressibleFlow.DistributionallyDivergenceFree (localizedDatum u R) := by
  have h : localizedDatum u R = u - localizationRemainder u R := funext fun y ↦
    eq_sub_of_add_eq (localizedDatum_add_localizationRemainder u R y)
  rw [h]
  exact hdiv.sub (distributionallyDivergenceFree_localizationRemainder hR hhom hu hdiv)

end Localization

/-! ### Integrability and scaling -/

section Integrability

variable {u : ℝ^3 → ℝ^3} {R : ℝ}

/-- The correction has compact support. -/
theorem hasCompactSupport_localizationCorrection (hR : 0 < R) :
    HasCompactSupport (localizationCorrection u R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) (2 * R)) fun x hx ↦
    localizationCorrection_of_two_mul_lt hR (by simpa using hx)

/-- The localized datum has compact support. -/
theorem hasCompactSupport_localizedDatum (hR : 0 < R) :
    HasCompactSupport (localizedDatum u R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) (2 * R)) fun x hx ↦
    localizedDatum_of_two_mul_lt hR (by simpa using hx)

/-- The localized datum lies in `Lᵠ` for every `q < 3`. -/
theorem memLp_localizedDatum (hR : 0 < R)
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x) {q : ℝ≥0∞} (hq : q < 3) :
    MemLp (localizedDatum u R) q volume := by
  obtain ⟨M, hM0, hM⟩ :=
    PDE.exists_norm_le_mul_inv_norm_of_homogeneous hhom fun x hx ↦ (hu x hx).continuousAt
  have hcorr : MemLp (localizationCorrection u R) q volume :=
    (contDiff_localizationCorrection hR hu).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_localizationCorrection hR)
  have hmeas : AEStronglyMeasurable (fun x ↦ localizationCutoff R x • u x) volume :=
    (contDiff_localizationCutoff R).continuous.aestronglyMeasurable.smul
      (PDE.aestronglyMeasurable_of_continuousAt_of_ne fun x hx ↦ (hu x hx).continuousAt)
  have hmain : MemLp (fun x ↦ localizationCutoff R x • u x) q volume := by
    rcases eq_or_ne q 0 with rfl | hq0
    · exact memLp_zero_iff_aestronglyMeasurable.mpr hmeas
    · set B := Metric.closedBall (0 : ℝ^3) (2 * R)
      have hqr : q.toReal < 3 := by
        have h := (ENNReal.toReal_lt_toReal hq.ne_top (by simp)).mpr hq
        simpa using h
      have hg : MemLp (B.indicator fun x ↦ M * ‖x - 0‖ ^ (-1 : ℝ)) q volume := by
        rw [memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet]
        exact (memLp_norm_sub_rpow_of_isBounded (by simp) hq0 hq.ne_top
          (by simpa using hqr) 0 Metric.isBounded_closedBall).const_mul M
      refine hg.of_le hmeas (Eventually.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx, sub_zero, Real.rpow_neg_one, norm_smul,
          Real.norm_of_nonneg (localizationCutoff_nonneg R x),
          Real.norm_of_nonneg (by positivity)]
        calc localizationCutoff R x * ‖u x‖ ≤ 1 * ‖u x‖ :=
              mul_le_mul_of_nonneg_right (localizationCutoff_le_one R x) (norm_nonneg _)
          _ ≤ M * ‖x‖⁻¹ := by rw [one_mul]; exact hM x
      · have h2 : 2 * R < ‖x‖ := by simpa [B] using hx
        rw [indicator_of_notMem hx, localizationCutoff_of_two_mul_le hR h2.le]
        simp
  exact hmain.add hcorr

/-- The remainder lies in `Lᵖ` for every finite `p > 3` and every radius: a negative radius
gives the remainder at `|R|`, and radius zero gives the zero field. -/
theorem memLp_localizationRemainder
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x) {p : ℝ≥0∞} (hp : 3 < p) (hp' : p ≠ ∞) :
    MemLp (localizationRemainder u R) p volume := by
  wlog hR : 0 < R generalizing R
  · rcases eq_or_ne R 0 with rfl | hR0
    · rw [localizationRemainder_radius_zero]
      exact MemLp.zero
    · rw [← localizationRemainder_abs]
      exact this (abs_pos.mpr hR0)
  obtain ⟨M, hM0, hM⟩ :=
    PDE.exists_norm_le_mul_inv_norm_of_homogeneous hhom fun x hx ↦ (hu x hx).continuousAt
  have hp0 : p ≠ 0 := (lt_trans (by norm_num) hp).ne'
  have hpr : 3 < p.toReal := by
    have h := (ENNReal.toReal_lt_toReal (by simp) hp').mpr hp
    simpa using h
  have hcorr : MemLp (localizationCorrection u R) p volume :=
    (contDiff_localizationCorrection hR hu).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_localizationCorrection hR)
  have hmeas : AEStronglyMeasurable (fun x ↦ (1 - localizationCutoff R x) • u x) volume :=
    (continuous_const.sub (contDiff_localizationCutoff R).continuous).aestronglyMeasurable.smul
      (PDE.aestronglyMeasurable_of_continuousAt_of_ne fun x hx ↦ (hu x hx).continuousAt)
  set C := M * (1 + R⁻¹)
  have hbound (x : ℝ^3) : ‖(1 - localizationCutoff R x) • u x‖ ≤ C * (1 + ‖x‖)⁻¹ := by
    by_cases hx : ‖x‖ < R
    · rw [localizationCutoff_of_norm_le hR hx.le, sub_self, zero_smul, norm_zero]
      positivity
    · have hRx : R ≤ ‖x‖ := not_lt.mp hx
      have hxpos : 0 < ‖x‖ := hR.trans_le hRx
      rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr (localizationCutoff_le_one R x))]
      calc (1 - localizationCutoff R x) * ‖u x‖ ≤ 1 * (M * ‖x‖⁻¹) :=
            mul_le_mul (by linarith [localizationCutoff_nonneg R x]) (hM x) (norm_nonneg _)
              zero_le_one
        _ ≤ C * (1 + ‖x‖)⁻¹ := by
          have h1 : 1 ≤ ‖x‖ * R⁻¹ := by
            rw [← div_eq_mul_inv]; exact (one_le_div hR).mpr hRx
          have h2 : ‖x‖⁻¹ ≤ (1 + R⁻¹) * (1 + ‖x‖)⁻¹ := by
            rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hxpos (by positivity)]
            nlinarith
          calc 1 * (M * ‖x‖⁻¹) = M * ‖x‖⁻¹ := one_mul _
            _ ≤ M * ((1 + R⁻¹) * (1 + ‖x‖)⁻¹) := mul_le_mul_of_nonneg_left h2 hM0
            _ = C * (1 + ‖x‖)⁻¹ := by rw [mul_assoc]
  have hmain : MemLp (fun x ↦ (1 - localizationCutoff R x) • u x) p volume := by
    refine (integrable_norm_rpow_iff hmeas hp0 hp').mp ?_
    refine ((integrable_one_add_norm (μ := volume) (E := ℝ^3) (r := p.toReal)
      (by simpa using hpr)).const_mul (C ^ p.toReal)).mono'
      ((hmeas.norm.aemeasurable.pow_const _).aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity),
      ← Real.inv_rpow (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hbound x) (by positivity)
  exact hmain.sub hcorr

/-- The remainder at radius `R` is the remainder at radius one rescaled as a field homogeneous
of degree `-1`: `w_R(x) = R⁻¹ w₁(x / R)`. -/
theorem localizationRemainder_eq_smul (hR : 0 < R)
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x) (x : ℝ^3) :
    localizationRemainder u R x = R⁻¹ • localizationRemainder u 1 (R⁻¹ • x) := by
  have hnorm : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  have harg : ‖R⁻¹ • x‖ ^ 2 / 1 ^ 2 = ‖x‖ ^ 2 / R ^ 2 := by
    rw [hnorm]; field_simp
  have hχ : localizationCutoff 1 (R⁻¹ • x) = localizationCutoff R x := by
    simp only [localizationCutoff, harg]
  have hk : localizationCutoffSlope 1 (R⁻¹ • x) = R ^ 2 * localizationCutoffSlope R x := by
    simp only [localizationCutoffSlope, harg]
    field_simp
  have hux : u (R⁻¹ • x) = R • u x := by rw [hhom x R⁻¹ (inv_pos.mpr hR), inv_inv]
  simp only [localizationRemainder, localizationCorrection, hχ, hk, hux, hnorm,
    real_inner_smul_left, real_inner_smul_right]
  match_scalars <;> field_simp

/-- Dilating the remainder as a field homogeneous of degree `-1` divides the radius:
`c w_R(c x) = w_{c⁻¹ R}(x)` for `c > 0`. -/
theorem localizationRemainder_smul_apply (hR : 0 < R)
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x) {c : ℝ} (hc : 0 < c) (x : ℝ^3) :
    c • localizationRemainder u R (c • x) = localizationRemainder u (c⁻¹ * R) x := by
  rw [localizationRemainder_eq_smul hR hhom, localizationRemainder_eq_smul
    (mul_pos (inv_pos.mpr hc) hR) hhom, smul_smul, smul_smul]
  congr 1
  · field_simp
  · congr 1; congr 1; field_simp

/-- The `Lᵖ` norm of the remainder scales as `R^{3/p - 1}`, which is `R^{-(p-3)/p}`. -/
theorem eLpNorm_localizationRemainder (hR : 0 < R)
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x) {p : ℝ≥0∞} :
    eLpNorm (localizationRemainder u R) p volume =
      ENNReal.ofReal (R ^ (3 / p.toReal - 1)) * eLpNorm (localizationRemainder u 1) p volume := by
  have hfun : localizationRemainder u R =
      R⁻¹ • fun x ↦ localizationRemainder u 1 (R⁻¹ • x) :=
    funext fun x ↦ localizationRemainder_eq_smul hR hhom x
  rw [hfun, eLpNorm_const_smul, eLpNorm_comp_smul
    (contDiff_localizationRemainder one_pos hu).continuous.aestronglyMeasurable
    (inv_ne_zero hR.ne'), dilationFactor, finrank_euclideanSpace_fin, inv_pow, inv_inv,
    abs_of_pos (by positivity), Real.enorm_eq_ofReal (inv_nonneg.mpr hR.le), ← mul_assoc,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hR.le)]
  congr 2
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ← Real.rpow_natCast, ← Real.rpow_mul hR.le,
    Real.rpow_sub hR, Real.rpow_one]
  rw [mul_one_div, div_eq_inv_mul (R ^ _) R]
  norm_cast

end Integrability

/-! ### The localization theorem -/

section Theorem

variable {u : ℝ^3 → ℝ^3} {R : ℝ}

/-- The constant of the localization estimate: the `L⁴` norm of the remainder at radius one. -/
def localizationConstant (u : ℝ^3 → ℝ^3) : ℝ :=
  (eLpNorm (localizationRemainder u 1) 4 volume).toReal

/-- The `L⁴` norm of the remainder is `C R^{-1/4}`, with `C` independent of `R`. -/
theorem eLpNorm_localizationRemainder_four (hR : 0 < R)
    (hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c⁻¹ • u x)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) u x) :
    eLpNorm (localizationRemainder u R) 4 volume =
      ENNReal.ofReal (localizationConstant u * R ^ (-(1 / 4 : ℝ))) := by
  have hfin : eLpNorm (localizationRemainder u 1) 4 volume ≠ ∞ :=
    (memLp_localizationRemainder (R := 1) hhom hu (by norm_num) (by simp)).eLpNorm_ne_top
  rw [eLpNorm_localizationRemainder hR hhom hu, localizationConstant,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin, mul_comm]
  norm_num

/-- Localization of the scale-invariant datum `‖x‖⁻¹ A(x)` (Hou, Wang and Yang,
Section 2.2). For an angular profile `A` homogeneous of degree zero and
smooth away from the origin, with `‖x‖⁻¹ A(x)` distributionally divergence free, and a radius
`R > 0`, the datum is `u_loc + w` with `u_loc` compactly supported, distributionally divergence
free, in `Lᵠ` for `q < 3` and smooth away from the origin, and `w` vanishing on the ball of
radius `R`, equal to the datum outside the ball of radius `2R`, with
`‖w‖_{L⁴} ≤ C R^{-1/4}` for the constant `C = localizationConstant (‖·‖⁻¹ • A)`. The fields are
`localizedDatum` and `localizationRemainder`, and `w` is moreover smooth and divergence free.
No axisymmetry of `A` is needed. -/
theorem exists_localization {A : ℝ^3 → ℝ^3}
    (hA : ∀ x (c : ℝ), 0 < c → A (c • x) = A x)
    (hA' : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) A x)
    (hdiv : IncompressibleFlow.DistributionallyDivergenceFree (fun x ↦ ‖x‖⁻¹ • A x))
    (hR : 0 < R) :
    ∃ uloc w : ℝ^3 → ℝ^3, (∀ x, ‖x‖⁻¹ • A x = uloc x + w x) ∧ HasCompactSupport uloc ∧
      IncompressibleFlow.DistributionallyDivergenceFree uloc ∧
      (∀ q : ℝ≥0∞, q < 3 → MemLp uloc q volume) ∧
      (∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) uloc x) ∧ (∀ x, ‖x‖ < R → w x = 0) ∧
      (∀ x, 2 * R < ‖x‖ → w x = ‖x‖⁻¹ • A x) ∧
      eLpNorm w 4 volume ≤
        ENNReal.ofReal (localizationConstant (fun x ↦ ‖x‖⁻¹ • A x) * R ^ (-(1 / 4 : ℝ))) := by
  have hhom := fun x (c : ℝ) (hc : 0 < c) ↦ PDE.inv_norm_smul_apply_smul_of_homogeneous hA x hc
  have hu : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ ‖y‖⁻¹ • A y) x :=
    fun x hx ↦ PDE.contDiffAt_inv_norm_smul hx (hA' x hx)
  exact ⟨_, _,
    fun x ↦ (localizedDatum_add_localizationRemainder (fun y ↦ ‖y‖⁻¹ • A y) R x).symm,
    hasCompactSupport_localizedDatum hR,
    distributionallyDivergenceFree_localizedDatum hR hhom hu hdiv,
    fun q hq ↦ memLp_localizedDatum hR hhom hu hq,
    fun x hx ↦ contDiffAt_localizedDatum (hu x hx),
    fun x hx ↦ localizationRemainder_of_norm_lt hR hx,
    fun x hx ↦ localizationRemainder_of_two_mul_lt hR hx,
    (eLpNorm_localizationRemainder_four hR hhom hu).le⟩

end Theorem

end NavierStokes.Nonuniqueness
