/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.SphericalForm
import PDE.FDeriv.Calculus

/-!
# Scaling and normalization of the ball modes

The modes on the ball of radius `R` are dilations of the modes on the unit ball:
`mode R meridional l α (R • y) = R^(l-1) • mode 1 meridional l α y` and
`mode R azimuthal l α (R • y) = R^l • mode 1 azimuthal l α y`.

`besselBasis` has the radial profiles and the coefficients of the unnormalized basis of Hou,
Wang and Yang's code (`Ur_func` with the coefficients of `preprocess_para!`), rescaled from the
unit ball to `B(0, R)`: `c_Y R^(-(l-1)) • mode R meridional l α` with
`c_Y = (α² - l(l-1)(l+2)) √(2/π) α^(l-1) / (l(l+1))`, the zero mode `e_z` at the meridional
root `α = 0`, and `√(2α/π) α^l R^(-l) • mode R azimuthal l α`. At every root its spherical
profiles are `Ur_func`'s formulas with the angular factors `S_l` and `S_l'`
(`besselBasis_meridional_point`, `besselBasis_azimuthal_point`); the meridional identity uses
the boundary condition through `c_Y b = A`. The basis functions keep the symmetries of the
modes: they commute with the rotations about the axis and have the equatorial parity
`modeParity k l` (the zero mode `e_z` is odd). Away from the meridional root `α = 0` a basis
function is `besselBasisScale R k l α` times its mode (`besselBasis_eq_besselBasisScale_smul`);
the azimuthal factor is positive for `α > 0` and the meridional one vanishes only at
`α² = l(l-1)(l+2)`. The basis functions are smooth and divergence free. Finally, every mode of
degree `l ≥ 1` and root `α ≠ 0` has positive `L²` norm on the ball (`integral_norm_sq_mode_pos`).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 6.2, Lemma 4, p. 50, and
  Appendix E, Steps 3 and 5 of the proof of Lemma 4, pp. 64-65.
  <https://arxiv.org/abs/2509.25116v2>
* T. Hou, Y. Wang, and C. Yang, code for arXiv:2509.25116, file src/My_Bessel.jl, functions
  `preprocess_para!` and `Ur_func`.
  <https://github.com/HouGroup2026/3d-navier-stokes-nonuniqueness>
-/

@[expose] public noncomputable section

open MeasureTheory MvPolynomial Set Real
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff

namespace PDE.Fluid.Stokes.Ball

open CAS.Analysis.SpecialFunctions

/-! ### Scaling -/

/-- The radial Bessel factor of the ball of radius `R` at `R² s` is the factor of the unit
ball at `s`. -/
theorem besselRadial_div_mul_sq {R : ℝ} (hR : R ≠ 0) (m : ℕ) (α s : ℝ) :
    besselRadial m (α / R) (R ^ 2 * s) = besselRadial m α s := by
  rw [besselRadial, besselRadial, besselFactor, besselFactor, div_pow, ← mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero 2 hR)]

private theorem norm_smul_sq (R : ℝ) (y : ℝ^3) : ‖R • y‖ ^ 2 = R ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

private theorem eval_smul_zonalSolidHarmonicPolynomial (l : ℕ) (R : ℝ) (y : ℝ^3) :
    eval (R • y).ofLp (zonalSolidHarmonicPolynomial l) =
      R ^ l * eval y.ofLp (zonalSolidHarmonicPolynomial l) := by
  rw [WithLp.ofLp_smul, (isHomogeneous_zonalSolidHarmonicPolynomial l).eval_smul]

private theorem polynomialGradient_smul_zonalSolidHarmonicPolynomial (l : ℕ) (R : ℝ)
    (y : ℝ^3) :
    polynomialGradient (zonalSolidHarmonicPolynomial l) (R • y) =
      R ^ (l - 1) • polynomialGradient (zonalSolidHarmonicPolynomial l) y := by
  ext i
  simp only [polynomialGradient, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_smul]
  rw [((isHomogeneous_zonalSolidHarmonicPolynomial l).pderiv (i := i)).eval_smul]

/-- The meridional modes on the ball of radius `R` are dilations of those on the unit ball:
`mode R meridional l α (R • y) = R^(l-1) • mode 1 meridional l α y`. -/
theorem mode_meridional_smul {R : ℝ} (hR : R ≠ 0) (l : ℕ) (α : ℝ) (y : ℝ^3) :
    mode R .meridional l α (R • y) = R ^ (l - 1) • mode 1 .meridional l α y := by
  rcases l with _ | m
  · simp [mode_degree_zero]
  simp only [mode, meridionalModeField_eq, div_one, norm_smul_sq,
    eval_smul_zonalSolidHarmonicPolynomial, polynomialGradient_smul_zonalSolidHarmonicPolynomial,
    meridionalGradientRadial_apply, meridionalRadial_apply, besselRadial_div_mul_sq hR,
    Nat.add_sub_cancel]
  rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  · congr 1
    rw [div_pow]
    field_simp
    ring
  · congr 1
    rw [div_pow]
    field_simp

/-- The azimuthal modes on the ball of radius `R` are dilations of those on the unit ball:
`mode R azimuthal l α (R • y) = R^l • mode 1 azimuthal l α y`. -/
theorem mode_azimuthal_smul {R : ℝ} (hR : R ≠ 0) (l : ℕ) (α : ℝ) (y : ℝ^3) :
    mode R .azimuthal l α (R • y) = R ^ l • mode 1 .azimuthal l α y := by
  rcases l with _ | m
  · simp [mode_degree_zero]
  have hcomp (R' : ℝ) (z : ℝ^3) (i : Fin 3) : mode R' .azimuthal (m + 1) α z i =
      besselRadial (m + 1) (α / R') (‖z‖ ^ 2) *
        (z (i + 1) * polynomialGradient (zonalSolidHarmonicPolynomial (m + 1)) z (i + 2) -
          z (i + 2) * polynomialGradient (zonalSolidHarmonicPolynomial (m + 1)) z (i + 1)) := by
    simp only [mode, azimuthalModeField_apply, swirlPolynomial, map_sub, map_mul, eval_X]
    rfl
  ext i
  rw [PiLp.smul_apply, hcomp, hcomp, norm_smul_sq, besselRadial_div_mul_sq hR, div_one,
    polynomialGradient_smul_zonalSolidHarmonicPolynomial, Nat.add_sub_cancel]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-! ### Radial profiles -/

/-- The radial profile of the meridional mode of degree `m + 1`:
`Y(r) = (m + 1) r^m ((m + 2) g_{m+1}(κ r) + b)`. -/
theorem meridionalRadialProfile_succ (R : ℝ) (m : ℕ) (α r : ℝ) :
    meridionalRadialProfile R (m + 1) α r = (m + 1) * r ^ m *
      ((m + 2) * reducedSphericalBesselJ (m + 1) (α / R * r) +
        boundaryCoefficient (m + 1) α) := by
  simp only [meridionalRadialProfile, meridionalRadial_apply, meridionalGradientRadial_apply,
    besselRadial_sq,
    Nat.add_sub_cancel]
  push_cast
  ring

/-- The polar profile of the meridional mode of degree `m + 1`:
`X(r) = r^m ((m + 2) g_{m+1}(κ r) - (κ r)² g_{m+2}(κ r) + b)`. -/
theorem meridionalPolarProfile_succ (R : ℝ) (m : ℕ) (α r : ℝ) :
    meridionalPolarProfile R (m + 1) α r = r ^ m *
      ((m + 2) * reducedSphericalBesselJ (m + 1) (α / R * r) -
        (α / R * r) ^ 2 * reducedSphericalBesselJ (m + 2) (α / R * r) +
        boundaryCoefficient (m + 1) α) := by
  simp only [meridionalPolarProfile, meridionalGradientRadial_apply, besselRadial_sq,
    Nat.add_sub_cancel]
  push_cast
  ring

/-! ### The Bessel basis -/

/-- The factor `c_Y = (α² - l(l-1)(l+2)) √(2/π) α^(l-1) / (l(l+1))` that turns the meridional
mode on the unit ball into the meridional basis function. -/
def meridionalBasisConstant (l : ℕ) (α : ℝ) : ℝ :=
  (α ^ 2 - l * (l - 1) * (l + 2)) * √(2 / π) * α ^ (l - 1) / (l * (l + 1))

/-- The coefficient `A = -(α² - (l+2)(l-1)) J_{l+1/2}(α) / α^(3/2)` of `r^(l-1)` in the
meridional basis function, written as `-(α² - (l+2)(l-1)) √(2/π) j_l(α) / α` through
`J_{l+1/2}(x) = √(2x/π) j_l(x)`. -/
def besselBasisCoefficientA (l : ℕ) (α : ℝ) : ℝ :=
  -(α ^ 2 - (l + 2) * (l - 1)) * √(2 / π) * sphericalBesselJ l α / α

/-- The coefficient `B = (α² - l(l-1)(l+2)) / α^(3/2)` of the meridional basis function times
the factor `√(2α/π)` that turns `J_{l+1/2}` into `j_l`. -/
def besselBasisCoefficientB (l : ℕ) (α : ℝ) : ℝ :=
  (α ^ 2 - l * (l - 1) * (l + 2)) * √(2 / π) / α

/-- The divergence-free basis functions on the ball of radius `R`: the radial profiles of the
unit ball, with the coefficients `A` and `B`, evaluated at `x / R`, with the angular factors `S_l`
and `S_l'`. They are fixed multiples of the modes: `c_Y R^(-(l-1)) • mode R meridional l α` for
`α ≠ 0`, the zero mode `e_z` for the meridional root `α = 0`, and
`√(2α/π) α^l R^(-l) • mode R azimuthal l α`. For `0 < α`, `1 ≤ l` and `α² < l(l-1)(l+2)` the
factor `c_Y` is negative. -/
def besselBasis (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) : ℝ^3 → ℝ^3 :=
  match k with
  | .meridional =>
      if α = 0 then zeroMode
      else (meridionalBasisConstant l α * (R ^ (l - 1))⁻¹) • mode R .meridional l α
  | .azimuthal => (√(2 * α / π) * α ^ l * (R ^ l)⁻¹) • mode R .azimuthal l α

/-- The meridional basis function at the root `α = 0` is the zero mode. -/
theorem besselBasis_meridional_zero (R : ℝ) (l : ℕ) :
    besselBasis R .meridional l 0 = zeroMode := by
  simp [besselBasis]

/-- The zero mode commutes with the rotations about the axis. -/
theorem zeroMode_axialRotation (φ : ℝ) (x : ℝ^3) :
    zeroMode (axialRotation φ x) = axialRotation φ (zeroMode x) := by
  ext i
  fin_cases i <;> simp [zeroMode]

/-- The zero mode is odd under the equatorial reflection: `e_z = -σ e_z`. -/
theorem zeroMode_equatorialReflection (x : ℝ^3) :
    zeroMode (equatorialReflection x) = -equatorialReflection (zeroMode x) := by
  ext i
  fin_cases i <;> simp [zeroMode, equatorialReflection_apply_zero, equatorialReflection_apply_one,
    equatorialReflection_apply_two]

/-- The basis functions commute with the rotations about the axis. -/
theorem besselBasis_axialRotation (R : ℝ) (k : ModeKind) (l : ℕ) (α φ : ℝ) (x : ℝ^3) :
    besselBasis R k l α (axialRotation φ x) = axialRotation φ (besselBasis R k l α x) := by
  cases k with
  | meridional =>
    by_cases hα : α = 0
    · simp only [besselBasis, hα, ite_true]
      exact zeroMode_axialRotation φ x
    · simp only [besselBasis, hα, ite_false, Pi.smul_apply, map_smul]
      rw [coe_axialRotation, mode_axisRotation]
  | azimuthal =>
    simp only [besselBasis, Pi.smul_apply, map_smul]
    rw [coe_axialRotation, mode_axisRotation]

/-- The modes commute with the rotations about the axis. -/
theorem mode_isEquivariantUnderAxisRotation (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) :
    IsEquivariantUnderAxisRotation (mode R k l α) :=
  fun θ x ↦ mode_axisRotation R k l α θ x

/-- The zero mode commutes with the rotations about the axis. -/
theorem zeroMode_isEquivariantUnderAxisRotation : IsEquivariantUnderAxisRotation zeroMode :=
  fun θ x ↦ by rw [← axialRotation_apply, ← axialRotation_apply, zeroMode_axialRotation]

/-- The basis functions commute with the rotations about the axis. -/
theorem besselBasis_isEquivariantUnderAxisRotation (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) :
    IsEquivariantUnderAxisRotation (besselBasis R k l α) :=
  fun θ x ↦ by rw [← axialRotation_apply, ← axialRotation_apply, besselBasis_axialRotation]

/-- The basis functions have the equatorial parity of their modes,
`ψ(σ x) = modeParity k l • σ ψ(x)`, at every azimuthal root and every nonzero meridional
root. -/
theorem besselBasis_equatorialReflection (R : ℝ) (k : ModeKind) (l : ℕ) {α : ℝ}
    (hα : k = .azimuthal ∨ α ≠ 0) (x : ℝ^3) :
    besselBasis R k l α (equatorialReflection x) =
      modeParity k l • equatorialReflection (besselBasis R k l α x) := by
  cases k with
  | meridional =>
    have hα0 : α ≠ 0 := hα.resolve_left (by simp)
    simp only [besselBasis, hα0, ite_false, Pi.smul_apply, map_smul]
    rw [mode_equatorialReflection, smul_comm]
  | azimuthal =>
    simp only [besselBasis, Pi.smul_apply, map_smul]
    rw [mode_equatorialReflection, smul_comm]

/-! ### The basis functions as multiples of the modes -/

/-- The factor between a basis function and its mode away from the meridional root `α = 0`:
`c_Y R^(-(l-1))` for the meridional and `√(2α/π) α^l R^(-l)` for the azimuthal family. -/
def besselBasisScale (R : ℝ) : ModeKind → ℕ → ℝ → ℝ
  | .meridional, l, α => meridionalBasisConstant l α * (R ^ (l - 1))⁻¹
  | .azimuthal, l, α => √(2 * α / π) * α ^ l * (R ^ l)⁻¹

/-- Away from the meridional root `α = 0` a basis function is `besselBasisScale` times its
mode. -/
theorem besselBasis_eq_besselBasisScale_smul (R : ℝ) {k : ModeKind} {l : ℕ} {α : ℝ}
    (h : k = .azimuthal ∨ α ≠ 0) :
    besselBasis R k l α = besselBasisScale R k l α • mode R k l α := by
  cases k with
  | meridional =>
    have hα : α ≠ 0 := h.resolve_left (by simp)
    simp only [besselBasis, hα, ↓reduceIte, besselBasisScale]
  | azimuthal => rfl

/-- The meridional factor vanishes only at `α = 0` and at `α² = l(l-1)(l+2)`, where `c_Y = 0`. -/
theorem besselBasisScale_meridional_ne_zero {R α : ℝ} (hR : R ≠ 0) {l : ℕ} (hl : 1 ≤ l)
    (hα : α ≠ 0) (hγ : α ^ 2 ≠ l * (l - 1) * (l + 2)) :
    besselBasisScale R .meridional l α ≠ 0 := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hπ : 0 < √(2 / π) := Real.sqrt_pos.mpr (by positivity)
  simp only [besselBasisScale, meridionalBasisConstant]
  refine mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hγ) hπ.ne')
    (pow_ne_zero _ hα)) (by positivity)) (inv_ne_zero (pow_ne_zero _ hR))

/-- The azimuthal factor is positive for `R > 0` and `α > 0`. -/
theorem besselBasisScale_azimuthal_pos {R α : ℝ} (hR : 0 < R) (hα : 0 < α) (l : ℕ) :
    0 < besselBasisScale R .azimuthal l α := by
  have h : 0 < √(2 * α / π) := Real.sqrt_pos.mpr (by positivity)
  simp only [besselBasisScale]
  positivity

/-- The basis functions are smooth. -/
theorem besselBasis_contDiff (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) :
    ContDiff ℝ ∞ (besselBasis R k l α) := by
  by_cases h : k = .azimuthal ∨ α ≠ 0
  · rw [besselBasis_eq_besselBasisScale_smul R h]
    exact contDiff_const.smul (mode_contDiff R k l α)
  · obtain ⟨hk, rfl⟩ : k = .meridional ∧ α = 0 := by
      cases k
      · exact ⟨rfl, by simpa using h⟩
      · exact absurd (Or.inl rfl) h
    rw [hk, besselBasis_meridional_zero]
    exact contDiff_const

/-- The basis functions are divergence free. -/
theorem besselBasis_divergence_eq_zero (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) (x : ℝ^3) :
    divergence (besselBasis R k l α) x = 0 := by
  by_cases h : k = .azimuthal ∨ α ≠ 0
  · rw [besselBasis_eq_besselBasisScale_smul R h]
    change divergence (fun y ↦ besselBasisScale R k l α • mode R k l α y) x = 0
    rw [divergence_const_smul, mode_divergence_eq_zero, mul_zero]
  · obtain ⟨hk, rfl⟩ : k = .meridional ∧ α = 0 := by
      cases k
      · exact ⟨rfl, by simpa using h⟩
      · exact absurd (Or.inl rfl) h
    rw [hk, besselBasis_meridional_zero]
    exact zeroMode_divergence_eq_zero x

/-- At a meridional root, the boundary coefficient times `c_Y` is the coefficient `A`. -/
theorem meridionalBasisConstant_mul_boundaryCoefficient {m : ℕ} {α : ℝ} (hα0 : α ≠ 0)
    (hα : boundaryFunction .meridional (m + 1) α = 0) :
    meridionalBasisConstant (m + 1) α * boundaryCoefficient (m + 1) α =
      besselBasisCoefficientA (m + 1) α := by
  have T := reducedSphericalBesselJ_eq_sub (m + 1) α
  simp only [boundaryFunction] at hα
  push_cast at hα T
  have key : (α ^ 2 - (m + 1) * m * (m + 3)) *
      ((m + 2) * reducedSphericalBesselJ (m + 2) α - α ^ 2 * reducedSphericalBesselJ (m + 3) α) =
      -((m + 2) * (α ^ 2 - (m + 3) * m) * reducedSphericalBesselJ (m + 1) α) := by
    linear_combination (-(α ^ 2 - (m + 1) * m * (m + 3))) * T - (m + 3) * hα
  simp only [meridionalBasisConstant, boundaryCoefficient, besselBasisCoefficientA,
    sphericalBesselJ_eq_pow_mul, Nat.add_sub_cancel]
  push_cast
  field_simp
  rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl]
  linear_combination (α * α ^ m) * key

private theorem meridionalBasis_radial {R α : ℝ} (hR : R ≠ 0) (hα0 : α ≠ 0) {m : ℕ}
    (hα : boundaryFunction .meridional (m + 1) α = 0) {r : ℝ} (hr : r ≠ 0) :
    meridionalBasisConstant (m + 1) α * (R ^ m)⁻¹ * meridionalRadialProfile R (m + 1) α r =
      (m + 1) * besselBasisCoefficientA (m + 1) α * (r / R) ^ m +
        besselBasisCoefficientB (m + 1) α * sphericalBesselJ (m + 1) (α * (r / R)) / (r / R) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = R * s := ⟨r / R, by field_simp⟩
  have hs : s ≠ 0 := right_ne_zero_of_mul hr
  rw [← meridionalBasisConstant_mul_boundaryCoefficient hα0 hα, meridionalRadialProfile_succ,
    sphericalBesselJ_eq_pow_mul, show α / R * (R * s) = α * s by field_simp,
    show R * s / R = s by field_simp, mul_pow]
  simp only [meridionalBasisConstant, besselBasisCoefficientB, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

private theorem meridionalBasis_polar {R α : ℝ} (hR : R ≠ 0) (hα0 : α ≠ 0) {m : ℕ}
    (hα : boundaryFunction .meridional (m + 1) α = 0) {r : ℝ} (hr : r ≠ 0) :
    meridionalBasisConstant (m + 1) α * (R ^ m)⁻¹ * meridionalPolarProfile R (m + 1) α r =
      besselBasisCoefficientA (m + 1) α * (r / R) ^ m +
        besselBasisCoefficientB (m + 1) α / ((m + 1) * (m + 2)) *
          (α * sphericalBesselJ m (α * (r / R)) -
            (m + 1) * sphericalBesselJ (m + 1) (α * (r / R)) / (r / R)) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = R * s := ⟨r / R, by field_simp⟩
  have hs : s ≠ 0 := right_ne_zero_of_mul hr
  have T := reducedSphericalBesselJ_eq_sub m (α * s)
  rw [← meridionalBasisConstant_mul_boundaryCoefficient hα0 hα, meridionalPolarProfile_succ,
    sphericalBesselJ_eq_pow_mul, sphericalBesselJ_eq_pow_mul,
    show α / R * (R * s) = α * s by field_simp, show R * s / R = s by field_simp, T, mul_pow]
  simp only [meridionalBasisConstant, besselBasisCoefficientB, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- The meridional basis function in the spherical frame, at a root
`α ≠ 0` of degree `l ≥ 1` and radius `r ≠ 0`, with `s = r / R`: the radial component is
`(l A s^(l-1) + B j_l(α s) / s) S_l(θ)` and the polar component is
`(A s^(l-1) + (B / (l (l + 1))) (α j_{l-1}(α s) - l j_l(α s) / s)) S_l'(θ)`. With
`J_{ν+1/2}(x) = √(2x/π) j_ν(x)` these are `Ur_func`'s `Y` and `X` profiles
`l A s^(l-1) + B' J_{l+1/2}(α s) / s^(3/2)` and
`A s^(l-1) + (B' / (l (l + 1))) (α J_{l-1/2}(α s) - l J_{l+1/2}(α s) / s) / √s`, where
`B' = (α² - l(l-1)(l+2)) / α^(3/2)` is the coefficient of `preprocess_para!`. -/
theorem besselBasis_meridional_point {R α : ℝ} (hR : R ≠ 0) (hα0 : α ≠ 0) {l : ℕ}
    (hl : 1 ≤ l) (hα : boundaryFunction .meridional l α = 0) {r : ℝ} (hr : r ≠ 0) (θ φ : ℝ) :
    besselBasis R .meridional l α (point r θ φ) =
      ((l * besselBasisCoefficientA l α * (r / R) ^ (l - 1) +
          besselBasisCoefficientB l α * sphericalBesselJ l (α * (r / R)) / (r / R)) *
        zonalHarmonic l θ) • radialFrame θ φ +
      ((besselBasisCoefficientA l α * (r / R) ^ (l - 1) +
          besselBasisCoefficientB l α / (l * (l + 1)) *
            (α * sphericalBesselJ (l - 1) (α * (r / R)) -
              l * sphericalBesselJ l (α * (r / R)) / (r / R))) *
        zonalHarmonicDeriv l θ) • polarFrame θ φ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hl
  have h1 := meridionalBasis_radial hR hα0 hα hr
  have h2 := meridionalBasis_polar hR hα0 hα hr
  simp only [besselBasis, hα0, ite_false, Pi.smul_apply, mode_meridional_point, smul_add,
    smul_smul, Nat.add_sub_cancel]
  push_cast at h1 h2 ⊢
  rw [← mul_assoc, ← mul_assoc, h1, h2, show (m : ℝ) + 1 + 1 = m + 2 by ring]

/-- The azimuthal basis function in the spherical frame:
`√(2α/π) j_l(α r / R) S_l'(θ) e_φ`, which is `Ur_func`'s `Z` profile `J_{l+1/2}(α s) / √s`
at `s = r / R` through `J_{l+1/2}(x) = √(2x/π) j_l(x)`. -/
theorem besselBasis_azimuthal_point {R : ℝ} (hR : R ≠ 0) (l : ℕ) (α r θ φ : ℝ) :
    besselBasis R .azimuthal l α (point r θ φ) =
      (√(2 * α / π) * sphericalBesselJ l (α * (r / R)) * zonalHarmonicDeriv l θ) •
        azimuthalFrame φ := by
  simp only [besselBasis, Pi.smul_apply, mode_azimuthal_point, smul_smul]
  congr 1
  rw [azimuthalProfile, besselRadial_sq, sphericalBesselJ_eq_pow_mul,
    show α / R * r = α * (r / R) by ring, mul_pow, div_pow]
  field_simp

/-! ### Positivity of the norm -/

/-- Near the origin the reduced Bessel function at `κ t` is positive: some `t ∈ (0, R)` has
`g_m(κ t) > 0`. -/
private theorem exists_reducedSphericalBesselJ_pos {R : ℝ} (hR : 0 < R) (m : ℕ) (κ : ℝ) :
    ∃ t ∈ Ioo 0 R, 0 < reducedSphericalBesselJ m (κ * t) := by
  have hc : Continuous fun t : ℝ ↦ reducedSphericalBesselJ m (κ * t) :=
    (differentiable_reducedSphericalBesselJ m).continuous.comp (continuous_const.mul continuous_id)
  have h0 : 0 < reducedSphericalBesselJ m (κ * 0) := by
    rw [mul_zero]
    exact reducedSphericalBesselJ_zero_pos m
  have hev := (hc.continuousAt.eventually (lt_mem_nhds h0)).filter_mono
    (nhdsWithin_le_nhds (s := Ioi 0))
  have hIoo : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioo 0 R :=
    Ioo_mem_nhdsGT hR
  obtain ⟨t, ht1, ht2⟩ := (hIoo.and hev).exists
  exact ⟨t, ht1, ht2⟩

/-- For `α ≠ 0`, some `t ∈ (0, R)` has `(m + 2) g_{m+1}(κ t) + b ≠ 0`: otherwise the derivative
`-(m + 2) κ² t g_{m+2}(κ t)` would vanish on `(0, R)`, against `g_{m+2}(0) > 0`. -/
private theorem exists_meridional_factor_ne_zero {R : ℝ} (hR : 0 < R) {κ : ℝ} (hκ : κ ≠ 0)
    (m : ℕ) (b : ℝ) :
    ∃ t ∈ Ioo 0 R, (m + 2) * reducedSphericalBesselJ (m + 1) (κ * t) + b ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨t, ht, hpos⟩ := exists_reducedSphericalBesselJ_pos hR (m + 2) κ
  have hderiv : HasDerivAt (fun s ↦ (m + 2) * reducedSphericalBesselJ (m + 1) (κ * s) + b)
      ((m + 2) * (-(κ * t) * reducedSphericalBesselJ (m + 1 + 1) (κ * t) * κ)) t := by
    have h1 := (hasDerivAt_reducedSphericalBesselJ (m + 1) (κ * t)).comp t
      ((hasDerivAt_id t).const_mul κ)
    simpa [mul_one] using (h1.const_mul ((m : ℝ) + 2)).add_const b
  have hzero : (fun s ↦ (m + 2) * reducedSphericalBesselJ (m + 1) (κ * s) + b) =ᶠ[nhds t]
      fun _ ↦ 0 := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact h s hs
  have hd := hderiv.deriv
  rw [hzero.deriv_eq, deriv_const] at hd
  have htpos : 0 < t := ht.1
  have : (m + 2 : ℝ) * (-(κ * t) * reducedSphericalBesselJ (m + 1 + 1) (κ * t) * κ) ≠ 0 := by
    have hm : (m : ℝ) + 2 ≠ 0 := by positivity
    have hg : reducedSphericalBesselJ (m + 1 + 1) (κ * t) ≠ 0 := hpos.ne'
    have ht0 : t ≠ 0 := htpos.ne'
    exact mul_ne_zero hm (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hκ ht0)) hg) hκ)
  exact this hd.symm

/-- Some point of the ball where the mode does not vanish, for `l ≥ 1` and `α ≠ 0`. -/
theorem exists_mode_ne_zero {R : ℝ} (hR : 0 < R) (k : ModeKind) {l : ℕ} (hl : 1 ≤ l) {α : ℝ}
    (hα : α ≠ 0) : ∃ x ∈ Metric.ball (0 : ℝ^3) R, mode R k l α x ≠ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hl
  have hκ : α / R ≠ 0 := div_ne_zero hα hR.ne'
  have hball {t θ φ : ℝ} (ht : t ∈ Ioo 0 R) : point t θ φ ∈ Metric.ball (0 : ℝ^3) R := by
    rw [mem_ball_zero_iff, norm_point ht.1]
    exact ht.2
  cases k
  · obtain ⟨t, ht, hne⟩ := exists_meridional_factor_ne_zero hR hκ m (boundaryCoefficient (m + 1) α)
    refine ⟨point t 0 0, hball ht, fun h0 ↦ ?_⟩
    have h := congrArg (fun v : ℝ^3 ↦ ⟪radialFrame 0 0, v⟫) h0
    simp only [mode_meridional_point, inner_zero_right] at h
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_radialFrame] at h
    have hpol : ⟪radialFrame 0 0, polarFrame 0 0⟫ = 0 := by
      simp [radialFrame, polarFrame, PiLp.inner_apply, Fin.sum_univ_three]
    rw [hpol, meridionalRadialProfile_succ] at h
    simp only [zonalHarmonic, Real.cos_zero, legendre_eval_one, mul_one, one_pow, mul_zero,
      add_zero] at h
    have htm : t ^ m ≠ 0 := pow_ne_zero m ht.1.ne'
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    exact mul_ne_zero (mul_ne_zero hm htm) hne h
  · obtain ⟨t, ht, hpos⟩ := exists_reducedSphericalBesselJ_pos hR (m + 1) (α / R)
    have hP := derivative_legendre_succ_ne_zero m
    obtain ⟨c, hc, hPc⟩ : ∃ c ∈ Ioo (-1 : ℝ) 1,
        (Polynomial.derivative (legendre (m + 1))).eval c ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hP (Polynomial.eq_zero_of_infinite_isRoot _ ((Set.Ioo_infinite (by norm_num)).mono
        fun c hc ↦ hall c hc))
    refine ⟨point t (Real.arccos c) 0, hball ht, fun h0 ↦ ?_⟩
    rw [mode_azimuthal_point, smul_eq_zero] at h0
    have hφ : azimuthalFrame 0 ≠ 0 := fun h ↦ by
      have := congrArg (fun v : ℝ^3 ↦ v 1) h
      simp [azimuthalFrame] at this
    have hsin : 0 < Real.sin (Real.arccos c) := by
      rw [Real.sin_arccos]
      exact Real.sqrt_pos.mpr (by nlinarith [hc.1, hc.2])
    rcases h0 with h0 | h0
    · rw [azimuthalProfile, besselRadial_sq, zonalHarmonicDeriv,
        Real.cos_arccos hc.1.le hc.2.le] at h0
      have htl : t ^ (m + 1) ≠ 0 := pow_ne_zero _ ht.1.ne'
      have : reducedSphericalBesselJ (m + 1) (α / R * t) * t ^ (m + 1) *
          -(Real.sin (Real.arccos c) * (Polynomial.derivative (legendre (m + 1))).eval c) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hpos.ne' htl) (neg_ne_zero.mpr (mul_ne_zero hsin.ne' hPc))
      exact this h0
    · exact hφ h0

/-- The modes of degree `l ≥ 1` and root `α ≠ 0` have positive `L²` norm on the ball. -/
theorem integral_norm_sq_mode_pos {R : ℝ} (hR : 0 < R) (k : ModeKind) {l : ℕ} (hl : 1 ≤ l)
    {α : ℝ} (hα : α ≠ 0) : 0 < ∫ x in Metric.ball (0 : ℝ^3) R, ‖mode R k l α x‖ ^ 2 := by
  obtain ⟨x₀, hx₀, hne⟩ := exists_mode_ne_zero hR k hl hα
  have hcont : Continuous fun x ↦ ‖mode R k l α x‖ ^ 2 :=
    ((mode_contDiff R k l α).continuous.norm).pow 2
  have hint : IntegrableOn (fun x ↦ ‖mode R k l α x‖ ^ 2) (Metric.ball (0 : ℝ^3) R) :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      Metric.ball_subset_closedBall
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun x ↦ by positivity) hint]
  refine (hcont.isOpen_support.inter Metric.isOpen_ball).measure_pos volume ⟨x₀, ?_, hx₀⟩
  simpa [Function.mem_support] using hne

end PDE.Fluid.Stokes.Ball
