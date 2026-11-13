/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.PolynomialFields
public import PDE.Analysis.SpecialFunctions.SphericalBessel.SquaredArgument
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.FDeriv.Calculus

/-!
# Bessel fields built from a harmonic homogeneous polynomial

Let `P` be a harmonic polynomial on `ℝ^3`, homogeneous of degree `l`, and write
`B_m(s) = G_m(κ² s)` for the reduced spherical Bessel function in the squared variable
(`j_m(x) = x^m G_m(x²)`). Two vector fields solve the Stokes eigenvalue equation
`-Δψ + ∇p = κ² ψ`, `div ψ = 0` on all of `ℝ^3`:

* the meridional field with components
  `l κ² B_{l+1}(‖x‖²) P(x) xᵢ + ((l + 1) B_l - κ² ‖x‖² B_{l+1} + b)(‖x‖²) ∂ᵢP(x)` and pressure
  `p = κ² b P`, for any constant `b`;
* the swirl field `B_l(‖x‖²) (x × ∇P)(x)`, with pressure zero.

These are `meridionalModeField` with the pressure `meridionalModePressure`
(`laplacian_meridionalModeField`, `divergence_meridionalModeField`) and `azimuthalModeField`
(`laplacian_azimuthalModeField`, `divergence_azimuthalModeField`), and both are smooth. On the
sphere `‖x‖ = R` they satisfy the natural boundary condition `∑ⱼ xⱼ ∂ⱼ ψᵢ = p xᵢ` of the
Neumann-type Stokes problem under one scalar condition on `κ R`: `meridionalModeField_boundary` when
the meridional boundary expression vanishes at `R` and `b` is the boundary coefficient, and
`azimuthalModeField_boundary` (where `p = 0`) when `l B_l(R²) = κ² R² B_{l+1}(R²)`.

## How it works

Hou, Wang and Yang (Appendix E) solve the same eigenvalue problem in vector spherical harmonics; we
write the solutions as Cartesian fields instead. The first is `curl curl (x B_l P) + b ∇P` and the
second is `x × ∇(B_l P)`, but we never take a curl. Each component is a sum of terms `F(‖x‖²) Q(x)`
with a polynomial `Q` (the meridional field is `meridionalField` for the factors `meridionalRadial`
and `meridionalGradientRadial`), and `laplacian_radial_mul_eval`, `partialDeriv_radial_mul_eval` and
`sum_partialDeriv_radial_mul_eval_mul` reduce its Laplacian, divergence and radial derivative to
derivatives of `F`, using `∑ⱼ xⱼ ∂ⱼ P = l P` and `ΔP = 0`. What remains are scalar identities for
the radial factors: the radial equations `meridionalRadial_ode`, `meridionalGradientRadial_ode` and
`besselRadial_ode`, the divergence identity `meridional_divergence_identity`, and the radial
derivatives `meridionalRadial_radial`, `meridionalGradientRadial_radial` and `besselRadial_radial`.
We prove them for the families `besselFactor m μ = G_m(μ s)`,
`meridionalFactorA l μ = l μ G_{l+1}(μ s)` and
`meridionalFactorB l μ = (l + 1) G_l(μ s) - μ s G_{l+1}(μ s)` of a real parameter `μ` and take
`μ = κ²`; each comes down to the derivative rule `d/ds G_m(μ s) = -(μ / 2) G_{m+1}(μ s)` and the
three-term relation `besselFactor_eq_sub`. The boundary theorems substitute the radial derivatives
into `sum_partialDeriv_meridionalModeField_mul` and `sum_partialDeriv_radial_mul_eval_mul`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Appendix E, Steps 1, 3 and 5 of the
  proof of Lemma 4, (E.1), (E.6) and (E.7), pp. 63-65.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open PDE (partialDeriv laplacian divergence)
open MvPolynomial EuclideanLaplacian PDE.Analysis.SpecialFunctions
open scoped ContDiff

namespace PDE.Fluid.Stokes.Ball

/-! ### Radial factors -/

/-- The Bessel factor `G_m(μ s)` for a real parameter `μ`; for `μ = κ²` it is `g_m(κ √s)`. -/
def besselFactor (m : ℕ) (μ s : ℝ) : ℝ :=
  reducedSphericalBesselJSq m (μ * s)

/-- The Bessel factor is smooth. -/
theorem contDiff_besselFactor (m : ℕ) (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (besselFactor m μ) :=
  (contDiff_reducedSphericalBesselJSq m).comp (contDiff_const.mul contDiff_id)

/-- `d/ds G_m(μ s) = -(μ / 2) G_{m+1}(μ s)`. -/
theorem hasDerivAt_besselFactor (m : ℕ) (μ s : ℝ) :
    HasDerivAt (besselFactor m μ) (-(μ / 2) * besselFactor (m + 1) μ s) s := by
  have h := (hasDerivAt_reducedSphericalBesselJSq m (μ * s)).comp s
    ((hasDerivAt_id s).const_mul μ)
  refine h.congr_deriv ?_
  simp only [besselFactor, mul_one]
  ring

/-- The derivative of the Bessel factor as a function. -/
theorem deriv_besselFactor (m : ℕ) (μ : ℝ) :
    deriv (besselFactor m μ) = fun s ↦ -(μ / 2) * besselFactor (m + 1) μ s :=
  funext fun s ↦ (hasDerivAt_besselFactor m μ s).deriv

/-- The second derivative of the Bessel factor: `(μ² / 4) G_{m+2}(μ s)`. -/
theorem deriv_deriv_besselFactor (m : ℕ) (μ : ℝ) :
    deriv (deriv (besselFactor m μ)) = fun s ↦ μ ^ 2 / 4 * besselFactor (m + 2) μ s := by
  rw [deriv_besselFactor]
  funext s
  refine (((hasDerivAt_besselFactor (m + 1) μ s).const_mul (-(μ / 2))).congr_deriv ?_).deriv
  ring

/-- The three-term relation `G_m = (2m + 3) G_{m+1} - μ s G_{m+2}` of the Bessel factors. -/
theorem besselFactor_eq_sub (m : ℕ) (μ s : ℝ) :
    besselFactor m μ s = (2 * m + 3) * besselFactor (m + 1) μ s -
      μ * s * besselFactor (m + 2) μ s := by
  unfold besselFactor
  rw [reducedSphericalBesselJSq_eq_sub, mul_assoc]

/-- The factor `l μ G_{l+1}(μ s)` of `h x` in the meridional field of parameter `μ`. -/
def meridionalFactorA (l : ℕ) (μ s : ℝ) : ℝ :=
  l * μ * besselFactor (l + 1) μ s

/-- The factor `(l + 1) G_l(μ s) - μ s G_{l+1}(μ s)` of `∇h` in the meridional field of
parameter `μ`. -/
def meridionalFactorB (l : ℕ) (μ s : ℝ) : ℝ :=
  (l + 1) * besselFactor l μ s - μ * s * besselFactor (l + 1) μ s

/-- The factor of `h x` is smooth. -/
theorem contDiff_meridionalFactorA (l : ℕ) (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (meridionalFactorA l μ) :=
  contDiff_const.mul (contDiff_besselFactor _ _)

/-- The factor of `∇h` is smooth. -/
theorem contDiff_meridionalFactorB (l : ℕ) (μ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (meridionalFactorB l μ) :=
  (contDiff_const.mul (contDiff_besselFactor _ _)).sub
    ((contDiff_const.mul contDiff_id).mul (contDiff_besselFactor _ _))

/-- The derivative of the factor of `h x`: `-(l μ² / 2) G_{l+2}(μ s)`. -/
theorem deriv_meridionalFactorA (l : ℕ) (μ : ℝ) :
    deriv (meridionalFactorA l μ) = fun s ↦ -(l * μ ^ 2 / 2) * besselFactor (l + 2) μ s := by
  funext s
  refine (((hasDerivAt_besselFactor (l + 1) μ s).const_mul ((l : ℝ) * μ)).congr_deriv
    ?_).deriv
  ring

/-- The second derivative of the factor of `h x`: `(l μ³ / 4) G_{l+3}(μ s)`. -/
theorem deriv_deriv_meridionalFactorA (l : ℕ) (μ : ℝ) :
    deriv (deriv (meridionalFactorA l μ)) =
      fun s ↦ l * μ ^ 3 / 4 * besselFactor (l + 3) μ s := by
  rw [deriv_meridionalFactorA]
  funext s
  refine (((hasDerivAt_besselFactor (l + 2) μ s).const_mul (-((l : ℝ) * μ ^ 2 / 2))).congr_deriv
    ?_).deriv
  ring

/-- The derivative of the factor of `∇h`:
`-(μ / 2) (l + 3) G_{l+1}(μ s) + (μ² s / 2) G_{l+2}(μ s)`. -/
theorem deriv_meridionalFactorB (l : ℕ) (μ : ℝ) :
    deriv (meridionalFactorB l μ) = fun s ↦
      -(μ / 2) * (l + 3) * besselFactor (l + 1) μ s + μ ^ 2 * s / 2 * besselFactor (l + 2) μ s := by
  funext s
  have h := ((hasDerivAt_besselFactor l μ s).const_mul ((l : ℝ) + 1)).sub
    (((hasDerivAt_id s).const_mul μ).mul (hasDerivAt_besselFactor (l + 1) μ s))
  refine (h.congr_deriv ?_).deriv
  simp only [id]
  ring

/-- The second derivative of the factor of `∇h`:
`(μ² / 4) (l + 5) G_{l+2}(μ s) - (μ³ s / 4) G_{l+3}(μ s)`. -/
theorem deriv_deriv_meridionalFactorB (l : ℕ) (μ : ℝ) :
    deriv (deriv (meridionalFactorB l μ)) = fun s ↦
      μ ^ 2 / 4 * (l + 5) * besselFactor (l + 2) μ s -
        μ ^ 3 * s / 4 * besselFactor (l + 3) μ s := by
  rw [deriv_meridionalFactorB]
  funext s
  have h1 := (hasDerivAt_besselFactor (l + 1) μ s).const_mul (-(μ / 2) * ((l : ℝ) + 3))
  have h2 := ((hasDerivAt_id' s).const_mul (μ ^ 2 / 2)).mul (hasDerivAt_besselFactor (l + 2) μ s)
  have h : HasDerivAt (fun s ↦ -(μ / 2) * ((l : ℝ) + 3) * besselFactor (l + 1) μ s +
      μ ^ 2 * s / 2 * besselFactor (l + 2) μ s)
      (μ ^ 2 / 4 * (l + 5) * besselFactor (l + 2) μ s -
        μ ^ 3 * s / 4 * besselFactor (l + 3) μ s) s := by
    have h3 := h1.add h2
    refine (h3.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
    · ring
    · simp only [Pi.add_apply, Pi.mul_apply]
      ring
  exact h.deriv

section FactorIdentities

variable (l : ℕ) (μ s : ℝ)

/-- The radial equation of the factor of `h x`: `4 s A'' + (4l + 10) A' = -μ A`. -/
theorem meridionalFactorA_ode :
    4 * s * deriv (deriv (meridionalFactorA l μ)) s +
        (4 * ((l : ℝ) + 1) + 6) * deriv (meridionalFactorA l μ) s =
      -(μ * meridionalFactorA l μ s) := by
  have T := besselFactor_eq_sub (l + 1) μ s
  simp only [show l + 1 + 1 = l + 2 from rfl, show l + 1 + 2 = l + 3 from rfl] at T
  rw [deriv_deriv_meridionalFactorA, deriv_meridionalFactorA]
  simp only [meridionalFactorA]
  push_cast at T ⊢
  linear_combination ((l : ℝ) * μ ^ 2) * T

/-- The radial equation of the factor of `∇h` with zero pressure:
`2 A + 4 s B'' + (4l + 2) B' = -μ B`. -/
theorem meridionalFactorB_ode :
    2 * meridionalFactorA l μ s + 4 * s * deriv (deriv (meridionalFactorB l μ)) s +
        (4 * ((l : ℝ) - 1) + 6) * deriv (meridionalFactorB l μ) s =
      -(μ * meridionalFactorB l μ s) := by
  have T0 := besselFactor_eq_sub l μ s
  have T1 := besselFactor_eq_sub (l + 1) μ s
  simp only [show l + 1 + 1 = l + 2 from rfl, show l + 1 + 2 = l + 3 from rfl] at T1
  rw [deriv_deriv_meridionalFactorB, deriv_meridionalFactorB]
  simp only [meridionalFactorA, meridionalFactorB]
  push_cast at T0 T1 ⊢
  linear_combination (μ * ((l : ℝ) + 1)) * T0 - μ ^ 2 * s * T1

/-- The divergence identity `2 s A' + (l + 3) A + 2 l B' = 0` of the meridional factors. -/
theorem meridionalFactor_free :
    2 * s * deriv (meridionalFactorA l μ) s + ((l : ℝ) + 3) * meridionalFactorA l μ s +
      2 * l * deriv (meridionalFactorB l μ) s = 0 := by
  rw [deriv_meridionalFactorA, deriv_meridionalFactorB]
  simp only [meridionalFactorA]
  ring

/-- The vorticity profile `2 B' - A = -μ G_l(μ s)` of the meridional factors. -/
theorem meridionalFactor_vorticity :
    2 * deriv (meridionalFactorB l μ) s - meridionalFactorA l μ s =
      -μ * reducedSphericalBesselJSq l (μ * s) := by
  have T0 := besselFactor_eq_sub l μ s
  rw [deriv_meridionalFactorB]
  simp only [meridionalFactorA, besselFactor] at T0 ⊢
  linear_combination μ * T0

/-- The radial derivative of the factor of `h x`:
`2 s A' + (l + 1) A = μ l ((l + 1) G_{l+1} - μ s G_{l+2})`. -/
theorem meridionalFactorA_radial :
    2 * s * deriv (meridionalFactorA l μ) s + ((l : ℝ) + 1) * meridionalFactorA l μ s =
      μ * (l * ((l + 1) * besselFactor (l + 1) μ s - μ * s * besselFactor (l + 2) μ s)) := by
  rw [deriv_meridionalFactorA]
  simp only [meridionalFactorA]
  ring

/-- The radial derivative of the factor of `∇h`: `2 s B' + (l - 1) B` is the meridional
boundary expression minus `(l - 1)` times the boundary coefficient. -/
theorem meridionalFactorB_radial :
    2 * s * deriv (meridionalFactorB l μ) s + ((l : ℝ) - 1) * meridionalFactorB l μ s =
      (((l : ℝ) - 1) * (2 * l + 1) - μ * s) * besselFactor l μ s +
        (μ * s - l * (l - 1) * (l + 2)) * besselFactor (l + 1) μ s -
        ((l : ℝ) - 1) * (l * ((l + 1) * besselFactor (l + 1) μ s -
          μ * s * besselFactor (l + 2) μ s)) := by
  have T0 := besselFactor_eq_sub l μ s
  rw [deriv_meridionalFactorB]
  simp only [meridionalFactorB]
  linear_combination (μ * s - l * ((l : ℝ) - 1)) * T0

/-- The radial equation of the Bessel factor: `4 s G'' + (4l + 6) G' = -μ G`. -/
theorem besselFactor_ode :
    4 * s * deriv (deriv (besselFactor l μ)) s + (4 * (l : ℝ) + 6) * deriv (besselFactor l μ) s =
      -(μ * besselFactor l μ s) := by
  have T0 := besselFactor_eq_sub l μ s
  rw [deriv_deriv_besselFactor, deriv_besselFactor]
  push_cast at T0 ⊢
  linear_combination μ * T0

/-- The radial derivative of the Bessel factor: `2 s G' + l G = l G - μ s G_{l+1}`. -/
theorem besselFactor_radial :
    2 * s * deriv (besselFactor l μ) s + l * besselFactor l μ s =
      l * besselFactor l μ s - μ * s * besselFactor (l + 1) μ s := by
  rw [deriv_besselFactor]
  ring

end FactorIdentities

/-- The radial Bessel factor `B_m(s) = G_m(κ² s)`, so that `B_m(‖x‖²) = g_m(κ ‖x‖)`. -/
def besselRadial (m : ℕ) (κ s : ℝ) : ℝ :=
  besselFactor m (κ ^ 2) s

/-- The radial Bessel factor is smooth. -/
theorem contDiff_besselRadial (m : ℕ) (κ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (besselRadial m κ) :=
  contDiff_besselFactor m (κ ^ 2)

/-- `B_m' = -(κ² / 2) B_{m+1}`. -/
theorem hasDerivAt_besselRadial (m : ℕ) (κ s : ℝ) :
    HasDerivAt (besselRadial m κ) (-(κ ^ 2 / 2) * besselRadial (m + 1) κ s) s :=
  hasDerivAt_besselFactor m (κ ^ 2) s

/-- The derivative of the radial Bessel factor as a function. -/
theorem deriv_besselRadial (m : ℕ) (κ : ℝ) :
    deriv (besselRadial m κ) = fun s ↦ -(κ ^ 2 / 2) * besselRadial (m + 1) κ s :=
  deriv_besselFactor m (κ ^ 2)

/-- `B_m'' = (κ⁴ / 4) B_{m+2}`, from `G_m'' = G_{m+2} / 4`. -/
theorem deriv_deriv_besselRadial (m : ℕ) (κ : ℝ) :
    deriv (deriv (besselRadial m κ)) = fun s ↦ κ ^ 4 / 4 * besselRadial (m + 2) κ s := by
  have h : besselRadial m κ = besselFactor m (κ ^ 2) := rfl
  rw [h, deriv_deriv_besselFactor]
  funext s
  simp only [besselRadial]
  ring

/-- At `s = r²` the radial Bessel factor is the reduced Bessel function at `κ r`. -/
theorem besselRadial_sq (m : ℕ) (κ r : ℝ) :
    besselRadial m κ (r ^ 2) = reducedSphericalBesselJ m (κ * r) := by
  rw [besselRadial, besselFactor, reducedSphericalBesselJ_eq_sq, mul_pow]

/-- The three-term relation `B_m = (2m + 3) B_{m+1} - κ² s B_{m+2}`. -/
theorem besselRadial_eq_sub (m : ℕ) (κ s : ℝ) :
    besselRadial m κ s = (2 * m + 3) * besselRadial (m + 1) κ s -
      κ ^ 2 * s * besselRadial (m + 2) κ s :=
  besselFactor_eq_sub m (κ ^ 2) s

/-- The factor `l κ² B_{l+1}` of `P x` in the meridional field. -/
def meridionalRadial (l : ℕ) (κ s : ℝ) : ℝ :=
  meridionalFactorA l (κ ^ 2) s

/-- The factor `(l + 1) B_l - κ² s B_{l+1} + b` of `∇P` in the meridional field. -/
def meridionalGradientRadial (l : ℕ) (κ b s : ℝ) : ℝ :=
  meridionalFactorB l (κ ^ 2) s + b

/-- The factor of `P x` in the meridional field is smooth. -/
theorem contDiff_meridionalRadial (l : ℕ) (κ : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (meridionalRadial l κ) :=
  contDiff_meridionalFactorA l (κ ^ 2)

/-- The factor of `∇P` in the meridional field is smooth. -/
theorem contDiff_meridionalGradientRadial (l : ℕ) (κ b : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (meridionalGradientRadial l κ b) :=
  (contDiff_meridionalFactorB l (κ ^ 2)).add contDiff_const

/-- The factor of `P x` in terms of the radial Bessel factor: `l κ² B_{l+1}(s)`. -/
theorem meridionalRadial_apply (l : ℕ) (κ s : ℝ) :
    meridionalRadial l κ s = l * κ ^ 2 * besselRadial (l + 1) κ s :=
  rfl

/-- The factor of `∇P` in terms of the radial Bessel factors:
`(l + 1) B_l(s) - κ² s B_{l+1}(s) + b`. -/
theorem meridionalGradientRadial_apply (l : ℕ) (κ b s : ℝ) :
    meridionalGradientRadial l κ b s =
      (l + 1) * besselRadial l κ s - κ ^ 2 * s * besselRadial (l + 1) κ s + b :=
  rfl

private theorem meridionalRadial_eq (l : ℕ) (κ : ℝ) :
    meridionalRadial l κ = meridionalFactorA l (κ ^ 2) := rfl

private theorem deriv_meridionalGradientRadial_eq (l : ℕ) (κ b : ℝ) :
    deriv (meridionalGradientRadial l κ b) = deriv (meridionalFactorB l (κ ^ 2)) :=
  funext fun _ ↦ deriv_add_const _

/-- The derivative `(l κ² B_{l+1})' = -(l κ⁴ / 2) B_{l+2}`. -/
theorem deriv_meridionalRadial (l : ℕ) (κ : ℝ) :
    deriv (meridionalRadial l κ) = fun s ↦ -(l * κ ^ 4 / 2) * besselRadial (l + 2) κ s := by
  rw [meridionalRadial_eq, deriv_meridionalFactorA]
  funext s
  simp only [besselRadial]
  ring

/-- The second derivative `(l κ² B_{l+1})'' = (l κ⁶ / 4) B_{l+3}`. -/
theorem deriv_deriv_meridionalRadial (l : ℕ) (κ : ℝ) :
    deriv (deriv (meridionalRadial l κ)) =
      fun s ↦ l * κ ^ 6 / 4 * besselRadial (l + 3) κ s := by
  rw [meridionalRadial_eq, deriv_deriv_meridionalFactorA]
  funext s
  simp only [besselRadial]
  ring

/-- The derivative of the factor of `∇P`:
`-(κ² / 2) (l + 3) B_{l+1} + (κ⁴ s / 2) B_{l+2}`. -/
theorem deriv_meridionalGradientRadial (l : ℕ) (κ b : ℝ) :
    deriv (meridionalGradientRadial l κ b) = fun s ↦
      -(κ ^ 2 / 2) * (l + 3) * besselRadial (l + 1) κ s +
        κ ^ 4 * s / 2 * besselRadial (l + 2) κ s := by
  rw [deriv_meridionalGradientRadial_eq, deriv_meridionalFactorB]
  funext s
  simp only [besselRadial]
  ring

/-- The second derivative of the factor of `∇P`:
`(κ⁴ / 4) (l + 5) B_{l+2} - (κ⁶ s / 4) B_{l+3}`. -/
theorem deriv_deriv_meridionalGradientRadial (l : ℕ) (κ b : ℝ) :
    deriv (deriv (meridionalGradientRadial l κ b)) = fun s ↦
      κ ^ 4 / 4 * (l + 5) * besselRadial (l + 2) κ s -
        κ ^ 6 * s / 4 * besselRadial (l + 3) κ s := by
  rw [deriv_meridionalGradientRadial_eq, deriv_deriv_meridionalFactorB]
  funext s
  simp only [besselRadial]
  ring

/-! ### Radial identities -/

section Identities

variable (l : ℕ) (κ b s : ℝ)

/-- The radial equation of the factor of `P x`: `4 s F'' + (4l + 10) F' = -κ² F`. -/
theorem meridionalRadial_ode :
    4 * s * deriv (deriv (meridionalRadial l κ)) s +
        (4 * ((l : ℝ) + 1) + 6) * deriv (meridionalRadial l κ) s =
      -(κ ^ 2 * meridionalRadial l κ s) :=
  meridionalFactorA_ode l (κ ^ 2) s

/-- The radial equation of the factor of `∇P`, with the pressure `κ² b P`:
`2 F + 4 s G'' + (4l + 2) G' - κ² b = -κ² G`. -/
theorem meridionalGradientRadial_ode :
    2 * meridionalRadial l κ s + 4 * s * deriv (deriv (meridionalGradientRadial l κ b)) s +
        (4 * ((l : ℝ) - 1) + 6) * deriv (meridionalGradientRadial l κ b) s - κ ^ 2 * b =
      -(κ ^ 2 * meridionalGradientRadial l κ b s) := by
  rw [deriv_meridionalGradientRadial_eq]
  have h := meridionalFactorB_ode l (κ ^ 2) s
  simp only [meridionalRadial, meridionalGradientRadial]
  linear_combination h

/-- The divergence identity `2 s F' + (l + 3) F + 2 l G' = 0`. -/
theorem meridional_divergence_identity :
    2 * s * deriv (meridionalRadial l κ) s + ((l : ℝ) + 3) * meridionalRadial l κ s +
      2 * l * deriv (meridionalGradientRadial l κ b) s = 0 := by
  rw [deriv_meridionalGradientRadial_eq]
  exact meridionalFactor_free l (κ ^ 2) s

/-- The radial derivative of the factor of `P x`: `2 s F' + (l + 1) F`. -/
theorem meridionalRadial_radial :
    2 * s * deriv (meridionalRadial l κ) s + ((l : ℝ) + 1) * meridionalRadial l κ s =
      κ ^ 2 * (l * ((l + 1) * besselRadial (l + 1) κ s -
        κ ^ 2 * s * besselRadial (l + 2) κ s)) :=
  meridionalFactorA_radial l (κ ^ 2) s

/-- The radial derivative of the factor of `∇P`: `2 s G' + (l - 1) G` equals the meridional
boundary expression plus `(l - 1)` times the defect of `b`. -/
theorem meridionalGradientRadial_radial :
    2 * s * deriv (meridionalGradientRadial l κ b) s +
        ((l : ℝ) - 1) * meridionalGradientRadial l κ b s =
      (((l : ℝ) - 1) * (2 * l + 1) - κ ^ 2 * s) * besselRadial l κ s +
        (κ ^ 2 * s - l * (l - 1) * (l + 2)) * besselRadial (l + 1) κ s +
        ((l : ℝ) - 1) * (b - l * ((l + 1) * besselRadial (l + 1) κ s -
          κ ^ 2 * s * besselRadial (l + 2) κ s)) := by
  rw [deriv_meridionalGradientRadial_eq]
  have h := meridionalFactorB_radial l (κ ^ 2) s
  simp only [meridionalGradientRadial, besselRadial]
  linear_combination h

/-- The radial equation of the swirl factor: `4 s B_l'' + (4l + 6) B_l' = -κ² B_l`. -/
theorem besselRadial_ode :
    4 * s * deriv (deriv (besselRadial l κ)) s + (4 * (l : ℝ) + 6) * deriv (besselRadial l κ) s =
      -(κ ^ 2 * besselRadial l κ s) :=
  besselFactor_ode l (κ ^ 2) s

/-- The radial derivative of the swirl factor: `2 s B_l' + l B_l = l B_l - κ² s B_{l+1}`. -/
theorem besselRadial_radial :
    2 * s * deriv (besselRadial l κ) s + l * besselRadial l κ s =
      l * besselRadial l κ s - κ ^ 2 * s * besselRadial (l + 1) κ s :=
  besselFactor_radial l (κ ^ 2) s

end Identities

/-! ### The fields -/

/-- The meridional field `A(‖x‖²) P(x) x + B(‖x‖²) ∇P(x)` with radial factors `A`, `B`. -/
def meridionalField (P : MvPolynomial (Fin 3) ℝ) (A B : ℝ → ℝ) (x : ℝ^3) : ℝ^3 :=
  WithLp.toLp 2 fun i ↦ A (‖x‖ ^ 2) * eval x.ofLp (P * X i) +
    B (‖x‖ ^ 2) * eval x.ofLp (pderiv i P)

/-- The components of a meridional field. -/
theorem meridionalField_apply (P : MvPolynomial (Fin 3) ℝ) (A B : ℝ → ℝ) (x : ℝ^3) (i : Fin 3) :
    meridionalField P A B x i =
      A (‖x‖ ^ 2) * eval x.ofLp (P * X i) + B (‖x‖ ^ 2) * eval x.ofLp (pderiv i P) :=
  rfl

/-- The meridional Bessel field with components
`l κ² B_{l+1}(‖x‖²) P(x) xᵢ + ((l + 1) B_l - κ² ‖x‖² B_{l+1} + b)(‖x‖²) ∂ᵢP(x)`. -/
def meridionalModeField (P : MvPolynomial (Fin 3) ℝ) (l : ℕ) (κ b : ℝ) : ℝ^3 → ℝ^3 :=
  meridionalField P (meridionalRadial l κ) (meridionalGradientRadial l κ b)

/-- The pressure `κ² b P` of the meridional Bessel field. -/
def meridionalModePressure (P : MvPolynomial (Fin 3) ℝ) (κ b : ℝ) (x : ℝ^3) : ℝ :=
  eval x.ofLp (C (κ ^ 2 * b) * P)

/-- The swirl Bessel field `B_l(‖x‖²) (x × ∇P)(x)`. -/
def azimuthalModeField (P : MvPolynomial (Fin 3) ℝ) (l : ℕ) (κ : ℝ) (x : ℝ^3) : ℝ^3 :=
  WithLp.toLp 2 fun i ↦ besselRadial l κ (‖x‖ ^ 2) * eval x.ofLp (swirlPolynomial P i)

/-- The components of the meridional Bessel field. -/
theorem meridionalModeField_apply (P : MvPolynomial (Fin 3) ℝ) (l : ℕ) (κ b : ℝ) (x : ℝ^3)
    (i : Fin 3) :
    meridionalModeField P l κ b x i =
      meridionalRadial l κ (‖x‖ ^ 2) * eval x.ofLp (P * X i) +
        meridionalGradientRadial l κ b (‖x‖ ^ 2) * eval x.ofLp (pderiv i P) :=
  rfl

/-- The components of the swirl Bessel field. -/
theorem azimuthalModeField_apply (P : MvPolynomial (Fin 3) ℝ) (l : ℕ) (κ : ℝ) (x : ℝ^3)
    (i : Fin 3) :
    azimuthalModeField P l κ x i = besselRadial l κ (‖x‖ ^ 2) * eval x.ofLp (swirlPolynomial P i) :=
  rfl

section Regularity

variable {F : ℝ → ℝ} {Q : MvPolynomial (Fin 3) ℝ}

/-- A radial factor times a polynomial is as smooth as the factor. -/
theorem contDiff_radial_mul_eval {k : WithTop ℕ∞} (hF : ContDiff ℝ k F) :
    ContDiff ℝ k (fun y : ℝ^3 ↦ F (‖y‖ ^ 2) * eval y.ofLp Q) :=
  (hF.comp (contDiff_norm_sq ℝ)).mul (contDiff_eval_ofLp Q)

end Regularity

/-- Meridional fields with smooth factors are smooth. -/
theorem contDiff_meridionalField (P : MvPolynomial (Fin 3) ℝ) {A B : ℝ → ℝ}
    {k : WithTop ℕ∞} (hA : ContDiff ℝ k A) (hB : ContDiff ℝ k B) :
    ContDiff ℝ k (meridionalField P A B) :=
  contDiff_piLp' 2 fun _ ↦ (contDiff_radial_mul_eval hA).add (contDiff_radial_mul_eval hB)

/-- The meridional Bessel field is smooth. -/
theorem contDiff_meridionalModeField (P : MvPolynomial (Fin 3) ℝ) (l : ℕ) (κ b : ℝ) :
    ContDiff ℝ ∞ (meridionalModeField P l κ b) :=
  contDiff_meridionalField P (contDiff_meridionalRadial l κ)
    (contDiff_meridionalGradientRadial l κ b)

/-- The swirl Bessel field is smooth. -/
theorem contDiff_azimuthalModeField (P : MvPolynomial (Fin 3) ℝ) (l : ℕ) (κ : ℝ) :
    ContDiff ℝ ∞ (azimuthalModeField P l κ) :=
  contDiff_piLp' 2 fun _ ↦ contDiff_radial_mul_eval (contDiff_besselRadial l κ)

/-- The pressure of the meridional Bessel field is smooth. -/
theorem contDiff_meridionalModePressure (P : MvPolynomial (Fin 3) ℝ) (κ b : ℝ) :
    ContDiff ℝ ∞ (meridionalModePressure P κ b) :=
  contDiff_eval_ofLp _

section Equations

variable {P : MvPolynomial (Fin 3) ℝ} {l : ℕ}

private theorem differentiable_radial_mul_eval {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (Q : MvPolynomial (Fin 3) ℝ) :
    Differentiable ℝ (fun y : ℝ^3 ↦ F (‖y‖ ^ 2) * eval y.ofLp Q) :=
  (contDiff_radial_mul_eval hF).differentiable one_ne_zero

/-- The meridional Bessel field is divergence free. -/
theorem divergence_meridionalModeField (hL : polynomialLaplacian P = 0)
    (hE : ∑ j, X j * pderiv j P = C (l : ℝ) * P) (κ b : ℝ) (x : ℝ^3) :
    divergence (meridionalModeField P l κ b) x = 0 := by
  have hF₁ : Differentiable ℝ (meridionalRadial l κ) :=
    (contDiff_meridionalRadial l κ (k := 1)).differentiable one_ne_zero
  have hF₂ : Differentiable ℝ (meridionalGradientRadial l κ b) :=
    (contDiff_meridionalGradientRadial l κ b (k := 1)).differentiable one_ne_zero
  have hcomp (i : Fin 3) : ∂[i] (fun y ↦ meridionalModeField P l κ b y i) x =
      2 * x i * deriv (meridionalRadial l κ) (‖x‖ ^ 2) * eval x.ofLp (P * X i) +
        meridionalRadial l κ (‖x‖ ^ 2) * eval x.ofLp (pderiv i (P * X i)) +
      (2 * x i * deriv (meridionalGradientRadial l κ b) (‖x‖ ^ 2) * eval x.ofLp (pderiv i P) +
        meridionalGradientRadial l κ b (‖x‖ ^ 2) * eval x.ofLp (pderiv i (pderiv i P))) := by
    simp only [meridionalModeField_apply]
    rw [partialDeriv_add
      (differentiable_radial_mul_eval (contDiff_meridionalRadial l κ) _ x)
      (differentiable_radial_mul_eval (contDiff_meridionalGradientRadial l κ b) _ x),
      partialDeriv_radial_mul_eval hF₁, partialDeriv_radial_mul_eval hF₂]
  unfold divergence
  rw [Finset.sum_congr rfl fun i _ ↦ hcomp i]
  have e1 := congrArg (eval x.ofLp) (sum_pderiv_mul_X hE)
  have e2 := congrArg (eval x.ofLp) hE
  have e3 := congrArg (eval x.ofLp) hL
  rw [polynomialLaplacian] at e3
  have e4 : ∑ i, x i * eval x.ofLp (P * X i) = ‖x‖ ^ 2 * eval x.ofLp P := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [map_mul, eval_X]
    ring
  simp only [map_sum, map_mul, eval_X, eval_C, map_zero] at e1 e2 e3
  have D := meridional_divergence_identity l κ b (‖x‖ ^ 2)
  simp only [Fin.sum_univ_three] at e1 e2 e3 e4 ⊢
  linear_combination 2 * deriv (meridionalRadial l κ) (‖x‖ ^ 2) * e4 +
    meridionalRadial l κ (‖x‖ ^ 2) * e1 +
    2 * deriv (meridionalGradientRadial l κ b) (‖x‖ ^ 2) * e2 +
    meridionalGradientRadial l κ b (‖x‖ ^ 2) * e3 + eval x.ofLp P * D

/-- The swirl Bessel field is divergence free. -/
theorem divergence_azimuthalModeField (P : MvPolynomial (Fin 3) ℝ) (l : ℕ) (κ : ℝ)
    (x : ℝ^3) : divergence (azimuthalModeField P l κ) x = 0 := by
  have hF : Differentiable ℝ (besselRadial l κ) :=
    (contDiff_besselRadial l κ (k := 1)).differentiable one_ne_zero
  unfold divergence
  simp only [azimuthalModeField_apply, partialDeriv_radial_mul_eval hF]
  have e1 := congrArg (eval x.ofLp) (sum_pderiv_swirlPolynomial P)
  have e2 := congrArg (eval x.ofLp) (sum_X_mul_swirlPolynomial P)
  simp only [map_sum, map_mul, eval_X, map_zero] at e1 e2
  simp only [Fin.sum_univ_three] at e1 e2 ⊢
  linear_combination 2 * deriv (besselRadial l κ) (‖x‖ ^ 2) * e2 +
    besselRadial l κ (‖x‖ ^ 2) * e1

/-- The meridional Bessel field solves `Δψ - ∇p = -κ² ψ` with the pressure `κ² b P`. -/
theorem laplacian_meridionalModeField (hL : polynomialLaplacian P = 0)
    (hE : ∑ j, X j * pderiv j P = C (l : ℝ) * P) (κ b : ℝ) (x : ℝ^3) (i : Fin 3) :
    laplacian (fun y ↦ meridionalModeField P l κ b y i) x -
        ∂[i] (meridionalModePressure P κ b) x =
      -(κ ^ 2 * meridionalModeField P l κ b x i) := by
  have hfun : (fun y ↦ meridionalModeField P l κ b y i) = fun y ↦
      meridionalRadial l κ (‖y‖ ^ 2) * eval y.ofLp (P * X i) +
        meridionalGradientRadial l κ b (‖y‖ ^ 2) * eval y.ofLp (pderiv i P) := rfl
  have hp : meridionalModePressure P κ b = fun y ↦ eval y.ofLp (C (κ ^ 2 * b) * P) := rfl
  have h2 : ContDiffAt ℝ 2 (fun y : ℝ^3 ↦ meridionalRadial l κ (‖y‖ ^ 2) * eval y.ofLp (P * X i))
      x := (contDiff_radial_mul_eval (contDiff_meridionalRadial l κ)).contDiffAt
  have h2' : ContDiffAt ℝ 2 (fun y : ℝ^3 ↦ meridionalGradientRadial l κ b (‖y‖ ^ 2) *
      eval y.ofLp (pderiv i P)) x :=
    (contDiff_radial_mul_eval (contDiff_meridionalGradientRadial l κ b)).contDiffAt
  rw [hfun, laplacian_add _ _ x h2 h2',
    laplacian_radial_mul_eval (contDiff_meridionalRadial l κ) (sum_X_mul_pderiv_mul_X hE i),
    laplacian_radial_mul_eval (contDiff_meridionalGradientRadial l κ b)
      (sum_X_mul_pderiv_pderiv hE i),
    polynomialLaplacian_mul_X hL i, polynomialLaplacian_pderiv_eq_zero hL i, hp,
    partialDeriv_eval_ofLp,
    meridionalModeField_apply]
  have hpd : eval x.ofLp (pderiv i (C (κ ^ 2 * b) * P)) = κ ^ 2 * b * eval x.ofLp (pderiv i P) := by
    rw [pderiv_C_mul, map_mul, eval_C]
  have htwo : eval x.ofLp (2 * pderiv i P) = 2 * eval x.ofLp (pderiv i P) := by
    rw [map_mul, map_ofNat]
  rw [hpd, htwo, map_zero, mul_zero, add_zero]
  have O1 := meridionalRadial_ode l κ (‖x‖ ^ 2)
  have O2 := meridionalGradientRadial_ode l κ b (‖x‖ ^ 2)
  linear_combination eval x.ofLp (P * X i) * O1 + eval x.ofLp (pderiv i P) * O2

/-- The swirl Bessel field solves `Δψ = -κ² ψ`. -/
theorem laplacian_azimuthalModeField (hL : polynomialLaplacian P = 0)
    (hE : ∑ j, X j * pderiv j P = C (l : ℝ) * P) (κ : ℝ) (x : ℝ^3) (i : Fin 3) :
    laplacian (fun y ↦ azimuthalModeField P l κ y i) x =
      -(κ ^ 2 * azimuthalModeField P l κ x i) := by
  have hfun : (fun y ↦ azimuthalModeField P l κ y i) = fun y ↦
      besselRadial l κ (‖y‖ ^ 2) * eval y.ofLp (swirlPolynomial P i) := rfl
  rw [hfun, laplacian_radial_mul_eval (contDiff_besselRadial l κ)
      (sum_X_mul_pderiv_swirlPolynomial hE i), polynomialLaplacian_swirlPolynomial hL i,
    azimuthalModeField_apply]
  simp only [map_zero, mul_zero, add_zero]
  have O := besselRadial_ode l κ (‖x‖ ^ 2)
  linear_combination eval x.ofLp (swirlPolynomial P i) * O

/-- The radial derivative of the meridional Bessel field. -/
theorem sum_partialDeriv_meridionalModeField_mul (hE : ∑ j, X j * pderiv j P = C (l : ℝ) * P)
    (κ b : ℝ) (x : ℝ^3) (i : Fin 3) :
    ∑ j, ∂[j] (fun y ↦ meridionalModeField P l κ b y i) x * x j =
      (2 * ‖x‖ ^ 2 * deriv (meridionalRadial l κ) (‖x‖ ^ 2) +
          ((l : ℝ) + 1) * meridionalRadial l κ (‖x‖ ^ 2)) * eval x.ofLp (P * X i) +
        (2 * ‖x‖ ^ 2 * deriv (meridionalGradientRadial l κ b) (‖x‖ ^ 2) +
          ((l : ℝ) - 1) * meridionalGradientRadial l κ b (‖x‖ ^ 2)) * eval x.ofLp (pderiv i P) := by
  have hF₁ : Differentiable ℝ (meridionalRadial l κ) :=
    (contDiff_meridionalRadial l κ (k := 1)).differentiable one_ne_zero
  have hF₂ : Differentiable ℝ (meridionalGradientRadial l κ b) :=
    (contDiff_meridionalGradientRadial l κ b (k := 1)).differentiable one_ne_zero
  have hsplit : ∀ j, ∂[j] (fun y ↦ meridionalModeField P l κ b y i) x * x j =
      ∂[j] (fun y : ℝ^3 ↦ meridionalRadial l κ (‖y‖ ^ 2) * eval y.ofLp (P * X i)) x * x j +
        ∂[j] (fun y : ℝ^3 ↦ meridionalGradientRadial l κ b (‖y‖ ^ 2) *
          eval y.ofLp (pderiv i P)) x * x j := by
    intro j
    simp only [meridionalModeField_apply]
    rw [partialDeriv_add
      (differentiable_radial_mul_eval (contDiff_meridionalRadial l κ) _ x)
      (differentiable_radial_mul_eval (contDiff_meridionalGradientRadial l κ b) _ x), add_mul]
  rw [Finset.sum_congr rfl fun j _ ↦ hsplit j, Finset.sum_add_distrib,
    sum_partialDeriv_radial_mul_eval_mul hF₁ (sum_X_mul_pderiv_mul_X hE i),
    sum_partialDeriv_radial_mul_eval_mul hF₂ (sum_X_mul_pderiv_pderiv hE i)]

/-- The natural boundary condition of the meridional Bessel field: on the sphere `‖x‖ = R`,
`∑ⱼ xⱼ ∂ⱼ ψᵢ = p xᵢ` when `b` is the boundary coefficient and the meridional boundary
expression vanishes at `R`. -/
theorem meridionalModeField_boundary (hE : ∑ j, X j * pderiv j P = C (l : ℝ) * P) {κ R b : ℝ}
    (hb : b = l * ((l + 1) * besselRadial (l + 1) κ (R ^ 2) -
      κ ^ 2 * R ^ 2 * besselRadial (l + 2) κ (R ^ 2)))
    (hbf : (((l : ℝ) - 1) * (2 * l + 1) - κ ^ 2 * R ^ 2) * besselRadial l κ (R ^ 2) +
      (κ ^ 2 * R ^ 2 - l * (l - 1) * (l + 2)) * besselRadial (l + 1) κ (R ^ 2) = 0)
    {x : ℝ^3} (hx : ‖x‖ = R) (i : Fin 3) :
    ∑ j, ∂[j] (fun y ↦ meridionalModeField P l κ b y i) x * x j =
      meridionalModePressure P κ b x * x i := by
  rw [sum_partialDeriv_meridionalModeField_mul hE, meridionalRadial_radial,
    meridionalGradientRadial_radial, hx, hbf, ← hb, sub_self, mul_zero, add_zero, zero_mul,
    add_zero, meridionalModePressure]
  simp only [map_mul, eval_C, eval_X]
  ring

/-- The natural boundary condition of the swirl Bessel field: on the sphere `‖x‖ = R`,
`∑ⱼ xⱼ ∂ⱼ ψᵢ = 0` when `l B_l(R²) = κ² R² B_{l+1}(R²)`. -/
theorem azimuthalModeField_boundary (hE : ∑ j, X j * pderiv j P = C (l : ℝ) * P) {κ R : ℝ}
    (hbf : l * besselRadial l κ (R ^ 2) - κ ^ 2 * R ^ 2 * besselRadial (l + 1) κ (R ^ 2) = 0)
    {x : ℝ^3} (hx : ‖x‖ = R) (i : Fin 3) :
    ∑ j, ∂[j] (fun y ↦ azimuthalModeField P l κ y i) x * x j = 0 := by
  have hF : Differentiable ℝ (besselRadial l κ) :=
    (contDiff_besselRadial l κ (k := 1)).differentiable one_ne_zero
  have hfun : (fun y ↦ azimuthalModeField P l κ y i) = fun y ↦
      besselRadial l κ (‖y‖ ^ 2) * eval y.ofLp (swirlPolynomial P i) := rfl
  rw [hfun, sum_partialDeriv_radial_mul_eval_mul hF (sum_X_mul_pderiv_swirlPolynomial hE i),
    besselRadial_radial, hx, hbf, zero_mul]

end Equations

end PDE.Fluid.Stokes.Ball
