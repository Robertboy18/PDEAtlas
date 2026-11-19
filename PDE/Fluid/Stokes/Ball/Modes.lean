/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.ModeFields
public import PDE.Fluid.Stokes.Ball.Green
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Vector.FirstOrder
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.FDeriv.Calculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Neumann-type Stokes modes on a ball

The eigenvalue problem `λ = inf ‖∇u‖² / ‖u‖²` over divergence-free fields on the ball
`B(0, R)` without boundary condition has the Euler-Lagrange equations
`-Δψ + ∇p = λ ψ`, `div ψ = 0` in the ball and the natural boundary condition
`∂ₙψ = p n` on the sphere (Hou, Wang and Yang, Lemma 4 and Appendix E).
The axisymmetric eigenfunctions are written below in Cartesian form. With `h_l` the zonal solid
harmonic `r^l P_l(cos θ)`,
`κ = α / R` and `B_m(s) = G_m(κ² s)` (`j_m(x) = x^m G_m(x²)`):

* the meridional mode (their `Y`-modes, components along `Y_l = S_l e_r` and `X_l = S_l' e_θ`)
  `ψ = l κ² B_{l+1} h_l x + ((l + 1) B_l - κ² ‖x‖² B_{l+1} + b) ∇h_l` with pressure
  `p = κ² b h_l` and the boundary coefficient
  `b = l ((l + 1) g_{l+1}(α) - α² g_{l+2}(α))`;
* the azimuthal mode (their `Z`-modes, along `Z_l = S_l' e_φ`) `ψ = B_l (x × ∇h_l)`, with
  pressure zero;
* the zero mode `e_z`, the constant field of eigenvalue `0`.

Both families satisfy the equations in the whole space for every `α`. The boundary condition
holds exactly when `boundaryFunction k l α = 0`, where in the reduced Bessel functions
`g_m(x) = j_m(x) / x^m`

* meridional: `((l - 1)(2l + 1) - α²) g_l(α) + (α² - l(l - 1)(l + 2)) g_{l+1}(α)`,
* azimuthal: `l g_l(α) - α² g_{l+1}(α)`.

Multiplied by `α^{l+1}`, respectively `α^l`, these are their equations (6.4) and (6.3) up to a
nonzero factor: `α^l` times the second is `α j_l'(α)`. Then `mode_weak_eigen` is the weak form:
for every weakly divergence-free field `v` with integrable weak derivatives on the ball,
`∫ ∇ψ : ∇v = (α / R)² ∫ ⟪ψ, v⟫`.

The modes of degree `l = 0` vanish identically (`mode_degree_zero`), although the boundary
functions of degree zero have positive roots; only `Admissible k l`, that is `1 ≤ l`, gives
eigenfunctions. The root `α = 0` of the meridional boundary function of degree one gives the
zero mode: `mode R .meridional 1 0 = (4 / 5) • zeroMode`. By Lemma 4 of Hou, Wang and Yang,
the positive roots of all admissible degrees together with `e_z` exhaust the eigenvalues. For
their computation they keep the first 1257 eigenfunctions of the parity of `U` and the first
1260 of the parity of `v`, enough that the next eigenvalue on their ball of radius 32 exceeds 10
(Section 6.2).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 5.6, (5.10), p. 43,
  Section 6.2, Lemma 4, p. 50, (6.3), (6.4), Remark 9 and the choice of `N`, p. 51, and Appendix E,
  proof of Lemma 4, pp. 62-65.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory MvPolynomial PDE.Analysis.SpecialFunctions
open PDE (partialDeriv laplacian divergence)
open scoped ContDiff Sobolev RealInnerProductSpace

namespace PDE.Fluid.Stokes.Ball

/-- The two families of axisymmetric Neumann-type Stokes modes: `meridional` (the `Y`-modes of
Hou, Wang and Yang, no swirl) and `azimuthal` (their `Z`-modes, pure swirl). -/
inductive ModeKind
  | meridional
  | azimuthal
  deriving DecidableEq, Repr

/-- The boundary function whose positive zeros `α` give the modes of eigenvalue `(α / R)²`,
written with the reduced spherical Bessel functions `g_m(α) = j_m(α) / α^m`. -/
def boundaryFunction : ModeKind → ℕ → ℝ → ℝ
  | .meridional, l, α =>
      (((l : ℝ) - 1) * (2 * l + 1) - α ^ 2) * reducedSphericalBesselJ l α +
        (α ^ 2 - l * (l - 1) * (l + 2)) * reducedSphericalBesselJ (l + 1) α
  | .azimuthal, l, α => l * reducedSphericalBesselJ l α - α ^ 2 * reducedSphericalBesselJ (l + 1) α

/-- The coefficient `b = l ((l + 1) g_{l+1}(α) - α² g_{l+2}(α))` of `∇h_l` that the boundary
condition on the radial component fixes; the pressure of the meridional mode is `κ² b h_l`. -/
def boundaryCoefficient (l : ℕ) (α : ℝ) : ℝ :=
  l * ((l + 1) * reducedSphericalBesselJ (l + 1) α - α ^ 2 * reducedSphericalBesselJ (l + 2) α)

/-- The axisymmetric Neumann-type Stokes mode of kind `k`, degree `l` and boundary root `α` on
the ball of radius `R`, of eigenvalue `(α / R)²`. -/
def mode (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) : ℝ^3 → ℝ^3 :=
  match k with
  | .meridional =>
      meridionalModeField (zonalSolidHarmonicPolynomial l) l (α / R) (boundaryCoefficient l α)
  | .azimuthal => azimuthalModeField (zonalSolidHarmonicPolynomial l) l (α / R)

/-- The pressure of the mode: `(α / R)² b h_l` for the meridional modes and zero for the
azimuthal ones. -/
def modePressure (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) : ℝ^3 → ℝ :=
  match k with
  | .meridional =>
      meridionalModePressure (zonalSolidHarmonicPolynomial l) (α / R) (boundaryCoefficient l α)
  | .azimuthal => fun _ ↦ 0

/-- The zero mode `e_z`, the constant eigenfunction of eigenvalue `0` (the
`ψ₀ = (cos θ, -sin θ, 0)` of Hou, Wang and Yang, written in the spherical frame). -/
def zeroMode : ℝ^3 → ℝ^3 := fun _ ↦ EuclideanSpace.single 2 1

/-- The degrees with nonzero modes: `1 ≤ l` for both kinds. -/
def Admissible (_k : ModeKind) (l : ℕ) : Prop :=
  1 ≤ l

instance (k : ModeKind) (l : ℕ) : Decidable (Admissible k l) :=
  inferInstanceAs (Decidable (1 ≤ l))

/-! ### Boundary functions -/

/-- The boundary functions are even in `α`. -/
theorem boundaryFunction_neg (k : ModeKind) (l : ℕ) (α : ℝ) :
    boundaryFunction k l (-α) = boundaryFunction k l α := by
  cases k <;> simp [boundaryFunction, reducedSphericalBesselJ_neg]

/-- The azimuthal boundary function times `α^l` is `l j_l(α) - α j_{l+1}(α) = α j_l'(α)`. -/
theorem pow_mul_boundaryFunction_azimuthal (l : ℕ) (α : ℝ) :
    α ^ l * boundaryFunction .azimuthal l α =
      l * sphericalBesselJ l α - α * sphericalBesselJ (l + 1) α := by
  simp only [boundaryFunction, sphericalBesselJ_eq_pow_mul]
  ring

/-- The azimuthal boundary function times `α^l` is `α j_l'(α)`, the left side of condition (6.3)
`α J_{l+1/2}'(α) - J_{l+1/2}(α) / 2 = 0` of Hou, Wang and Yang divided by `√(2α/π)`. -/
theorem pow_mul_boundaryFunction_azimuthal_eq_deriv (l : ℕ) (α : ℝ) :
    α ^ l * boundaryFunction .azimuthal l α = α * deriv (sphericalBesselJ l) α := by
  rw [pow_mul_boundaryFunction_azimuthal, mul_deriv_sphericalBesselJ]

/-- The meridional boundary function times `α^{l+1}` in terms of `j_l` and `j_{l+1}`. -/
theorem pow_mul_boundaryFunction_meridional (l : ℕ) (α : ℝ) :
    α ^ (l + 1) * boundaryFunction .meridional l α =
      (((l : ℝ) - 1) * (2 * l + 1) - α ^ 2) * α * sphericalBesselJ l α +
        (α ^ 2 - l * (l - 1) * (l + 2)) * sphericalBesselJ (l + 1) α := by
  simp only [boundaryFunction, sphericalBesselJ_eq_pow_mul]
  ring

/-- At the boundary radius the radial Bessel factor is the reduced Bessel function at `α`. -/
theorem besselRadial_div_sq {R : ℝ} (hR : R ≠ 0) (m : ℕ) (α : ℝ) :
    besselRadial m (α / R) (R ^ 2) = reducedSphericalBesselJ m α := by
  rw [besselRadial, besselFactor, reducedSphericalBesselJ_eq_sq, div_pow,
    div_mul_cancel₀ _ (pow_ne_zero 2 hR)]

/-- The meridional boundary function of degree one vanishes at `α = 0`. -/
theorem boundaryFunction_meridional_one_zero : boundaryFunction .meridional 1 0 = 0 := by
  simp [boundaryFunction]

/-- The meridional boundary function at `α = 0`: `3 (l - 1) (l + 1)² / (2l + 3)!!`. -/
theorem boundaryFunction_meridional_zero (l : ℕ) :
    boundaryFunction .meridional l 0 =
      3 * ((l : ℝ) - 1) * ((l : ℝ) + 1) ^ 2 / ((2 * l + 3).doubleFactorial : ℝ) := by
  have hrec : ((2 * l + 3).doubleFactorial : ℝ) =
      (2 * l + 3) * ((2 * l + 1).doubleFactorial : ℝ) := by
    rw [show 2 * l + 3 = (2 * l + 1) + 2 by ring, Nat.doubleFactorial_add_two]
    push_cast
    ring
  have h1 : (0 : ℝ) < ((2 * l + 1).doubleFactorial : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos _
  simp only [boundaryFunction, reducedSphericalBesselJ_zero, zero_pow two_ne_zero, sub_zero,
    zero_sub]
  rw [show 2 * (l + 1) + 1 = 2 * l + 3 by ring, hrec]
  field_simp
  ring

/-- The boundary functions of admissible degree have no root at `α = 0`, except the meridional
one of degree one. -/
theorem boundaryFunction_zero_ne {k : ModeKind} {l : ℕ} (hl : 1 ≤ l)
    (h : ¬ (k = .meridional ∧ l = 1)) : boundaryFunction k l 0 ≠ 0 := by
  have hdf (m : ℕ) : (0 : ℝ) < ((2 * m + 1).doubleFactorial : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos _
  cases k with
  | meridional =>
    have hl2 : (2 : ℝ) ≤ l := by
      have : 2 ≤ l := by
        by_contra h'
        exact h ⟨rfl, by omega⟩
      exact_mod_cast this
    rw [boundaryFunction_meridional_zero]
    have h3 : (0 : ℝ) < ((2 * l + 3).doubleFactorial : ℝ) := by
      exact_mod_cast Nat.doubleFactorial_pos _
    have : 0 < 3 * ((l : ℝ) - 1) * ((l : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) < (l : ℝ) - 1 := by linarith
      positivity
    positivity
  | azimuthal =>
    simp only [boundaryFunction, reducedSphericalBesselJ_zero]
    have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have h1 := hdf l
    simp only [ne_eq, zero_pow two_ne_zero, zero_mul, sub_zero]
    positivity

/-- The meridional mode of degree one at the root `α = 0` is `(4 / 5) e_z`, a multiple of the
zero mode, the eigenfunction `ψ₀ = (cos θ, -sin θ, 0)` of eigenvalue `0` of Hou, Wang and
Yang. -/
theorem mode_meridional_one_zero (R : ℝ) : mode R .meridional 1 0 = (4 / 5 : ℝ) • zeroMode := by
  have hG (m : ℕ) (s : ℝ) : besselFactor m 0 s = 1 / ((2 * m + 1).doubleFactorial : ℝ) := by
    rw [besselFactor, zero_mul, ← reducedSphericalBesselJ_zero, reducedSphericalBesselJ_eq_sq,
      zero_pow two_ne_zero]
  funext x
  ext i
  simp only [mode, meridionalModeField_apply, zonalSolidHarmonicPolynomial_one, zero_div,
    meridionalRadial, meridionalGradientRadial, meridionalFactorA, meridionalFactorB,
    zero_pow two_ne_zero, boundaryCoefficient, hG, reducedSphericalBesselJ_zero, Pi.smul_apply,
    PiLp.smul_apply, smul_eq_mul, zeroMode]
  fin_cases i
  · simp
  · simp
  · simp only [Fin.reduceFinMk, Fin.isValue]
    norm_num [Nat.doubleFactorial]

/-- The modes depend on `α` only through `α²`. -/
theorem mode_neg (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) : mode R k l (-α) = mode R k l α := by
  have hb : boundaryCoefficient l (-α) = boundaryCoefficient l α := by
    simp [boundaryCoefficient, reducedSphericalBesselJ_neg]
  have hB (m : ℕ) : besselRadial m (-(α / R)) = besselRadial m (α / R) := by
    funext s
    simp [besselRadial]
  funext x
  cases k
  · simp only [mode, hb, neg_div]
    unfold meridionalModeField meridionalRadial meridionalGradientRadial
    simp only [neg_sq]
  · simp only [mode, neg_div]
    unfold azimuthalModeField
    simp only [hB]

/-- The modes of degree zero vanish identically: `h_0 = 1` has gradient zero and the factor
`l κ²` of `h_0 x` vanishes. -/
theorem mode_degree_zero (R : ℝ) (k : ModeKind) (α : ℝ) : mode R k 0 α = 0 := by
  funext x
  ext i
  cases k
  · simp [mode, meridionalModeField_apply, meridionalRadial, meridionalFactorA,
      zonalSolidHarmonicPolynomial_zero]
  · simp [mode, azimuthalModeField_apply, swirlPolynomial, zonalSolidHarmonicPolynomial_zero]

/-! ### Regularity and equations -/

/-- Euler's identity for the zonal solid harmonic: `∑ⱼ Xⱼ ∂ⱼ h_l = l h_l`. -/
theorem euler_zonalSolidHarmonicPolynomial (l : ℕ) :
    ∑ j, X j * pderiv j (zonalSolidHarmonicPolynomial l) =
      C (l : ℝ) * zonalSolidHarmonicPolynomial l := by
  rw [sum_X_mul_pderiv_zonalSolidHarmonicPolynomial, map_natCast]

/-- The modes are smooth. -/
theorem mode_contDiff (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) :
    ContDiff ℝ ∞ (mode R k l α) := by
  cases k
  · exact contDiff_meridionalModeField _ _ _ _
  · exact contDiff_azimuthalModeField _ _ _

/-- The pressures of the modes are smooth. -/
theorem modePressure_contDiff (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) :
    ContDiff ℝ ∞ (modePressure R k l α) := by
  cases k
  · exact contDiff_meridionalModePressure _ _ _
  · exact contDiff_const

/-- The modes are divergence free. -/
theorem mode_divergence_eq_zero (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) (x : ℝ^3) :
    divergence (mode R k l α) x = 0 := by
  cases k
  · exact divergence_meridionalModeField (polynomialLaplacian_zonalSolidHarmonicPolynomial l)
      (euler_zonalSolidHarmonicPolynomial l) _ _ x
  · exact divergence_azimuthalModeField _ _ _ x

/-- The modes solve the Stokes eigenvalue equation `Δψ - ∇p = -(α / R)² ψ` on all of `ℝ^3`. -/
theorem mode_stokes_eigen (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) (x : ℝ^3) (i : Fin 3) :
    laplacian (fun y ↦ mode R k l α y i) x - ∂[i] (modePressure R k l α) x =
      -((α / R) ^ 2 * mode R k l α x i) := by
  cases k
  · exact laplacian_meridionalModeField (polynomialLaplacian_zonalSolidHarmonicPolynomial l)
      (euler_zonalSolidHarmonicPolynomial l) _ _ x i
  · have h := laplacian_azimuthalModeField (polynomialLaplacian_zonalSolidHarmonicPolynomial l)
      (euler_zonalSolidHarmonicPolynomial l) (α / R) x i
    have h0 : ∂[i] (fun _ : ℝ^3 ↦ (0 : ℝ)) x = 0 := by
      simp [partialDeriv]
    simp only [mode, modePressure]
    rw [h0, sub_zero]
    exact h

/-- The natural boundary condition: on the sphere `‖x‖ = R`, `∑ⱼ xⱼ ∂ⱼ ψᵢ = p xᵢ` when `α` is
a root of the boundary function. -/
theorem mode_boundary {R : ℝ} (hR : R ≠ 0) {k : ModeKind} {l : ℕ} {α : ℝ}
    (hα : boundaryFunction k l α = 0) {x : ℝ^3} (hx : ‖x‖ = R) (i : Fin 3) :
    ∑ j, ∂[j] (fun y ↦ mode R k l α y i) x * x j = modePressure R k l α x * x i := by
  have hκ : (α / R) ^ 2 * R ^ 2 = α ^ 2 := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hR)]
  cases k
  · refine meridionalModeField_boundary (euler_zonalSolidHarmonicPolynomial l) ?_ ?_ hx i
    · rw [boundaryCoefficient, besselRadial_div_sq hR, besselRadial_div_sq hR, hκ]
    · rw [besselRadial_div_sq hR, besselRadial_div_sq hR, hκ]
      exact hα
  · rw [modePressure, zero_mul]
    refine azimuthalModeField_boundary (euler_zonalSolidHarmonicPolynomial l) ?_ hx i
    rw [besselRadial_div_sq hR, besselRadial_div_sq hR, hκ]
    exact hα

/-! ### Weak eigenvalue equations -/

/-- The weak Neumann-type Stokes eigenvalue equation of a mode on the ball `B(0, R)`: for every
field `v` with integrable components and integrable weak derivatives `Dv i j = ∂ⱼ vᵢ` on the
ball and weakly divergence free,
`∫ ∑ᵢⱼ ∂ⱼ ψᵢ ∂ⱼ vᵢ = (α / R)² ∫ ⟪ψ, v⟫`. No boundary condition and no symmetry of `v` is
assumed, so this holds on every sector of the space `H¹_σ(B(0, R))`. -/
theorem mode_weak_eigen {R : ℝ} (hR : 0 < R) {k : ModeKind} {l : ℕ} {α : ℝ}
    (hα : boundaryFunction k l α = 0) {v : ℝ^3 → ℝ^3} {Dv : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hv : ∀ i, IntegrableOn (fun x ↦ v x i) (Metric.ball (0 : ℝ^3) R))
    (hDv : ∀ i j, IntegrableOn (Dv i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ v x i) (Dv i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Dv i i x = 0) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, ∂[j] (fun y ↦ mode R k l α y i) x * Dv i j x =
      (α / R) ^ 2 * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, v x⟫ :=
  integral_gradient_pairing_eq_of_neumann hR (mode_contDiff R k l α)
    (modePressure_contDiff R k l α) (fun x _ i ↦ mode_stokes_eigen R k l α x i)
    (fun _ hx i ↦ mode_boundary hR.ne' hα hx i) hv hDv hweak hdiv

/-- The weak eigenvalue equation of a mode against a `C¹` field that is divergence free in the
ball. -/
theorem mode_weak_eigen_of_contDiff {R : ℝ} (hR : 0 < R) {k : ModeKind} {l : ℕ} {α : ℝ}
    (hα : boundaryFunction k l α = 0) {v : ℝ^3 → ℝ^3} (hv : ContDiff ℝ 1 v)
    (hdiv : ∀ x ∈ Metric.ball (0 : ℝ^3) R, divergence v x = 0) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        ∂[j] (fun y ↦ mode R k l α y i) x * ∂[j] (fun y ↦ v y i) x =
      (α / R) ^ 2 * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, v x⟫ := by
  have hvi (i : Fin 3) : ContDiff ℝ 1 (fun y ↦ v y i) := (contDiff_piLp_apply 2).comp hv
  have hint {f : ℝ^3 → ℝ} (hf : Continuous f) : IntegrableOn f (Metric.ball (0 : ℝ^3) R) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      Metric.ball_subset_closedBall
  refine mode_weak_eigen hR hα (fun i ↦ hint (hvi i).continuous)
    (fun i j ↦ hint (continuous_iff_continuousAt.mpr fun x ↦
      (contDiffAt_partialDeriv 0 (hvi i).contDiffAt j).continuousAt))
    (fun i j ↦ SobolevSpace.hasWeakDerivativeOn_of_contDiffAt_one Metric.isOpen_ball
      (fun x _ ↦ (hvi i).contDiffAt) j) ?_
  exact (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
    (Filter.Eventually.of_forall fun x hx ↦ hdiv x hx)

/-- The weak eigenvalue equation of a mode against a field `u` of `H¹(B(0, R); ℝ³)`, with no
boundary condition, whose weak gradient has zero trace almost everywhere. The gradient entry
`(i, j)` of `u` is `∂ⱼ uᵢ`. -/
theorem mode_weak_eigen_sobolev {R : ℝ} (hR : 0 < R) {k : ModeKind} {l : ℕ} {α : ℝ}
    (hα : boundaryFunction k l α = 0) (u : Fin 3 → H¹(Metric.ball (0 : ℝ^3) R))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)),
      ∑ i, SobolevSpace.GraphSpace.vectorWkpGradientCLM u x (finProdFinEquiv (i, i)) = 0) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, ∂[j] (fun y ↦ mode R k l α y i) x *
        SobolevSpace.GraphSpace.vectorWkpGradientCLM u x (finProdFinEquiv (i, j)) =
      (α / R) ^ 2 * ∫ x in Metric.ball (0 : ℝ^3) R,
        ⟪mode R k l α x, SobolevSpace.GraphSpace.vectorWkpValueCLM u x⟫ := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : ℝ^3) R)) :=
    ⟨by simpa using measure_ball_lt_top⟩
  refine mode_weak_eigen hR hα (fun i ↦ ?_) (fun i j ↦ ?_)
    (fun i j ↦ SobolevSpace.GraphSpace.hasWeakDerivativeOn_vectorWkpGradientCLM u i j) hdiv
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp'
      (Lp.memLp (SobolevSpace.GraphSpace.vectorWkpValueCLM u))).integrable one_le_two
  · exact ((EuclideanSpace.proj (𝕜 := ℝ) (finProdFinEquiv (i, j))).comp_memLp'
      (Lp.memLp (SobolevSpace.GraphSpace.vectorWkpGradientCLM u))).integrable one_le_two

/-- The zero mode has vanishing gradient, so its weak eigenvalue equation holds with eigenvalue
`0` against every field. -/
theorem zeroMode_weak_eigen (R : ℝ) (Dv : Fin 3 → Fin 3 → ℝ^3 → ℝ) (v : ℝ^3 → ℝ^3) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, ∂[j] (fun y ↦ zeroMode y i) x * Dv i j x =
      0 * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪zeroMode x, v x⟫ := by
  simp [zeroMode, partialDeriv]

/-- The zero mode is smooth. -/
theorem zeroMode_contDiff : ContDiff ℝ ∞ zeroMode :=
  contDiff_const

/-- The zero mode is divergence free. -/
theorem zeroMode_divergence_eq_zero (x : ℝ^3) : divergence zeroMode x = 0 := by
  simp [divergence, zeroMode, partialDeriv]

end PDE.Fluid.Stokes.Ball
