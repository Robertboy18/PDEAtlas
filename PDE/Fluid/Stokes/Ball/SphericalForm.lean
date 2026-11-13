/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.Modes

/-!
# Spherical form and symmetry of the ball modes

In the spherical frame `(e_r, e_θ, e_φ)` at the point of radius `r`, polar angle `θ` and
azimuth `φ`, the modes are

`mode R meridional l α = Y(r) S_l(θ) e_r + X(r) S_l'(θ) e_θ`,
`mode R azimuthal l α = Z(r) S_l'(θ) e_φ`,

with `S_l(θ) = P_l(cos θ)` (`zonalHarmonic`), `S_l'` its derivative (`zonalHarmonicDeriv`) and
the radial profiles `meridionalRadialProfile`, `meridionalPolarProfile` and `azimuthalProfile`.
These are Hou, Wang and Yang's `Y_l`, `X_l` and `Z_l` components (Lemma 4).
The modes are equivariant under the rotations about the symmetry axis, and the equatorial
reflection `σ = diag(1, 1, -1)` acts on them by the sign `(-1)^l` (meridional) or `(-1)^(l+1)`
(azimuthal).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 5.6, (5.10), p. 43, and
  Section 6.2, Lemma 4, pp. 50-51.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory MvPolynomial Set Real
open PDE (partialDeriv laplacian divergence)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff

namespace PDE.Fluid.Stokes.Ball

/-! ### Spherical form -/

/-- The radial profile `Y(r)` of the meridional mode along `S_l(θ) e_r`. -/
def meridionalRadialProfile (R : ℝ) (l : ℕ) (α r : ℝ) : ℝ :=
  meridionalRadial l (α / R) (r ^ 2) * r ^ (l + 1) +
    l * meridionalGradientRadial l (α / R) (boundaryCoefficient l α) (r ^ 2) * r ^ (l - 1)

/-- The polar profile `X(r)` of the meridional mode along `S_l'(θ) e_θ`. -/
def meridionalPolarProfile (R : ℝ) (l : ℕ) (α r : ℝ) : ℝ :=
  meridionalGradientRadial l (α / R) (boundaryCoefficient l α) (r ^ 2) * r ^ (l - 1)

/-- The profile `Z(r) = r^l g_l(α r / R)` of the azimuthal mode along `S_l'(θ) e_φ`. -/
def azimuthalProfile (R : ℝ) (l : ℕ) (α r : ℝ) : ℝ :=
  besselRadial l (α / R) (r ^ 2) * r ^ l

/-- The azimuthal profile in terms of `j_l`: `Z(r) = (R / α)^l j_l(α r / R)` for `α ≠ 0`. -/
theorem azimuthalProfile_eq {R α : ℝ} (hR : R ≠ 0) (hα : α ≠ 0) (l : ℕ) (r : ℝ) :
    azimuthalProfile R l α r = (R / α) ^ l * sphericalBesselJ l (α * r / R) := by
  rw [azimuthalProfile, besselRadial_sq, sphericalBesselJ_eq_pow_mul, ← mul_assoc, ← mul_pow,
    show R / α * (α * r / R) = r by field_simp, div_mul_eq_mul_div]
  ring

private theorem point_apply (r θ φ : ℝ) (i : Fin 3) :
    (point r θ φ) i = r * radialFrame θ φ i :=
  rfl

private theorem mul_pow_pred_mul_zonalHarmonicDeriv (l : ℕ) (r θ : ℝ) :
    r * (r ^ (l - 1) * zonalHarmonicDeriv l θ) = r ^ l * zonalHarmonicDeriv l θ := by
  rcases l with _ | l
  · simp [zonalHarmonicDeriv_zero]
  · rw [Nat.add_sub_cancel, ← mul_assoc, ← pow_succ']

/-- The meridional mode in the spherical frame. -/
theorem mode_meridional_point (R : ℝ) (l : ℕ) (α r θ φ : ℝ) :
    mode R .meridional l α (point r θ φ) =
      (meridionalRadialProfile R l α r * zonalHarmonic l θ) • radialFrame θ φ +
        (meridionalPolarProfile R l α r * zonalHarmonicDeriv l θ) • polarFrame θ φ := by
  have hg := polynomialGradient_zonalSolidHarmonicPolynomial_point l r θ φ
  have hh := eval_zonalSolidHarmonicPolynomial_point l r θ φ
  ext i
  have hgi := congrArg (fun v : ℝ^3 ↦ v i) hg
  simp only [polynomialGradient, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hgi
  simp only [mode, meridionalModeField_apply, map_mul, eval_X]
  rw [hh, hgi, norm_point_sq, point_apply]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, meridionalRadialProfile,
    meridionalPolarProfile]
  ring

/-- The azimuthal mode in the spherical frame. -/
theorem mode_azimuthal_point (R : ℝ) (l : ℕ) (α r θ φ : ℝ) :
    mode R .azimuthal l α (point r θ φ) =
      (azimuthalProfile R l α r * zonalHarmonicDeriv l θ) • azimuthalFrame φ := by
  have hrc : r * r ^ (l - 1) * zonalHarmonicDeriv l θ = r ^ l * zonalHarmonicDeriv l θ := by
    rw [mul_assoc, mul_pow_pred_mul_zonalHarmonicDeriv]
  have htrig := Real.sin_sq_add_cos_sq θ
  set B := besselRadial l (α / R) (r ^ 2)
  set c := r ^ (l - 1) * zonalHarmonicDeriv l θ
  ext i
  have hcomp : mode R .azimuthal l α (point r θ φ) i = B *
      ((point r θ φ) (i + 1) *
          polynomialGradient (zonalSolidHarmonicPolynomial l) (point r θ φ) (i + 2) -
        (point r θ φ) (i + 2) *
          polynomialGradient (zonalSolidHarmonicPolynomial l) (point r θ φ) (i + 1)) := by
    simp only [mode, azimuthalModeField_apply, swirlPolynomial, map_sub, map_mul, eval_X,
      norm_point_sq, B]
    rfl
  rw [hcomp, polynomialGradient_zonalSolidHarmonicPolynomial_point]
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd, point_apply,
      radialFrame, polarFrame, azimuthalFrame, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_neg, mul_zero,
      azimuthalProfile]
  · linear_combination (-(B * r * c * Real.sin φ)) * htrig - B * Real.sin φ * hrc
  · linear_combination (B * r * c * Real.cos φ) * htrig + B * Real.cos φ * hrc
  · ring

/-! ### Rotation equivariance -/

/-- A vector form of the meridional Bessel field: `F h x + G ∇h`. -/
theorem meridionalModeField_eq (P : MvPolynomial (Fin 3) ℝ) (l : ℕ) (κ b : ℝ) (x : ℝ^3) :
    meridionalModeField P l κ b x =
      (meridionalRadial l κ (‖x‖ ^ 2) * eval x.ofLp P) • x +
        meridionalGradientRadial l κ b (‖x‖ ^ 2) • polynomialGradient P x := by
  ext i
  simp only [meridionalModeField_apply, map_mul, eval_X, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, polynomialGradient]
  ring

/-- The modes are equivariant under rotations about the axis. -/
theorem mode_axisRotation (R : ℝ) (k : ModeKind) (l : ℕ) (α φ : ℝ) (x : ℝ^3) :
    mode R k l α (axisRotation φ x) = axisRotation φ (mode R k l α x) := by
  have hnorm : ‖axisRotation φ x‖ = ‖x‖ := (axialRotation φ).norm_map x
  have hh := eval_zonalSolidHarmonicPolynomial_axisRotation l φ x
  have hg := polynomialGradient_zonalSolidHarmonicPolynomial_axisRotation l φ x
  cases k
  · simp only [mode, meridionalModeField_eq]
    rw [hnorm, hh, hg, ← coe_axialRotation, map_add, map_smul, map_smul]
  · have hcomp (y : ℝ^3) (i : Fin 3) : mode R .azimuthal l α y i =
        besselRadial l (α / R) (‖y‖ ^ 2) *
          (y (i + 1) * polynomialGradient (zonalSolidHarmonicPolynomial l) y (i + 2) -
            y (i + 2) * polynomialGradient (zonalSolidHarmonicPolynomial l) y (i + 1)) := by
      simp only [mode, azimuthalModeField_apply, swirlPolynomial, map_sub, map_mul, eval_X]
      rfl
    have htrig := Real.sin_sq_add_cos_sq φ
    ext i
    rw [hcomp, hnorm, hg]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd,
        axisRotation, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hcomp]
    · ring
    · ring
    · linear_combination besselRadial l (α / R) (‖x‖ ^ 2) *
        (x 0 * polynomialGradient (zonalSolidHarmonicPolynomial l) x 1 -
          x 1 * polynomialGradient (zonalSolidHarmonicPolynomial l) x 0) * htrig

/-! ### Equatorial parity -/

/-- The parity of a mode under the equatorial reflection `σ`: `(-1)^l` for the meridional modes
and `(-1)^(l+1)` for the azimuthal ones. -/
def modeParity : ModeKind → ℕ → ℝ
  | .meridional, l => (-1) ^ l
  | .azimuthal, l => (-1) ^ (l + 1)

/-- The modes have the parity `σ ψ(σ x) = modeParity k l • ψ(x)` under the equatorial
reflection `σ = diag(1, 1, -1)`, stated as `ψ(σ x) = modeParity k l • σ ψ(x)`. -/
theorem mode_equatorialReflection (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) (x : ℝ^3) :
    mode R k l α (equatorialReflection x) =
      modeParity k l • equatorialReflection (mode R k l α x) := by
  have hnorm : ‖equatorialReflection x‖ = ‖x‖ := equatorialReflection.norm_map x
  have hh := eval_zonalSolidHarmonicPolynomial_equatorialReflection l x
  have hg := polynomialGradient_zonalSolidHarmonicPolynomial_equatorialReflection l x
  cases k
  · simp only [mode, meridionalModeField_eq, modeParity]
    rw [hnorm, hh, hg, map_add, map_smul, map_smul, smul_add, smul_smul, smul_smul]
    congr 1
    · congr 1
      ring
    · rw [smul_smul, mul_comm]
  · have hcomp (y : ℝ^3) (i : Fin 3) : mode R .azimuthal l α y i =
        besselRadial l (α / R) (‖y‖ ^ 2) *
          (y (i + 1) * polynomialGradient (zonalSolidHarmonicPolynomial l) y (i + 2) -
            y (i + 2) * polynomialGradient (zonalSolidHarmonicPolynomial l) y (i + 1)) := by
      simp only [mode, azimuthalModeField_apply, swirlPolynomial, map_sub, map_mul, eval_X]
      rfl
    ext i
    rw [hcomp, hnorm, hg]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd,
        PiLp.smul_apply, smul_eq_mul, equatorialReflection_apply_zero,
        equatorialReflection_apply_one, equatorialReflection_apply_two, hcomp, modeParity] <;>
      ring

end PDE.Fluid.Stokes.Ball
