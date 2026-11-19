/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
public import PDE.Elliptic.Variational.LowerOrderForm
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
import PDE.Analysis.Evolution.Galerkin.Measurable.Existence
import PDE.Spaces.Sobolev.Variational.Galerkin.SpectralTrial

/-!
# Time-dependent divergence-form heat equations

We apply the abstract Galerkin theory of evolution equations on the Gelfand triple
`H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)` to an operator-valued extension of the
homogeneous-Dirichlet problem

`u_t - ∂ᵢ(aⁱʲ(t) ∂ⱼu) + bⁱ(t) ∂ᵢu + c(t)u = f`

on a bounded open set `Ω`. The principal and lower-order coefficients are
represented by bounded `L²(Ω)` operators, as in the elliptic divergence-form
theory. Pointwise `L∞` coefficient fields enter through multiplication
operators, and the operator form also allows nonlocal bounded coefficients.
The form is

`B(t;u,v) = ∑ᵢⱼ ⟪Aᵢⱼ(t) Dⱼu, Dᵢv⟫
           + ∑ᵢ ⟪bᵢ(t) Dᵢu, v⟫ + ⟪c(t)u,v⟫`.

Uniform ellipticity and uniform bounds on the lower-order coefficients give
the Gårding inequality, Evans's (22),

`(α/2) ‖u‖²_{H¹₀} ≤ B(t;u,u) + γ₀ ‖u‖²_{L²}`.

The abstract Gårding-shift theorem then supplies existence for every Bochner
`L²(a,b;H⁻¹(Ω))` forcing and `L²` initial value. Uniqueness uses the energy identity of the
Lions-Magenes continuous `L²` representative and Grönwall's inequality, as in Evans's
proof of §7.1.2, Theorem 4.

The theorem assumes strong measurability of the induced operator-valued form
on `[a,b]`. The finite-dimensional Galerkin solution coefficients are therefore
absolutely continuous and solve their equations almost everywhere, as in
Evans's proof of §7.1.2, Theorem 1. For bounded measurable coefficients,
`PDE.Parabolic.Heat.Variational.MeasurableExistence` uses strong measurability of each
fixed-vector form evaluation instead.

With multiplication operators as coefficients, the problem is Evans's (1)-(2), and the
theorems extend his §7.1.2, Theorems 3 and 4, to forcing in `L²(a,b;H⁻¹(Ω))`; Evans assumes
`f ∈ L²(U_T)`, (6). The measurability hypothesis on the form can fail for coefficients
that are only in `L∞(U_T)`, Evans's (5), which is the case of `MeasurableExistence`.
No symmetry of the principal coefficients is assumed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3 (More calculus), pp. 303-304; §7.1.1,
  (1)-(2) and (5)-(8), pp. 372-373, and the definition of weak solution, p. 374; §7.1.2, Theorem 1
  (Construction of approximate solutions), p. 376, Theorem 2 (Energy estimates), (20)-(26),
  pp. 376-377, Theorem 3 (Existence of weak solution), (32), pp. 378-379, and Theorem 4 (Uniqueness
  of weak solutions), p. 379.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace HeatEquation.Variational.DivergenceForm

open PDE.Analysis.Evolution
open scoped InnerProductSpace

open SobolevSpace
open SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The time-dependent full divergence-form bilinear form, regarded as an
operator from `H¹₀(Ω)` to `H⁻¹(Ω)`. -/
noncomputable def form
    (A : ℝ → (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (bCoeff : ℝ → (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : ℝ → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω) :
    ℝ → H¹₀(Ω) →L[ℝ]
      StrongDual ℝ (H¹₀(Ω)) :=
  fun t ↦
    fullDivergenceForm (n := n) (Ω := Ω)
      (A t) (bCoeff t) (c t)

/-- Expands the divergence-form operator into its principal, drift, and zeroth-order pairings. -/
@[simp]
theorem form_apply
    (A : ℝ → (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (bCoeff : ℝ → (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : ℝ → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    (t : ℝ) (u v : H¹₀(Ω)) :
    form A bCoeff c t u v =
      (∑ i : Fin n, ∑ j : Fin n,
        ⟪A t i j
            (derivCoordCLM (n := n) (Ω := Ω) j u),
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ) +
      (∑ i : Fin n,
        ⟪bCoeff t i
            (derivCoordCLM (n := n) (Ω := Ω) i u),
          baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ) +
      ⟪c t (baseCoordCLM (n := n) (Ω := Ω) u),
        baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
  exact fullDivergenceForm_apply
    (n := n) (Ω := Ω) (A t) (bCoeff t) (c t) u v

/-- The integrated variational solution for the operator-valued,
time-dependent divergence-form equation with forcing in
`L²(a,b;H⁻¹(Ω))`. Pointwise coefficients, as in Evans's (2), are obtained by choosing
multiplication operators. -/
def IsWeakSolution
    (hΩopen : IsOpen Ω)
    (A : ℝ → (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (bCoeff : ℝ → (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : ℝ → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    {a b : ℝ}
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)))
    (u : Lp (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc a b)))
    (uInit : DerivLp n 2 Ω) : Prop :=
  IsGelfandIntegratedWeakSolution
    (h10L2GelfandTriple hΩopen)
    (form A bCoeff c)
    (fun t ↦ (ell : ℝ → StrongDual ℝ (H¹₀(Ω))) t)
    u uInit

/-- The continuous `L²` representative, residual equation and Gårding energy estimate of a
weak divergence-form solution. The last integral is the lower-order mass correction;
Grönwall's inequality, as in Evans's (24)-(26), turns the estimate into an exponential
bound. -/
def HasGardingEnergyEstimate
    (hΩopen : IsOpen Ω)
    (A : ℝ → (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (bCoeff : ℝ → (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : ℝ → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    {a b : ℝ}
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)))
    (u : Lp (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc a b)))
    (uInit : DerivLp n 2 Ω)
    (theta gammaShift : ℝ) : Prop :=
  ∃ g : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)),
    ∃ E : ContinuousPivotEvolutionOn
        (h10L2GelfandTriple hΩopen)
        (fun t ↦ (u : ℝ → H¹₀(Ω)) t)
        (fun t ↦ (g : ℝ → StrongDual ℝ (H¹₀(Ω))) t)
        a b,
      HasGelfandWeakTimeDerivativeOn
        (h10L2GelfandTriple hΩopen) u g ∧
      E.representative a = uInit ∧
      (g : ℝ → StrongDual ℝ (H¹₀(Ω))) =ᵐ[
        volume.restrict (Set.Ioc a b)]
          (fun t ↦
            (ell : ℝ → StrongDual ℝ (H¹₀(Ω))) t -
              form A bCoeff c t
                ((u : ℝ → H¹₀(Ω)) t)) ∧
      ∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
            (theta / 2) * ∫ s in a..t,
              ‖(u : ℝ → H¹₀(Ω)) s‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
            (1 / (2 * theta)) * (∫ s in a..t,
              ‖(ell : ℝ → StrongDual ℝ (H¹₀(Ω))) s‖ ^ 2) +
            gammaShift * (∫ s in a..t, ‖E.representative s‖ ^ 2)

/-- Existence and uniqueness of the weak solution of the time-dependent operator-valued
divergence-form parabolic equation, for forcing in `L²(a,b;H⁻¹(Ω))` and initial value
in `L²(Ω)`.

The hypotheses `hElliptic` and `hLower` are uniform on `[a,b]`.  The
form-level measurability and norm bound are stated explicitly because the
coefficient representation permits general bounded `L²` operators, not only
pointwise multiplication operators. With multiplication operators as
coefficients, this extends Evans's §7.1.2, Theorems 3 and 4, to `H⁻¹` forcing. -/
theorem existsUnique_weakSolution
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b)
    (A : ℝ → (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (bCoeff : ℝ → (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : ℝ → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    {alpha beta gamma : ℝ}
    (hElliptic : ∀ t ∈ Set.Icc a b,
      IntegratedElliptic (n := n) (Ω := Ω)
        (A t) alpha)
    (hLower : ∀ t ∈ Set.Icc a b,
      LowerOrderBounds (n := n) (Ω := Ω)
        (bCoeff t) (c t) beta gamma)
    (hformMeas : AEStronglyMeasurable (form A bCoeff c)
      (volume.restrict (Set.Icc a b)))
    (MB : NNReal)
    (hformNorm : ∀ t ∈ Set.Icc a b,
      ‖form A bCoeff c t‖ ≤ MB)
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)))
    (uInit : DerivLp n 2 Ω) :
    ∃! u : Lp (H¹₀(Ω)) 2
        (volume.restrict (Set.Ioc a b)),
      IsWeakSolution hΩopen A bCoeff c ell u uInit := by
  have htheta : 0 < alpha / 2 := half_pos (hElliptic a ⟨le_rfl, hab.le⟩).1
  have hGarding (t : ℝ) (ht : t ∈ Set.Icc a b) (w : H¹₀(Ω)) :
      alpha / 2 * ‖w‖ ^ 2 ≤ form A bCoeff c t w w + coerciveShift (n := n) alpha beta gamma *
        ‖(h10L2GelfandTriple hΩopen).inclusion w‖ ^ 2 := by
    simpa only [form, shiftedDivergenceForm_apply, h10L2GelfandTriple_inclusion_apply,
      real_inner_self_eq_norm_sq, pow_two, mul_assoc] using
      shiftedDivergenceForm_coercive_bound (A t) (bCoeff t) (c t) (hElliptic t ht) (hLower t ht) w
  simpa only [IsWeakSolution] using!
    @IsGelfandIntegratedWeakSolution.existsUnique_of_measurable_galerkin_garding_L2
      (H¹₀(Ω)) (DerivLp n 2 Ω) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (h10L2GelfandTriple hΩopen)
      (h10L2SpectralTrialSystem hΩopen hΩbounded).space
      (h10L2SpectralTrialSystem hΩopen hΩbounded).finiteDimensional
      1
      (h10L2SpectralTrialSystem hΩopen hΩbounded).projection
      (h10L2SpectralTrialSystem hΩopen hΩbounded).denseEnergy
      (form A bCoeff c) a b (alpha / 2) (coerciveShift (n := n) alpha beta gamma) ell
      hab htheta (fun v ↦ hformMeas.apply_continuousLinearMap v) MB hformNorm hGarding uInit

/-- Existence and uniqueness for the time-dependent divergence-form problem, with the weak
time derivative, the continuous `L²` representative (Evans's §5.9.2, Theorem 3), the
residual equation and the Gårding energy estimate. -/
theorem existsUnique_weakSolution_with_energy
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b)
    (A : ℝ → (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (bCoeff : ℝ → (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : ℝ → DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)
    {alpha beta gamma : ℝ}
    (hElliptic : ∀ t ∈ Set.Icc a b,
      IntegratedElliptic (n := n) (Ω := Ω)
        (A t) alpha)
    (hLower : ∀ t ∈ Set.Icc a b,
      LowerOrderBounds (n := n) (Ω := Ω)
        (bCoeff t) (c t) beta gamma)
    (hformMeas : AEStronglyMeasurable (form A bCoeff c)
      (volume.restrict (Set.Icc a b)))
    (MB : NNReal)
    (hformNorm : ∀ t ∈ Set.Icc a b,
      ‖form A bCoeff c t‖ ≤ MB)
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)))
    (uInit : DerivLp n 2 Ω) :
    ∃! u : Lp (H¹₀(Ω)) 2
        (volume.restrict (Set.Ioc a b)),
      IsWeakSolution hΩopen A bCoeff c ell u uInit ∧
        HasGardingEnergyEstimate hΩopen A bCoeff c ell u uInit
          (alpha / 2) (coerciveShift (n := n) alpha beta gamma) := by
  let h10InnerProductSpace : InnerProductSpace ℝ (H¹₀(Ω)) := inferInstance
  let h10CompleteSpace : CompleteSpace (H¹₀(Ω)) := inferInstance
  have htheta : 0 < alpha / 2 := half_pos (hElliptic a ⟨le_rfl, hab.le⟩).1
  have hGarding (t : ℝ) (ht : t ∈ Set.Icc a b) (w : H¹₀(Ω)) :
      alpha / 2 * ‖w‖ ^ 2 ≤ form A bCoeff c t w w + coerciveShift (n := n) alpha beta gamma *
        ‖(h10L2GelfandTriple hΩopen).inclusion w‖ ^ 2 := by
    simpa only [form, shiftedDivergenceForm_apply, h10L2GelfandTriple_inclusion_apply,
      real_inner_self_eq_norm_sq, pow_two, mul_assoc] using
      shiftedDivergenceForm_coercive_bound (A t) (bCoeff t) (c t) (hElliptic t ht) (hLower t ht) w
  obtain ⟨u, g, E, hu, hunique, hgweak, hEa, hresidual, henergy⟩ :=
    @IsGelfandIntegratedWeakSolution.exists_of_measurable_galerkin_garding_L2_full
      (H¹₀(Ω)) (DerivLp n 2 Ω) inferInstance h10InnerProductSpace h10CompleteSpace
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance (h10L2GelfandTriple hΩopen)
      (h10L2SpectralTrialSystem hΩopen hΩbounded).space
      (h10L2SpectralTrialSystem hΩopen hΩbounded).finiteDimensional
      1
      (h10L2SpectralTrialSystem hΩopen hΩbounded).projection
      (h10L2SpectralTrialSystem hΩopen hΩbounded).denseEnergy
      (form A bCoeff c) a b (alpha / 2)
      (coerciveShift (n := n) alpha beta gamma) ell
      hab htheta (fun v ↦ hformMeas.apply_continuousLinearMap v) MB hformNorm hGarding uInit
  have henergy' :
      ∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
            ((alpha / 2) / 2) * ∫ s in a..t,
              ‖(u : ℝ → H¹₀(Ω)) s‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
            (1 / (2 * (alpha / 2))) * (∫ s in a..t,
              ‖(ell : ℝ → StrongDual ℝ (H¹₀(Ω))) s‖ ^ 2) +
            coerciveShift (n := n) alpha beta gamma *
              (∫ s in a..t, ‖E.representative s‖ ^ 2) := by
    simpa only [add_assoc] using! henergy
  exact ⟨u, ⟨hu, g, E, hgweak, hEa, hresidual, henergy'⟩, fun v hv ↦ hunique v hv.1⟩

end HeatEquation.Variational.DivergenceForm
