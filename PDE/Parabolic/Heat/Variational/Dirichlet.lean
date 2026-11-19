/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Variational.DivergenceForm
import PDE.Analysis.Evolution.Integrated.EnergyBounds
import PDE.Analysis.Evolution.Integrated.Regularity

/-!
# Weak Dirichlet heat equation

We specialize the abstract Gelfand-triple evolution theory to

`H¹₀(Ω) ↪ L²(Ω) ↪ H⁻¹(Ω)`

and the Dirichlet form

`B(u,v) = ∑ᵢ ∫_Ω ∂ᵢu ∂ᵢv`.

Thus the abstract evolution equation

`⟨uₜ,v⟩ + B(u,v) = ⟨f,v⟩`

is the homogeneous-Dirichlet heat equation `uₜ - Δu = f` in variational form. A weak
solution (`IsWeakSolution`) is an `IsGelfandIntegratedWeakSolution` for the triple
`h10L2GelfandTriple` and the form `form`, with forcing `ell ∈ L²(a,b;H⁻¹(Ω))` and initial
value `uInit ∈ L²(Ω)`. On a bounded open set it exists and is unique
(`existsUnique_weakSolution`), and it has a weak time derivative in `L²(a,b;H⁻¹(Ω))`, a
continuous `L²` representative attaining `uInit` and an energy estimate
(`existsUnique_weakSolution_with_energy`).

This is the case `L = -Δ` of Evans's §7.1.2, Theorems 3 and 4, with forcing in
`L²(a,b;H⁻¹(Ω))` in place of `f ∈ L²(U_T)`, (6). The integrated equation is Evans's (32)
for test functions `τ(t) v` with `τ(b) = 0`, so the initial value enters through `τ(a)`.

## How it works

The Dirichlet form is the divergence form with identity principal coefficients
and no lower-order terms (`form_eq_divergenceForm`), so existence and uniqueness are the
divergence-form theorem `HeatEquation.Variational.DivergenceForm.existsUnique_weakSolution`.
Evans proves the energy estimate (20) for the Galerkin approximations, from Gårding's
inequality (22) and Gronwall's inequality, (23)-(26). We prove it for the solution itself,
from the energy identity of its continuous `L²` representative (Evans's §5.9.2, Theorem 3)
and the coercivity of the Dirichlet form on a bounded set (`dirichletForm_isCoercive`),
which needs no `L²` shift and no Gronwall step.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3 (More calculus), pp. 303-304; §7.1.1, (8)
  and the definition of weak solution, pp. 373-374; §7.1.2, Theorem 2 (Energy estimates), (20)-(26),
  pp. 376-377, Theorem 3 (Existence of weak solution), (32), pp. 378-379, and Theorem 4 (Uniqueness
  of weak solutions), p. 379.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace HeatEquation.Variational.Dirichlet

open Function
open PDE.Analysis.Evolution
open scoped InnerProductSpace

open SobolevSpace
open SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The time-independent Dirichlet form, viewed as a nonautonomous form. -/
noncomputable def form :
    ℝ → H¹₀(Ω) →L[ℝ]
      StrongDual ℝ (H¹₀(Ω)) :=
  fun _ ↦ dirichletForm (n := n) (Ω := Ω)

/-- The Dirichlet heat form pairs spatial gradients through the `L²` inner product. -/
@[simp]
theorem form_apply
    (t : ℝ)
    (u v : H¹₀(Ω)) :
    form (n := n) (Ω := Ω) t u v =
      ∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i u,
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ := by
  exact dirichletForm_apply (n := n) (Ω := Ω) u v

/-- The Dirichlet heat form is the divergence form with identity principal
coefficients and zero lower-order coefficients. -/
theorem form_eq_divergenceForm :
    form (n := n) (Ω := Ω) =
      DivergenceForm.form (fun _ ↦ identityCoefficientOperator) (fun _ ↦ 0) (fun _ ↦ 0) := by
  funext t
  ext u v
  change dirichletForm u v = fullDivergenceForm identityCoefficientOperator 0 0 u v
  simp only [fullDivergenceForm, add_apply, variableCoeffForm_identity,
    lowerOrderForm_apply]
  simp

/-- The integrated weak solution of the homogeneous-Dirichlet heat equation with
forcing in `L²(a,b;H⁻¹(Ω))`. The integrated equation is Evans's (32) in §7.1.2 for test
functions `τ(t) v`.

The forcing is a Bochner equivalence class, so changing it on a null set of
times leaves the integrated equation unchanged. `HasEnergyEstimate` records the
continuous `L²` representative that attains the initial value. -/
def IsWeakSolution
    (hΩopen : IsOpen Ω) {a b : ℝ}
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)))
    (u : Lp (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc a b)))
    (uInit : DerivLp n 2 Ω) : Prop :=
  IsGelfandIntegratedWeakSolution
    (h10L2GelfandTriple hΩopen) (form (n := n) (Ω := Ω))
    (fun t ↦ (ell : ℝ → StrongDual ℝ (H¹₀(Ω))) t)
    u uInit

/-- The Lions-Magenes regularity and energy conclusion attached to a
weak heat solution with `L²(a,b;H⁻¹(Ω))` forcing. -/
def HasEnergyEstimate
    (hΩopen : IsOpen Ω) {a b : ℝ}
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)))
    (u : Lp (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc a b)))
    (uInit : DerivLp n 2 Ω) (C : ℝ) : Prop :=
  ∃ g : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)),
    ∃ E : ContinuousPivotEvolutionOn
        (h10L2GelfandTriple hΩopen)
        (fun t ↦ (u : ℝ → H¹₀(Ω)) t)
        (fun t ↦ (g : ℝ → StrongDual ℝ (H¹₀(Ω))) t)
        a b,
      HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hΩopen) u g ∧
      E.representative a = uInit ∧
      (g : ℝ → StrongDual ℝ (H¹₀(Ω))) =ᵐ[
        volume.restrict (Set.Ioc a b)]
          (fun t ↦
            (ell : ℝ → StrongDual ℝ (H¹₀(Ω))) t -
              form (n := n) (Ω := Ω) t
                ((u : ℝ → H¹₀(Ω)) t)) ∧
      ∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) * ‖E.representative t‖ ^ 2 +
            (C / 2) * ∫ s in a..t,
              ‖(u : ℝ → H¹₀(Ω)) s‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖uInit‖ ^ 2 +
            (1 / (2 * C)) * ∫ s in a..t,
              ‖(ell : ℝ → StrongDual ℝ (H¹₀(Ω))) s‖ ^ 2

/-- Existence and uniqueness of the weak solution of the homogeneous-Dirichlet heat
equation on a bounded open set, for forcing `ell ∈ L²(a,b;H⁻¹(Ω))` and initial value
`uInit ∈ L²(Ω)`. For `L = -Δ` this extends Evans's §7.1.2, Theorems 3 and 4, from
`L²(U_T)` forcing.

The finite-dimensional spaces are the canonical spectral spaces of the
compact inclusion `H¹₀(Ω) ↪ L²(Ω)`, so no basis or approximation data
appear in the statement. -/
theorem existsUnique_weakSolution
    (hΩopen : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b)
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)))
    (uInit : DerivLp n 2 Ω) :
    ∃! u : Lp (H¹₀(Ω)) 2
        (volume.restrict (Set.Ioc a b)),
      IsWeakSolution hΩopen ell u uInit := by
  have h := DivergenceForm.existsUnique_weakSolution hΩopen hΩbounded hab
    (fun _ ↦ identityCoefficientOperator) (fun _ ↦ 0) (fun _ ↦ 0)
    (fun _ _ ↦ integratedElliptic_identity)
    (fun _ _ ↦ ⟨le_rfl, le_rfl, fun _ ↦ norm_zero.le, norm_zero.le⟩)
    aestronglyMeasurable_const ‖fullDivergenceForm (n := n) (Ω := Ω)
      identityCoefficientOperator 0 0‖₊ (fun _ _ ↦ le_rfl) ell uInit
  simpa only [IsWeakSolution, DivergenceForm.IsWeakSolution, ← form_eq_divergenceForm] using h

/-- Existence and uniqueness of the weak heat solution, with its energy estimate.

Besides existence and uniqueness, the solution has an
`L²(a,b;H⁻¹(Ω))` weak time derivative, a representative in
`C([a,b];L²(Ω))` with the prescribed initial value, the residual identity
`uₜ = ell + Δu`, and the integral energy estimate with the coercivity constant `C` of the
Dirichlet form. Evans proves the corresponding estimate (20) for the Galerkin
approximations. -/
theorem existsUnique_weakSolution_with_energy
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω)
    {a b : ℝ} (hab : a < b)
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Set.Ioc a b)))
    (uInit : DerivLp n 2 Ω) :
    ∃ C : ℝ, 0 < C ∧
      ∃! u : Lp (H¹₀(Ω)) 2
          (volume.restrict (Set.Ioc a b)),
        IsWeakSolution hΩopen ell u uInit ∧
          HasEnergyEstimate hΩopen ell u uInit C := by
  let h10InnerProductSpace : InnerProductSpace ℝ (H¹₀(Ω)) := inferInstance
  let h10CompleteSpace : CompleteSpace (H¹₀(Ω)) := inferInstance
  obtain ⟨C, hC, hcoercive⟩ := dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded
  let MB : NNReal := ⟨‖form (n := n) (Ω := Ω) a‖, norm_nonneg (form (n := n) (Ω := Ω) a)⟩
  have hformMeas : AEStronglyMeasurable (form (n := n) (Ω := Ω))
      (volume.restrict (Set.Ioc a b)) := aestronglyMeasurable_const
  have hformCoercive (t : ℝ) (_ : t ∈ Set.Icc a b) (w : H¹₀(Ω)) :
      C * ‖w‖ ^ 2 ≤ form (n := n) (Ω := Ω) t w w := by
    simpa only [form, pow_two, mul_assoc] using hcoercive w
  obtain ⟨u, hu, hunique⟩ := existsUnique_weakSolution hΩopen hΩbounded hab ell uInit
  change IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hΩopen) (form (n := n) (Ω := Ω))
    (fun t ↦ (ell : ℝ → StrongDual ℝ (H¹₀(Ω))) t) u uInit at hu
  obtain ⟨g, E, hgweak, hEa, hresidual⟩ :=
    @IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_initial_L2
      (H¹₀(Ω)) (DerivLp n 2 Ω)
      inferInstance h10InnerProductSpace h10CompleteSpace
      inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
      a b (h10L2GelfandTriple hΩopen) (form (n := n) (Ω := Ω)) ell u uInit
      (fun v ↦ hformMeas.apply_continuousLinearMap v) (MB : ℝ) (.of_forall fun _ ↦ le_rfl) hu
      hab
  exact ⟨C, hC, u, ⟨hu, g, E, hgweak, hEa, hresidual,
    E.coercive_energy_bound_L2 hEa hresidual hC hformCoercive hab.le⟩, fun v hv ↦ hunique v hv.1⟩

end HeatEquation.Variational.Dirichlet
