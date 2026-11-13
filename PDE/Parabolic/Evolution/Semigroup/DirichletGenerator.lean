/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Form.Resolvent
public import PDE.Elliptic.Variational.DistributionalPoisson
public import PDE.Elliptic.Variational.ModifiedHelmholtz
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2

/-!
# The weak Dirichlet Laplacian on `L²`

On any open set, the generator domain consists of the `L²` representatives of `H¹₀` functions whose
distributional Laplacian belongs to `L²` (`mem_generator_domain_iff`), and the generator is that
Laplacian (`mem_generator_graph_iff`). The domain is dense (`dense_generator_domain`). For `λ > 0`
the resolvent is the modified Helmholtz solver `modifiedHelmholtzSolve`
(`resolvent_generator_eq_modifiedHelmholtzSolve`), and its `1 / λ` bound follows from testing the
variational equation with the solution itself (`hasContractionResolvent_generator`).

For `L = -Δ`, Evans's §7.4.3(a) takes `D(A) = H¹₀(U) ∩ H²(U)`, (25), and `Au = -Lu`, (26), on a
bounded open set with smooth boundary. We use the weak domain, which needs neither boundedness nor
boundary smoothness. The resolvent equation is Evans's (30), which he solves by §6.2.2, Theorem 3,
and the `1 / λ` bound is (32) with `γ = 0`, obtained as in step 4 of his proof of Theorem 5.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.2, Theorem 3 (First Existence Theorem for weak
  solutions), p. 319; §7.4.3(a), (25)-(26), (30)-(32) and steps 3-4 of the proof of Theorem 5,
  pp. 442-443.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace HeatEquation.Semigroup.Dirichlet

open PDE.Analysis.Evolution PDE.Analysis.Variational
open SobolevSpace SobolevSpace.GraphSpace
open scoped InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} (hΩopen : IsOpen Ω)

local notation "L2" => DerivLp n 2 Ω

/-- The negative Dirichlet form, realized as a partial Laplacian on `L²(Ω)`. -/
def generator : L2 →ₗ.[ℝ] L2 :=
  (h10L2GelfandTriple hΩopen).formOperator dirichletForm

/-- Adding `λ` times the pivot mass term gives the modified Helmholtz form. -/
theorem dirichletForm_add_smul_energyToDual (lambda : ℝ) :
    dirichletForm + lambda • (h10L2GelfandTriple hΩopen).energyToDual =
      modifiedHelmholtzForm (n := n) (Ω := Ω) lambda := by
  ext u v
  rfl

/-- The positive unit shift is coercive without a Poincaré inequality. -/
theorem isCoercive_dirichletForm_add_energyToDual :
    IsCoercive (dirichletForm + (h10L2GelfandTriple hΩopen).energyToDual) := by
  have h := modifiedHelmholtzForm_isCoercive (n := n) (Ω := Ω) 1 zero_lt_one
  rwa [← dirichletForm_add_smul_energyToDual hΩopen, one_smul] at h

/-- The form `dirichletForm u` is represented by `-f` in the pivot exactly when `u` is a weak
Poisson solution with right side `-f`. -/
theorem dirichletForm_eq_neg_pivot_iff (u : H¹₀(Ω)) (f : L2) :
    dirichletForm u = -(h10L2GelfandTriple hΩopen).pivotToDual f ↔
      IsWeakPoissonSolution (-f) u := by
  rw [← isWeakSolution_iff_isWeakPoissonSolution hΩopen]
  change (dirichletForm u = -(h10L2GelfandTriple hΩopen).pivotToDual f) ↔
    ∀ v, dirichletForm u v = loadFunctional (-f) v
  rw [DFunLike.ext_iff]
  simp only [neg_apply, GelfandTriple.pivotToDual_apply,
    h10L2GelfandTriple_inclusion_apply, loadFunctional_apply, inner_neg_left]

/-- The generator graph is `f = Δu` with zero boundary values in the `H¹₀` sense. -/
theorem mem_generator_graph_iff (x f : L2) :
    (x, f) ∈ (generator hΩopen).graph ↔
      ∃ u : H¹₀(Ω), baseCoordCLM u = x ∧ IsWeakPoissonSolution (-f) u := by
  rw [generator, GelfandTriple.mem_formOperator_graph_iff]
  simp only [h10L2GelfandTriple_inclusion_apply, dirichletForm_eq_neg_pivot_iff]

/-- The generator domain consists of the `H¹₀` functions with `L²` Laplacian. -/
theorem mem_generator_domain_iff (x : L2) :
    x ∈ (generator hΩopen).domain ↔
      ∃ u : H¹₀(Ω), baseCoordCLM u = x ∧ ∃ f : L2, IsWeakPoissonSolution f u := by
  rw [generator, GelfandTriple.mem_formOperator_domain_iff]
  simp only [h10L2GelfandTriple_inclusion_apply, dirichletForm_eq_neg_pivot_iff]
  constructor
  · rintro ⟨u, hu, f, hf⟩
    exact ⟨u, hu, -f, hf⟩
  · rintro ⟨u, hu, f, hf⟩
    exact ⟨u, hu, -f, by simpa using hf⟩

/-- The partial Dirichlet Laplacian is densely defined in `L²`. -/
theorem dense_generator_domain :
    Dense ((generator hΩopen).domain : Set L2) :=
  (h10L2GelfandTriple hΩopen).dense_formOperator_domain dirichletForm
    (isCoercive_dirichletForm_add_energyToDual hΩopen)

/-- For every `λ > 0`, `λ - Δ` maps the generator domain onto `L²`, with inverse norm at most
`1 / λ`. -/
theorem hasContractionResolvent_generator :
    HasContractionResolvent (generator hΩopen) :=
  (h10L2GelfandTriple hΩopen).hasContractionResolvent_formOperator dirichletForm
    dirichletForm_self_nonneg (isCoercive_dirichletForm_add_energyToDual hΩopen)

/-- The resolvent of the generator is the weak modified Helmholtz solver. -/
theorem resolvent_generator_eq_modifiedHelmholtzSolve {lambda : ℝ} (hlambda : 0 < lambda)
    (f : L2) :
    (hasContractionResolvent_generator hΩopen).resolvent hlambda f =
      baseCoordCLM (modifiedHelmholtzSolve lambda hlambda f) := by
  let u := modifiedHelmholtzSolve lambda hlambda f
  have hBu : dirichletForm u =
      -(h10L2GelfandTriple hΩopen).pivotToDual (lambda • baseCoordCLM u - f) := by
    ext v
    have h := modifiedHelmholtzSolve.isWeakSolution lambda hlambda f v
    rw [modifiedHelmholtzForm_apply, loadFunctional_apply] at h
    change dirichletForm u v = -⟪lambda • baseCoordCLM u - f, baseCoordCLM v⟫_ℝ
    rw [inner_sub_left, real_inner_smul_left]
    linarith
  have hg := (h10L2GelfandTriple hΩopen).mem_formOperator_graph_iff dirichletForm
    (baseCoordCLM u) (lambda • baseCoordCLM u - f)
  have hgraph : (baseCoordCLM u, lambda • baseCoordCLM u - f) ∈
      (generator hΩopen).graph := hg.2 ⟨u, rfl, hBu⟩
  obtain ⟨x, hx, hAx⟩ := (LinearPMap.mem_graph_iff _).1 hgraph
  have hshift : lambda • (x : L2) - generator hΩopen x = f := by
    rw [hx, hAx, sub_sub_cancel]
  calc
    (hasContractionResolvent_generator hΩopen).resolvent hlambda f =
        (hasContractionResolvent_generator hΩopen).resolvent hlambda
          (lambda • (x : L2) - generator hΩopen x) := congrArg _ hshift.symm
    _ = (x : L2) := (hasContractionResolvent_generator hΩopen).resolvent_shift hlambda x
    _ = _ := hx

end HeatEquation.Semigroup.Dirichlet
