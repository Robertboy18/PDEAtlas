/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Finite-order linear PDEs

`SameJetUpTo` says that two fields have the same Fréchet jet through order `k`. A `LinearPDE`
bundles an operator defined on every field with proofs that, on `C^k` functions, it is linear
and depends only on derivatives through order `k`. The restriction to `C^k` is needed because
Mathlib's `fderiv` is not linear on nondifferentiable functions.

The operator and the residual are defined on every field, since Lean's derivatives are total
functions. A value of either one says nothing by itself about whether the field is `C^k` or
whether the point lies in the domain of the equation.

Evans, §1.1, Definitions (i), calls an equation of order `k` linear if it has the form
`Σ_{|α| ≤ k} a_α(x) Dᵅu = f(x)`; such operators are linear on `C^k` fields and depend only on
derivatives through order `k`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §1.1, Definitions (i), p. 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

universe u𝕜 uE uF

noncomputable section

namespace PDE

/-- Two fields have the same Fréchet jet through order `k` at `x`. -/
def SameJetUpTo (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (k : ℕ) (u v : E → F) (x : E) : Prop :=
  ∀ j, j ≤ k → iteratedFDeriv 𝕜 j u x = iteratedFDeriv 𝕜 j v x

/-- A linear PDE `L u = f` of order at most `k`.

The operator laws are asserted only for `C^k` functions. The last law says the operator is local
in the order-`k` jet, so it cannot depend on higher derivatives or on global data. -/
structure LinearPDE (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (k : ℕ) where
  /-- The differential operator `L`, defined on every field. Its laws are the fields below. -/
  operator : (E → F) → E → F
  /-- `L 0 = 0`. -/
  map_zero : ∀ x, operator 0 x = 0
  /-- Additivity on fields with the regularity required by an order-`k` equation. -/
  map_add : ∀ u v, ContDiff 𝕜 k u → ContDiff 𝕜 k v →
    ∀ x, operator (u + v) x = operator u x + operator v x
  /-- Homogeneity on fields with the regularity required by an order-`k` equation. -/
  map_smul : ∀ (c : 𝕜) u, ContDiff 𝕜 k u →
    ∀ x, operator (c • u) x = c • operator u x
  /-- On `C^k` fields the operator depends only on derivatives through order `k`. -/
  congr_jet : ∀ u v x, ContDiffAt 𝕜 k u x → ContDiffAt 𝕜 k v x →
    SameJetUpTo 𝕜 k u v x → operator u x = operator v x
  /-- Right-hand side `f`. -/
  rhs : E → F
  /-- Domain where `L u = f` is imposed. -/
  domain : Set E := Set.univ

/-- The residual `L u - f`, defined for every field and point.

No regularity or domain condition is built in. Reading this value as a classical PDE residual
needs the `C^k` hypothesis on `u` and `x ∈ pde.domain`. -/
def LinearPDE.residual {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {k : ℕ} (pde : LinearPDE 𝕜 E F k) (u : E → F) (x : E) : F :=
  pde.operator u x - pde.rhs x

end PDE
