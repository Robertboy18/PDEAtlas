/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.Convergence
public import PDE.Elliptic.Homogenization.Uniqueness

/-!
# Periodic elliptic homogenization on the unit interval

Given a positive continuous one-periodic coefficient and a continuous source, the
zero-Dirichlet solution family converges to the harmonic-mean limiting solution, with a
normalized periodic cell corrector. Both the solutions and the corrected gradients satisfy
uniform order-`|ε|` estimates.

The reference is Evans, *Partial Differential Equations*, second edition (2010),
§4.5.4, Example 5, pp. 229–232. This development proves the scalar one-dimensional
case on `[0,1]`, with continuous coefficients and sources given on the real line.
The solutions have continuous first derivatives; the divergence equation is stated
using their differentiable fluxes. It does not require derivatives of the medium.
-/

@[expose] public section

namespace PDE.Elliptic.Homogenization.PeriodicMedium

open Set
open scoped Topology

/-- Existence, the harmonic-mean effective equation, a periodic cell corrector, and quantitative
uniform homogenization, with all witnesses constructed from the coefficient and source. -/
theorem exists_dirichlet_homogenization (a : PeriodicMedium) {f : ℝ → ℝ} (hf : Continuous f) :
    ∃ (u : ℝ → ℝ → ℝ) (u₀ χ : ℝ → ℝ),
      (∀ ε, ContDiff ℝ 1 (u ε)) ∧ ContDiff ℝ 1 u₀ ∧ ContDiff ℝ 1 χ ∧
      (∀ ε > 0, IsFluxDirichletSolution (fun x ↦ a.coefficient (x / ε)) f (u ε)) ∧
      IsFluxDirichletSolution (fun _ ↦ a.effective) f u₀ ∧
      Function.Periodic χ 1 ∧ χ 0 = 0 ∧
      (∀ y, a.coefficient y * (1 + deriv χ y) = a.effective) ∧
      TendstoUniformlyOn u u₀ (𝓝[>] (0 : ℝ)) (Icc (0 : ℝ) 1) ∧
      (∃ C > 0, ∃ ε₀ > 0, ∀ ε : ℝ, ε ≠ 0 → |ε| ≤ ε₀ →
        ∀ x ∈ Icc (0 : ℝ) 1, |u ε x - u₀ x| ≤ C * |ε|) ∧
      (∃ C > 0, ∃ ε₀ > 0, ∀ ε : ℝ, ε ≠ 0 → |ε| ≤ ε₀ →
        ∀ x ∈ Icc (0 : ℝ) 1,
          |deriv (u ε) x - (1 + deriv χ (x / ε)) * deriv u₀ x| ≤ C * |ε|) := by
  exact ⟨a.solution f, a.homogenizedSolution f, a.corrector,
    a.contDiff_solution hf, a.contDiff_homogenizedSolution hf, a.contDiff_corrector,
    fun ε _ ↦ a.solution_isFluxDirichletSolution hf ε,
    a.homogenizedSolution_isFluxDirichletSolution hf,
    a.periodic_corrector, a.corrector_zero, a.cell_flux,
    a.tendstoUniformlyOn_solution hf, a.exists_solution_error_bound hf,
    a.exists_gradient_corrector_error_bound hf⟩

end PDE.Elliptic.Homogenization.PeriodicMedium
