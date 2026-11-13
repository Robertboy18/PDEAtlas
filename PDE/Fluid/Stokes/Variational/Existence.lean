/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Variational.Energy
import PDE.Analysis.Variational.QuadraticEnergy.Constrained
import PDE.Elliptic.Variational.VectorForms

/-!
# Existence of the steady Stokes energy minimizer

The divergence-free fields form the closed kernel of the weak divergence
map. On a bounded domain, the scalar Poincaré inequality controls every
component of a vector H¹₀ field. The full gradient energy is consequently
coercive on this kernel, so the constrained Lax–Milgram argument constructs
its unique minimizer for every L² force.

No boundary charts are needed (`existsUnique_minimizes_energy`). The coercivity is
`vectorDirichletForm_isCoercive`, and the constrained minimization is
`PDE.Analysis.Variational.existsUnique_minimizer_on_submodule`, which rests on the Lax–Milgram
theorem of Mathlib. Pressure recovery is in the `Stokes.Pressure` modules. Evans (§8.4.4(a)) notes
that customary methods give the unique minimizer for bounded, simply connected open sets in
`ℝ^3`; the Lax–Milgram theorem is Theorem 1 of his §6.2.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, Theorem 1 (Lax–Milgram Theorem), pp. 315-316, and
  §8.4.4(a), p. 497.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace IncompressibleFlow.Stokes

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Every L² force on a bounded domain of positive dimension has a unique
divergence-free zero-boundary minimizer of the steady unit-viscosity energy. -/
theorem existsUnique_minimizes_energy
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) :
    ∃! u : H¹₀(Ω; ℝ^n),
      ∇· u = 0 ∧
      ∀ v : H¹₀(Ω; ℝ^n), ∇· v = 0 →
        energy f u ≤ energy f v := by
  let B := vectorDirichletForm (n := n) (m := n) (Ω := Ω)
  let ell := (innerSL ℝ f).comp toLp
  have hsymm (u v : H¹₀(Ω; ℝ^n)) : B u v = B v u := by
    simp only [B, vectorDirichletForm_eq_inner_gradient]
    exact real_inner_comm _ _
  have henergy (u : H¹₀(Ω; ℝ^n)) :
      PDE.Analysis.Variational.energy B ell u = energy f u := by
    simp only [PDE.Analysis.Variational.energy, B, ell, energy,
      vectorDirichletForm_self, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  let K := (divergence (n := n) (Ω := Ω)).ker
  have : CompleteSpace K := divergence.isClosed_ker.completeSpace_coe
  obtain ⟨u, hu, huniq⟩ :=
    PDE.Analysis.Variational.existsUnique_minimizer_on_submodule
      (V := H¹₀(Ω; ℝ^n)) B
      (vectorDirichletForm_isCoercive hn hΩbounded) hsymm ell K
  refine ⟨u, ⟨u.property, fun v hv ↦ ?_⟩, fun v hv ↦ ?_⟩
  · simpa only [henergy] using hu ⟨v, hv⟩
  · exact congrArg Subtype.val (huniq ⟨v, hv.1⟩ (fun w ↦ by
      simpa only [henergy] using hv.2 w w.property))

end IncompressibleFlow.Stokes
