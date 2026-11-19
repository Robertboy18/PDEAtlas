/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.QuadraticEnergy
import PDE.Analysis.Operator.Coercivity
import PDE.Analysis.Variational.LaxMilgram

/-!
# Quadratic minimization under a closed linear constraint

Restricting a coercive symmetric form to a complete subspace preserves its
coercivity. Lax–Milgram on that subspace therefore gives the unique constrained
minimizer. The load can be any continuous linear functional; the constraint
does not need a finite-dimensional description.

On the subspace this is the abstract Dirichlet principle of
`PDE.Analysis.Variational.QuadraticEnergy`, with the weak solution supplied by Lax–Milgram,
Evans, §6.2.1, Theorem 1.

## Main results

* `existsUnique_minimizer_on_submodule`: `½ B(u, u) - ell(u)` has a unique minimizer on every
  complete subspace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, Theorem 1 (Lax–Milgram Theorem), p. 315.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Variational

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A symmetric coercive energy has a unique minimizer on every complete
linear subspace. For a closed subspace of a Hilbert space, completeness is
inherited from the ambient space. -/
theorem existsUnique_minimizer_on_submodule
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hsymm : ∀ u v, B u v = B v u) (ell : StrongDual ℝ V)
    (K : Submodule ℝ V) [CompleteSpace K] :
    ∃! u : K, ∀ v : K, energy B ell u ≤ energy B ell v := by
  let BK := B.bilinearComp K.subtypeL K.subtypeL
  let ellK := ell.comp K.subtypeL
  have hBK : IsCoercive BK := by
    obtain ⟨c, hc, hbound⟩ := hB
    exact ⟨c, hc, fun u ↦ hbound (u : V)⟩
  have hsymmK (u v : K) : BK u v = BK v u := hsymm u v
  have henergy (u : K) : energy BK ellK u = energy B ell u := rfl
  obtain ⟨u, hu, _⟩ := IsWeakSolution.existsUnique BK hBK ellK
  refine ⟨u, fun v ↦ ?_, fun v hv ↦ ?_⟩
  · simpa only [henergy] using hu.energy_le hsymmK hBK.self_nonneg v
  · exact hu.eq_of_minimizes_energy hBK hsymmK (fun w ↦ by
      simpa only [henergy] using hv w)

end PDE.Analysis.Variational
