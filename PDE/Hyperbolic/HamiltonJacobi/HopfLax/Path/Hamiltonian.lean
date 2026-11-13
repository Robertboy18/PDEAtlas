/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Path
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Hamiltonian

/-!
# The path formula for a prescribed Hamiltonian

For a finite convex superlinear Hamiltonian, its Legendre transform is a
finite continuous convex superlinear Lagrangian. Thus the integral
action on absolutely continuous paths gives the Hopf–Lax formula and attains
its minimum at a straight path. All dual growth and attainment hypotheses
are derived from the Hamiltonian and the Lipschitz datum. With `L = H*` as in (45) of
Evans, §10.3.4, this is Theorem 4 of §3.3.2 for a prescribed Hamiltonian.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2, Theorems 3 and 4; §10.3.4, equation (45).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

set_option linter.missingDocs true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Starting with a convex superlinear Hamiltonian, the Hopf–Lax evolution
is the infimum of the integral action of its Legendre transform over
absolutely continuous paths. -/
theorem value_hamiltonian_eq_variationalValue {H g : E → ℝ}
    (hH : Superlinear H) (hconv : ConvexOn ℝ Set.univ H)
    {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} {x : E} (ht : 0 < t) :
    value (hamiltonian H) g t x = variationalValue (hamiltonian H) g t x := by
  have hcont : Continuous H := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  exact value_eq_variationalValue_of_lipschitz (convexOn_hamiltonian hH)
    (superlinear_hamiltonian hH hcont) hg ht

/-- Evans's Hopf–Lax footpoint formula (21) for the path action of the
Legendre transform of a prescribed Hamiltonian, in arbitrary finite dimension. -/
theorem variationalValue_hamiltonian_eq_inf_footpoints {H g : E → ℝ}
    (hH : Superlinear H) (hconv : ConvexOn ℝ Set.univ H)
    {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} {x : E} (ht : 0 < t) :
    variationalValue (hamiltonian H) g t x =
      sInf (Set.range fun y : E ↦ g y + t * hamiltonian H (t⁻¹ • (x - y))) := by
  rw [← value_hamiltonian_eq_variationalValue hH hconv hg ht,
    value_eq_inf_footpoints (hamiltonian H) g (ne_of_gt ht)]

/-- A convex superlinear Hamiltonian and Lipschitz datum admit a straight
path attaining the least integral action among all finite-action paths. -/
theorem exists_isMinOn_pathCost_hamiltonian {H g : E → ℝ}
    (hH : Superlinear H) (hconv : ConvexOn ℝ Set.univ H)
    {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} {x : E} (ht : 0 < t) :
    ∃ y : E, variationalValue (hamiltonian H) g t x =
        pathCost (hamiltonian H) g (straightPath (hamiltonian H) (x := x) ht y) ∧
      IsMinOn (pathCost (hamiltonian H) g : AdmissiblePath (hamiltonian H) t x → ℝ)
        Set.univ (straightPath (hamiltonian H) (x := x) ht y) := by
  have hcont : Continuous H := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  exact exists_isMinOn_pathCost_straightPath (convexOn_hamiltonian hH)
    (superlinear_hamiltonian hH hcont) hg ht

end HamiltonJacobi.HopfLax

end
