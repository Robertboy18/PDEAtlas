/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PoissonDirichlet
import PDE.CalculusOfVariations.SecondVariation

/-!
# Second variation of the Dirichlet energy

We specialize the abstract quadratic-energy calculus to the Dirichlet energy on
`H10SpaceOn`. The first variation is the weak Poisson equation, while the second variation is the
Dirichlet form and therefore the sum of the squared `L2` norms of the weak derivatives.

The statements are the Dirichlet-energy case of the Euler-Lagrange equation in Evans's §8.1.2
(Example 2 with `aⁱʲ = δᵢⱼ`) and of the second variation inequality (11) of §8.1.3. The
dependency points from elliptic theory to the abstract calculus-of-variations layer, not
conversely.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.2, the first variation (6)-(9) and Example 2
  (Generalized Dirichlet's principle), pp. 455-456; §8.1.3, the second variation (11), p. 458.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

open Filter Set
open PDE.Analysis.Variational
open SobolevSpace

namespace SobolevSpace.GraphSpace

open PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The first Fréchet derivative of the Dirichlet energy is the weak Poisson residual. -/
theorem dirichletEnergy_hasFDerivAt
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω)) :
    HasFDerivAt (dirichletEnergy (n := n) (Ω := Ω) f)
      (dirichletForm (n := n) (Ω := Ω) u -
        loadFunctional (n := n) (Ω := Ω) f) u := by
  unfold dirichletEnergy
  exact @quadraticEnergy_hasFDerivAt
    (H¹₀(Ω))
    inferInstance
    (Submodule.innerProductSpace
      ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule))
    (dirichletForm (n := n) (Ω := Ω))
    (dirichletForm_symm (n := n) (Ω := Ω))
    (loadFunctional (n := n) (Ω := Ω) f) u

/-- The second variation of the Dirichlet energy is its Dirichlet form. -/
theorem dirichletEnergy_secondVariation_eq
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω)) :
    fderiv ℝ
        (fun w ↦
          fderiv ℝ (dirichletEnergy (n := n) (Ω := Ω) f) w)
        u =
      dirichletForm (n := n) (Ω := Ω) := by
  unfold dirichletEnergy
  exact @quadraticEnergy_secondVariation_eq
    (H¹₀(Ω))
    inferInstance
    (Submodule.innerProductSpace
      ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule))
    (dirichletForm (n := n) (Ω := Ω))
    (dirichletForm_symm (n := n) (Ω := Ω))
    (loadFunctional (n := n) (Ω := Ω) f) u

/-- Evaluation of the Dirichlet second variation in two test directions. -/
theorem dirichletEnergy_secondVariation_apply
    (f : DerivLp n 2 Ω)
    (u v w : H¹₀(Ω)) :
    fderiv ℝ
          (fun z ↦
            fderiv ℝ (dirichletEnergy (n := n) (Ω := Ω) f) z)
          u v w =
      dirichletForm (n := n) (Ω := Ω) v w := by
  rw [dirichletEnergy_secondVariation_eq f u]

/-- The diagonal Dirichlet second variation is the sum of the squared weak-derivative norms. -/
theorem dirichletEnergy_secondVariation_self_eq
    (f : DerivLp n 2 Ω)
    (u v : H¹₀(Ω)) :
    fderiv ℝ
          (fun z ↦
            fderiv ℝ (dirichletEnergy (n := n) (Ω := Ω) f) z)
          u v v =
      ∑ i : Fin n,
        ‖derivCoordCLM (n := n) (Ω := Ω) i v‖ ^ 2 := by
  rw [dirichletEnergy_secondVariation_apply f u v v]
  exact dirichletForm_self_eq_sum_norm_sq (n := n) (Ω := Ω) v

/-- A local minimizer of the Dirichlet energy is a weak solution of the Poisson equation. -/
theorem dirichletEnergy_isWeakSolution_of_isLocalMin
    (f : DerivLp n 2 Ω)
    {u : H¹₀(Ω)}
    (hmin : IsLocalMin
      (dirichletEnergy (n := n) (Ω := Ω) f) u) :
    IsWeakSolution
      (dirichletForm (n := n) (Ω := Ω))
      (loadFunctional (n := n) (Ω := Ω) f) u := by
  unfold dirichletEnergy at hmin
  exact @quadraticEnergy_isWeakSolution_of_isLocalMin
    (H¹₀(Ω))
    inferInstance
    (Submodule.innerProductSpace
      ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule))
    (dirichletForm (n := n) (Ω := Ω))
    (dirichletForm_symm (n := n) (Ω := Ω))
    (loadFunctional (n := n) (Ω := Ω) f)
    u hmin

/-- The Dirichlet second variation is nonnegative in every direction. -/
theorem dirichletEnergy_secondVariation_nonneg
    (f : DerivLp n 2 Ω)
    (u v : H¹₀(Ω)) :
    0 ≤ fderiv ℝ
      (fun z ↦
        fderiv ℝ (dirichletEnergy (n := n) (Ω := Ω) f) z)
      u v v := by
  rw [dirichletEnergy_secondVariation_apply f u v v]
  exact dirichletForm_self_nonneg (n := n) (Ω := Ω) v

/-- Local minimizers of the Dirichlet energy are exactly weak solutions of the Poisson
equation. -/
theorem dirichletEnergy_isLocalMin_iff_isWeakSolution
    (f : DerivLp n 2 Ω)
    {u : H¹₀(Ω)} :
    IsLocalMin (dirichletEnergy (n := n) (Ω := Ω) f) u ↔
      IsWeakSolution
        (dirichletForm (n := n) (Ω := Ω))
        (loadFunctional (n := n) (Ω := Ω) f) u := by
  constructor
  · exact dirichletEnergy_isWeakSolution_of_isLocalMin f
  · intro hu
    -- The Dirichlet principle upgrades a weak solution to a global minimizer.
    have hglobal :
        ∀ v : H¹₀(Ω),
          dirichletEnergy (n := n) (Ω := Ω) f u ≤
            dirichletEnergy (n := n) (Ω := Ω) f v :=
      dirichletEnergy_minimal_of_weakSolution f hu
    exact
      (show IsMinOn
          (dirichletEnergy (n := n) (Ω := Ω) f)
          Set.univ u from fun _ _ ↦ hglobal _).isLocalMin Filter.univ_mem

end SobolevSpace.GraphSpace
