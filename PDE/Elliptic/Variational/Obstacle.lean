/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PoissonDirichlet
import PDE.Analysis.Variational.Inequality
import PDE.Elliptic.Semilinear.VariationalInequality

/-!
# The Dirichlet obstacle problem

The obstacle restricts the admissible functions to
`K = {u ∈ H¹₀(Ω) | ψ ≤ u almost everywhere}`. We prove that this set is closed
and convex, and minimize the Dirichlet energy on it. On a bounded domain of
positive dimension, every obstacle with an `H¹₀` majorant has a unique minimizer.
In particular, any nonpositive `L²` obstacle is admissible.

The minimizer satisfies `∫ f (v-u) ≤ ∫ ∇u · ∇(v-u)` for every `v ∈ K`.
This variational inequality also characterizes it uniquely. The obstacle needs
only to lie in `L²`; no boundary smoothness or pointwise representative is used.
For a fixed obstacle, `dirichletObstacle_solution_norm_sub_le` bounds the `H¹₀` distance
between two solutions by a constant times the `L²` distance between their loads. The
constant comes from Dirichlet coercivity of the domain and does not depend on the obstacle.

This is the existence and variational characterization of the obstacle problem
in Evans, *Partial Differential Equations*, second edition, §8.4.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The homogeneous Dirichlet functions lying above an `L²` obstacle almost
everywhere. The order on `Lp` makes this independent of representatives. -/
def dirichletObstacleSet (ψ : DerivLp n 2 Ω) : Set (H¹₀(Ω)) :=
  {u | ψ ≤ baseCoordCLM (n := n) (Ω := Ω) u}

/-- Membership in the obstacle class is the almost-everywhere obstacle
inequality for any representatives of the two `L²` functions. -/
theorem mem_dirichletObstacleSet_iff
    (ψ : DerivLp n 2 Ω) (u : H¹₀(Ω)) :
    u ∈ dirichletObstacleSet ψ ↔
      ∀ᵐ x ∂domainMeasure n Ω,
        ψ x ≤ (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) x :=
  (Lp.coeFn_le ψ (baseCoordCLM (n := n) (Ω := Ω) u)).symm

/-- The obstacle constraint is closed in the Sobolev norm, by continuity of
the inclusion into `L²` and Mathlib's closed order on `Lp`. -/
theorem isClosed_dirichletObstacleSet (ψ : DerivLp n 2 Ω) :
    IsClosed (dirichletObstacleSet ψ) :=
  isClosed_Ici.preimage (baseCoordCLM (n := n) (Ω := Ω)).continuous

/-- Convex combinations of admissible Sobolev functions remain above the
obstacle. No regularity of the obstacle beyond `L²` is needed. -/
theorem convex_dirichletObstacleSet (ψ : DerivLp n 2 Ω) :
    Convex ℝ (dirichletObstacleSet ψ) := by
  intro u hu v hv a b ha hb hab
  rw [mem_dirichletObstacleSet_iff] at hu hv ⊢
  let P := baseCoordCLM (n := n) (Ω := Ω)
  change ∀ᵐ x ∂domainMeasure n Ω, ψ x ≤ (P (a • u + b • v) : ℝ^n → ℝ) x
  rw [map_add, map_smul, map_smul]
  filter_upwards [hu, hv, Lp.coeFn_add (a • P u) (b • P v),
    Lp.coeFn_smul a (P u), Lp.coeFn_smul b (P v)] with x hx hy hadd hsmulU hsmulV
  rw [hadd, Pi.add_apply, hsmulU, hsmulV]
  change ψ x ≤ a * (P u : ℝ^n → ℝ) x + b * (P v : ℝ^n → ℝ) x
  calc
    ψ x = a * ψ x + b * ψ x := by rw [← add_mul, hab, one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)

/-- A nonpositive obstacle admits the zero Sobolev function. -/
theorem zero_mem_dirichletObstacleSet {ψ : DerivLp n 2 Ω} (hψ : ψ ≤ 0) :
    0 ∈ dirichletObstacleSet ψ := by
  change ψ ≤ baseCoordCLM (n := n) (Ω := Ω) 0
  simpa only [map_zero] using hψ

/-- On a bounded domain of positive dimension, an `L²` obstacle admitting
an `H¹₀` majorant has a unique Dirichlet-energy minimizer above it. -/
theorem existsUnique_dirichletObstacle_minimizer
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (ψ f : DerivLp n 2 Ω) (w : H¹₀(Ω))
    (hw : w ∈ dirichletObstacleSet ψ) :
    ∃! u, u ∈ dirichletObstacleSet ψ ∧
      IsMinOn (dirichletEnergy f) (dirichletObstacleSet ψ) u := by
  obtain ⟨c, hc, hcoercive⟩ := dirichletForm_isCoercive
    (n := n) (Ω := Ω) hn hΩbounded
  convert! @PDE.Elliptic.Semilinear.existsUnique_variationalEnergy_minimizerOn
      (H¹₀(Ω)) inferInstance inferInstance inferInstance
      (dirichletForm (n := n) (Ω := Ω)) (dirichletForm_symm (n := n) (Ω := Ω))
      c hc hcoercive (fun _ ↦ 0) (convexOn_const 0 convex_univ)
      continuous_const.lowerSemicontinuous 0 0 le_rfl (by simp)
      (loadFunctional (n := n) (Ω := Ω) f)
      (dirichletObstacleSet ψ)
      (convex_dirichletObstacleSet ψ) (isClosed_dirichletObstacleSet ψ) ⟨w, hw⟩ using 1
  all_goals simp only [isMinOn_iff, PDE.Elliptic.Semilinear.variationalEnergy, add_zero,
    dirichletEnergy, PDE.Analysis.Variational.energy]

/-- For an admissible function, minimizing the Dirichlet energy is equivalent
to the obstacle variational inequality. This direction does not need a
bounded domain or an existence theorem. -/
theorem isMinOn_dirichletEnergy_obstacle_iff
    (ψ f : DerivLp n 2 Ω) {u : H¹₀(Ω)}
    (hu : u ∈ dirichletObstacleSet ψ) :
    IsMinOn (dirichletEnergy f) (dirichletObstacleSet ψ) u ↔
      ∀ v ∈ dirichletObstacleSet ψ,
        loadFunctional f (v - u) ≤ dirichletForm u (v - u) := by
  convert! @PDE.Elliptic.Semilinear.isMinOn_variationalEnergy_iff
      (H¹₀(Ω)) inferInstance inferInstance
      (dirichletForm (n := n) (Ω := Ω)) (dirichletForm_symm (n := n) (Ω := Ω))
      (dirichletForm_self_nonneg (n := n) (Ω := Ω))
      (fun _ ↦ 0) (convexOn_const 0 convex_univ)
      (loadFunctional (n := n) (Ω := Ω) f)
      (dirichletObstacleSet ψ) (convex_dirichletObstacleSet ψ) u hu 0
      (hasFDerivAt_const (c := (0 : ℝ)) u) using 1
  all_goals simp only [isMinOn_iff, PDE.Elliptic.Semilinear.variationalEnergy, add_zero,
    dirichletEnergy, PDE.Analysis.Variational.energy, zero_apply]

/-- The obstacle variational inequality has exactly one admissible solution
whenever the obstacle has an `H¹₀` majorant. -/
theorem existsUnique_dirichletObstacle_solution
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (ψ f : DerivLp n 2 Ω) (w : H¹₀(Ω))
    (hw : w ∈ dirichletObstacleSet ψ) :
    ∃! u, u ∈ dirichletObstacleSet ψ ∧
      ∀ v ∈ dirichletObstacleSet ψ,
        loadFunctional f (v - u) ≤ dirichletForm u (v - u) := by
  obtain ⟨u, ⟨hu, hmin⟩, huniq⟩ :=
    existsUnique_dirichletObstacle_minimizer hn hΩbounded ψ f w hw
  refine ⟨u, ⟨hu, (isMinOn_dirichletEnergy_obstacle_iff ψ f hu).mp hmin⟩,
    fun v ⟨hv, hVI⟩ ↦ ?_⟩
  exact huniq v ⟨hv, (isMinOn_dirichletEnergy_obstacle_iff ψ f hv).mpr hVI⟩

/-- The obstacle solution depends Lipschitz-continuously on the `L²` load.
The constant depends only on the domain's Dirichlet coercivity bound; it is
uniform over all obstacles and all admissible solutions. -/
theorem dirichletObstacle_solution_norm_sub_le
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ f g : DerivLp n 2 Ω) (u v : H¹₀(Ω)),
      u ∈ dirichletObstacleSet ψ → v ∈ dirichletObstacleSet ψ →
      (∀ w ∈ dirichletObstacleSet ψ,
        loadFunctional f (w - u) ≤ dirichletForm u (w - u)) →
      (∀ w ∈ dirichletObstacleSet ψ,
        loadFunctional g (w - v) ≤ dirichletForm v (w - v)) →
      ‖u - v‖ ≤ C * ‖f - g‖ := by
  obtain ⟨c, hc, hcoercive⟩ := dirichletForm_isCoercive
    (n := n) (Ω := Ω) hn hΩbounded
  refine ⟨c⁻¹, inv_pos.mpr hc, fun ψ f g u v huK hvK hu hv ↦ ?_⟩
  have hmono : c * ‖u - v‖ * ‖u - v‖ ≤
      (dirichletForm u - dirichletForm v) (u - v) := by
    rw [← map_sub (dirichletForm (n := n) (Ω := Ω)) u v]
    exact hcoercive (u - v)
  have hnorm := @PDE.Analysis.Variational.norm_sub_le_of_variationalInequalities
    (H¹₀(Ω)) inferInstance inferInstance
    (dirichletForm (n := n) (Ω := Ω)) c hc (dirichletObstacleSet ψ) u v huK hvK hmono
    (loadFunctional f) (loadFunctional g) hu hv
  calc
    ‖u - v‖ ≤ ‖loadFunctional f - loadFunctional g‖ / c := hnorm
    _ = ‖loadFunctional (f - g)‖ / c := by rw [← loadFunctional_sub]
    _ ≤ ‖f - g‖ / c := div_le_div_of_nonneg_right (norm_loadFunctional_le _) hc.le
    _ = c⁻¹ * ‖f - g‖ := div_eq_inv_mul _ _

end SobolevSpace.GraphSpace
