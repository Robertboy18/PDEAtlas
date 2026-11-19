/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Constraints.Integral
public import PDE.Elliptic.Variational.PoissonDirichlet
public import PDE.CalculusOfVariations.DirectMethod.CompactConstraint
import PDE.CalculusOfVariations.WeakLowerSemicontinuity
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension

/-!
# Dirichlet minimizers under nonlinear integral constraints

Rellich compactness makes the nonlinear constraint continuous on a bounded
weak energy sublevel. Poincaré bounds that sublevel and convexity of the
Dirichlet energy gives weak lower semicontinuity. Consequently every nonempty
level constraint for a potential with linearly growing derivative admits a
minimizer. The domain is bounded and open, of positive dimension; the
supported-core definition of `H¹₀` needs no boundary regularity or connectedness.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis.Variational PDE.CalculusOfVariations

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "dΩ" => domainMeasure n Ω

/-- The unforced Dirichlet energy is one half of the squared gradient norm. -/
theorem dirichletEnergy_zero_eq_norm_gradient_sq (u : H¹₀(Ω)) :
    dirichletEnergy (n := n) (Ω := Ω) 0 u =
      (1 / 2 : ℝ) * ‖∇ (u : H¹(Ω))‖ ^ 2 := by
  simp only [dirichletEnergy, energy, loadFunctional_zero, zero_apply, sub_zero,
    dirichletForm_self_eq_sum_norm_sq]
  exact congrArg ((1 / 2 : ℝ) * ·) (norm_gradientCLM_sq_eq_sum_deriv_sq u).symm

/-- The energy minimized here is the integral of the squared weak
gradient, with the usual factor of one half. -/
theorem dirichletEnergy_zero_eq_integral_norm_sq (u : H¹₀(Ω)) :
    dirichletEnergy (n := n) (Ω := Ω) 0 u =
      (1 / 2 : ℝ) * ∫ x, ‖∇ (u : H¹(Ω)) x‖ ^ 2 ∂dΩ := by
  simp only [dirichletEnergy, energy, loadFunctional_zero, zero_apply, sub_zero,
    dirichletForm_eq_integral_gradient, real_inner_self_eq_norm_sq]

/-- The Dirichlet energy is weakly lower semicontinuous on the zero-boundary
space, independently of the nonlinear constraint. -/
theorem lowerSemicontinuous_weak_dirichletEnergy_zero :
    LowerSemicontinuous (fun w : WeakSpace ℝ H¹₀(Ω) ↦
      dirichletEnergy (n := n) (Ω := Ω) 0 ((toWeakSpace ℝ H¹₀(Ω)).symm w)) := by
  have hnorm : ConvexOn ℝ univ (fun u : H¹₀(Ω) ↦ ‖∇ (u : H¹(Ω))‖) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
    simpa only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul] using
      (convexOn_univ_norm (E := Lp (ℝ^n) 2 dΩ)).2
        (mem_univ (∇ (x : H¹(Ω)))) (mem_univ (∇ (y : H¹(Ω)))) ha hb hab
  have heq : dirichletEnergy (n := n) (Ω := Ω) 0 =
      fun u : H¹₀(Ω) ↦ (1 / 2 : ℝ) * ‖∇ (u : H¹(Ω))‖ ^ 2 :=
    funext dirichletEnergy_zero_eq_norm_gradient_sq
  have hconv : ConvexOn ℝ univ (dirichletEnergy (n := n) (Ω := Ω) 0) := by
    rw [heq]
    exact (hnorm.pow (fun _ _ ↦ norm_nonneg _) 2).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply lowerSemicontinuous_weakSpace_of_convex _ hconv
  have hc : Continuous (dirichletEnergy (n := n) (Ω := Ω) 0) := by
    rw [heq]
    exact continuous_const.mul ((gradientCLM (n := n) (Ω := Ω)).continuous.norm.pow 2)
  exact hc.lowerSemicontinuous

/-- Poincaré bounds every unforced Dirichlet energy sublevel in the full `H¹₀` norm. -/
theorem isBounded_sublevel_dirichletEnergy_zero
    (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) (R : ℝ) :
    Bornology.IsBounded {u : H¹₀(Ω) | dirichletEnergy 0 u ≤ R} := by
  obtain ⟨c, hc, hbound⟩ := dirichletForm_isCoercive hn hΩ
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max 1 (2 * R / c), ?_⟩
  intro u hu
  have henergy : dirichletForm u u ≤ 2 * R := by
    change energy dirichletForm (loadFunctional 0) u ≤ R at hu
    simp only [energy, loadFunctional_zero, zero_apply, sub_zero] at hu
    linarith
  by_cases hu1 : ‖u‖ ≤ 1
  · exact hu1.trans (le_max_left _ _)
  · have hnorm : c * ‖u‖ ≤ c * ‖u‖ * ‖u‖ := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (le_of_not_ge hu1) (mul_nonneg hc.le (norm_nonneg u))
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hc).mpr
    nlinarith [hbound u]

/-- A nonempty nonlinear integral level constraint admits a Dirichlet
energy minimizer. Its density and derivative may have arbitrary values at zero;
the derivative need only have linear growth. -/
theorem exists_isMinOn_dirichletEnergy_integralConstraint
    (hn : 0 < n) (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    {G g : ℝ → ℝ} {C : ℝ}
    (hd : ∀ s, HasDerivAt G (g s) s)
    (hg : ∀ s, |g s| ≤ C * (1 + |s|)) {a : ℝ}
    (hne : {u : H¹₀(Ω) | integralConstraint G u = a}.Nonempty) :
    ∃ u : H¹₀(Ω), integralConstraint G u = a ∧
      IsMinOn (dirichletEnergy 0) {v | integralConstraint G v = a} u := by
  let : IsFiniteMeasure (domainMeasure n Ω) :=
    ⟨by simpa [domainMeasure] using hΩbounded.measure_lt_top (μ := volume)⟩
  obtain ⟨u₀, hu₀⟩ := hne
  have hcompact : IsCompactOperator (baseCoordCLM (n := n) (Ω := Ω)) :=
    baseCoordCLM.isCompactOperator_of_bounded hΩopen.measurableSet hΩbounded
  have hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H¹₀(Ω)) :=
    @PDE.Analysis.inclusionInDoubleDual_surjective H¹₀(Ω)
      inferInstance inferInstance inferInstance
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_of_compact_constraint
      (E := H¹₀(Ω)) (H := Lp ℝ 2 dΩ) (Y := ℝ)
      hreflexive
      (baseCoordCLM (n := n) (Ω := Ω))
      hcompact
      (fun w : Lp ℝ 2 dΩ ↦ ∫ x, G (w x) ∂dΩ)
      (continuous_integral_L2_of_deriv_growth
        (by simpa using (abs_nonneg (g 0)).trans (hg 0)) hd hg)
      (C := {a}) isClosed_singleton
      (dirichletEnergy (n := n) (Ω := Ω) 0)
      lowerSemicontinuous_weak_dirichletEnergy_zero
      (x₀ := u₀) (show (∫ x, G (baseCoordCLM u₀ x) ∂dΩ) ∈ ({a} : Set ℝ) from hu₀)
      (isBounded_sublevel_dirichletEnergy_zero hn hΩbounded _)
  exact ⟨u, hu, hmin⟩

end SobolevSpace.GraphSpace
