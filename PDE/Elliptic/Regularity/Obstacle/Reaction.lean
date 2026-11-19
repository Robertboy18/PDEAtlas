/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Obstacle
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Lattice
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian
import PDE.Elliptic.Regularity.Obstacle.Dual
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianH10

/-!
# The Lewy--Stampacchia reaction bound

For an `H²` obstacle with nonpositive boundary trace, the dual construction
produces a feasible obstacle solution. Testing with the positive part of
`ψ-u` proves feasibility, rather than assuming it. The reaction is bounded by
`(-Δψ-f)⁺`, is nonnegative, and vanishes above the obstacle.

The regularity assumption concerns the obstacle alone. At this stage the
solution belongs only to `H¹₀`; its `L²` Laplacian is a conclusion.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev Laplacian

namespace PDE.Elliptic.Obstacle

open SobolevSpace SobolevSpace.GraphSpace

open Boundary Approximation.UpToBoundary Boundary.Geometry.SurfaceMeasure

section Complementarity

variable {n : ℕ} {Ω : Set ℝ^n}

/-- A nonnegative reaction supported on contact gives the obstacle variational
inequality and hence minimizes the Dirichlet energy. -/
theorem isMinOn_dirichletEnergy_of_reaction
    (ψ f l : DerivLp n 2 Ω) (u : H¹₀(Ω))
    (hu : u ∈ dirichletObstacleSet ψ) (hl : 0 ≤ l)
    (heq : dirichletForm u = loadFunctional (f + l))
    (hcontact : ∀ᵐ x ∂domainMeasure n Ω, l x * (baseCoordCLM u x - ψ x) = 0) :
    IsMinOn (dirichletEnergy f) (dirichletObstacleSet ψ) u := by
  apply (isMinOn_dirichletEnergy_obstacle_iff ψ f hu).mpr
  intro v hv
  have hnonneg : 0 ≤ loadFunctional l (v - u) := by
    rw [loadFunctional_apply, L2.inner_def]
    apply integral_nonneg_of_ae
    have hb : (baseCoordCLM (v - u) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ baseCoordCLM v x - baseCoordCLM u x := by
      rw [map_sub]
      exact Lp.coeFn_sub _ _
    filter_upwards [(Lp.coeFn_nonneg l).mpr hl,
      (mem_dirichletObstacleSet_iff ψ v).mp hv, hcontact, hb] with x hlx hvx hx hb
    rw [hb, Real.inner_apply]
    change 0 ≤ l x * (baseCoordCLM v x - baseCoordCLM u x)
    have h := mul_nonneg hlx (sub_nonneg.mpr hvx)
    nlinarith
  rw [heq, loadFunctional_add, add_apply]
  exact le_add_of_nonneg_right hnonneg

end Complementarity

section Reaction

variable {m : ℕ} {Ω : Set ℝ^(m + 1)} [H : C1ExtensionAtlas (m + 1) Ω]

private theorem obstacle_le_of_saturated_reaction
    (P : InwardPartition Ω) (hbounded : Bornology.IsBounded Ω)
    (Ψ : W^{2,2}(Ω)) (f l : DerivLp (m + 1) 2 Ω) (u : H¹₀(Ω))
    (htrace : ∀ᵐ x ∂surfaceMeasure Ω,
      Trace.C1.trace (lowerOrderCLM (by norm_num : 1 ≤ 2) Ψ) x ≤ 0)
    (heq : dirichletForm u = loadFunctional (f + l))
    (hsat : ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      baseCoordCLM u x < wkpBaseCoordinateCLM Ψ x →
        l x = Lp.posPart (-(Δ Ψ) - f) x) :
    u ∈ dirichletObstacleSet (wkpBaseCoordinateCLM Ψ) := by
  let ψ := lowerOrderCLM (by norm_num : 1 ≤ 2) Ψ
  let w := ψ - (u : H¹(Ω))
  have htrace' : ∀ᵐ x ∂surfaceMeasure Ω,
      Trace.C1.trace ψ x ≤ Trace.C1.trace (u : H¹(Ω)) x := by
    rw [Trace.C1.trace_coe_H10_eq_zero]
    filter_upwards [htrace, Lp.coeFn_zero ℝ 2 (surfaceMeasure Ω)] with x hx hz
    exact hx.trans_eq hz.symm
  let t : H¹₀(Ω) :=
    ⟨lipschitzCompositionOn H.isOpen Lp.lipschitzWith_pos_part w,
      (Trace.C1.posPart_sub_mem_H10_iff_trace_le P ψ (u : H¹(Ω))).mpr htrace'⟩
  have hψ : wkpBaseCoordinateCLM ψ = wkpBaseCoordinateCLM Ψ := by
    apply Lp.ext
    exact Filter.Eventually.of_forall
      (congrFun (baseRepresentative_lowerOrderCLM (by norm_num : 1 ≤ 2) Ψ))
  have hw : (wkpBaseCoordinateCLM w : ℝ^(m + 1) → ℝ)
      =ᵐ[domainMeasure (m + 1) Ω]
        fun x ↦ wkpBaseCoordinateCLM Ψ x - baseCoordCLM u x := by
    change (wkpBaseCoordinateCLM (ψ - (u : H¹(Ω))) : ℝ^(m + 1) → ℝ) =ᵐ[_] _
    rw [map_sub, hψ]
    exact Lp.coeFn_sub _ _
  have htbase : (baseCoordCLM t : ℝ^(m + 1) → ℝ)
      =ᵐ[domainMeasure (m + 1) Ω]
        fun x ↦ max (wkpBaseCoordinateCLM Ψ x - baseCoordCLM u x) 0 :=
    (lipschitzCompositionOn_base_ae H.isOpen Lp.lipschitzWith_pos_part w).trans
      (hw.fun_comp (fun s : ℝ ↦ max s 0))
  have hloc (i : Fin (m + 1)) :
      inner ℝ (wkpCoordinateCLM (singleDerivIndex (m + 1) i) w) (derivCoordCLM i t) =
        inner ℝ (derivCoordCLM i t) (derivCoordCLM i t) := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    have hd := lipschitzCompositionOn_posPart_coordinate_ae w (singleDerivIndex (m + 1) i)
    filter_upwards [hd] with x hx
    change derivCoordCLM i t x =
      (if 0 < wkpBaseCoordinateCLM w x then
        wkpCoordinateCLM (singleDerivIndex (m + 1) i) w x else 0) at hx
    rw [hx]
    split_ifs <;> simp
  have henergy : dirichletForm t t =
      inner ℝ (-(Δ Ψ) - f - l) (baseCoordCLM t) := by
    rw [dirichletForm_apply]
    simp_rw [← hloc]
    simp only [w, map_sub, inner_sub_left, Finset.sum_sub_distrib]
    rw [sum_inner_gradient_eq_neg_inner_laplacian Ψ t]
    change -inner ℝ (Δ Ψ) (baseCoordCLM t) - dirichletForm u t = _
    rw [heq, loadFunctional_apply, inner_add_left]
    simp only [inner_neg_left]
    ring
  have hnonpos : dirichletForm t t ≤ 0 := by
    rw [henergy, L2.inner_def]
    apply integral_nonpos_of_ae
    filter_upwards [htbase, hsat, Lp.coeFn_sub (-(Δ Ψ) - f) l,
      Lp.coeFn_posPart (-(Δ Ψ) - f)] with x ht hs hd hp
    rw [Real.inner_apply, hd, Pi.sub_apply, ht]
    by_cases h : baseCoordCLM u x < wkpBaseCoordinateCLM Ψ x
    · rw [hs h, hp]
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_max_left _ _)) (le_max_right _ _)
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt h)), mul_zero]
      exact le_rfl
  have htzero : t = 0 := by
    obtain ⟨c, hc, hcoercive⟩ := dirichletForm_isCoercive (by omega) hbounded
    apply norm_eq_zero.mp
    have hnorm : ‖t‖ * ‖t‖ ≤ 0 := by
      apply le_of_mul_le_mul_left ?_ hc
      simpa only [mul_assoc, mul_zero] using (hcoercive t).trans hnonpos
    exact mul_self_eq_zero.mp (le_antisymm hnorm (mul_self_nonneg _))
  rw [mem_dirichletObstacleSet_iff]
  rw [htzero, map_zero] at htbase
  filter_upwards [htbase, Lp.coeFn_zero ℝ 2 (domainMeasure (m + 1) Ω)] with x ht hz
  rw [hz, Pi.zero_apply] at ht
  exact sub_nonpos.mp ((le_max_left _ _).trans_eq ht.symm)

/-- An `H²` obstacle with nonpositive trace has an obstacle minimizer whose
reaction is an `L²` function between zero and `(-Δψ-f)⁺`. Complementarity is
derived from minimization of the dual energy and the positive-part test. -/
theorem exists_dirichletObstacle_reaction
    (P : InwardPartition Ω) (hbounded : Bornology.IsBounded Ω)
    (Ψ : W^{2,2}(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (htrace : ∀ᵐ x ∂surfaceMeasure Ω,
      Trace.C1.trace (lowerOrderCLM (by norm_num : 1 ≤ 2) Ψ) x ≤ 0) :
    ∃ (u : H¹₀(Ω)) (l : DerivLp (m + 1) 2 Ω),
      u ∈ dirichletObstacleSet (wkpBaseCoordinateCLM Ψ) ∧
      IsMinOn (dirichletEnergy f) (dirichletObstacleSet (wkpBaseCoordinateCLM Ψ)) u ∧
      l ∈ Icc 0 (Lp.posPart (-(Δ Ψ) - f)) ∧
      dirichletForm u = loadFunctional (f + l) ∧
      (∀ᵐ x ∂domainMeasure (m + 1) Ω,
        l x * (baseCoordCLM u x - wkpBaseCoordinateCLM Ψ x) = 0) := by
  obtain ⟨l, u, hl, heq, hpoint⟩ :=
    exists_dirichletObstacle_dual_reaction (by omega) hbounded
      (wkpBaseCoordinateCLM Ψ) f (Lp.posPart (-(Δ Ψ) - f))
      ((Lp.coeFn_nonneg _).mp (Lp.posPart_nonneg_ae _))
  have hu := obstacle_le_of_saturated_reaction P hbounded Ψ f l u htrace heq
    (hpoint.mono fun _ hx ↦ hx.1)
  have hcontact : ∀ᵐ x ∂domainMeasure (m + 1) Ω,
      l x * (baseCoordCLM u x - wkpBaseCoordinateCLM Ψ x) = 0 := by
    filter_upwards [hpoint, (mem_dirichletObstacleSet_iff _ u).mp hu] with x hx hux
    rcases hux.eq_or_lt with h | h
    · rw [h, sub_self, mul_zero]
    · rw [hx.2 h, zero_mul]
  exact ⟨u, l, hu, isMinOn_dirichletEnergy_of_reaction _ f l u hu hl.1 heq hcontact,
    hl, heq, hcontact⟩

end Reaction

end PDE.Elliptic.Obstacle
