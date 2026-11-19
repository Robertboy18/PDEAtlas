/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PoissonDirichlet
import PDE.Analysis.MeasureTheory.Lp.RealL2.OrderInterval
import PDE.Analysis.Variational.Inequality.Existence

/-!
# Construction of a bounded obstacle reaction

Minimize the quadratic energy of the inverse Dirichlet Laplacian over
`0 ≤ λ ≤ g`. Its first variation is the gap between the corresponding Poisson
solution and the obstacle. The pointwise normal cone identifies the reaction
on both strict sides of the obstacle. A subsequent truncation argument rules
out the lower side for the Lewy--Stampacchia choice of `g`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev

namespace PDE.Elliptic.Obstacle

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set ℝ^n}

/-- The dual obstacle problem has a bounded `L²` reaction. Its Poisson solution
saturates the upper reaction bound below the obstacle, and has zero reaction
above it. No Sobolev regularity of the obstacle is needed at this stage. -/
theorem exists_dirichletObstacle_dual_reaction
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω)
    (ψ f g : DerivLp n 2 Ω) (hg : 0 ≤ g) :
    ∃ (l : DerivLp n 2 Ω) (u : H¹₀(Ω)),
      l ∈ Icc 0 g ∧ dirichletForm u = loadFunctional (f + l) ∧
      (∀ᵐ x ∂domainMeasure n Ω,
        (baseCoordCLM u x < ψ x → l x = g x) ∧
        (ψ x < baseCoordCLM u x → l x = 0)) := by
  let S := dirichletSolveCLM (n := n) (Ω := Ω) hn hbounded
  let T := (baseCoordCLM (n := n) (Ω := Ω)).comp S
  let B : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω →L[ℝ] ℝ := (innerSL ℝ).comp T
  have hB (a b : DerivLp n 2 Ω) : B a b = dirichletForm (S a) (S b) := by
    change inner ℝ (baseCoordCLM (S a)) b = dirichletForm (S a) (S b)
    rw [real_inner_comm]
    exact ((dirichletSolve.isWeakSolution hn hbounded b) (S a)).symm.trans
      (dirichletForm_symm (S b) (S a))
  have hsymm (a b : DerivLp n 2 Ω) : B a b = B b a := by
    rw [hB, hB, dirichletForm_symm]
  have hpos (a : DerivLp n 2 Ω) : 0 ≤ B a a := by
    rw [hB]
    exact dirichletForm_self_nonneg _
  obtain ⟨l, hl, hvi⟩ :=
    PDE.Analysis.Variational.exists_variationalInequality_of_isBounded
      B hsymm hpos (innerSL ℝ (ψ - T f))
      (L2.convex_Icc 0 g) isClosed_Icc (L2.isBounded_Icc_zero g) ⟨0, le_rfl, hg⟩
  let u := S (f + l)
  have hnormal : ∀ v ∈ Icc 0 g,
      0 ≤ inner ℝ (baseCoordCLM u - ψ) (v - l) := by
    intro v hv
    have h := hvi v hv
    change inner ℝ (ψ - T f) (v - l) ≤ inner ℝ (T l) (v - l) at h
    change 0 ≤ inner ℝ (T (f + l) - ψ) (v - l)
    rw [map_add, inner_sub_left, inner_add_left]
    rw [inner_sub_left] at h
    linarith
  refine ⟨l, u, hl, ?_, ?_⟩
  · ext v
    exact dirichletSolve.isWeakSolution hn hbounded (f + l) v
  · have hpoint := L2.ae_eq_endpoints_of_box_variationalInequality
      g l (baseCoordCLM u - ψ) hl hnormal
    filter_upwards [hpoint, Lp.coeFn_sub (baseCoordCLM u) ψ] with x hx hd
    rw [hd, Pi.sub_apply] at hx
    exact ⟨fun h ↦ hx.1 (sub_neg.mpr h), fun h ↦ hx.2 (sub_pos.mpr h)⟩

end PDE.Elliptic.Obstacle
