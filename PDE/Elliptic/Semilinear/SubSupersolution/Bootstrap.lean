/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.SubSupersolution.Regularity
public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.Domain

/-!
# All-order regularity of bounded semilinear weak solutions

The essential bound on a weak solution makes smooth composition preserve each
positive Sobolev order, independently of dimension. The full elliptic estimate
then gains two derivatives. Iteration keeps the original weak solution fixed:
every Sobolev representative has the same order-zero coordinate.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Semilinear

open SobolevSpace SobolevSpace.GraphSpace
open MeasureTheory Set BoundaryRegularity
open scoped ENNReal Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}

/-- A bounded weak solution of a smooth semilinear equation has Sobolev
representatives of every finite order. Smoothness of the reaction is needed
only on an open neighborhood of its essential value range. The solution's
higher regularity is entirely a conclusion. -/
theorem exists_allOrderSobolevRepresentatives_of_bounded_semilinear_solution
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ) (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (ha : ∀ k i j, ContDiffUpToBoundary k (fun x ↦ a x i j) Ω)
    (hb : ∀ k i, ContDiffUpToBoundary k (b i) Ω)
    (hc : ∀ k, ContDiffUpToBoundary k c Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha)
    {f : ℝ → ℝ} {left right : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hinterval : Icc left right ⊆ s)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s)
    (u : H¹₀(Ω))
    (hrange : ∀ᵐ x ∂domainMeasure n Ω, baseCoordCLM u x ∈ Icc left right)
    (hu : ∀ v : H¹₀(Ω), interiorFullDivergenceOperator
      (fun i j ↦ (ha 0 i j).toLp hopen hbounded ∞)
      (fun i ↦ (hb 0 i).toLp hopen hbounded ∞) ((hc 0).toLp hopen hbounded ∞)
      (u : H¹(Ω)) v =
        ∫ x, f (baseCoordCLM u x) * baseCoordCLM v x ∂domainMeasure n Ω) :
    ∀ k, ∃ W : W^{k,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ) := by
  have hpositive : ∀ k, ∃ W : W^{k + 1,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ) := by
    intro k
    induction k with
    | zero => exact ⟨u.val, Filter.EventuallyEq.rfl⟩
    | succ k ih =>
      obtain ⟨U, hU⟩ := ih
      obtain ⟨F, hF⟩ :=
        Composition.exists_hk_composition_on_domain_of_contDiffOn (Nat.succ_pos k)
          hopen hbounded (hgraph (k + 1)) hs hinterval hf U (by
            filter_upwards [hU, hrange] with x hx hr
            exact hx ▸ hr)
      have hforce : baseRepresentative F =ᵐ[domainMeasure n Ω]
          fun x ↦ f (baseCoordCLM u x) := by
        filter_upwards [hF, hU] with x hx hy
        exact hx.trans (congrArg f hy)
      have hweak := isWeakShiftedFullDivergenceSolution_of_reaction_eq hopen
        (fun i j ↦ (ha 0 i j).toLp hopen hbounded ∞)
        (fun i ↦ (hb 0 i).toLp hopen hbounded ∞) ((hc 0).toLp hopen hbounded ∞)
        f u (wkpBaseCoordinateCLM F) hforce hu
      obtain ⟨_, _, hreg⟩ :=
        exists_global_higherOrder_estimate_of_contDiffUpToBoundary (k + 1)
          hopen hbounded (hgraph (k + 1 + 2)) a b c
          (ha (k + 1 + 1)) (hb (k + 1 + 1)) (hc (k + 1 + 1))
          0 alpha halpha hell
      obtain ⟨W, hW, _⟩ := hreg F u (by
        simpa only [ContDiffUpToBoundary.toLp] using hweak)
      refine ⟨lowerOrderCLM (by omega : k + 1 + 1 ≤ k + 1 + 2) W, ?_⟩
      rw [baseRepresentative_lowerOrderCLM]
      change (wkpBaseCoordinateCLM W : ℝ^n → ℝ) =ᵐ[_] _
      rw [hW]
  intro k
  obtain ⟨W, hW⟩ := hpositive k
  refine ⟨lowerOrderCLM (Nat.le_succ k) W, ?_⟩
  rw [baseRepresentative_lowerOrderCLM]
  exact hW

end PDE.Elliptic.Semilinear
