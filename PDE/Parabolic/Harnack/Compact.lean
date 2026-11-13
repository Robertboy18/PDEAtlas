/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.TerminalTime
public import PDE.Analysis.Geometry.BallChain.CompactTime

/-!
# Compact propagation of the parabolic Harnack estimate

The local estimate and the time-ordered interior-ball chain give a
uniform comparison on a compact interior set. Only the spatial second jets
and the first time derivative are prescribed. The later comparison time may
equal the terminal time.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Compact forward comparison from space-time derivatives and bounded
coefficients. The constant precedes the coefficients, the solution and its jets. -/
theorem exists_harnack_comparison_on_isCompact
    {U S : Set (ℝ^n)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    {ℓ T s t : ℝ} (hs : ℓ < s) (hst : s < t) (ht : t ≤ T)
    {α τ B K : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
        (c : ℝ^n → ℝ → ℝ),
        let D := U ×ˢ Ioo ℓ T
        ContinuousOn (Function.uncurry a) D →
        (∀ p ∈ D, (a p.1 p.2).PosSemidef) →
        (∀ p ∈ D, ∀ w : ℝ^n,
          α * ‖w‖ ^ 2 ≤ ⟪w, (a p.1 p.2).toEuclideanLin w⟫) →
        (∀ p ∈ D, (a p.1 p.2).trace ≤ τ) →
        (∀ p ∈ D, ‖d p.1 p.2‖ ≤ B) →
        (∀ p ∈ D, |c p.1 p.2| ≤ K) →
        ∀ (u : ℝ^n → ℝ → ℝ)
          (Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ) (Dt : ℝ^n × ℝ → ℝ)
          (Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ),
          ContinuousOn (Function.uncurry u) (U ×ˢ Ioc ℓ T) →
          ContinuousOn Dx D → ContinuousOn Dt D → ContinuousOn Dxx D →
          (∀ p ∈ D, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1) →
          (∀ p ∈ D, HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1) →
          (∀ p ∈ D, HasDerivAt (u p.1) (Dt p) p.2) →
          (∀ p ∈ U ×ˢ Ioc ℓ T, 0 ≤ u p.1 p.2) →
          (∀ p ∈ D, matrixParabolicOperator a d c u p.1 p.2 = 0) →
          ∀ x ∈ S, ∀ y ∈ S, u x s ≤ C * u y t := by
  obtain ⟨A, hA, hlocal⟩ :=
    exists_forward_comparison_of_space_time_derivatives (n := n) hα hτ hB hK
  obtain ⟨C, hC, hchain⟩ := exists_forward_comparison_constant_of_ballChain
    hU hconn hS hSU (L := 13) (ρ := 1) (κ := 129 / 2) (A := A)
    (by norm_num) zero_lt_one (by norm_num) hA hs hst ht
  refine ⟨C, hC, ?_⟩
  intro a d c D hacont ha hell htrace hdrift hpotential u Dx Dt Dxx
    hu hDx hDt hDxx hd hdd htime hnonneg hsol
  apply hchain u hnonneg
  intro x y r v hr hr₁ hball hxy hstart hend
  exact hlocal a d c U ℓ T hacont ha hell htrace hdrift hpotential
    u Dx Dt Dxx hu hDx hDt hDxx hd hdd htime
    (fun p hp ↦ hnonneg p ⟨hp.1, hp.2.1, hp.2.2.le⟩) hsol
    x y r v hr hr₁ (ball_subset_closedBall.trans hball) hxy hstart hend

end ParabolicHarnack
