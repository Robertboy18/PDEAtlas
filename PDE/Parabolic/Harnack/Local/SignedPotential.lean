/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.Comparison
public import PDE.Parabolic.MaximumPrinciple.ExponentialExtension

/-!
# Local parabolic comparison with a signed potential

The exponential extension uses one additional spatial coordinate. The
original potential becomes a drift coefficient, whose uniform bound depends
only on the absolute potential bound. Restriction to the zero slice removes
the exponential factor from both sides of the local comparison.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis PDE.Common ParabolicMaximum EllipticHarnack Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The jointly C² local comparison for a bounded potential of either sign.
All constants precede the coefficients and the nonnegative solution. -/
theorem exists_local_signed_comparison_of_contDiff_two
    {α τ B K : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n)
        (c : ℝ^n → ℝ → ℝ),
        let Q := closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64
        (∀ v ∈ Q, (a v.1 v.2).PosSemidef) →
        (∀ v ∈ Q, ∀ w : ℝ^n,
          α * ‖w‖ ^ 2 ≤ ⟪w, (a v.1 v.2).toEuclideanLin w⟫) →
        (∀ v ∈ Q, (a v.1 v.2).trace ≤ τ) →
        (∀ v ∈ Q, ‖d v.1 v.2‖ ≤ B) →
        (∀ v ∈ Q, |c v.1 v.2| ≤ K) →
        ∀ u : ℝ^n → ℝ → ℝ,
          (∀ v ∈ Q, ContDiffAt ℝ 2 (Function.uncurry u) v) →
          (∀ v ∈ Q, 0 ≤ u v.1 v.2) →
          (∀ v ∈ Q, matrixParabolicOperator a d c u v.1 v.2 = 0) →
          ∀ x ∈ closedBall (0 : ℝ^n) (1 / 2), ∀ t ∈ Icc (-1 / 2) 0,
            ∀ y ∈ closedBall (0 : ℝ^n) 1, u x t ≤ C * u y 64 := by
  obtain ⟨C, hC, hcompare⟩ := exists_local_comparison_of_contDiff_two (n := n + 1)
    (α := min 1 α) (τ := 1 + τ) (B := B + 1 + K)
    (lt_min zero_lt_one hα) (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro a d c
  dsimp only
  intro ha hell htrace hdrift hpotential u hreg hnonneg hsol x hx t ht y hy
  have hmaps : MapsTo (fun p : ℝ^(n + 1) × ℝ ↦ (spatialPart p.1, p.2))
      (closedBall (0 : ℝ^(n + 1)) 12 ×ˢ Icc (-1) 64) (closedBall (0 : ℝ^n) 12 ×ˢ Icc (-1) 64) :=
    fun p hp ↦ ⟨mem_closedBall_zero_iff.2
      ((norm_spatialPart_le p.1).trans (mem_closedBall_zero_iff.1 hp.1)), hp.2⟩
  have hsmall (z : ℝ^n) (r : ℝ) (hz : z ∈ closedBall (0 : ℝ^n) r) :
      timeSpaceCons 0 z ∈ closedBall (0 : ℝ^(n + 1)) r := by
    simpa only [mem_closedBall, dist_zero_right, norm_timeSpaceCons_zero] using hz
  specialize hcompare (fun p s ↦ liftedPrincipal (fun z ↦ a z s) p)
    (fun p s ↦ liftedDrift (fun z ↦ d z s) (fun z ↦ c z s) p)
  dsimp only at hcompare
  specialize hcompare
    (fun p hp ↦ posSemidef_prependScalarBlock (d := 1) (A := a (spatialPart p.1) p.2)
      zero_le_one (ha (spatialPart p.1, p.2) (@hmaps p hp)))
    (fun p hp w ↦ elliptic_prependScalarBlock (d := 1) (α := α)
      (A := a (spatialPart p.1) p.2) (hell (spatialPart p.1, p.2) (@hmaps p hp)) w)
    (fun p hp ↦ by
      change (prependScalarBlock 1 (a (spatialPart p.1) p.2)).trace ≤ 1 + τ
      rw [trace_prependScalarBlock]
      exact add_le_add le_rfl (htrace (spatialPart p.1, p.2) (@hmaps p hp)))
    (fun p hp ↦ norm_liftedDrift_le (fun z ↦ d z p.2) (fun z ↦ c z p.2) p.1
      (hdrift (spatialPart p.1, p.2) (@hmaps p hp))
      (hpotential (spatialPart p.1, p.2) (@hmaps p hp)))
    (fun p s ↦ exponentialExtension (fun z ↦ u z s) p)
  specialize hcompare
    (fun p hp ↦ contDiffAt_exponentialExtension_uncurry (u := u) (p := p)
      (hreg (spatialPart p.1, p.2) (@hmaps p hp)))
    (fun p hp ↦ mul_nonneg (Real.exp_pos _).le (hnonneg (spatialPart p.1, p.2) (@hmaps p hp)))
    (fun p hp ↦ by
      have hu := hreg (spatialPart p.1, p.2) (@hmaps p hp)
      rw [matrixParabolicOperator_exponentialExtension a d c (u := u) (x := p.1) (t := p.2)
        (hu.comp (spatialPart p.1) (contDiffAt_id.prodMk contDiffAt_const))
        ((hu.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
          (by norm_num)),
        hsol (spatialPart p.1, p.2) (@hmaps p hp), mul_zero])
  have h := hcompare (timeSpaceCons 0 x) (hsmall x (1 / 2) hx) t ht
    (timeSpaceCons 0 y) (hsmall y 1 hy)
  simpa only [exponentialExtension_timeSpaceCons, Real.exp_zero, one_mul] using h

end ParabolicHarnack
