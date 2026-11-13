/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.WeakEquation

/-!
# Constant coefficient equations under affine rescaling

The Sobolev and coefficient pullbacks preserve a specified constant
matrix. Keeping their almost-everywhere identities also transports estimates
for the original weak derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace.MeanScaling

variable {n : ℕ}

/-- Rescale a constant coefficient weak solution, preserving the matrix,
ellipticity, coefficient bounds, and all first weak derivatives. -/
theorem exists_scaledBallWeakSolution_of_constant_representatives
    (z : ℝ^n) {s : ℝ} (hs : 0 < s) (r : ℝ)
    (A : Fin n → Fin n → DerivLp n ∞ (ball z (s * r)))
    (a : Fin n → Fin n → ℝ)
    (hrep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z (s * r))]
      fun _ ↦ a i j)
    {α Λ : ℝ} (hA : AEUniformlyElliptic A α) (hΛ : ∀ i j, ‖A i j‖ ≤ Λ)
    (u : H¹(ball z (s * r))) (hu : IsInteriorWeakDivergenceSolution A 0 u) :
    ∃ (B : Fin n → Fin n → DerivLp n ∞ (ball (0 : ℝ^n) r))
      (v : H¹(ball (0 : ℝ^n) r)),
      (∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)] fun _ ↦ a i j) ∧
      AEUniformlyElliptic B α ∧ (∀ i j, ‖B i j‖ ≤ Λ) ∧
      IsInteriorWeakDivergenceSolution B 0 v ∧
      (wkpBaseCoordinateCLM v : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 r)]
        (fun y ↦ wkpBaseCoordinateCLM u (ballHomeomorph z hs y)) ∧
      ∀ i, (wkpCoordinateCLM (singleDerivIndex n i) v : ℝ^n → ℝ)
        =ᵐ[domainMeasure n (ball 0 r)]
          fun y ↦ s * wkpCoordinateCLM (singleDerivIndex n i) u
            (ballHomeomorph z hs y) := by
  obtain ⟨v, hvbase, hv⟩ := exists_scaledBallSobolevPullback z hs r u
  obtain ⟨B, hB, hBΛ, hb⟩ := exists_scaledBallCoefficientPullback z hs r A hA hΛ
  refine ⟨B, v, ?_, hB, hBΛ,
    isInteriorWeakDivergenceSolution_of_scaledBall_representatives z hs r A u hu B v hb hv,
    hvbase, hv⟩
  intro i j
  exact (hb i j).trans ((ae_comp_ballHomeomorph_iff z hs r
    (fun x ↦ A i j x = a i j)).mpr (hrep i j))

end SobolevSpace.GraphSpace.MeanScaling
