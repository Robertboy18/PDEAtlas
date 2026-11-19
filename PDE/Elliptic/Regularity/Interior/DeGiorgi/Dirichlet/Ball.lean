/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Dirichlet.Boundedness
import PDE.Elliptic.Regularity.Interior.DeGiorgi.BallGeometry
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Dirichlet
import PDE.Elliptic.Regularity.Interior.DeGiorgi.Rescaling.Forcing

/-!
# The quadratic-radius bound for the Dirichlet correction

On every ball of radius `R`, a zero-boundary solution of `-div(A Du) = f`
satisfies `‖u‖∞ ≤ C R² ‖f‖∞`. The constant is uniform in the centre, radius,
measurable coefficient matrix and solution. It depends only on the dimension,
ellipticity lower bound and the chosen Sobolev exponent.

The unit-ball Stampacchia estimate, preservation of zero trace under affine
pullback and transport of the scalar load derive the radius factor.
This is the decaying error needed to apply De Giorgi's homogeneous oscillation
estimate to an equation with bounded forcing.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev ENNReal NNReal

namespace SobolevSpace.GraphSpace

open Approximation.UpToBoundary MeanScaling

variable {n : ℕ} [Fact (0 < n)]

/-- The scalar Dirichlet solution on a ball has a bound proportional
to the square of the radius and the essential bound of the forcing. -/
theorem exists_norm_le_radius_sq_of_bounded_dirichlet_load
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (z : ℝ^n) (R : ℝ), 0 < R →
      ∀ a : Fin n → Fin n → DerivLp n ∞ (ball z R), AEUniformlyElliptic a α →
      ∀ (f : DerivLp n 2 (ball z R)) (u : H¹₀(ball z R)),
        IsWeakDivergenceSolution a f u →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂domainMeasure n (ball z R), ‖f x‖ ≤ M) →
        ∀ᵐ x ∂domainMeasure n (ball z R), ‖baseCoordCLM u x‖ ≤ K * R ^ 2 * M := by
  classical
  obtain ⟨atlas⟩ := Boundary.nonempty_c1ExtensionAtlas_ball (0 : ℝ^n) zero_lt_one
  let := atlas
  obtain ⟨P⟩ := exists_inwardPartition isOpen_ball isBounded_ball
    (Boundary.hasC1Boundary_of_local_graph
      ((Boundary.hasContDiffGraphBoundary_ball (0 : ℝ^n) zero_lt_one).hasC1GraphBoundary
        le_rfl))
  obtain ⟨K, hK, hbound⟩ :=
    exists_norm_le_of_bounded_dirichlet_load P isBounded_ball hq2 hq hα
  refine ⟨K, hK, ?_⟩
  intro z R hR a ha f u hu M hM hf
  let Λ := ∑ i, ∑ j, ‖a i j‖
  have hΛ (i j : Fin n) : ‖a i j‖ ≤ Λ :=
    (Finset.single_le_sum (f := fun j ↦ ‖a i j‖)
      (fun j _ ↦ norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i ↦ ∑ j, ‖a i j‖)
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ norm_nonneg _) (Finset.mem_univ i))
  have hcoeff := exists_scaledBallCoefficientPullback (α := α) (Λ := Λ) z hR 1
  rw [mul_one] at hcoeff
  obtain ⟨b, hb, _, hbRep⟩ := hcoeff a ha hΛ
  have hstate := exists_scaledBallDirichletPullback z hR 1
  rw [mul_one] at hstate
  obtain ⟨v, hvRep, hvD⟩ := hstate u
  have hload := exists_scaledBallLoadPullback (M := M) z hR 1
  rw [mul_one] at hload
  obtain ⟨g, hgRep, hgBound⟩ := hload f hf
  have htransport := isInteriorWeakDivergenceSolution_of_scaledBall_forcing z hR 1
  rw [mul_one] at htransport
  have hv := htransport a f (u : H¹(ball z R)) hu.toInterior b g
    (v : H¹(ball (0 : ℝ^n) 1)) hbRep hgRep hvD
  have hvWeak : IsWeakDivergenceSolution b g v := by
    apply (isWeakSolution_iff_isWeakDivergenceSolution isOpen_ball b g v).mp
    intro w
    have hh := hv.equation w
    change interiorVariableCoeffForm _ (h10SubtypeL v) w = _ at hh
    rwa [interiorVariableCoeffForm_h10SubtypeL] at hh
  have hvBound := hbound b hb g v hvWeak (R ^ 2 * M)
    (mul_nonneg (sq_nonneg R) hM) hgBound
  have hae := ae_comp_ballHomeomorph_iff z hR 1
    (fun x ↦ ‖baseCoordCLM u x‖ ≤ K * R ^ 2 * M)
  simp only [mul_one] at hae
  apply hae.mp
  filter_upwards [hvRep, hvBound] with y hy hb
  rw [hy] at hb
  simpa only [mul_assoc] using hb

end SobolevSpace.GraphSpace
