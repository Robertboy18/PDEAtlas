/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Nondivergence
public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixEigenfunction

/-!
# Strict positivity for smooth full loads

Coefficient regularity provides the continuous principal trace and effective
drift and the upper bound on the potential required by the matrix strong maximum
principle. This local positivity statement imposes no sign on the potential.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open Set

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A nonnegative classical supersolution for the full load, positive at
one interior point, is positive on a connected domain. -/
theorem pos_of_nonneg_of_classicalLoad_nonneg
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsPreconnected Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    {u : ℝ^n → ℝ} (hreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hload : ∀ x ∈ Ω, 0 ≤ P.classicalLoad u x)
    (hu : ∀ x ∈ Ω, 0 ≤ u x) (hpos : ∃ x ∈ Ω, 0 < u x) :
    ∀ x ∈ Ω, 0 < u x := by
  have htrace : ContinuousOn (fun x ↦ ∑ i : Fin n, P.principal x i i) Ω :=
    continuousOn_finsetSum Finset.univ
      (fun i _ ↦ (P.principal_smooth 0 i i).contDiffOn.continuousOn)
  have hdrift : ContinuousOn P.nondivergenceDrift Ω :=
    (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp_continuousOn
      (continuousOn_pi.mpr
        (fun i ↦ (P.nondivergenceDrift_regular hopen 0 i).contDiffOn.continuousOn))
  have hell' (x : ℝ^n) (hx : x ∈ Ω) (v : ℝ^n) :
      alpha * ‖v‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, P.principal x i j * v i * v j := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [principalEnergy, dotProduct, pow_two] using hell x hx (fun j ↦ v j)
  obtain ⟨C, _, hC⟩ := (P.potential_smooth 0).exists_derivative_bound hbounded [] (by simp)
  apply EllipticMaximum.pos_of_nonneg_of_matrix_supersolution hopen hconn
    (fun x ↦ Matrix.of (P.principal x)) P.nondivergenceDrift htrace hdrift halpha hell'
    P.potential (fun x hx ↦ (le_abs_self _).trans (hC x hx)) hreg ?_ hu hpos
  intro x hx
  exact (hload x hx).trans_eq (P.classicalLoad_eq_matrixOperator hopen hx (hreg x hx))

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
