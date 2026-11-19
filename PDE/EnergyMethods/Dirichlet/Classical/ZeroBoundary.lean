/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.ZeroBoundary
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure

/-!
# Dirichlet energy for classical zero boundary data

C² regularity up to the boundary makes the first and second partial derivatives
integrable. Integration by parts against a function vanishing on the frontier then
gives the energy identity on a bounded C¹ graph domain, without a compact support
assumption.

Both identities are Green's formula (ii) of Evans, Appendix C.2, Theorem 3, whose boundary term
vanishes for zero boundary values. Evans assumes both functions in `C²(Ū)`; in the first identity
the factor that vanishes on the boundary needs only one derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix C.2, Theorem 3 (Green's formulas), p. 712.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public noncomputable section

namespace PDE.EnergyMethods

open Set MeasureTheory SobolevSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- The bilinear Dirichlet identity when only the second factor vanishes on
the boundary. The first factor needs two classical derivatives, the second one. -/
theorem sum_integral_partialDeriv_mul_eq_neg_integral_laplacian_mul
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) {u v : ℝ^n → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hv : ContDiffUpToBoundary 1 v Ω)
    (hc : ContinuousOn v (closure Ω)) (hzero : ∀ x ∈ frontier Ω, v x = 0) :
    (∑ i : Fin n, ∫ x in Ω, (∂[i] u) x * (∂[i] v) x) =
      -(∫ x in Ω, laplacian u x * v x) := by
  have hi (i : Fin n) := integral_mul_partialDeriv_eq_neg_of_eq_zero_on_frontier
    hopen hbounded hgraph (hu.partialDeriv_of_succ hopen i) hv hc hzero i
  have hint (i : Fin n) : IntegrableOn
      (fun x ↦ (∂[i] (∂[i] u)) x * v x) Ω :=
    (((hu.partialDeriv_of_succ hopen i).partialDeriv_of_succ hopen i).mul
      (hv.of_le (Nat.zero_le 1)) hopen hbounded).integrableOn hopen hbounded
  simp only [hi, Finset.sum_neg_distrib, laplacian, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hint i)]

/-- The classical Dirichlet energy identity, including integrability, from C²
regularity up to the boundary and pointwise zero boundary values. -/
theorem integral_mul_laplacian_eq_neg_energy_of_zero_boundary
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) {u : ℝ^n → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hc : ContinuousOn u (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, u x = 0) :
    IntegrableOn (fun x ↦ u x * laplacian u x) Ω ∧
      IntegrableOn (fun x ↦ ‖∇ u x‖ ^ 2) Ω ∧
        (∫ x in Ω, u x * laplacian u x) = -(∫ x in Ω, ‖∇ u x‖ ^ 2) := by
  have hd (i : Fin n) : ContDiffUpToBoundary 1 (∂[i] u) Ω :=
    hu.partialDeriv_of_succ hopen i
  have hl (i : Fin n) : IntegrableOn
      (fun x ↦ u x * (∂[i] (∂[i] u)) x) Ω :=
    ((hu.of_le (show 0 ≤ 2 by omega)).mul ((hd i).partialDeriv_of_succ hopen i)
      hopen hbounded).integrableOn hopen hbounded
  have hs (i : Fin n) : IntegrableOn (fun x ↦ (∂[i] u) x ^ 2) Ω := by
    simpa only [pow_two] using
      ((hd i).mul (hd i) hopen hbounded).integrableOn hopen hbounded
  have hi (i : Fin n) :
      (∫ x in Ω, u x * (∂[i] (∂[i] u)) x) =
        -(∫ x in Ω, (∂[i] u) x ^ 2) := by
    have hibp := integral_mul_partialDeriv_eq_neg_of_eq_zero_on_frontier
      hopen hbounded hgraph (hd i) (hu.of_le (show 1 ≤ 2 by omega)) hc hzero i
    have hcomm : (∫ x in Ω, (∂[i] (∂[i] u)) x * u x) =
        ∫ x in Ω, u x * (∂[i] (∂[i] u)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact mul_comm _ _
    simp only [← pow_two, hcomm] at hibp
    linarith
  have hnorm (x : ℝ^n) : ‖∇ u x‖ ^ 2 = ∑ i : Fin n, (∂[i] u) x ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [gradient_apply_eq_partialDeriv]
  have hprod (x : ℝ^n) : u x * laplacian u x =
      ∑ i : Fin n, u x * (∂[i] (∂[i] u)) x := by
    simp only [laplacian, Finset.mul_sum]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [IntegrableOn, hprod] using integrable_finsetSum Finset.univ (fun i _ ↦ hl i)
  · simpa only [IntegrableOn, hnorm] using integrable_finsetSum Finset.univ (fun i _ ↦ hs i)
  · simp only [hprod, hnorm]
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hl i),
      integral_finsetSum Finset.univ (fun i _ ↦ hs i)]
    simp only [hi, Finset.sum_neg_distrib]

end PDE.EnergyMethods
