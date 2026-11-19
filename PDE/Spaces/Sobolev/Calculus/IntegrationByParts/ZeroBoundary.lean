/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ClassicalZero
public import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
public import PDE.FDeriv.Operators

/-!
# Classical integration by parts with zero boundary values

The boundary condition is converted to membership in the closure-defined `H¹₀`.
The weak derivative identity then extends from interior tests by density. In particular,
the classical factor need not have compact support inside the domain.
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace SobolevSpace

open MeasureTheory Set GraphSpace
open scoped InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a f : ℝ^n → ℝ}

/-- Integration by parts for raw classical closure data on a bounded C¹ graph domain,
when the second factor vanishes pointwise on the boundary. -/
theorem integral_mul_partialDeriv_eq_neg_of_eq_zero_on_frontier
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (ha : ContDiffUpToBoundary 1 a Ω) (hf : ContDiffUpToBoundary 1 f Ω)
    (hc : ContinuousOn f (closure Ω)) (hzero : ∀ x ∈ frontier Ω, f x = 0)
    (i : Fin n) :
    (∫ x in Ω, a x * (∂[i] f) x) =
      -(∫ x in Ω, (∂[i] a) x * f x) := by
  obtain ⟨U, hU, hdU⟩ :=
    hf.exists_H10_of_eq_zero_on_frontier hopen hbounded hgraph hc hzero
  let A := ha.toLp hopen hbounded 2
  let B := (ha.partialDeriv_of_succ hopen i).toLp hopen hbounded 2
  have hA : (A : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a :=
    ha.toLp_coeFn hopen hbounded 2
  have hB : (B : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] ∂[i] a :=
    (ha.partialDeriv_of_succ hopen i).toLp_coeFn hopen hbounded 2
  have hweak := (hasWeakDerivativeOn_of_contDiffAt_one hopen
    (fun x hx ↦ ha.contDiffOn.contDiffAt (hopen.mem_nhds hx)) i).congr_ae
      hA.symm hB.symm
  have hleft : ⟪A, derivCoordCLM i U⟫_ℝ =
      ∫ x in Ω, a x * (∂[i] f) x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hA, hdU i] with x hx hdx
    simp only [hx, hdx, RCLike.inner_apply, conj_trivial, mul_comm]
  have hright : ⟪B, baseCoordCLM U⟫_ℝ =
      ∫ x in Ω, (∂[i] a) x * f x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hB, hU] with x hx hux
    simp only [hx, hux, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [← hleft, ← hright]
  exact weakDerivative_integrationByParts_H10 i A B hweak U

/-- Green's energy pairing for one-sided classical closure jets. The second
factor has zero boundary values but need not be supported away from the boundary. -/
theorem integral_sum_partialDeriv_mul_eq_neg_laplacian
    {u v : ℝ^n → ℝ}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hu : ContDiffUpToBoundary 2 u Ω) (hv : ContDiffUpToBoundary 1 v Ω)
    (hc : ContinuousOn v (closure Ω)) (hzero : ∀ x ∈ frontier Ω, v x = 0) :
    (∫ x in Ω, ∑ i, (∂[i] u) x * (∂[i] v) x) =
      -(∫ x in Ω, laplacian u x * v x) := by
  have hleft (i : Fin n) : IntegrableOn
      (fun x ↦ (∂[i] u) x * (∂[i] v) x) Ω :=
    (hu.memLp_iteratedPartialDeriv hopen hbounded 2 [i] (by simp)).integrable_mul
      (hv.memLp_iteratedPartialDeriv hopen hbounded 2 [i] (by simp))
  have hright (i : Fin n) : IntegrableOn
      (fun x ↦ (∂[i] (∂[i] u)) x * v x) Ω :=
    (hu.memLp_iteratedPartialDeriv hopen hbounded 2 [i, i] (by simp)).integrable_mul
      (hv.memLp_iteratedPartialDeriv hopen hbounded 2 [] (by simp))
  rw [integral_finsetSum _ (fun i _ ↦ hleft i)]
  have heq : (∑ i, ∫ x in Ω, (∂[i] u) x * (∂[i] v) x) =
      ∑ i, -(∫ x in Ω, (∂[i] (∂[i] u)) x * v x) :=
    Finset.sum_congr rfl fun i _ ↦
      integral_mul_partialDeriv_eq_neg_of_eq_zero_on_frontier
        hopen hbounded hgraph (hu.partialDeriv_of_succ hopen i) hv hc hzero i
  rw [heq, Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum _ (fun i _ ↦ hright i)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by
    simp only [laplacian, Finset.sum_mul])

end SobolevSpace
