/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder

/-!
# The L² divergence of a first-order Sobolev flux

For a finite family of `H¹` fields, the sum of the matching weak
derivative coordinates is an `L²` divergence. Integration by parts
identifies its negative with the Dirichlet weak functional. No boundary
regularity or differential equation is needed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The negative weak divergence as an `L²` element. -/
def negativeDivergence (Q : Fin n → H¹(Ω)) : DerivLp n 2 Ω :=
  -∑ i, wkpCoordinateCLM (singleDerivIndex n i) (Q i)

/-- Integration by parts against every zero-boundary Sobolev test
fixes the sign of the negative divergence. -/
theorem negativeDivergence_pairing (Q : Fin n → H¹(Ω))
    (v : H¹₀(Ω)) :
    ⟪negativeDivergence Q, baseCoordCLM v⟫ =
      ∑ i, ⟪wkpBaseCoordinateCLM (Q i), derivCoordCLM i v⟫ := by
  classical
  rw [negativeDivergence, inner_neg_left, sum_inner, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  symm
  exact weakDerivative_integrationByParts_H10 i
    (wkpBaseCoordinateCLM (Q i)) (wkpCoordinateCLM (singleDerivIndex n i) (Q i))
    (by simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply,
      wkpCoordinateCLM_apply] using
      (Q i).property.hasWeakDerivativeOn_first (by norm_num) i) v

/-- The stored `L²` representative is the negative sum of the
weak derivative representatives, including the empty sum in dimension zero. -/
theorem negativeDivergence_ae (Q : Fin n → H¹(Ω)) :
    (negativeDivergence Q : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ -∑ i, wkpCoordinateCLM (singleDerivIndex n i) (Q i) x := by
  filter_upwards [Lp.coeFn_neg (∑ i, wkpCoordinateCLM (singleDerivIndex n i) (Q i)),
    Lp.coeFn_fun_finsetSum Finset.univ
      (fun i ↦ wkpCoordinateCLM (singleDerivIndex n i) (Q i))] with x hn hs
  exact hn.trans (congrArg Neg.neg hs)

end SobolevSpace.GraphSpace
