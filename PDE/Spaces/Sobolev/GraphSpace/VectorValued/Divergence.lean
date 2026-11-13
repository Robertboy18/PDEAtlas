/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Notation.Divergence
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Components
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Derivatives

/-!
# Divergence of Sobolev vector fields

For a vector field in `W^{k+1,p}(Ω; ℝ^n)`, the divergence belongs to
`W^{k,p}(Ω)`. It is the sum of the diagonal weak derivatives, built from the
derivative and codomain maps. The shared notation `∇· u` gives this
scalar Sobolev function directly from the input type.

The construction works on every open domain, including both normed exponent
endpoints. No boundary condition is imposed.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n m k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}

/-- The sum of the diagonal weak partial derivatives, as a scalar Sobolev function. -/
def divergenceCLM : W^{k + 1,p}(Ω; ℝ^n) →L[ℝ] W^{k,p}(Ω) :=
  ∑ i : Fin n, (componentCLM i).comp (partialDerivCLM i)

/-- The shared divergence notation returns a scalar Sobolev function for this input. -/
instance instDivergence : PDE.Divergence (W^{k + 1,p}(Ω; ℝ^n)) (W^{k,p}(Ω)) where
  divergence u := divergenceCLM u

/-- The divergence is the sum of the diagonal partial derivatives. -/
theorem divergence_eq_sum (u : W^{k + 1,p}(Ω; ℝ^n)) :
    ∇· u = ∑ i : Fin n, componentCLM i (∂[i] u) := by
  simp only [divergenceCLM, sum_apply, ContinuousLinearMap.comp_apply]

/-- Each derivative of the divergence is the sum of the corresponding diagonal rows. -/
theorem divergence_coordinate_ae (u : W^{k + 1,p}(Ω; ℝ^n)) (a : DerivIndex n k) :
    ((∇· u).val a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
      ∑ i : Fin n, u.val (derivativeWordIndex [i] (by simp [Nat.add_comm]) a) x i := by
  change (wkpCoordinateCLM a (∇· u) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] _
  rw [divergence_eq_sum, map_sum]
  have hcomponent := ae_all_iff.mpr fun i : Fin n ↦
    componentCLM_apply_ae i (∂[i] u) a
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : Fin n ↦ wkpCoordinateCLM a (componentCLM i (∂[i] u))), hcomponent]
    with x hsum hrow
  exact hsum.trans (Finset.sum_congr rfl fun i _ ↦ hrow i)

/-- A dimension bound for divergence in the graph norm, valid for every normed exponent. -/
theorem norm_divergence_le (u : W^{k + 1,p}(Ω; ℝ^n)) :
    ‖∇· u‖ ≤ n * ‖u‖ := by
  rw [divergence_eq_sum]
  calc
    ‖∑ i : Fin n, componentCLM i (∂[i] u)‖
        ≤ ∑ i : Fin n, ‖componentCLM i (∂[i] u)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖u‖ := Finset.sum_le_sum fun i _ ↦
      (norm_componentCLM_apply_le i _).trans (norm_partialDeriv_le i u)
    _ = n * ‖u‖ := by simp

/-- The bounded divergence operator has norm at most the spatial dimension. -/
theorem norm_divergenceCLM_le :
    ‖divergenceCLM (k := k) (p := p) (Ω := Ω)‖ ≤ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
  exact norm_divergence_le

public meta section

open Lean PrettyPrinter.Delaborator SubExpr

/-- Display applied divergence in mathematical notation, retaining the name of
the bounded map when it is used as an operator. -/
@[delab app.DFunLike.coe]
def delabDivergence : Delab := whenPPOption getPPNotation do
  guard <| !(← getPPOption getPPExplicit)
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  guard <| (e.getArg! 4).isAppOf ``divergenceCLM
  let u ← withAppArg delab
  `(∇· $u)

end

end SobolevSpace.VectorValued
