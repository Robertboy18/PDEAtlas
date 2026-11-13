/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Jacobian.Determinant.WeakConvergence
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.ExponentRestriction
public import PDE.Analysis.Matrix.Euclidean.WithScalar
public import PDE.Analysis.MeasureTheory.Lp.Products

/-!
# Joint weak gradient and determinant

The gradient and its determinant have different natural Lebesgue exponents.
Restricting the original Sobolev graph to the smaller exponent preserves every
weak derivative. The two fields can then be packed in one Euclidean space,
where convex supporting fields apply to the full independent matrix and scalar.

The lift represents the determinant graph almost everywhere. Its weak
sequential continuity follows from linearity of the gradient and the
weak continuity of the determinant.

The pair `(Du, det Du)` is what Evans uses in the proof of §8.2.4(b), Theorem 8 (lower
semicontinuity of polyconvex functionals): from (53), `u_k ⇀ u` weakly in `W^{1,q}`, and (54),
`det Du_k ⇀ det Du` weakly in `L^{q/n}`, he uses the weak convergence of `Du_k` and of `det Du_k`
together with the convexity (52) of `F(P, r, z, x)` in `(P, r)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), (51)-(52), Theorem 8 and its proof, (53)-(54),
  pp. 478-479.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology Matrix.Norms.Elementwise Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}
    [Fact (1 ≤ p / ENNReal.ofReal (n : ℝ))]
    [IsFiniteMeasure (domainMeasure n Ω)]

local notation "ρ" => p / ENNReal.ofReal (n : ℝ)
local notation "μΩ" => domainMeasure n Ω

/-- For `0 < n` and `u : Fin n → W^{1,p}(Ω)` with `1 ≤ p/n` on a set of finite measure, the pair
`(Du, det Du)` of the weak gradient matrix and its determinant, as one element of
`L^{p/n}(Ω; ℝ^{n·n+1})`. -/
def wkpJacobianDetLift (hn : 0 < n) (u : (Fin n → W^{1,p}(Ω))) : Lp (ℝ^(n * n + 1)) ρ μΩ :=
  Matrix.euclideanScalarEquiv.toContinuousLinearMap.compLpPair
    (vectorWkpJacobianCLM (vectorLowerExponentCLM (ENNReal.div_ofReal_nat_le p hn) u),
      wkpJacobianDetLp u)

/-- Almost everywhere, `wkpJacobianDetLift hn u` is the weak gradient matrix of `u` together with
its determinant, under `Matrix.euclideanScalarEquiv`. -/
theorem coeFn_wkpJacobianDetLift (hn : 0 < n) (u : (Fin n → W^{1,p}(Ω))) :
    wkpJacobianDetLift hn u =ᵐ[μΩ] fun x ↦
      Matrix.euclideanScalarEquiv
        (Matrix.euclideanEquiv.symm (∇ u x),
          (Matrix.euclideanEquiv.symm (∇ u x)).det) := by
  filter_upwards [
    Matrix.euclideanScalarEquiv.toContinuousLinearMap.coeFn_compLpPair
      (vectorWkpJacobianCLM (vectorLowerExponentCLM (ENNReal.div_ofReal_nat_le p hn) u))
      (wkpJacobianDetLp u),
    vectorWkpJacobianCLM_vectorLowerExponentCLM_apply_ae (ENNReal.div_ofReal_nat_le p hn) u,
    Matrix.euclideanEquiv.symm.toContinuousLinearMap.coeFn_compLpL
      (∇ u),
    coeFn_wkpJacobianDetLp u, vectorWkpJacobianCLM_apply_ae u] with x hx hl hg hd hc
  have hmatrix : vectorWkpJacobianCLM u x =
      Matrix.euclideanEquiv.symm (∇ u x) := hg
  have hdet : wkpJacobianDetLp u x = (vectorWkpJacobianCLM u x).det :=
    hd.trans (congrArg Matrix.det (Matrix.ext fun i j ↦ (hc i j).symm))
  change Matrix.euclideanScalarEquiv.toContinuousLinearMap.compLpPair _ x = _
  rw [hx, hl, hdet, hmatrix]
  rfl

/-- Let `Ω` be bounded and open with C¹ graph boundary and `q` real with `n < q`. If `u k → U`
weakly in `(W^{1,q}(Ω))ⁿ`, then `wkpJacobianDetLift (u k) → wkpJacobianDetLift U` weakly in
`L^{q/n}(Ω; ℝ^{n·n+1})`, along the whole sequence. In Evans §8.2.4(b) this is the consequence of
(53) used with (54) in the proof of Theorem 8. -/
theorem tendsto_weak_wkpJacobianDetLift_of_c1GraphBoundary
    [Fact (0 < n)] {Ω : Opens (ℝ^n)}
    (hbounded : Bornology.IsBounded (Ω : Set (ℝ^n)))
    (hgraph : Boundary.HasC1GraphBoundary (Ω : Set (ℝ^n)))
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    [Fact (1 ≤ ENNReal.ofReal q / ENNReal.ofReal (n : ℝ))]
    [IsFiniteMeasure (domainMeasure n Ω)] (hq : (n : ℝ) < q)
    {u : ℕ → Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    {U : Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ
      (Fin n → W^{1,ENNReal.ofReal q}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin n → W^{1,ENNReal.ofReal q}(Ω)) U))) :
    Tendsto (fun k ↦ toWeakSpace ℝ
        (Lp (ℝ^(n * n + 1)) (ENNReal.ofReal q / ENNReal.ofReal (n : ℝ))
          (domainMeasure n Ω)) (wkpJacobianDetLift (Fact.out : 0 < n) (u k))) atTop
      (𝓝 (toWeakSpace ℝ
        (Lp (ℝ^(n * n + 1)) (ENNReal.ofReal q / ENNReal.ofReal (n : ℝ))
          (domainMeasure n Ω)) (wkpJacobianDetLift (Fact.out : 0 < n) U))) := by
  let B := vectorWkpJacobianCLM.comp
    (vectorLowerExponentCLM (m := n) (n := n) (Ω := (Ω : Set (ℝ^n)))
      (ENNReal.div_ofReal_nat_le (ENNReal.ofReal q) (Fact.out : 0 < n)))
  apply Matrix.euclideanScalarEquiv.toContinuousLinearMap.tendsto_weak_compLpPair
  · exact (WeakSpace.map B).continuous.continuousAt.tendsto.comp hu
  · exact tendsto_weak_wkpJacobianDetLp_of_c1GraphBoundary hbounded hgraph hq hu

end SobolevSpace.GraphSpace
