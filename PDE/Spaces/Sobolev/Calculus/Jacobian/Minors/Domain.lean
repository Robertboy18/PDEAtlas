/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.WeakConvergence
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.C1Domain.FiniteExponent
public import PDE.Analysis.Operator.CompactConvergence

/-!
# Weak continuity of minors on C¹ extension domains

The compact value projection supplies the strong factors in the minor
induction. The exponent is an arbitrary finite real number, and no bound or
boundary condition is added to weak convergence of the original Sobolev sequence.
The compactness theorem used here needs dimension at least two; in dimension one
the degree-one determinant is covered by the linear theorem.

For `m = n` and `σ = id`, `tendsto_weak_wkpJacobianMinorLp_of_c1Domain` is Evans's lemma on weak
continuity of determinants (§8.2.4(b)): if `n < q < ∞` and `u_k ⇀ u` weakly in `W^{1,q}(U; ℝⁿ)`,
then `det Du_k ⇀ det Du` weakly in `L^{q/n}(U)`. Evans gets uniform convergence of `u_k` from
Morrey's inequality and the Arzelà–Ascoli theorem; we get strong convergence in `L^q` from the
compactness of `W^{1,q}(Ω) → L^q(Ω)`
(`RellichKondrachov.baseCoordinate_isCompactOperator_of_c1Domain`). The theorem holds for every
minor of degree `m < q`, including the case `q ≤ n`, where Morrey's inequality is not available.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), Lemma (Weak continuity of determinants), p. 476,
  and its proof, pp. 477-478.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- Let `Ω` carry a `C1ExtensionAtlas` with `n ≥ 2`, and let `q` be real with `0 < m < q`. If
`u k → U` weakly in `(W^{1,q}(Ω))^m`, then `wkpJacobianMinorLp σ (u k)` converges weakly in
`L^{q/m}` to `wkpJacobianMinorLp σ U`. For `m = n` and `σ = id` this is Evans §8.2.4(b), Lemma
(Weak continuity of determinants). -/
theorem tendsto_weak_wkpJacobianMinorLp_of_c1Domain
    {m n : ℕ} [Fact (0 < n)] {Ω : Opens (ℝ^n)} [Boundary.C1ExtensionAtlas n Ω]
    (hn : 2 ≤ n) {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    [Fact (1 ≤ ENNReal.ofReal q / ENNReal.ofReal (m : ℝ))]
    (hm : 0 < m) (hmq : (m : ℝ) < q) (σ : Fin m → Fin n)
    {u : ℕ → Fin m → W^{1,ENNReal.ofReal q}(Ω)}
    {U : Fin m → W^{1,ENNReal.ofReal q}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ
      (Fin m → W^{1,ENNReal.ofReal q}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin m → W^{1,ENNReal.ofReal q}(Ω)) U))) :
    Tendsto (fun k ↦ toWeakSpace ℝ
        (Lp ℝ (ENNReal.ofReal q / ENNReal.ofReal (m : ℝ)) (domainMeasure n Ω))
        (wkpJacobianMinorLp σ (u k))) atTop
      (𝓝 (toWeakSpace ℝ
        (Lp ℝ (ENNReal.ofReal q / ENNReal.ofReal (m : ℝ)) (domainMeasure n Ω))
        (wkpJacobianMinorLp σ U))) := by
  have : Fact (1 ≤ q.toNNReal) :=
    ⟨ENNReal.coe_le_coe.mp (Fact.out : 1 ≤ ENNReal.ofReal q)⟩
  have hcompact : IsCompactOperator
      (wkpBaseCoordinateCLM (n := n) (m := 1) (p := ENNReal.ofReal q) (Ω := Ω)) :=
    RellichKondrachov.baseCoordinate_isCompactOperator_of_c1Domain (p := q.toNNReal) hn
  apply tendsto_weak_wkpJacobianMinorLp_of_strong_base hm hmq σ hu
  intro i
  have hcomponent : Tendsto (fun k ↦ toWeakSpace ℝ
      (W^{1,ENNReal.ofReal q}(Ω)) (u k i)) atTop
      (𝓝 (toWeakSpace ℝ (W^{1,ENNReal.ofReal q}(Ω)) (U i))) :=
    (WeakSpace.map (ContinuousLinearMap.proj i :
      (Fin m → W^{1,ENNReal.ofReal q}(Ω)) →L[ℝ]
        W^{1,ENNReal.ofReal q}(Ω))).continuous.continuousAt.tendsto.comp hu
  exact PDE.Analysis.tendsto_compactOperator_of_tendsto_weak
    (wkpBaseCoordinateCLM (n := n) (m := 1) (p := ENNReal.ofReal q) (Ω := Ω))
    hcompact hcomponent

end SobolevSpace.GraphSpace
