/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Jacobian.Determinant.Model
public import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.Domain
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction

/-!
# Weak continuity of the Jacobian determinant

For every positive dimension and finite real `q > n`, weak `W¹ᑫ` convergence
implies weak `L^(q/n)` convergence of the Jacobian determinants. The
domain is specified by raw boundedness, openness and C¹ graph boundary.
Compactness and every intermediate minor limit are derived in the proof.

Dimension one uses the linear derivative coordinate directly. Empty and
disconnected domains and singular Jacobians require no separate assumptions.

`tendsto_weak_wkpJacobianDetLp_of_c1GraphBoundary` is Evans's lemma on weak continuity of
determinants (§8.2.4(b)): if `n < q < ∞` and `u_k ⇀ u` weakly in `W^{1,q}(U; ℝⁿ)`, then
`det Du_k ⇀ det Du` weakly in `L^{q/n}(U)`. In dimension at least two it is the case `m = n`,
`σ = id` of `tendsto_weak_wkpJacobianMinorLp_of_c1Domain`, with the atlas built from the graph
boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), Lemma (Weak continuity of determinants), p. 476,
  and its proof, pp. 477-478.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- Evans §8.2.4(b), Lemma (Weak continuity of determinants): let `Ω` be bounded and open with C¹
graph boundary and let `q` be real with `n < q`. If `u k → U` weakly in `(W^{1,q}(Ω))ⁿ`, then
`wkpJacobianDetLp (u k) → wkpJacobianDetLp U` weakly in `L^{q/n}(Ω)`, along the whole
sequence. -/
theorem tendsto_weak_wkpJacobianDetLp_of_c1GraphBoundary
    {n : ℕ} [Fact (0 < n)] {Ω : Opens (ℝ^n)}
    (hbounded : Bornology.IsBounded (Ω : Set (ℝ^n)))
    (hgraph : Boundary.HasC1GraphBoundary (Ω : Set (ℝ^n)))
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    [Fact (1 ≤ ENNReal.ofReal q / ENNReal.ofReal (n : ℝ))] (hq : (n : ℝ) < q)
    {u : ℕ → Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    {U : Fin n → W^{1,ENNReal.ofReal q}(Ω)}
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ
      (Fin n → W^{1,ENNReal.ofReal q}(Ω)) (u k)) atTop
      (𝓝 (toWeakSpace ℝ (Fin n → W^{1,ENNReal.ofReal q}(Ω)) U))) :
    Tendsto (fun k ↦ toWeakSpace ℝ
        (Lp ℝ (ENNReal.ofReal q / ENNReal.ofReal (n : ℝ)) (domainMeasure n Ω))
        (wkpJacobianDetLp (u k))) atTop
      (𝓝 (toWeakSpace ℝ
        (Lp ℝ (ENNReal.ofReal q / ENNReal.ofReal (n : ℝ)) (domainMeasure n Ω))
        (wkpJacobianDetLp U))) := by
  have hn : 0 < n := Fact.out
  by_cases hn1 : n = 1
  · subst n
    exact tendsto_weak_wkpJacobianMinorLp_one
      (ENNReal.one_lt_ofReal_div_nat hn hq) (ENNReal.ofReal_div_nat_ne_top q hn) id hu
  · obtain ⟨atlas, _, _⟩ :=
      (Boundary.hasContDiffGraphBoundary_one_iff.mpr hgraph).exists_c1ExtensionAtlas
        le_rfl Ω.isOpen hbounded
    let := atlas
    exact tendsto_weak_wkpJacobianMinorLp_of_c1Domain (by omega) hn hq id hu

end SobolevSpace.GraphSpace
