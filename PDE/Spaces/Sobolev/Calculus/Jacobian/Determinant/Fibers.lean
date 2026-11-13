/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Jacobian.Determinant.WeakConvergence

/-!
# Weak sequential closure of prescribed Jacobian determinants

For a finite real exponent above the positive spatial dimension, the
Sobolev determinant preserves weak sequence limits. Its fibres are therefore
sequentially closed in the weak topology. This is the closure property needed
for determinant constraints in the direct method, where the weak topology
need not be metrizable.

Both theorems follow from `tendsto_weak_wkpJacobianDetLp_of_c1GraphBoundary`, Evans's lemma on weak
continuity of determinants (§8.2.4(b)).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), Lemma (Weak continuity of determinants), p. 476.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Opens (ℝ^n)}
  {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
  [Fact (1 ≤ ENNReal.ofReal q / ENNReal.ofReal (n : ℝ))]

/-- Let `Ω` be bounded and open with C¹ graph boundary, `q` real with `n < q`, and
`ρ ∈ L^{q/n}(Ω)`. Then `{u : wkpJacobianDetLp u = ρ}` is sequentially closed in the weak topology
of `(W^{1,q}(Ω))ⁿ`. -/
theorem isSeqClosed_weak_fiber_wkpJacobianDetLp
    (hbounded : Bornology.IsBounded (Ω : Set (ℝ^n)))
    (hgraph : Boundary.HasC1GraphBoundary (Ω : Set (ℝ^n))) (hq : (n : ℝ) < q)
    (ρ : Lp ℝ (ENNReal.ofReal q / ENNReal.ofReal (n : ℝ)) (domainMeasure n Ω)) :
    IsSeqClosed (toWeakSpace ℝ (Fin n → W^{1,ENNReal.ofReal q}(Ω)) ''
      {u | wkpJacobianDetLp u = ρ}) := by
  intro v U hv hU
  let e := toWeakSpace ℝ (Fin n → W^{1,ENNReal.ofReal q}(Ω))
  let u : ℕ → Fin n → W^{1,ENNReal.ofReal q}(Ω) :=
    fun j ↦ e.symm (v j)
  have hu (j : ℕ) : wkpJacobianDetLp (u j) = ρ := by
    obtain ⟨w, hw, he⟩ := hv j
    simpa only [u, ← he, e, LinearEquiv.symm_apply_apply, mem_ofPred_eq] using hw
  have hweak : Tendsto (fun j ↦ e (u j)) atTop (𝓝 (e (e.symm U))) := by
    simpa only [u, LinearEquiv.apply_symm_apply] using hU
  have hdet := tendsto_weak_wkpJacobianDetLp_of_c1GraphBoundary
    hbounded hgraph hq hweak
  refine ⟨e.symm U, ?_, e.apply_symm_apply U⟩
  apply (toWeakSpace ℝ
    (Lp ℝ (ENNReal.ofReal q / ENNReal.ofReal (n : ℝ)) (domainMeasure n Ω))).injective
  exact tendsto_nhds_unique hdet (by simpa only [hu] using tendsto_const_nhds)

/-- Let `Ω` be bounded and open with C¹ graph boundary, `q` real with `n < q`, and `ρ` a function
in `L^{q/n}(Ω)`. Then the set of `u` with `det (∂_j u_i) = ρ` almost everywhere is sequentially
closed in the weak topology of `(W^{1,q}(Ω))ⁿ`. -/
theorem isSeqClosed_weak_setOf_jacobianDet_eq_ae
    (hbounded : Bornology.IsBounded (Ω : Set (ℝ^n)))
    (hgraph : Boundary.HasC1GraphBoundary (Ω : Set (ℝ^n))) (hq : (n : ℝ) < q)
    (ρ : ℝ^n → ℝ)
    (hρ : MemLp ρ (ENNReal.ofReal q / ENNReal.ofReal (n : ℝ)) (domainMeasure n Ω)) :
    IsSeqClosed (toWeakSpace ℝ (Fin n → W^{1,ENNReal.ofReal q}(Ω)) ''
      {u | (fun x ↦ Matrix.det (Matrix.of fun i j ↦
        wkpCoordinateCLM (singleDerivIndex n j) (u i) x)) =ᵐ[domainMeasure n Ω] ρ}) := by
  have heq (u : Fin n → W^{1,ENNReal.ofReal q}(Ω)) :
      wkpJacobianDetLp u = hρ.toLp ρ ↔
        (fun x ↦ Matrix.det (Matrix.of fun i j ↦
          wkpCoordinateCLM (singleDerivIndex n j) (u i) x)) =ᵐ[domainMeasure n Ω] ρ := by
    constructor
    · intro h
      have h' : wkpJacobianDetLp u =ᵐ[domainMeasure n Ω] ρ := by
        rw [h]
        exact hρ.coeFn_toLp
      exact (coeFn_wkpJacobianDetLp u).symm.trans h'
    · intro h
      exact Lp.ext ((coeFn_wkpJacobianDetLp u).trans (h.trans hρ.coeFn_toLp.symm))
  simpa only [heq] using
    isSeqClosed_weak_fiber_wkpJacobianDetLp hbounded hgraph hq (hρ.toLp ρ)

end SobolevSpace.GraphSpace
