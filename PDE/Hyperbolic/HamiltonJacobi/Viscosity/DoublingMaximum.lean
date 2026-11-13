/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Comparison

/-!
# A compact maximum principle for doubled viscosity variables

Let `u` be a viscosity subsolution and `v` a viscosity supersolution of the
same autonomous Hamilton–Jacobi equation. On a compact product `K × L`,
consider

`u(z) - v(w) - (P(z - w) + c * zₜ)`, with `c > 0`.

Upper semicontinuity of `u`, lower semicontinuity of `v`, and continuity of
the penalty give a maximizer. If both points were interior, fixing each in
turn would give touching tests for the two viscosity inequalities. Their
spatial derivatives agree, so the Hamiltonians cancel; their time
derivatives leave the contradiction `c ≤ 0`. The maximum must therefore
occur with at least one point on the frontier.

The theorem derives the maximizer from compactness. It uses the local `C¹` touching tests.

The frontier is the full spacetime frontier. For a closed time
cylinder it includes the terminal-time face. Initial-value comparison
still needs to exclude that face, control initial contact as the two
points approach each other, and localize unbounded spatial domains.

In Evans's proof of Theorem 1 in §10.2 the term `ε(|x|²+|y|²)` in (5) localizes the maximum (6)
on the whole space; on a compact product no localization is needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, proof of Theorem 1, equations (5)-(6) and
  (12)-(14).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open Set

/-- A positive linear time penalty forces the maximum of a doubled
subsolution-supersolution difference onto the frontier of a compact
product.

The solutions may be only upper and lower semicontinuous, respectively.
They satisfy the viscosity inequalities on the interiors of the two
compact sets. The penalty is `C¹`, and the frontier in the conclusion is the full spacetime
frontier. -/
theorem IsSpatialViscositySubsolution.exists_isMaxOn_doubling_frontier {H : E → ℝ}
    {K L : Set (E × ℝ)} {u v P : (E × ℝ) → ℝ} {c : ℝ}
    (hu : IsSpatialViscositySubsolution (fun p _ ↦ H p) (interior K) u)
    (hv : IsSpatialViscositySupersolution (fun p _ ↦ H p) (interior L) v) (hK : IsCompact K)
    (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty) (huusc : UpperSemicontinuousOn u K)
    (hvlsc : LowerSemicontinuousOn v L) (hP : ContDiff ℝ 1 P) (hc : 0 < c) :
    ∃ z ∈ K, ∃ w ∈ L, (z ∈ frontier K ∨ w ∈ frontier L) ∧ IsMaxOn
      (fun q : (E × ℝ) × (E × ℝ) ↦ u q.1 - v q.2 - (P (q.1 - q.2) + c * q.1.2)) (K ×ˢ L)
      (z, w) := by
  let F : (E × ℝ) × (E × ℝ) → ℝ := fun q ↦ u q.1 - v q.2 - (P (q.1 - q.2) + c * q.1.2)
  have hu' : UpperSemicontinuousOn (fun q : (E × ℝ) × (E × ℝ) ↦ u q.1) (K ×ˢ L) :=
    huusc.comp continuous_fst.continuousOn (fun _ hq ↦ hq.1)
  have hv' : UpperSemicontinuousOn (fun q : (E × ℝ) × (E × ℝ) ↦ -v q.2) (K ×ˢ L) :=
    (continuous_neg : Continuous (fun r : ℝ ↦ -r)).comp_lowerSemicontinuousOn_antitone
      (hvlsc.comp continuous_snd.continuousOn (fun _ hq ↦ hq.2)) (fun _ _ hab ↦ neg_le_neg hab)
  have hpenalty : Continuous (fun q : (E × ℝ) × (E × ℝ) ↦ -(P (q.1 - q.2) + c * q.1.2)) :=
    ((hP.continuous.comp (continuous_fst.sub continuous_snd)).add (continuous_const.mul
        ((continuous_snd : Continuous (Prod.snd : E × ℝ → ℝ)).comp continuous_fst))).neg
  have hF : UpperSemicontinuousOn F (K ×ˢ L) := by
    simpa only [F, sub_eq_add_neg] using
      (hu'.add hv').add hpenalty.continuousOn.upperSemicontinuousOn
  obtain ⟨q, hq, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn (hKne.prod hLne) (hK.prod hL) hF
  refine ⟨q.1, hq.1, q.2, hq.2, ?_, hmax⟩
  by_contra hboundary
  have hz : q.1 ∈ interior K :=
    (mem_interior_iff_notMem_frontier hq.1).mpr (fun hz ↦ hboundary (Or.inl hz))
  have hw : q.2 ∈ interior L :=
    (mem_interior_iff_notMem_frontier hq.2).mpr (fun hw ↦ hboundary (Or.inr hw))
  exact hu.not_isLocalMaxOn_sub_penalty hv hz hw hP.contDiffAt hc
    (hmax.isLocalMaxOn.mono (Set.prod_mono interior_subset interior_subset))

end

end HamiltonJacobi
