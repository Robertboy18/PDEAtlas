/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Caratheodory.Affine
public import PDE.Spaces.Sobolev.Approximation.Mollification.L2Operator

/-!
# The Cauchy problem for a mollified first-order operator

Fix a mollifier `ρ_ε`. Let `J_ε` be convolution by `ρ_ε` on `L²(ℝ^n; E)` and let `K_{ε,j}`
be convolution by its coordinate derivative. We construct

`A_ε(t)u = -∑ⱼ J_ε (Bⱼ(t) K_{ε,j}u)`

from spatial `L∞` coefficient fields. If the coefficients are continuous in time in that
norm, arbitrary `L²` initial data and integrable `L²`-valued forcing give an absolutely
continuous solution on every finite interval. The coefficient bound on the time interval
follows from compactness; affine Picard iteration constructs the trajectory.

Evans, §7.3.2, approximates symmetric hyperbolic systems by the viscous problems (11); we
regularize the operator by mollification instead, and this is the existence step at fixed `ε`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2, equation (11) and Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Convolution ENNReal Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis PDE.Analysis.Evolution SobolevSpace.Approximation

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- The bounded mollified principal operator `-∑ⱼ J_ε Bⱼ K_{ε,j}`.

The coefficient argument consists of spatial `L∞` fields, with no solution or differential
operator supplied as an assumption. -/
def mollifiedPrincipalOperator (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (B : Fin n → Lp (E →L[ℝ] E) ∞ (volume : Measure (ℝ^n))) :
    Lp E 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp E 2 (volume : Measure (ℝ^n)) :=
  -∑ j, (mollifierL2CLM μ hε).comp
    ((multiplicationL2CLM (B j)).comp (mollifierDerivativeL2CLM μ hε j))

omit [CompleteSpace E] in
/-- Applying the principal operator gives its finite sum of mollified coefficient terms. -/
theorem mollifiedPrincipalOperator_apply (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (B : Fin n → Lp (E →L[ℝ] E) ∞ (volume : Measure (ℝ^n))) (u : Lp E 2 (volume : Measure (ℝ^n))) :
    mollifiedPrincipalOperator μ hε B u = -∑ j,
      mollifierL2CLM μ hε (multiplicationL2CLM (B j) (mollifierDerivativeL2CLM μ hε j u)) := by
  simp only [mollifiedPrincipalOperator, neg_apply, sum_apply, ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
/-- Continuity in the uniform coefficient norm gives operator-norm continuity in time. -/
theorem continuous_mollifiedPrincipalOperator (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (B : Fin n → ℝ → Lp (E →L[ℝ] E) ∞ (volume : Measure (ℝ^n))) (hB : ∀ j, Continuous (B j)) :
    Continuous (fun t ↦ mollifiedPrincipalOperator μ hε (fun j ↦ B j t)) := by
  unfold mollifiedPrincipalOperator
  apply Continuous.neg
  apply continuous_finsetSum
  intro j _
  exact (((multiplicationL2CLM (n := n) (E := E)).continuous.comp (hB j)).clm_comp_const
    (mollifierDerivativeL2CLM μ hε j)).const_clm_comp (mollifierL2CLM μ hε)

/-- The mollified Cauchy problem has a solution for every `L²` initial state and integrable
`L²`-valued forcing on a finite time interval.

Coefficients are continuous in time as `L∞` spatial operator fields. This is stronger than
pointwise time continuity on the unbounded spatial domain. The operator bound follows from
continuity on the compact time interval, and the trajectory is constructed by affine Picard
iteration. -/
theorem exists_mollified_cauchy (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (B : Fin n → ℝ → Lp (E →L[ℝ] E) ∞ (volume : Measure (ℝ^n))) (hB : ∀ j, Continuous (B j))
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → Lp E 2 (volume : Measure (ℝ^n)))
    (hf : IntegrableOn f (Icc a b) volume) (u₀ : Lp E 2 (volume : Measure (ℝ^n))) :
    Nonempty (AffineCaratheodorySolutionOn
      (fun t ↦ mollifiedPrincipalOperator μ hε (fun j ↦ B j t)) f a b u₀) := by
  let A := fun t ↦ mollifiedPrincipalOperator μ hε (fun j ↦ B j t)
  have hA : Continuous A := continuous_mollifiedPrincipalOperator μ hε B hB
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hA.continuousOn
  have hMnonneg : 0 ≤ M := (norm_nonneg (A a)).trans (hM a ⟨le_rfl, hab⟩)
  let : SecondCountableTopologyEither ℝ
      (Lp E 2 (volume : Measure (ℝ^n)) →L[ℝ] Lp E 2 (volume : Measure (ℝ^n))) :=
    ⟨Or.inl inferInstance⟩
  exact AffineCaratheodorySolutionOn.exists hab A f hA.aestronglyMeasurable hf ⟨M, hMnonneg⟩ hM u₀

/-- In particular, square-integrable `L²`-valued forcing supplies a mollified Cauchy solution
on every finite time interval. -/
theorem exists_mollified_cauchy_of_memLp (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (B : Fin n → ℝ → Lp (E →L[ℝ] E) ∞ (volume : Measure (ℝ^n))) (hB : ∀ j, Continuous (B j))
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → Lp E 2 (volume : Measure (ℝ^n)))
    (hf : MemLp f 2 (volume.restrict (Icc a b))) (u₀ : Lp E 2 (volume : Measure (ℝ^n))) :
    Nonempty (AffineCaratheodorySolutionOn
      (fun t ↦ mollifiedPrincipalOperator μ hε (fun j ↦ B j t)) f a b u₀) :=
  exists_mollified_cauchy μ hε B hB hab f
    (MeasureTheory.MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf) u₀

end PDE.Hyperbolic.FirstOrder
