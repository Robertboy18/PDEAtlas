/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.LaplaceTransform
public import PDE.Analysis.Operator.Resolvent.Set

/-!
# Real resolvents of semigroup generators

The closed generator has a bounded resolvent at every parameter in its
real resolvent set. These resolvents satisfy the first resolvent identity and commute
without a sign restriction. For a contraction semigroup, every positive parameter
belongs to the set, and the constructed inverse equals the semigroup Laplace transform.
These are the two parts of Evans §7.4.1, Theorem 3. Boundedness of the resolvent comes from
the closedness of the generator, as in Evans's definition of the resolvent, which uses the
closed graph theorem.

The Laplace transform of a contraction semigroup solves the shifted generator
equation. Its two inverse identities imply the two-parameter resolvent identity
and the operator-norm bound

`‖R_λ - R_μ‖ ≤ |μ - λ| / (λ * μ)`.

Consequently, the resolvent is continuous in operator norm on the positive
parameter axis, although the semigroup itself is only strongly continuous.
No boundedness of the generator or spatial regularity is assumed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.1, definition of the resolvent, p. 437, and Theorem 3,
  pp. 438-439. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : StronglyContinuousSemigroup E) (hT : T.IsContraction)

/-- The bounded resolvent of the entire generator at any real resolvent parameter. -/
def generatorResolvent {lambda : ℝ}
    (hlambda : lambda ∈ T.generatorPMap.realResolventSet) : E →L[ℝ] E :=
  T.generatorPMap.realResolvent T.isClosed_generatorPMap hlambda

/-- The generator resolvents satisfy the resolvent identity `R_λ - R_μ = (μ - λ) R_λ R_μ` at
every pair of real resolvent parameters (Evans §7.4.1, Theorem 3, (12)). -/
theorem generatorResolvent_identity {lambda mu : ℝ}
    (hlambda : lambda ∈ T.generatorPMap.realResolventSet)
    (hmu : mu ∈ T.generatorPMap.realResolventSet) :
    T.generatorResolvent hlambda - T.generatorResolvent hmu =
      (mu - lambda) • (T.generatorResolvent hlambda).comp (T.generatorResolvent hmu) :=
  T.generatorPMap.realResolvent_identity T.isClosed_generatorPMap hlambda hmu

/-- The generator resolvents commute for every pair in the real resolvent set. -/
theorem generatorResolvent_commute {lambda mu : ℝ}
    (hlambda : lambda ∈ T.generatorPMap.realResolventSet)
    (hmu : mu ∈ T.generatorPMap.realResolventSet) :
    Commute (T.generatorResolvent hlambda) (T.generatorResolvent hmu) :=
  T.generatorPMap.realResolvent_commute T.isClosed_generatorPMap hlambda hmu

include hT in
/-- Every positive shift of a contraction generator is bijective on its entire domain. -/
theorem mem_realResolventSet_generatorPMap {lambda : ℝ} (hlambda : 0 < lambda) :
    lambda ∈ T.generatorPMap.realResolventSet :=
  T.generatorPMap.mem_realResolventSet_of_inverse (T.laplaceTransform hT hlambda)
    (T.laplaceTransform_mem_generatorPMap_domain hT hlambda)
    (T.laplaceTransform_generator_identity hT hlambda)
    (T.generator_laplaceTransform_identity hT hlambda)

/-- At positive parameters the constructed resolvent is the semigroup Laplace transform. -/
theorem generatorResolvent_eq_laplaceTransform {lambda : ℝ}
    (hlambda : lambda ∈ T.generatorPMap.realResolventSet) (hpos : 0 < lambda) :
    T.generatorResolvent hlambda = T.laplaceTransform hT hpos :=
  (T.generatorPMap.eq_realResolvent T.isClosed_generatorPMap hlambda
    (T.laplaceTransform hT hpos) (T.laplaceTransform_mem_generatorPMap_domain hT hpos)
    (T.generator_laplaceTransform_identity hT hpos)).symm

include hT in
/-- The positive generator resolvent has the improper Laplace integral formula. -/
theorem generatorResolvent_apply {lambda : ℝ}
    (hlambda : lambda ∈ T.generatorPMap.realResolventSet) (hpos : 0 < lambda) (x : E) :
    T.generatorResolvent hlambda x =
      ∫ s in Ioi (0 : ℝ), Real.exp (-lambda * s) • T.realOrbit x s := by
  rw [T.generatorResolvent_eq_laplaceTransform hT hlambda hpos, laplaceTransform_apply]

include hT in
/-- The positive generator resolvent has operator norm at most `λ⁻¹`. -/
theorem norm_generatorResolvent_le {lambda : ℝ}
    (hlambda : lambda ∈ T.generatorPMap.realResolventSet) (hpos : 0 < lambda) :
    ‖T.generatorResolvent hlambda‖ ≤ lambda⁻¹ := by
  rw [T.generatorResolvent_eq_laplaceTransform hT hlambda hpos]
  exact T.norm_laplaceTransform_le hT hpos

/-- The Laplace transforms at two positive parameters satisfy
`R_λ - R_μ = (μ - λ) R_λ R_μ`. -/
theorem laplaceTransform_resolvent_identity {lambda mu : ℝ}
    (hlambda : 0 < lambda) (hmu : 0 < mu) :
    T.laplaceTransform hT hlambda - T.laplaceTransform hT hmu =
      (mu - lambda) •
        (T.laplaceTransform hT hlambda).comp (T.laplaceTransform hT hmu) := by
  have hlambda_mem := T.mem_realResolventSet_generatorPMap hT hlambda
  have hmu_mem := T.mem_realResolventSet_generatorPMap hT hmu
  rw [← T.generatorResolvent_eq_laplaceTransform hT hlambda_mem hlambda,
    ← T.generatorResolvent_eq_laplaceTransform hT hmu_mem hmu]
  exact T.generatorResolvent_identity hlambda_mem hmu_mem

/-- The positive resolvent parameters have an operator-norm stability estimate. -/
theorem norm_laplaceTransform_sub_le {lambda mu : ℝ}
    (hlambda : 0 < lambda) (hmu : 0 < mu) :
    ‖T.laplaceTransform hT hlambda - T.laplaceTransform hT hmu‖ ≤
      |mu - lambda| * (lambda⁻¹ * mu⁻¹) := by
  rw [T.laplaceTransform_resolvent_identity hT hlambda hmu, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (T.norm_laplaceTransform_le hT hlambda)
      (T.norm_laplaceTransform_le hT hmu) (norm_nonneg _) (inv_nonneg.mpr hlambda.le))

/-- The Laplace resolvent depends continuously in operator norm on its positive
parameter. Strong continuity of the original semigroup suffices. -/
theorem continuous_laplaceTransform :
    Continuous fun lambda : Ioi (0 : ℝ) ↦ T.laplaceTransform hT lambda.property := by
  apply continuous_iff_continuousAt.mpr
  intro lambda
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun mu ↦ T.norm_laplaceTransform_sub_le hT mu.property lambda.property)
  have hparam : Tendsto (fun mu : Ioi (0 : ℝ) ↦ (mu : ℝ))
      (𝓝 lambda) (𝓝 (lambda : ℝ)) := continuous_subtype_val.tendsto lambda
  have hlimit := (hparam.const_sub (lambda : ℝ)).abs.mul
    ((hparam.inv₀ (ne_of_gt lambda.property)).mul_const (lambda : ℝ)⁻¹)
  simpa only [sub_self, abs_zero, zero_mul] using hlimit

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
