/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generation.Construction
import PDE.Analysis.Evolution.Semigroup.LaplaceTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Identification of the generated operator

Dominated convergence passes the integrated orbit identity from the Yosida semigroups
to their limit. The resulting generator extends the original operator. Surjectivity of
the original shift and injectivity of the generator shift give equality of the domains
and operators. This is step 6 of the proof of Evans §7.4.2, Theorem 4, where the identity
being passed to the limit is (22).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.2, proof of Theorem 4, step 6, (22), pp. 440-441.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set Topology

namespace PDE.Analysis.Evolution.HasContractionResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : E →ₗ.[ℝ] E} (hA : HasContractionResolvent A)
  (hdense : Dense (A.domain : Set E))

/-- On the original domain, the constructed semigroup has the prescribed generator value. -/
theorem semigroup_hasGeneratorAt (x : A.domain) :
    (hA.semigroup hdense).HasGeneratorAt x (A x) := by
  apply ((hA.semigroup hdense).hasGeneratorAt_iff_integratedOperator x (A x)).mpr
  intro t
  have hidentity (lambda : Ioi (0 : ℝ)) :
      (hA.yosidaSemigroup lambda.property).integratedOperator t
          (hA.yosidaApproximation lambda.property x) =
        hA.yosidaSemigroup lambda.property t x - x :=
    ((hA.yosidaSemigroup lambda.property).hasGeneratorAt_iff_integratedOperator x _).mp
      (StronglyContinuousSemigroup.exponential_hasGeneratorAt
        (hA.yosidaApproximation lambda.property) (x : E)) t
  have hintegral : Tendsto (fun lambda : Ioi (0 : ℝ) ↦
      (hA.yosidaSemigroup lambda.property).integratedOperator t
        (hA.yosidaApproximation lambda.property x))
      atTop (𝓝 ((hA.semigroup hdense).integratedOperator t (A x))) := by
    simp only [StronglyContinuousSemigroup.integratedOperator_apply]
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ ‖A x‖)
    · exact Eventually.of_forall fun lambda ↦
        ((hA.yosidaSemigroup lambda.property).continuous_realOrbit _).aestronglyMeasurable
    · refine Eventually.of_forall fun lambda ↦ MeasureTheory.ae_of_all _ fun s _ ↦ ?_
      calc
        ‖(hA.yosidaSemigroup lambda.property).realOrbit
            (hA.yosidaApproximation lambda.property x) s‖ ≤
            ‖hA.yosidaApproximation lambda.property x‖ :=
          (hA.yosidaSemigroup_isContraction lambda.property).norm_apply_le s.toNNReal _
        _ ≤ ‖A x‖ := by
          rw [hA.yosidaApproximation_domain lambda.property x]
          exact ((lambda : ℝ) • hA.resolvent lambda.property).le_opNorm (A x) |>.trans
            (mul_le_of_le_one_left (norm_nonneg _) (hA.norm_smul_resolvent_le lambda.property))
    · exact intervalIntegrable_const
    · exact MeasureTheory.ae_of_all _ fun s _ ↦
        hA.tendsto_yosidaSemigroup_apply hdense
          (hA.tendsto_yosidaApproximation hdense x) s.toNNReal
  exact tendsto_nhds_unique hintegral
    (((hA.tendsto_yosidaSemigroup hdense x t).sub_const (x : E)).congr
      (fun lambda ↦ (hidentity lambda).symm))

/-- Every generator pair of the constructed semigroup belongs to the original operator. -/
theorem mem_domain_of_semigroup_hasGeneratorAt {x Ax : E}
    (hx : (hA.semigroup hdense).HasGeneratorAt x Ax) :
    ∃ hxD : x ∈ A.domain, A ⟨x, hxD⟩ = Ax := by
  let S := hA.semigroup hdense
  let y := hA.resolventToDomain (show (0 : ℝ) < 1 by norm_num) (x - Ax)
  have hy := hA.semigroup_hasGeneratorAt hdense y
  let xx : S.generatorPMap.domain := ⟨x, ⟨Ax, hx⟩⟩
  let yy : S.generatorPMap.domain := ⟨y, ⟨A y, hy⟩⟩
  have hxx : S.generatorPMap xx = Ax :=
    (S.hasGeneratorAt_generatorPMap xx).unique hx
  have hyy : S.generatorPMap yy = A y :=
    (S.hasGeneratorAt_generatorPMap yy).unique hy
  have hshift : (y : E) - A y = x - Ax := by
    simpa only [y, coe_resolventToDomain, one_smul] using
      hA.shift_resolvent (show (0 : ℝ) < 1 by norm_num) (x - Ax)
  have heq : (y : E) = x := by
    have hleft := S.laplaceTransform_generator_identity (hA.semigroup_isContraction hdense)
      (show (0 : ℝ) < 1 by norm_num) xx
    have hright := S.laplaceTransform_generator_identity (hA.semigroup_isContraction hdense)
      (show (0 : ℝ) < 1 by norm_num) yy
    rw [hxx, one_smul] at hleft
    rw [hyy, one_smul] at hright
    change S.laplaceTransform _ _ ((y : E) - A y) = (y : E) at hright
    rw [hshift] at hright
    exact hright.symm.trans hleft
  have hvalue : A y = Ax := hy.unique (by simpa only [heq] using hx)
  refine ⟨heq ▸ y.property, ?_⟩
  have hsubtype : (⟨x, heq ▸ y.property⟩ : A.domain) = y := Subtype.ext heq.symm
  rw [hsubtype]
  exact hvalue

/-- The generator of the constructed contraction semigroup is exactly the original operator. -/
theorem generatorPMap_semigroup : (hA.semigroup hdense).generatorPMap = A := by
  apply LinearPMap.ext
  · apply SetLike.ext
    intro x
    constructor
    · rintro ⟨Ax, hx⟩
      exact (hA.mem_domain_of_semigroup_hasGeneratorAt hdense hx).choose
    · intro hx
      exact ⟨A ⟨x, hx⟩, hA.semigroup_hasGeneratorAt hdense ⟨x, hx⟩⟩
  · intro x hx hy
    exact ((hA.semigroup hdense).hasGeneratorAt_generatorPMap ⟨x, hx⟩).unique
      (hA.semigroup_hasGeneratorAt hdense ⟨x, hy⟩)

end PDE.Analysis.Evolution.HasContractionResolvent
