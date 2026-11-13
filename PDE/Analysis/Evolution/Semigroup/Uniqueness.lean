/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Yosida
import PDE.Analysis.Evolution.Semigroup.JointContinuity
import PDE.Analysis.Calculus.StrongOperator
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# A semigroup is determined by its generator

For two semigroups with the same generator, differentiate `T(t-s)S(s)x`.
The two generator terms cancel. This first proves equality on the generator
domain; its density then gives equality on the whole Banach space.

The argument only needs inclusion of the first generator in the second. It also
works without a contraction bound. Strong continuity gives the joint continuity
needed to differentiate a moving vector, even when the generator is unbounded.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- If one semigroup generator extends another, the two semigroups already agree.
This also rules out proper generator extensions between strongly continuous semigroups. -/
theorem eq_of_generatorPMap_le {S T : StronglyContinuousSemigroup E}
    (hST : S.generatorPMap ≤ T.generatorPMap) : S = T := by
  have htransfer {x Ax : E} (hx : S.HasGeneratorAt x Ax) : T.HasGeneratorAt x Ax :=
    (T.hasGeneratorAt_iff_mem_generatorPMap_graph x Ax).2
      (LinearPMap.le_graph_of_le hST
        ((S.hasGeneratorAt_iff_mem_generatorPMap_graph x Ax).1 hx))
  have hagree (t : NNReal) (x : S.generatorPMap.domain) : S t x = T t x := by
    let Ax := S.generatorPMap x
    have hx : S.HasGeneratorAt x Ax := S.hasGeneratorAt_generatorPMap x
    let f : ℝ → E := fun s ↦ T.realOrbit (S.realOrbit x s) ((t : ℝ) - s)
    have hcont : Continuous f := by
      exact T.continuous_apply.comp
        ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).prodMk
          (S.continuous_realOrbit x))
    have hderiv (s : ℝ) (hs : s ∈ Ico (0 : ℝ) (t : ℝ)) :
        HasDerivWithinAt f 0 (Ici s) s := by
      let sn : NNReal := ⟨s, hs.1⟩
      have hstate : T.HasGeneratorAt (S.realOrbit x s) (S.realOrbit Ax s) := by
        change T.HasGeneratorAt (S.realOrbit x (sn : ℝ)) (S.realOrbit Ax (sn : ℝ))
        simpa only [realOrbit_coe] using htransfer (hx.map sn)
      have hfixed : HasDerivAt
          (fun r : ℝ ↦ T.realOrbit (S.realOrbit x s) ((t : ℝ) - r))
          (-T.realOrbit (S.realOrbit Ax s) ((t : ℝ) - s)) s := by
        simpa only [Function.comp_def, neg_smul, one_smul] using
          (hstate.hasDerivAt_realOrbit (sub_pos.mpr hs.2)).scomp s
            ((hasDerivAt_id s).const_sub (t : ℝ))
      have hmoving : HasDerivWithinAt (S.realOrbit x) (S.realOrbit Ax s) (Ici s) s := by
        change HasDerivWithinAt (S.realOrbit x) (S.realOrbit Ax (sn : ℝ))
          (Ici (sn : ℝ)) (sn : ℝ)
        simpa only [realOrbit_coe] using hx.hasDerivWithinAt_realOrbit sn
      have haction :
          Continuous (fun p : ℝ × E ↦ T ((t : ℝ) - p.1).toNNReal p.2) :=
        T.continuous_apply.comp
          ((continuous_real_toNNReal.comp (continuous_const.sub continuous_fst)).prodMk
            continuous_snd)
      simpa only [f, realOrbit, neg_add_cancel] using
        PDE.Analysis.hasDerivWithinAt_clm_apply_of_continuousAt
          haction.continuousAt hfixed.hasDerivWithinAt hmoving
    have h := constant_of_has_deriv_right_zero hcont.continuousOn hderiv
      (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
    simpa only [f, sub_self, realOrbit_zero, sub_zero, realOrbit_coe] using h
  apply ext
  intro t
  apply ContinuousLinearMap.ext
  exact congrFun (Continuous.ext_on S.dense_generatorPMap_domain_of_complete
    (S t).continuous (T t).continuous (fun x hx ↦ hagree t ⟨x, hx⟩))

/-- Strongly continuous semigroups on a Banach space with equal generators are equal. -/
theorem eq_of_generatorPMap_eq {S T : StronglyContinuousSemigroup E}
    (hST : S.generatorPMap = T.generatorPMap) : S = T :=
  eq_of_generatorPMap_le hST.le

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
