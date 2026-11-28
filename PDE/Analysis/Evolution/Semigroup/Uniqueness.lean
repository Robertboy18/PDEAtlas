/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Intertwining

/-!
# A semigroup is determined by its generator

If the generator of a strongly continuous semigroup `S` on a Banach space is contained in the
generator of `T`, then `S = T`. In particular two semigroups with the same generator are equal,
and the generator of a semigroup has no proper extension that generates another one. No
contraction bound is needed. This is the case `C = 1` of
`StronglyContinuousSemigroup.apply_eq_of_map_hasGeneratorAt`: the identity maps the generator
relation of `S` into that of `T`, so it intertwines the two semigroups. That theorem
differentiates `T(t - s) S(s) x` on the generator domain, where the two generator terms cancel,
and passes to all `x` by density of the domain.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- If one semigroup generator extends another, the two semigroups already agree.
This also rules out proper generator extensions between strongly continuous semigroups. The
identity maps the generator relation of `S` into that of `T`, so
`apply_eq_of_map_hasGeneratorAt` applies with `C = 1`. -/
theorem eq_of_generatorPMap_le {S T : StronglyContinuousSemigroup E}
    (hST : S.generatorPMap ≤ T.generatorPMap) : S = T := by
  refine StronglyContinuousSemigroup.ext fun t ↦ ContinuousLinearMap.ext fun x ↦ ?_
  exact apply_eq_of_map_hasGeneratorAt (ContinuousLinearMap.id ℝ E)
    (fun x Ax hx ↦ (T.hasGeneratorAt_iff_mem_generatorPMap_graph x Ax).2
      (LinearPMap.le_graph_of_le hST
        ((S.hasGeneratorAt_iff_mem_generatorPMap_graph x Ax).1 hx))) t x

/-- Strongly continuous semigroups on a Banach space with equal generators are equal. -/
theorem eq_of_generatorPMap_eq {S T : StronglyContinuousSemigroup E}
    (hST : S.generatorPMap = T.generatorPMap) : S = T :=
  eq_of_generatorPMap_le hST.le

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
