/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Yosida
import PDE.Analysis.Evolution.Semigroup.JointContinuity
import PDE.Analysis.Calculus.StrongOperator
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# An operator that intertwines two generators intertwines the semigroups

Let `S` and `T` be strongly continuous semigroups on Banach spaces with generators `A` and `B`,
and let `C` be a bounded operator with `C A ⊆ B C`: `C` maps the domain of `A` into the domain
of `B`, and `B C x = C A x` there. Then `C S(t) = T(t) C` for all `t ≥ 0`. A projection onto an
invariant subspace, or its complement, is the typical `C`. For `C = 1` on one space this says
that a semigroup is determined by its generator,
`StronglyContinuousSemigroup.eq_of_generatorPMap_le`, which is proved from it. In the other
direction, an operator that commutes with one semigroup maps its generator relation into
itself (`StronglyContinuousSemigroup.HasGeneratorAt.map_of_commute`). The theorem for a closed
unbounded `C` is not proved here.

## Main results

* `StronglyContinuousSemigroup.apply_eq_of_map_hasGeneratorAt`: if a bounded operator `C` maps
  the generator relation of `S` into that of `T`, then `C S(t) x = T(t) C x` for all `t ≥ 0` and
  all `x`.

## How it works

For `x` in the domain of `A` and a fixed `t`, the curve `s ↦ T(t - s) C S(s) x` on `[0, t]` has
right derivative `-T(t - s) B C S(s) x + T(t - s) C A S(s) x = 0`, so it is constant. The
derivative of a moving vector under a strongly continuous family is
`PDE.Analysis.hasDerivWithinAt_clm_apply_of_continuousAt`, with the joint continuity of the
semigroup (`StronglyContinuousSemigroup.continuous_apply`). The values at `s = 0` and `s = t` are
`T(t) C x` and `C S(t) x`. The domain of `A` is dense, and both sides are continuous in `x`.
-/

@[expose] public noncomputable section

open Set Topology

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **An operator that intertwines the generators intertwines the semigroups.** Let `C` be a
bounded operator such that, whenever `x` is in the domain of the generator of `S` with value
`Ax`, `C x` is in the domain of the generator of `T` with value `C Ax`. Then
`C S(t) x = T(t) C x` for all `t ≥ 0` and all `x`. -/
theorem apply_eq_of_map_hasGeneratorAt {S : StronglyContinuousSemigroup E}
    {T : StronglyContinuousSemigroup F} (C : E →L[ℝ] F)
    (hC : ∀ ⦃x Ax : E⦄, S.HasGeneratorAt x Ax → T.HasGeneratorAt (C x) (C Ax))
    (t : NNReal) (x : E) : C (S t x) = T t (C x) := by
  have hagree (x : S.generatorPMap.domain) : C (S t x) = T t (C x) := by
    let Ax := S.generatorPMap x
    have hx : S.HasGeneratorAt x Ax := S.hasGeneratorAt_generatorPMap x
    let f : ℝ → F := fun s ↦ T.realOrbit (C (S.realOrbit x s)) ((t : ℝ) - s)
    have hcont : Continuous f :=
      T.continuous_apply.comp
        ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).prodMk
          (C.continuous.comp (S.continuous_realOrbit x)))
    have hderiv (s : ℝ) (hs : s ∈ Ico (0 : ℝ) (t : ℝ)) :
        HasDerivWithinAt f 0 (Ici s) s := by
      let sn : NNReal := ⟨s, hs.1⟩
      have hstate : T.HasGeneratorAt (C (S.realOrbit x s)) (C (S.realOrbit Ax s)) := by
        change T.HasGeneratorAt (C (S.realOrbit x (sn : ℝ))) (C (S.realOrbit Ax (sn : ℝ)))
        simpa only [realOrbit_coe] using hC (hx.map sn)
      have hfixed : HasDerivAt
          (fun r : ℝ ↦ T.realOrbit (C (S.realOrbit x s)) ((t : ℝ) - r))
          (-T.realOrbit (C (S.realOrbit Ax s)) ((t : ℝ) - s)) s := by
        simpa only [Function.comp_def, neg_smul, one_smul] using
          (hstate.hasDerivAt_realOrbit (sub_pos.mpr hs.2)).scomp s
            ((hasDerivAt_id s).const_sub (t : ℝ))
      have hmoving : HasDerivWithinAt (fun r ↦ C (S.realOrbit x r)) (C (S.realOrbit Ax s))
          (Ici s) s := by
        have h0 : HasDerivWithinAt (S.realOrbit x) (S.realOrbit Ax s) (Ici s) s := by
          change HasDerivWithinAt (S.realOrbit x) (S.realOrbit Ax (sn : ℝ))
            (Ici (sn : ℝ)) (sn : ℝ)
          simpa only [realOrbit_coe] using hx.hasDerivWithinAt_realOrbit sn
        exact C.hasFDerivAt.comp_hasDerivWithinAt s h0
      have haction :
          Continuous (fun p : ℝ × F ↦ T ((t : ℝ) - p.1).toNNReal p.2) :=
        T.continuous_apply.comp
          ((continuous_real_toNNReal.comp (continuous_const.sub continuous_fst)).prodMk
            continuous_snd)
      simpa only [f, realOrbit, neg_add_cancel] using
        PDE.Analysis.hasDerivWithinAt_clm_apply_of_continuousAt
          haction.continuousAt hfixed.hasDerivWithinAt hmoving
    have h := constant_of_has_deriv_right_zero hcont.continuousOn hderiv
      (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
    simpa only [f, sub_self, realOrbit_zero, sub_zero, realOrbit_coe] using h
  exact congrFun (Continuous.ext_on S.dense_generatorPMap_domain_of_complete
    (C.continuous.comp (S t).continuous) ((T t).continuous.comp C.continuous)
    (fun x hx ↦ hagree ⟨x, hx⟩)) x

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
