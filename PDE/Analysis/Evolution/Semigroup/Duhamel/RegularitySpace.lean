/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.Differentiability
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Duhamel differentiation through a space of more regular vectors

Let a semigroup on a Banach space `F` agree, through a bounded map `J : F → E`,
with a semigroup on `E`. Suppose its generator on these vectors is represented
by a bounded map `A : F → E`. Continuous `F`-valued forcing then produces a
Duhamel integral whose image under `J` is differentiable in `E`, with derivative
`A` applied to that same integral plus the forcing.

This separates spatial regularity from time regularity. For example, the two
bounded maps can be value and Laplacian evaluation from a Sobolev space to `L²`.
Neither finite dimension nor a time derivative of the forcing is required.
-/

@[expose] public noncomputable section

open Set

universe u v

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A bounded intertwining map commutes with the constructed Duhamel integral. -/
theorem map_duhamel (S : StronglyContinuousSemigroup F) (T : StronglyContinuousSemigroup E)
    (L : F →L[ℝ] E) (hL : ∀ s x, L (S s x) = T s (L x))
    {f : ℝ → F} (hf : Continuous f) (t : ℝ) :
    L (S.duhamel f t) = T.duhamel (fun s ↦ L (f s)) t := by
  rw [duhamel, ← L.intervalIntegral_comp_comm
    ((S.continuous_duhamelIntegrand hf t).intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact hL _ _

/-- If a bounded map represents the generator on an invariant space of regular
vectors, the image of its Duhamel integral solves the forced equation. -/
theorem hasDerivAt_map_duhamel (S : StronglyContinuousSemigroup F)
    (T : StronglyContinuousSemigroup E) (J A : F →L[ℝ] E)
    (hJ : ∀ s x, J (S s x) = T s (J x))
    (hA : ∀ x, T.HasGeneratorAt (J x) (A x))
    {f : ℝ → F} (hf : Continuous f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r ↦ J (S.duhamel f r)) (A (S.duhamel f t) + J (f t)) t := by
  have hcomm (s : NNReal) (x : F) : A (S s x) = T s (A x) := by
    apply (hA (S s x)).unique
    rw [hJ]
    exact (hA x).map s
  have hd := T.hasDerivAt_duhamel (J.continuous.comp hf) (A.continuous.comp hf)
    (b := t + 1) ⟨ht, lt_add_one t⟩ (fun s _ ↦ hA (f s))
  simp only [Function.comp_def] at hd
  rw [← S.map_duhamel T A hcomm hf t] at hd
  exact hd.congr_of_eventuallyEq (.of_forall fun r ↦ S.map_duhamel T J hJ hf r)

/-- The free-plus-forced value constructed in the regularity space satisfies the
inhomogeneous equation after applying its bounded value map. -/
theorem hasDerivAt_map_orbit_add_duhamel (S : StronglyContinuousSemigroup F)
    (T : StronglyContinuousSemigroup E) (J A : F →L[ℝ] E)
    (hJ : ∀ s x, J (S s x) = T s (J x))
    (hA : ∀ x, T.HasGeneratorAt (J x) (A x))
    {f : ℝ → F} (hf : Continuous f) (x : F) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r ↦ J (S.realOrbit x r + S.duhamel f r))
      (A (S.realOrbit x t + S.duhamel f t) + J (f t)) t := by
  have hcomm (s : NNReal) (y : F) : A (S s y) = T s (A y) := by
    apply (hA (S s y)).unique
    rw [hJ]
    exact (hA y).map s
  have horbit : HasDerivAt (fun r ↦ J (S.realOrbit x r))
      (A (S.realOrbit x t)) t := by
    have hd := (hA x).hasDerivAt_realOrbit ht
    change HasDerivAt (T.realOrbit (J x)) (T t.toNNReal (A x)) t at hd
    rw [← hcomm] at hd
    exact hd.congr_of_eventuallyEq (.of_forall fun r ↦ hJ r.toNNReal x)
  simpa only [ContinuousLinearMap.map_add, add_assoc] using
    horbit.fun_add (S.hasDerivAt_map_duhamel T J A hJ hA hf ht)

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
