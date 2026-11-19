/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.Basic
public import PDE.Analysis.Evolution.Semigroup.Generator.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Classical solutions constructed by the semigroup Duhamel integral

Continuous forcing in the generator graph norm suffices to differentiate the
retarded integral. Both the forcing and its generator image are continuous;
the forcing itself need not have a time derivative.

First, integration preserves the generator relation. The restart identity then
gives a right derivative of the constructed integral. The fundamental theorem
of calculus upgrades this to an ordinary derivative at positive interior times.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- At the initial time the Duhamel integral has derivative equal to the forcing,
without a generator-domain assumption. -/
theorem hasDerivAt_duhamel_zero (T : StronglyContinuousSemigroup E)
    {f : ℝ → E} (hf : Continuous f) :
    HasDerivAt (T.duhamel f) (f 0) 0 := by
  let q : ℝ → E := fun h ↦ ∫ s in (0 : ℝ)..1, T (h - h * s).toNNReal (f (h * s))
  have hkernel : Continuous
      (fun p : ℝ × ℝ ↦ T (p.1 - p.1 * p.2).toNNReal (f (p.1 * p.2))) :=
    T.continuous_apply.comp
      ((continuous_real_toNNReal.comp
        (continuous_fst.sub (continuous_fst.mul continuous_snd))).prodMk
          (hf.comp (continuous_fst.mul continuous_snd)))
  have hq : Continuous q :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      hkernel continuous_const
  have hqzero : q 0 = f 0 := by simp [q]
  have heq (h : ℝ) : T.duhamel f h = h • q h := by
    simpa only [mul_zero, mul_one, duhamel, q] using
      (intervalIntegral.smul_integral_comp_mul_left
        (fun s ↦ T (h - s).toNNReal (f s)) h (a := 0) (b := 1)).symm
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hlim : Tendsto q (𝓝[≠] 0) (𝓝 (f 0)) := by
    rw [← hqzero]
    exact hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhzero : h ≠ 0 := hh
  simp only [zero_add, heq, zero_smul, sub_zero, inv_smul_smul₀ hhzero]

/-- The constructed Duhamel value lies in the generator domain, and its
generator image is the Duhamel integral of the generator image of the forcing. -/
theorem hasGeneratorAt_duhamel (T : StronglyContinuousSemigroup E)
    {f Af : ℝ → E} (hf : Continuous f) (hAf : Continuous Af) {t : ℝ}
    (hA : ∀ s ∈ uIcc 0 t, T.HasGeneratorAt (f s) (Af s)) :
    T.HasGeneratorAt (T.duhamel f t) (T.duhamel Af t) := by
  apply T.hasGeneratorAt_intervalIntegral
    ((T.continuous_duhamelIntegrand hf t).intervalIntegrable 0 t)
    ((T.continuous_duhamelIntegrand hAf t).intervalIntegrable 0 t)
  intro s hs
  exact (hA s hs).map _

/-- The restart identity differentiates the constructed integral from the right.
Only the forcing values up to the current time need belong to the generator domain. -/
theorem hasDerivWithinAt_duhamel (T : StronglyContinuousSemigroup E)
    {f Af : ℝ → E} (hf : Continuous f) (hAf : Continuous Af) {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ s ∈ Icc 0 t, T.HasGeneratorAt (f s) (Af s)) :
    HasDerivWithinAt (T.duhamel f) (T.duhamel Af t + f t) (Ici t) t := by
  have hgen : HasDerivWithinAt (T.realOrbit (T.duhamel f t))
      (T.duhamel Af t) (Ici 0) 0 :=
    T.hasGeneratorAt_duhamel hf hAf (by simpa only [uIcc_of_le ht] using hA)
  have hforcing := T.hasDerivAt_duhamel_zero (f := fun r ↦ f (t + r))
    (hf.comp (continuous_const.add continuous_id))
  have hsum : HasDerivWithinAt (fun h ↦ T.duhamel f (t + h))
      (T.duhamel Af t + f t) (Ici 0) 0 := by
    simpa only [add_zero] using
      (hgen.add hforcing.hasDerivWithinAt).congr_of_mem
        (fun h hh ↦ T.duhamel_add hf ht hh) self_mem_Ici
  have hmaps : MapsTo (fun r : ℝ ↦ r - t) (Ici t) (Ici 0) :=
    fun r hr ↦ sub_nonneg.mpr hr
  have hshift := hsum.scomp_of_eq t ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
    hmaps (sub_self t).symm
  simpa only [Function.comp_def, id_eq, one_smul, add_sub_cancel] using hshift

/-- The constructed integral is a primitive of its generator image plus the forcing.
Generator-domain membership is required only on the integration interval. -/
theorem duhamel_eq_integral_generator_add (T : StronglyContinuousSemigroup E)
    {f Af : ℝ → E} (hf : Continuous f) (hAf : Continuous Af) {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ s ∈ Icc 0 t, T.HasGeneratorAt (f s) (Af s)) :
    T.duhamel f t = ∫ s in (0 : ℝ)..t, T.duhamel Af s + f s := by
  have hd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivWithinAt (T.duhamel f) (T.duhamel Af s + f s) (Ioi s) s :=
    (T.hasDerivWithinAt_duhamel hf hAf hs.1.le
      (fun r hr ↦ hA r ⟨hr.1, hr.2.trans hs.2.le⟩)).mono Ioi_subset_Ici_self
  simpa only [duhamel_zero, sub_zero] using
    (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
      (T.continuous_duhamel hf).continuousOn hd
      (((T.continuous_duhamel hAf).add hf).intervalIntegrable 0 t)).symm

/-- Graph-norm continuous forcing gives an ordinary derivative of the constructed
Duhamel integral at every positive interior time. No derivative of the forcing
or pre-existing solution is assumed. -/
theorem hasDerivAt_duhamel (T : StronglyContinuousSemigroup E)
    {f Af : ℝ → E} (hf : Continuous f) (hAf : Continuous Af) {b t : ℝ}
    (ht : t ∈ Ioo 0 b) (hA : ∀ s ∈ Icc 0 b, T.HasGeneratorAt (f s) (Af s)) :
    HasDerivAt (T.duhamel f) (T.duhamel Af t + f t) t := by
  have hc := (T.continuous_duhamel hAf).add hf
  have hprim := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  apply hprim.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact T.duhamel_eq_integral_generator_add hf hAf hr.1.le
    (fun s hs ↦ hA s ⟨hs.1, hs.2.trans hr.2.le⟩)

/-- The free orbit plus the constructed forcing integral belongs to the generator
domain, with the generator acting term by term. -/
theorem hasGeneratorAt_orbit_add_duhamel (T : StronglyContinuousSemigroup E)
    {x Ax : E} (hx : T.HasGeneratorAt x Ax) {f Af : ℝ → E}
    (hf : Continuous f) (hAf : Continuous Af) {t : ℝ}
    (hA : ∀ s ∈ uIcc 0 t, T.HasGeneratorAt (f s) (Af s)) :
    T.HasGeneratorAt (T.realOrbit x t + T.duhamel f t)
      (T.realOrbit Ax t + T.duhamel Af t) :=
  (hx.map t.toNNReal).add (T.hasGeneratorAt_duhamel hf hAf hA)

/-- The free orbit plus the forcing integral has the expected right derivative,
including at the initial time. -/
theorem hasDerivWithinAt_orbit_add_duhamel (T : StronglyContinuousSemigroup E)
    {x Ax : E} (hx : T.HasGeneratorAt x Ax) {f Af : ℝ → E}
    (hf : Continuous f) (hAf : Continuous Af) {t : ℝ} (ht : 0 ≤ t)
    (hA : ∀ s ∈ Icc 0 t, T.HasGeneratorAt (f s) (Af s)) :
    HasDerivWithinAt (fun r ↦ T.realOrbit x r + T.duhamel f r)
      (T.realOrbit Ax t + T.duhamel Af t + f t) (Ici t) t := by
  have horbit : HasDerivWithinAt (T.realOrbit x) (T.realOrbit Ax t) (Ici t) t := by
    simpa only [Real.coe_toNNReal t ht, realOrbit] using
      hx.hasDerivWithinAt_realOrbit t.toNNReal
  simpa only [Pi.add_def, add_assoc] using
    horbit.add (T.hasDerivWithinAt_duhamel hf hAf ht hA)

/-- Duhamel's constructed free-plus-forced value is a classical solution for
generator-domain initial data and graph-norm continuous forcing. -/
theorem hasDerivAt_orbit_add_duhamel (T : StronglyContinuousSemigroup E)
    {x Ax : E} (hx : T.HasGeneratorAt x Ax) {f Af : ℝ → E}
    (hf : Continuous f) (hAf : Continuous Af) {b t : ℝ} (ht : t ∈ Ioo 0 b)
    (hA : ∀ s ∈ Icc 0 b, T.HasGeneratorAt (f s) (Af s)) :
    HasDerivAt (fun r ↦ T.realOrbit x r + T.duhamel f r)
      (T.realOrbit Ax t + T.duhamel Af t + f t) t := by
  simpa only [add_assoc] using
    (hx.hasDerivAt_realOrbit ht.1).fun_add (T.hasDerivAt_duhamel hf hAf ht hA)

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
