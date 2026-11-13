/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.ObservedEvolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import CAS.ExactTactic
import PDE.Analysis.Calculus.StrongOperator

/-!
# Integrable forcing for the wave evolution

A locally integrable force gives a continuous Duhamel trajectory for a uniformly
bounded propagator. This allows weak wave forces to be identified without first
assuming continuity of their higher Sobolev representatives.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded semigroup kernel preserves interval integrability of the force. The global bound
gives the joint continuity of the action directly, so `E` need not be complete. -/
theorem intervalIntegrable_duhamelIntegrand (S : StronglyContinuousSemigroup E) {M : ℝ}
    (hS : ∀ r, ‖S r‖ ≤ M) {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b) (t : ℝ) :
    IntervalIntegrable (fun s ↦ S (t - s).toNNReal (f s)) volume a b := by
  apply (hf.norm.const_mul M).mono_fun'
  · exact (PDE.Analysis.continuous_apply_prod_of_norm_le S.continuous_orbit
      hS).comp_aestronglyMeasurable
      ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        |>.prodMk hf.def'.aestronglyMeasurable)
  · exact Eventually.of_forall fun s ↦ (S (t - s).toNNReal).le_of_opNorm_le (hS _) (f s)

/-- The retarded integral is Lipschitz in the L¹ norm of its force. -/
theorem norm_duhamel_sub_le_integral_of_integrable (S : StronglyContinuousSemigroup E) {M : ℝ}
    (hS : ∀ r, ‖S r‖ ≤ M) {f g : ℝ → E} {t : ℝ} (ht : 0 ≤ t) (hf : IntervalIntegrable f volume 0 t)
    (hg : IntervalIntegrable g volume 0 t) :
    ‖S.duhamel f t - S.duhamel g t‖ ≤ M * ∫ s in (0 : ℝ)..t, ‖f s - g s‖ := by
  rw [StronglyContinuousSemigroup.duhamel, StronglyContinuousSemigroup.duhamel,
    ← intervalIntegral.integral_sub (intervalIntegrable_duhamelIntegrand S hS hf t)
      (intervalIntegrable_duhamelIntegrand S hS hg t), ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le ht
    (Eventually.of_forall fun s _ ↦ ?_) ((hf.sub hg).norm.const_mul M)
  rw [← map_sub]
  exact (S (t - s).toNNReal).le_of_opNorm_le (hS _) (f s - g s)

/-- One L¹ error on a terminal interval bounds all preceding Duhamel errors. -/
theorem norm_duhamel_sub_le_integral_of_mem_Icc (S : StronglyContinuousSemigroup E) {M : ℝ}
    (hS : ∀ r, ‖S r‖ ≤ M) {f g : ℝ → E} {t T : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hf : IntervalIntegrable f volume 0 T) (hg : IntervalIntegrable g volume 0 T) :
    ‖S.duhamel f t - S.duhamel g t‖ ≤ M * ∫ s in (0 : ℝ)..T, ‖f s - g s‖ := by
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2
  refine (norm_duhamel_sub_le_integral_of_integrable S hS ht.1
    (hf.mono_set hsub) (hg.mono_set hsub)).trans ?_
  apply mul_le_mul_of_nonneg_left _ ((norm_nonneg (S 0)).trans (hS 0))
  rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le (ht.1.trans ht.2)]
  exact setIntegral_mono_set ((hf.sub hg).norm.1) (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Eventually.of_forall (Ioc_subset_Ioc le_rfl ht.2))

variable [CompleteSpace E]

/-- Local integrability suffices for continuity of the retarded integral of a
uniformly bounded semigroup. -/
theorem continuous_duhamel_of_locallyIntegrable (S : StronglyContinuousSemigroup E) {M : ℝ}
    (hS : ∀ r, ‖S r‖ ≤ M) {f : ℝ → E} (hf : LocallyIntegrable f volume) :
    Continuous (S.duhamel f) := by
  rw [continuous_iff_continuousAt]
  intro t
  let a : ℝ := min 0 t - 1
  let b : ℝ := max 0 t + 1
  have ha : 0 ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_left (0 : ℝ) t],
    by dsimp [b]; linarith [le_max_left (0 : ℝ) t]⟩
  have hb : t ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_right (0 : ℝ) t],
    by dsimp [b]; linarith [le_max_right (0 : ℝ) t]⟩
  have hi : IntervalIntegrable f volume a b := intervalIntegrable_iff.mpr
      ((hf.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self)
  have hm (r : ℝ) : AEStronglyMeasurable
      (fun s ↦ S (r - s).toNNReal (f s)) (volume.restrict (Ι a b)) :=
    S.continuous_apply.comp_aestronglyMeasurable
      ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        |>.prodMk hi.def'.aestronglyMeasurable)
  have hc := intervalIntegral.continuousAt_parametric_primitive_of_dominated
    (μ := volume) (x₀ := t) (F := fun r s : ℝ ↦ S (r - s).toNNReal (f s)) (fun s ↦ M * ‖f s‖) a b hm
    (Eventually.of_forall fun r ↦ Eventually.of_forall fun s ↦
      (S (r - s).toNNReal).le_of_opNorm_le (hS _) (f s)) (hi.norm.const_mul M)
    (Eventually.of_forall fun s ↦ ((S.continuous_orbit (f s)).comp
        (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))).continuousAt)
    ha hb (measure_singleton t)
  have hd : ContinuousAt (fun r : ℝ ↦ (r, r)) t := (continuous_id.prodMk continuous_id).continuousAt
  exact hc.comp (f := fun r : ℝ ↦ (r, r)) hd

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- Integrable forcing satisfies the same weak observation identity as continuous
forcing. Bounded continuous approximations converge in L¹ and their retarded
integrals converge uniformly on the finite observation interval. -/
theorem observed_duhamel_integral_of_locallyIntegrable (S : StronglyContinuousSemigroup E) {M : ℝ}
    (hS : ∀ r, ‖S r‖ ≤ M) (Q R : E →L[ℝ] Z) (hdense : Dense (S.generatorPMap.domain : Set E))
    (hQR : ∀ x y, S.HasGeneratorAt x y → Q y = R x) {f : ℝ → E} (hf : LocallyIntegrable f volume)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, R (S.duhamel f s) + Q (f s)) = Q (S.duhamel f t) := by
  have hM : 0 ≤ M := (norm_nonneg (S 0)).trans (hS 0)
  have hfi : IntervalIntegrable f volume 0 t := intervalIntegrable_iff.mpr
      ((hf.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self)
  have hc := continuous_duhamel_of_locallyIntegrable S hS hf
  let e := fun g : ℝ → E ↦ R (∫ s in (0 : ℝ)..t, S.duhamel g s) +
    Q (∫ s in (0 : ℝ)..t, g s) - Q (S.duhamel g t)
  have hz {g : ℝ → E} (hg : Continuous g) : e g = 0 := by
    have h := observed_forced_integral S Q R hdense hQR hg (0 : E) ht
    simp only [StronglyContinuousSemigroup.realOrbit, map_zero, zero_add, sub_zero] at h
    have hRi : IntervalIntegrable (fun s ↦ R (S.duhamel g s)) volume 0 t :=
      (R.continuous.comp (S.continuous_duhamel hg)).intervalIntegrable _ _
    have hQi : IntervalIntegrable (fun s ↦ Q (g s)) volume 0 t :=
      (Q.continuous.comp hg).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hRi hQi,
      R.intervalIntegral_comp_comm ((S.continuous_duhamel hg).intervalIntegrable _ _),
      Q.intervalIntegral_comp_comm (hg.intervalIntegrable _ _)] at h
    exact sub_eq_zero.mpr h
  let C := ‖R‖ * M * t + ‖Q‖ + ‖Q‖ * M
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hbound {g : ℝ → E} (hg : Continuous g) :
      ‖e f‖ ≤ C * ∫ s in (0 : ℝ)..t, ‖f s - g s‖ := by
    let D := ∫ s in (0 : ℝ)..t, ‖f s - g s‖
    have hgi := hg.intervalIntegrable (μ := volume) 0 t
    have hduh : ‖(∫ s in (0 : ℝ)..t, S.duhamel f s) -
        (∫ s in (0 : ℝ)..t, S.duhamel g s)‖ ≤ M * D * t := by
      rw [← intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
        ((S.continuous_duhamel hg).intervalIntegrable _ _)]
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun s ↦ S.duhamel f s - S.duhamel g s) (a := 0) (b := t)
        (C := M * D) (fun s hs ↦ norm_duhamel_sub_le_integral_of_mem_Icc S hS
          (by rw [uIoc_of_le ht] at hs; exact Ioc_subset_Icc_self hs) hfi hgi)
      simpa only [sub_zero, abs_of_nonneg ht] using h
    have hforce : ‖(∫ s in (0 : ℝ)..t, f s) - (∫ s in (0 : ℝ)..t, g s)‖ ≤ D := by
      rw [← intervalIntegral.integral_sub hfi hgi]
      exact intervalIntegral.norm_integral_le_integral_norm ht
    have hend : ‖S.duhamel f t - S.duhamel g t‖ ≤ M * D :=
      norm_duhamel_sub_le_integral_of_integrable S hS ht hfi hgi
    have he : e f - e g =
        R ((∫ s in (0 : ℝ)..t, S.duhamel f s) - (∫ s in (0 : ℝ)..t, S.duhamel g s)) +
        Q ((∫ s in (0 : ℝ)..t, f s) - (∫ s in (0 : ℝ)..t, g s)) -
        Q (S.duhamel f t - S.duhamel g t) := by
      dsimp only [e]
      simp only [map_sub]
      abel
    rw [← sub_zero (e f), ← hz hg, he]
    calc
      _ ≤ ‖R ((∫ s in (0 : ℝ)..t, S.duhamel f s) - (∫ s in (0 : ℝ)..t, S.duhamel g s))‖ +
          ‖Q ((∫ s in (0 : ℝ)..t, f s) - (∫ s in (0 : ℝ)..t, g s))‖ +
          ‖Q (S.duhamel f t - S.duhamel g t)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖R‖ * (M * D * t) + ‖Q‖ * D + ‖Q‖ * (M * D) := add_le_add (add_le_add
          ((R.le_opNorm _).trans (mul_le_mul_of_nonneg_left hduh (norm_nonneg R)))
          ((Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left hforce (norm_nonneg Q))))
          ((Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left hend (norm_nonneg Q)))
      _ = C * D := by dsimp only [C]; cas
  have he : e f = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨g, hg, _⟩ := hfi.1.exists_boundedContinuous_integral_sub_le
      (div_pos hε (by positivity : 0 < C + 1))
    have hd : (∫ s in (0 : ℝ)..t, ‖f s - g s‖) ≤ ε / (C + 1) := by
      rwa [intervalIntegral.integral_of_le ht]
    have h := (hbound g.continuous).trans (mul_le_mul_of_nonneg_left hd hC)
    have hε' : C * (ε / (C + 1)) ≤ ε := by
      have hp : 0 < C + 1 := by positivity
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hp).mpr (by nlinarith)
    simpa only [zero_add] using h.trans hε'
  have hQi : IntervalIntegrable (fun s ↦ Q (f s)) volume 0 t :=
    ⟨Q.integrable_comp hfi.1, Q.integrable_comp hfi.2⟩
  have hRi : IntervalIntegrable (fun s ↦ R (S.duhamel f s)) volume 0 t :=
    (R.continuous.comp hc).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hRi hQi,
    R.intervalIntegral_comp_comm (hc.intervalIntegrable _ _), Q.intervalIntegral_comp_comm hfi]
  exact sub_eq_zero.mp he

/-- Every forced orbit with locally integrable forcing satisfies the integrated
observation equation, including its initial trace. -/
theorem observed_forced_integral_of_locallyIntegrable (S : StronglyContinuousSemigroup E) {M : ℝ}
    (hS : ∀ r, ‖S r‖ ≤ M) (Q R : E →L[ℝ] Z) (hdense : Dense (S.generatorPMap.domain : Set E))
    (hQR : ∀ x y, S.HasGeneratorAt x y → Q y = R x) {f : ℝ → E} (hf : LocallyIntegrable f volume)
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    let z := fun s ↦ S.realOrbit x s + S.duhamel f s; (∫ s in (0 : ℝ)..t, R (z s) + Q (f s)) =
      Q (z t) - Q x := by
  have hfi : IntervalIntegrable f volume 0 t := intervalIntegrable_iff.mpr
      ((hf.integrableOn_isCompact isCompact_uIcc).mono_set Ioc_subset_Icc_self)
  have hRi : IntervalIntegrable (fun s ↦ R (S.duhamel f s)) volume 0 t :=
    (R.continuous.comp (continuous_duhamel_of_locallyIntegrable S hS hf)).intervalIntegrable _ _
  have hQi : IntervalIntegrable (fun s ↦ Q (f s)) volume 0 t :=
    ⟨Q.integrable_comp hfi.1, Q.integrable_comp hfi.2⟩
  have hOi : IntervalIntegrable (fun s ↦ R (S.realOrbit x s)) volume 0 t :=
    (R.continuous.comp (S.continuous_realOrbit x)).intervalIntegrable _ _
  have ho := observed_orbit_integral S Q R hdense hQR x t.toNNReal
  rw [Real.coe_toNNReal _ ht] at ho
  dsimp only
  simp only [map_add, add_assoc]
  rw [intervalIntegral.integral_add hOi (hRi.add hQi), ho,
    observed_duhamel_integral_of_locallyIntegrable S hS Q R hdense hQR hf ht]
  change Q (S t.toNNReal x) - Q x + Q (S.duhamel f t) = Q (S t.toNNReal x) + Q (S.duhamel f t) - Q x
  abel

end PDE.Hyperbolic.NonlinearWave.Cauchy
