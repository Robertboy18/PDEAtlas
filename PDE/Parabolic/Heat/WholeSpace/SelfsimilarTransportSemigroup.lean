/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarTransportGain

/-!
# Self-similar evolution perturbed by an operator losing one derivative

Let `T` be a bounded operator from vector `Hᵏ⁺¹(ℝ³)` to vector `Hᵏ(ℝ³)`. The evolution `S` on
vector `Hᵏ` with generator `L₀ - Π T` is the gaining path with the gained derivative forgotten
at positive times, and the identity at time zero. Uniqueness of the fixed point of the Volterra
equation gives the semigroup law, and the free semigroup gives strong continuity at time zero.
The evolution solves the Duhamel equation
`S(t) u = S₀(t) u - ∫₀ᵗ Π S₀(t - s) T S(s) u ds`, has an exponential bound, gains one
derivative with the bound `C t^{-1/2} e^{ω t}`, and preserves fields fixed by the Leray
projection. The gain is jointly continuous in the time and the datum at positive times, since
its operator norm is locally bounded there.

If an operator `T'` from `Hᵏ⁺²` to `Hᵏ⁺¹` agrees with `T` once the top order is forgotten, the
evolution of `T'` on `Hᵏ⁺¹` is the restriction of the evolution of `T`. Forgetting the top order
is injective, so the evolution of `T'` continues the gaining path of `T`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution
open scoped NNReal Sobolev BoundedContinuousFunction

namespace HeatEquation.WholeSpace

variable {k : ℕ} (T : VectorH 3 (k + 1) →L[ℝ] VectorH 3 k)

/-! ### The evolution -/

/-- The evolution on vector `Hᵏ`: the identity at time zero, and at positive times the gaining
path with the gained derivative forgotten. -/
def transportEvolution (t : ℝ≥0) : VectorH 3 k →L[ℝ] VectorH 3 k :=
  if 0 < (t : ℝ) then (vectorLower 3 k).comp (transportGain T t) else ContinuousLinearMap.id ℝ _

/-- At time zero the evolution is the identity. -/
theorem transportEvolution_zero : transportEvolution T 0 = ContinuousLinearMap.id ℝ _ := by
  simp [transportEvolution]

/-- At positive times the evolution is the gaining path with the gained derivative
forgotten. -/
theorem transportEvolution_of_pos {t : ℝ≥0} (ht : 0 < (t : ℝ)) :
    transportEvolution T t = (vectorLower 3 k).comp (transportGain T t) :=
  ite_eq_left ht

/-- The evolution solves the Duhamel equation in vector `Hᵏ`, with the projected free
evolution as kernel. -/
private theorem transportEvolution_eq_lower {t : ℝ≥0} (ht : 0 < (t : ℝ)) (u : VectorH 3 k) :
    transportEvolution T t u = vectorSelfsimilarHeat 3 k t u -
      ∫ s in (0 : ℝ)..t, transportLowerKernel T (t - s) (transportGain T s u) := by
  rw [transportEvolution_of_pos T ht, ContinuousLinearMap.comp_apply,
    transportGain_eq_forwardDuhamel T ht, map_sub,
    vectorLower_vectorSelfsimilarHeatGainKernel ht, Real.toNNReal_coe, forwardDuhamel,
    ← (vectorLower 3 k).intervalIntegral_comp_comm (intervalIntegrable_transportKernel T ht.le u)]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (t : ℝ)] with s hst hs
  rw [uIoc_of_le ht.le] at hs
  exact vectorLower_transportKernel T (sub_pos.mpr (lt_of_le_of_ne hs.2 hst)) _

/-- The gaining path restarted at a positive time solves the Volterra identity with the
evolved datum. -/
theorem transportGain_add_forwardDuhamel {τ : ℝ} (hτ : 0 < τ) {s : ℝ≥0} (hs : 0 < (s : ℝ))
    (u : VectorH 3 k) :
    transportGain T (τ + s) u +
        ∫ r in (0 : ℝ)..τ, transportKernel T (τ - r) (transportGain T (r + s) u) =
      vectorSelfsimilarHeatGainKernel 3 k τ (transportEvolution T s u) := by
  have hτs : 0 < τ + s := by linarith
  have hint := intervalIntegrable_transportKernel T hτs.le u
  have hint1 : IntervalIntegrable
      (fun r ↦ transportKernel T (τ + s - r) (transportGain T r u)) volume 0 s :=
    hint.mono_set (by
      rw [uIcc_of_le hs.le, uIcc_of_le hτs.le]
      exact Icc_subset_Icc le_rfl (by linarith))
  have hint2 : IntervalIntegrable
      (fun r ↦ transportKernel T (τ + s - r) (transportGain T r u)) volume s (τ + s) :=
    hint.mono_set (by
      rw [uIcc_of_le (by linarith : (s : ℝ) ≤ τ + s), uIcc_of_le hτs.le]
      exact Icc_subset_Icc hs.le le_rfl)
  have hshift : (∫ r in (0 : ℝ)..τ, transportKernel T (τ - r) (transportGain T (r + s) u)) =
      ∫ r in (s : ℝ)..τ + s, transportKernel T (τ + s - r) (transportGain T r u) := by
    have h := intervalIntegral.integral_comp_add_right
      (fun r ↦ transportKernel T (τ + s - r) (transportGain T r u)) (s : ℝ) (a := 0) (b := τ)
    simp only [zero_add, add_sub_add_right_eq_sub] at h
    exact h
  have hfirst : (∫ r in (0 : ℝ)..s, transportKernel T (τ + s - r) (transportGain T r u)) =
      vectorSelfsimilarHeatGainKernel 3 k τ
        (∫ r in (0 : ℝ)..s, transportLowerKernel T (s - r) (transportGain T r u)) := by
    rw [← (vectorSelfsimilarHeatGainKernel 3 k τ).intervalIntegral_comp_comm
      (intervalIntegrable_transportLowerKernel T hs.le u)]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.le] at hr
    change transportKernel T (τ + s - r) _ = _
    rw [show τ + s - r = τ + (s - r) by ring, transportKernel_add T hτ (sub_nonneg.mpr hr.2)]
  have hduh := transportGain_eq_forwardDuhamel T hτs u
  rw [forwardDuhamel, ← intervalIntegral.integral_add_adjacent_intervals hint1 hint2] at hduh
  rw [hduh, hshift, transportEvolution_eq_lower T hs u, map_sub, ← hfirst,
    vectorSelfsimilarHeatGainKernel_add hτ hs.le, Real.toNNReal_coe]
  abel

/-- The gaining path at a time shifted by `s > 0` has the singular bound with the constant
`‖transportGainPath T u‖ e^{ω s}`. -/
theorem norm_transportGain_add_le {s : ℝ≥0} (hs : 0 < (s : ℝ)) (u : VectorH 3 k) {t : ℝ}
    (ht : 0 < t) :
    ‖transportGain T (t + s) u‖ ≤
      ‖transportGainPath T u‖ * Real.exp (transportWeight T * s) * t ^ (-(1 / 2 : ℝ)) *
        Real.exp (transportWeight T * t) := by
  have hts : 0 < t + s := add_pos ht hs
  have hroot : (t + s) ^ (-(1 / 2 : ℝ)) ≤ t ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
  have hexp : Real.exp (transportWeight T * (t + s)) =
      Real.exp (transportWeight T * s) * Real.exp (transportWeight T * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ‖transportGainPath T u‖ * (t + s) ^ (-(1 / 2 : ℝ)) *
        Real.exp (transportWeight T * (t + s)) := norm_transportGain_apply_le T hts u
    _ ≤ ‖transportGainPath T u‖ * t ^ (-(1 / 2 : ℝ)) *
        Real.exp (transportWeight T * (t + s)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (norm_nonneg _))
        (Real.exp_pos _).le
    _ = _ := by
      rw [hexp]
      ring

/-- The gaining path shifted by a positive time, as a bounded weighted path. -/
def transportGainPathShift {s : ℝ≥0} (hs : 0 < (s : ℝ)) (u : VectorH 3 k) :
    Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1) :=
  forwardEncode (transportWeight T) le_rfl (v := fun t ↦ transportGain T (t + s) u)
    ((continuousOn_transportGain_apply T u).comp (continuousOn_id.add continuousOn_const)
      fun _ ht ↦ add_pos ht hs)
    (fun _ ht ↦ norm_transportGain_add_le T hs u ht)

/-- The shifted path is the gaining path at `t + s` with the weight `√t e^{-ω t}`. -/
theorem transportGainPathShift_apply {s : ℝ≥0} (hs : 0 < (s : ℝ)) (u : VectorH 3 k)
    (t : Ioi (0 : ℝ)) :
    transportGainPathShift T hs u t =
      (Real.sqrt t * Real.exp (-(transportWeight T * t))) • transportGain T (t + s) u :=
  rfl

/-- Restarting at a positive time: the gaining path at `t + s` is the gaining path at `t` of
the evolved datum. -/
theorem transportGain_add {t : ℝ} (ht : 0 < t) {s : ℝ≥0} (hs : 0 < (s : ℝ)) (u : VectorH 3 k) :
    transportGain T (t + s) u = transportGain T t (transportEvolution T s u) := by
  have key : transportGainPathShift T hs u +
      transportVolterra T (transportGainPathShift T hs u) =
      vectorSelfsimilarHeatGainPath 3 k (transportWeight T) (lt_transportWeight T)
        (transportEvolution T s u) := by
    refine BoundedContinuousFunction.ext fun τ ↦ ?_
    have hτ : (0 : ℝ) < τ := τ.2
    have hdec : ∀ r ∈ uIoc (0 : ℝ) τ,
        transportKernel T (τ - r)
            (forwardDecode (transportWeight T) (transportGainPathShift T hs u) r) =
          transportKernel T (τ - r) (transportGain T (r + s) u) := by
      intro r hr
      rw [uIoc_of_le hτ.le] at hr
      rw [transportGainPathShift, forwardDecode_forwardEncode _ _ _ _ hr.1]
    rw [BoundedContinuousFunction.add_apply, transportGainPathShift_apply, transportVolterra_apply,
      vectorSelfsimilarHeatGainPath_apply, ← smul_add,
      ← transportGain_add_forwardDuhamel T hτ hs u,
      forwardDuhamel, intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hdec)]
  have h := congrArg (fun w : Ioi (0 : ℝ) →ᵇ VectorH 3 (k + 1) ↦ w ⟨t, ht⟩)
    (eq_transportGainPath T key)
  rw [transportGainPathShift_apply] at h
  rw [transportGain_apply T t, forwardDecode_of_pos _ _ ht, ← h, smul_smul,
    rpow_neg_one_half_mul_exp_mul_sqrt_mul_exp ht _, one_smul]

/-- The semigroup law of the evolution. -/
theorem transportEvolution_add (s t : ℝ≥0) :
    transportEvolution T (s + t) = (transportEvolution T s).comp (transportEvolution T t) := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [zero_add, transportEvolution_zero]
    rfl
  rcases eq_zero_or_pos t with rfl | ht
  · rw [add_zero, transportEvolution_zero]
    rfl
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  have hst : (0 : ℝ) < ((s + t : ℝ≥0) : ℝ) := by positivity
  apply ContinuousLinearMap.ext
  intro u
  rw [transportEvolution_of_pos T hst, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, transportEvolution_of_pos T hs',
    ContinuousLinearMap.comp_apply, NNReal.coe_add, transportGain_add T hs' ht' u]

/-- Near time zero the evolution stays within `C √t` of the free evolution. -/
theorem norm_transportEvolution_sub_le (t : ℝ≥0) (u : VectorH 3 k) :
    ‖transportEvolution T t u - vectorSelfsimilarHeat 3 k t u‖ ≤
      2 * (selfsimilarGraphConstant 3 k * ‖T‖) * ‖transportGainPath T u‖ *
        Real.exp (transportWeight T * t) * Real.sqrt t := by
  rcases eq_zero_or_pos t with rfl | ht
  · simp [transportEvolution_zero]
  have ht' : (0 : ℝ) < t := ht
  rw [transportEvolution_eq_lower T ht' u, sub_sub_cancel_left, norm_neg]
  exact norm_forwardDuhamel_le_of_bounded (fun r _ ↦ norm_transportLowerKernel_le T r)
    (fun _ hs ↦ norm_transportGain_apply_le T hs u) (transportWeight_pos T).le t.coe_nonneg

/-- The orbits of the evolution are continuous, including at time zero. -/
theorem continuous_transportEvolution (u : VectorH 3 k) :
    Continuous (fun t : ℝ≥0 ↦ transportEvolution T t u) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rcases eq_zero_or_pos t₀ with rfl | ht₀
  · have hfree : Tendsto (fun t : ℝ≥0 ↦ vectorSelfsimilarHeat 3 k t u) (𝓝 0) (𝓝 u) := by
      have h := (continuous_vectorSelfsimilarHeat (n := 3) (k := k) u).tendsto 0
      rwa [vectorSelfsimilarHeat_zero] at h
    have hbound : Continuous (fun t : ℝ≥0 ↦ 2 * (selfsimilarGraphConstant 3 k * ‖T‖) *
        ‖transportGainPath T u‖ * Real.exp (transportWeight T * t) * Real.sqrt t) := by
      fun_prop
    have hsmall : Tendsto
        (fun t : ℝ≥0 ↦ transportEvolution T t u - vectorSelfsimilarHeat 3 k t u)
        (𝓝 0) (𝓝 0) := by
      apply squeeze_zero_norm (fun t ↦ norm_transportEvolution_sub_le T t u)
      have h := hbound.tendsto 0
      simpa only [NNReal.coe_zero, Real.sqrt_zero, mul_zero] using h
    have h := hsmall.add hfree
    simp only [sub_add_cancel, zero_add] at h
    rw [ContinuousAt, transportEvolution_zero]
    exact h
  · have ht₀' : (0 : ℝ) < t₀ := ht₀
    have hev : (fun t : ℝ≥0 ↦ transportEvolution T t u) =ᶠ[𝓝 t₀]
        fun t : ℝ≥0 ↦ vectorLower 3 k (transportGain T t u) := by
      filter_upwards [lt_mem_nhds ht₀] with t ht
      rw [transportEvolution_of_pos T (NNReal.coe_pos.mpr ht)]
      rfl
    refine ContinuousAt.congr ?_ hev.symm
    have hc : ContinuousAt (fun t : ℝ ↦ transportGain T t u) t₀ :=
      (continuousOn_transportGain_apply T u).continuousAt (Ioi_mem_nhds ht₀')
    have hc' := ContinuousAt.comp (x := t₀) hc NNReal.continuous_coe.continuousAt
    exact (vectorLower 3 k).continuous.continuousAt.comp (x := t₀) hc'

/-! ### The semigroup -/

/-- The self-similar evolution perturbed by `-Π T`, as a strongly continuous semigroup on
vector `Hᵏ`. Its generator is `L₀ - Π T`. -/
def transportSemigroup : StronglyContinuousSemigroup (VectorH 3 k) where
  toMonoidHom :=
    { toFun := fun τ ↦ transportEvolution T τ.toAdd
      map_one' := transportEvolution_zero T
      map_mul' := fun s t ↦ transportEvolution_add T s.toAdd t.toAdd }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    exact continuous_transportEvolution T

/-- The semigroup acts by the evolution. -/
theorem transportSemigroup_apply (t : ℝ≥0) :
    transportSemigroup T t = transportEvolution T t :=
  rfl

/-- The Duhamel formula of the semigroup. The operator `T` loses one derivative, so it acts on
the gaining path in `Hᵏ⁺¹`; the projected free gain returns to `Hᵏ⁺¹`, and the integral is
lowered to `Hᵏ`. -/
theorem transportSemigroup_duhamel (t : ℝ≥0) (u : VectorH 3 k) :
    transportSemigroup T t u = vectorSelfsimilarHeatSemigroup 3 k t u -
      vectorLower 3 k (∫ s in (0 : ℝ)..t, projectedSelfsimilarHeatGainKernel 3 k (t - s)
        (T (transportGain T s u))) := by
  rcases eq_zero_or_pos t with rfl | ht
  · simp
  have ht' : (0 : ℝ) < t := ht
  rw [transportSemigroup_apply, transportEvolution_of_pos T ht', ContinuousLinearMap.comp_apply,
    transportGain_eq_forwardDuhamel T ht', map_sub, vectorLower_vectorSelfsimilarHeatGainKernel ht',
    Real.toNNReal_coe, vectorSelfsimilarHeatSemigroup_apply]
  rfl

/-- The Duhamel formula of the semigroup in vector `Hᵏ`, with the projected free evolution as
kernel. -/
theorem transportSemigroup_duhamel_lower (t : ℝ≥0) (u : VectorH 3 k) :
    transportSemigroup T t u = vectorSelfsimilarHeatSemigroup 3 k t u -
      ∫ s in (0 : ℝ)..t, leraySobolev 3 k (vectorSelfsimilarHeat 3 k (t - s).toNNReal
        (T (transportGain T s u))) := by
  rcases eq_zero_or_pos t with rfl | ht
  · simp
  rw [transportSemigroup_apply, transportEvolution_eq_lower T ht u,
    vectorSelfsimilarHeatSemigroup_apply]
  rfl

/-- At positive time the semigroup is the gaining path with the gained derivative
forgotten. -/
theorem vectorLower_comp_transportGain {t : ℝ≥0} (ht : 0 < t) :
    (vectorLower 3 k).comp (transportGain T t) = transportSemigroup T t :=
  (transportEvolution_of_pos T (NNReal.coe_pos.mpr ht)).symm

/-- The gaining path has the singular bound `C t^{-1/2} e^{ω t}` in operator norm. -/
theorem norm_transportGain_le {t : ℝ} (ht : 0 < t) :
    ‖transportGain T t‖ ≤
      transportGainConstant T * t ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T * t) := by
  have hw : 0 ≤ t ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T * t) :=
    mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  have hC := transportGainConstant_nonneg T
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    rw [mul_assoc]
    exact mul_nonneg hC hw)
  intro u
  calc
    _ ≤ ‖transportGainPath T u‖ * t ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T * t) :=
      norm_transportGain_apply_le T ht u
    _ ≤ (transportGainConstant T * ‖u‖) * t ^ (-(1 / 2 : ℝ)) *
        Real.exp (transportWeight T * t) := by
      rw [mul_assoc, mul_assoc (transportGainConstant T * ‖u‖)]
      exact mul_le_mul_of_nonneg_right (norm_transportGainPath_apply_le T u) hw
    _ = _ := by ring

/-- The action of the gaining path is jointly continuous in the time and the datum at positive
times. -/
theorem continuousOn_transportGain_apply_prod :
    ContinuousOn (fun p : ℝ × VectorH 3 k ↦ transportGain T p.1 p.2) (Ioi 0 ×ˢ univ) := by
  intro p hp
  have hp1 : 0 < p.1 := hp.1
  set B := transportGainConstant T * (p.1 / 2) ^ (-(1 / 2 : ℝ)) *
    Real.exp (transportWeight T * (p.1 + 1)) with hB
  have hbound : ∀ r, p.1 / 2 < r → r < p.1 + 1 → ‖transportGain T r‖ ≤ B := by
    intro r h1 h2
    have hr : 0 < r := lt_trans (half_pos hp1) h1
    refine (norm_transportGain_le T hr).trans ?_
    have hroot : r ^ (-(1 / 2 : ℝ)) ≤ (p.1 / 2) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (half_pos hp1) h1.le (by norm_num)
    have hexp : Real.exp (transportWeight T * r) ≤ Real.exp (transportWeight T * (p.1 + 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2.le (transportWeight_pos T).le)
    have hC := transportGainConstant_nonneg T
    calc
      _ ≤ transportGainConstant T * (p.1 / 2) ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T * r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot hC) (Real.exp_pos _).le
      _ ≤ B := mul_le_mul_of_nonneg_left hexp
        (mul_nonneg hC (Real.rpow_nonneg (half_pos hp1).le _))
  have hnear : ∀ᶠ q : ℝ × VectorH 3 k in 𝓝 p, p.1 / 2 < q.1 ∧ q.1 < p.1 + 1 :=
    (continuous_fst.continuousAt.eventually (lt_mem_nhds (half_lt_self hp1))).and
      (continuous_fst.continuousAt.eventually (gt_mem_nhds (lt_add_one p.1)))
  apply ContinuousAt.continuousWithinAt
  change Tendsto (fun q : ℝ × VectorH 3 k ↦ transportGain T q.1 q.2) (𝓝 p)
    (𝓝 (transportGain T p.1 p.2))
  have hsmall :
      Tendsto (fun q : ℝ × VectorH 3 k ↦ transportGain T q.1 (q.2 - p.2)) (𝓝 p) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun q : ℝ × VectorH 3 k ↦ B * ‖q.2 - p.2‖) ?_ ?_
    · filter_upwards [hnear] with q hq
      exact (transportGain T q.1).le_of_opNorm_le (hbound q.1 hq.1 hq.2) (q.2 - p.2)
    · have hcont : Continuous (fun q : ℝ × VectorH 3 k ↦ B * ‖q.2 - p.2‖) :=
        (continuous_snd.sub continuous_const).norm.const_mul B
      simpa only [sub_self, norm_zero, mul_zero] using hcont.tendsto p
  have horbit : Tendsto (fun q : ℝ × VectorH 3 k ↦ transportGain T q.1 p.2) (𝓝 p)
      (𝓝 (transportGain T p.1 p.2)) :=
    ((continuousOn_transportGain_apply T p.2).continuousAt (Ioi_mem_nhds hp1)).tendsto.comp
      continuous_fst.continuousAt.tendsto
  simpa only [map_sub, sub_add_cancel, zero_add] using hsmall.add horbit

/-- The semigroup gains one derivative with the bound `C t^{-1/2} e^{ω t}`. -/
theorem transportSemigroup_exists_gain :
    ∃ C ω : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0, 0 < t →
      ∃ G : VectorH 3 k →L[ℝ] VectorH 3 (k + 1),
        (vectorLower 3 k).comp G = transportSemigroup T t ∧
          ‖G‖ ≤ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t) :=
  ⟨transportGainConstant T, transportWeight T, transportGainConstant_nonneg T,
    fun t ht ↦ ⟨transportGain T t, vectorLower_comp_transportGain T ht,
      norm_transportGain_le T (NNReal.coe_pos.mpr ht)⟩⟩

/-- The semigroup has an exponential bound. -/
theorem transportSemigroup_exists_norm_le :
    ∃ M ω : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, ‖transportSemigroup T t‖ ≤ M * Real.exp (ω * t) := by
  have hL := mul_nonneg (selfsimilarGraphConstant_nonneg 3 k) (norm_nonneg T)
  have hS := selfsimilarGraphConstant_nonneg 3 k
  have hW := transportGainConstant_nonneg T
  have hω := (transportWeight_pos T).le
  refine ⟨selfsimilarGraphConstant 3 k +
      2 * (selfsimilarGraphConstant 3 k * ‖T‖) * transportGainConstant T,
    transportWeight T + 1, by positivity, fun t ↦ ?_⟩
  have ht := t.coe_nonneg
  have hsqrt : Real.sqrt t ≤ Real.exp t := by
    calc
      Real.sqrt t ≤ (t : ℝ) + 1 := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      _ ≤ Real.exp t := by linarith [Real.add_one_le_exp (t : ℝ)]
  have hexp1 : 1 ≤ Real.exp ((transportWeight T + 1) * t) :=
    Real.one_le_exp (by positivity)
  have hexp2 : Real.exp (transportWeight T * t) * Real.sqrt t ≤
      Real.exp ((transportWeight T + 1) * t) := by
    rw [add_mul, one_mul, Real.exp_add]
    gcongr
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  have h1 := norm_transportEvolution_sub_le T t u
  have h2 := norm_vectorSelfsimilarHeat_le_of_two_le (by norm_num) t u
  have h3 := norm_transportGainPath_apply_le T u
  rw [transportSemigroup_apply]
  calc
    _ ≤ ‖vectorSelfsimilarHeat 3 k t u‖ +
        ‖transportEvolution T t u - vectorSelfsimilarHeat 3 k t u‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ selfsimilarGraphConstant 3 k * ‖u‖ +
        2 * (selfsimilarGraphConstant 3 k * ‖T‖) * (transportGainConstant T * ‖u‖) *
          Real.exp (transportWeight T * t) * Real.sqrt t := add_le_add h2 (h1.trans (by gcongr))
    _ ≤ selfsimilarGraphConstant 3 k * ‖u‖ * Real.exp ((transportWeight T + 1) * t) +
        2 * (selfsimilarGraphConstant 3 k * ‖T‖) * (transportGainConstant T * ‖u‖) *
          Real.exp ((transportWeight T + 1) * t) := by
      rw [mul_assoc _ (Real.exp _)]
      exact add_le_add (le_mul_of_one_le_right (by positivity) hexp1)
        (mul_le_mul_of_nonneg_left hexp2 (by positivity))
    _ = _ := by ring

/-- The semigroup preserves fields fixed by the Leray projection. -/
theorem leraySobolev_transportSemigroup (t : ℝ≥0) {u : VectorH 3 k}
    (hu : leraySobolev 3 k u = u) :
    leraySobolev 3 k (transportSemigroup T t u) = transportSemigroup T t u := by
  rcases eq_zero_or_pos t with rfl | ht
  · rw [transportSemigroup_apply, transportEvolution_zero]
    exact hu
  have ht' : (0 : ℝ) < t := ht
  rw [transportSemigroup_apply, transportEvolution_eq_lower T ht' u, map_sub,
    leraySobolev_vectorSelfsimilarHeat, hu,
    ← (leraySobolev 3 k).intervalIntegral_comp_comm
      (intervalIntegrable_transportLowerKernel T ht'.le u)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [transportLowerKernel_apply, leraySobolev_idempotent]

/-! ### Restriction to the next order -/

section Restriction

variable (T' : VectorH 3 (k + 2) →L[ℝ] VectorH 3 (k + 1))
  (hT : ∀ v, vectorLower 3 k (T' v) = T (vectorLower 3 (k + 1) v))
include hT

/-- The evolution of `T'` on `Hᵏ⁺¹` is the restriction of the evolution of `T` on `Hᵏ`. -/
theorem vectorLower_transportSemigroup (t : ℝ≥0) (u : VectorH 3 (k + 1)) :
    vectorLower 3 k (transportSemigroup T' t u) = transportSemigroup T t (vectorLower 3 k u) := by
  rcases eq_zero_or_pos t with rfl | ht
  · simp
  have ht' : (0 : ℝ) < t := ht
  rw [transportSemigroup_apply, transportSemigroup_apply, transportEvolution_of_pos T' ht',
    transportEvolution_of_pos T ht', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ← vectorLower_transportGain T T' hT ht' u]

/-- The evolution of `T'` on `Hᵏ⁺¹`, applied after the gaining path of `T` at a positive time,
continues the gaining path. -/
theorem transportSemigroup_transportGain (t : ℝ≥0) {s : ℝ} (hs : 0 < s) (u : VectorH 3 k) :
    transportSemigroup T' t (transportGain T s u) = transportGain T (t + s) u := by
  apply vectorLower_injective 3 k
  have hts : 0 < (t : ℝ) + s := add_pos_of_nonneg_of_pos t.coe_nonneg hs
  have hgain (r : ℝ) (hr : 0 < r) : vectorLower 3 k (transportGain T r u) =
      transportSemigroup T r.toNNReal u := by
    rw [← vectorLower_comp_transportGain T (Real.toNNReal_pos.mpr hr),
      ContinuousLinearMap.comp_apply, Real.coe_toNNReal _ hr.le]
  rw [vectorLower_transportSemigroup T T' hT, hgain s hs, hgain _ hts,
    ← StronglyContinuousSemigroup.map_add_apply, Real.toNNReal_add t.coe_nonneg hs.le,
    Real.toNNReal_coe]

end Restriction

end HeatEquation.WholeSpace
