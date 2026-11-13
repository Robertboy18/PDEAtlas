/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Derivative.Source
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Pullback.FirstOrder
public import PDE.Fluid.DeGregorio.Iteration.Derivative.Pullback
public import PDE.Analysis.Evolution.Core.Gronwall
import PDE.Spaces.Sobolev.GraphSpace.RealLine.WeightedEnergy

/-!
# H¹ estimates and uniqueness for the derivative evolution

The existing spatial derivative belongs to H¹. Uniqueness must therefore be
proved in that space before the constructed H² derivative can be identified
with it. The weak chain rule and the existing multiplier theorem supply the
two bounded operations needed for this comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Sobolev
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The characteristic coordinates preserve H¹ with one uniform
bound. This applies to the original derivative before higher regularity has
been established. -/
theorem HkCharacteristics.exists_h1_pullbacks
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} {hT : 0 ≤ T}
    {f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)}
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkCharacteristics hT f c X Y) :
    ∃ P Q : Icc (0 : ℝ) T → W^{1,2}(ℝ^1) → W^{1,2}(ℝ^1),
      (∀ t V, realLineRepresentative (P t V) =
        fun x ↦ realLineRepresentative V (X x t)) ∧
      (∀ t V, realLineRepresentative (Q t V) =
        fun x ↦ realLineRepresentative V (Y x t)) ∧
      ∃ C ≥ 0, ∀ t V, ‖P t V‖ ≤ C * ‖V‖ ∧ ‖Q t V‖ ≤ C * ‖V‖ := by
  let M := Real.exp (2 * (B : ℝ) * T)
  have hM : 0 ≤ M := Real.exp_nonneg _
  let C := Real.sqrt M * (1 + M)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hex (t : Icc (0 : ℝ) T) (V : W^{1,2}(ℝ^1)) :
      ∃ U W : W^{1,2}(ℝ^1),
        realLineRepresentative U = (fun x ↦ realLineRepresentative V (X x t)) ∧
        realLineRepresentative W = (fun x ↦ realLineRepresentative V (Y x t)) ∧
        ‖U‖ ≤ C * ‖V‖ ∧ ‖W‖ ≤ C * ‖V‖ := by
    let J : ℝ → ℝ := fun x ↦ Real.exp (∫ s in 0..(t : ℝ), c (X x s) s)
    have hJ := (contDiff_one_hkCurve_jacobian_slice hT f
      hchar.toHkForwardCharacteristics t.property).continuous
    have hJbound (x : ℝ) : ‖J x‖ ≤ M :=
      norm_exp_integral_flow_le hchar.coefficient_bound x t t.property
    let e := hchar.inverseHomeomorph t
    have hXderiv (x : ℝ) : HasDerivAt e.symm (J x) x :=
      hasDerivAt_hkCurve_hilbert_flow_space hT f hchar.velocity_derivative
        hchar.flow_initial hchar.flow_derivative x t t.property
    have helip : LipschitzWith ⟨M, hM⟩ e.symm :=
      lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (hXderiv x).differentiableAt) fun x ↦
        show ‖deriv e.symm x‖ ≤ M from (hXderiv x).deriv ▸ hJbound x
    obtain ⟨U, hU, hUnorm⟩ := exists_h1_comp_of_bounded_positive_jacobian e.symm
      (hchar.inverse_lipschitz t t.property) hJ (fun x ↦ Real.exp_nonneg _)
      hXderiv hJbound V
    let I : ℝ → ℝ := fun y ↦ (J (e y))⁻¹
    have hI : Continuous I := (hJ.comp e.continuous).inv₀
      (fun y ↦ Real.exp_ne_zero _)
    have hederiv (y : ℝ) : HasDerivAt e (I y) y :=
      hasDerivAt_hkCurve_inverse_space hT f hchar.velocity_derivative
        hchar.flow_initial hchar.flow_derivative hchar.inverse_continuous
        hchar.flow_inverse y t t.property
    have hIbound (y : ℝ) : ‖I y‖ ≤ M :=
      (hederiv y).deriv ▸ norm_deriv_le_of_lipschitz (hchar.inverse_lipschitz t t.property)
    obtain ⟨W, hW, hWnorm⟩ := exists_h1_comp_of_bounded_positive_jacobian e helip hI
      (fun _ ↦ inv_nonneg.mpr (Real.exp_nonneg _)) hederiv hIbound V
    exact ⟨U, W, hU, hW, hUnorm, hWnorm⟩
  choose P Q hP hQ hPnorm hQnorm using hex
  exact ⟨P, Q, hP, hQ, C, hC, fun t V ↦ ⟨hPnorm t V, hQnorm t V⟩⟩

/-- The source `ω Hq` is bounded in H¹ for an H² coefficient and an H¹
unknown. This is the lower-order estimate needed for uniqueness. -/
theorem exists_h1_firstDerivativeSource (W : W^{2,2}(ℝ^1)) (Q : W^{1,2}(ℝ^1)) :
    ∃ S : W^{1,2}(ℝ^1),
      realLineRepresentative S =
        (fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) x *
          realLineRepresentative (realHilbertH1 Q) x) ∧
      ‖S‖ ≤ 12 * ‖W‖ * ‖Q‖ := by
  let m := realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W)
  obtain ⟨hm, hmbound⟩ := contDiff_and_bounds_of_h2_representative W
    (continuous_realLineRepresentative _) (realLineRepresentative_lowerOrder_ae W)
  obtain ⟨S, hSnorm, hSrep, _hSrow⟩ := exists_h1_mul_of_bounded_c1 (realHilbertH1 Q)
    hm.continuous (hm.continuous_deriv le_rfl)
    (fun x ↦ (hm.differentiable one_ne_zero x).hasDerivAt)
    (fun x ↦ (hmbound x).1) (fun x ↦ (hmbound x).2)
  refine ⟨S, ?_, hSnorm.trans ?_⟩
  · simpa only [mul_comm] using hSrep
  · have hb := (norm_realLineCoordinateCLM_le (baseIndex 1 1) (realHilbertH1 Q)).trans
      (norm_realHilbertH1_le Q)
    have hd := (norm_realLineCoordinateCLM_le (singleDerivIndex 1 0)
      (realHilbertH1 Q)).trans (norm_realHilbertH1_le Q)
    calc
      _ ≤ (2 * ‖W‖ + 2 * ‖W‖) * (2 * ‖Q‖) + 2 * ‖W‖ * (2 * ‖Q‖) := by
        gcongr
      _ = _ := by ring

/-- The H¹ source graphs are measurable when their coefficient and unknown
graphs are measurable. The proof uses the canonical pointwise product. -/
theorem stronglyMeasurable_h1_firstDerivativeSource
    {T : Type*} [MeasurableSpace T]
    {W : T → W^{2,2}(ℝ^1)} {Q S : T → W^{1,2}(ℝ^1)}
    (hW : StronglyMeasurable W) (hQ : StronglyMeasurable Q)
    (hS : ∀ t, realLineRepresentative (S t) =
      fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) x *
        realLineRepresentative (realHilbertH1 (Q t)) x) :
    StronglyMeasurable S := by
  have hm : StronglyMeasurable
      (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (W t)) :=
    (lowerOrderCLM (by decide : 1 ≤ 2)).continuous.comp_stronglyMeasurable hW
  have hh : StronglyMeasurable (fun t ↦ realHilbertH1 (Q t)) :=
    continuous_realHilbertH1.comp_stronglyMeasurable hQ
  have hrep := (stronglyMeasurable_realLineRepresentative hm).mul
    (stronglyMeasurable_realLineRepresentative hh)
  apply stronglyMeasurable_hk_of_joint_representative S
    (v := fun t x ↦
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) x *
        realLineRepresentative (realHilbertH1 (Q t)) x) hrep
  intro t
  exact (realLineCoordinate_ae_representative (S t)).trans
    (Filter.EventuallyEq.of_eq (hS t))

/-- The homogeneous derivative equation along the flow has only the
zero solution among bounded measurable H¹ graphs. Graph continuity follows
from the integral equation; it is not a separate assumption. -/
theorem HkCharacteristics.eq_zero_of_h1_firstDerivative_integral
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} {hT : 0 ≤ T}
    {f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)}
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkCharacteristics hT f c X Y)
    {W : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hW : StronglyMeasurable W)
    (hWnorm : ∀ t, ‖W t‖ ≤ B)
    {q : Icc (0 : ℝ) T → W^{1,2}(ℝ^1)} (hq : StronglyMeasurable q)
    (hqbound : ∃ D ≥ 0, ∀ t, ‖q t‖ ≤ D)
    (heq : ∀ a (t : Icc (0 : ℝ) T),
      realLineRepresentative (q t) (X a t) =
        ∫ s in 0..(t : ℝ),
          realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
            (W (projIcc 0 T hT s))) (X a s) *
          realLineRepresentative (realHilbertH1 (q (projIcc 0 T hT s))) (X a s)) :
    ∀ t, q t = 0 := by
  obtain ⟨P, Q, hP, hQ, C, hC, hnorm⟩ := hchar.exists_h1_pullbacks
  have hXm : Measurable (Function.uncurry (fun (t : Icc (0 : ℝ) T) x ↦ X x t)) :=
    (hchar.flow_continuous.comp continuous_swap).measurable
  choose S hSrep hSnorm using fun t ↦ exists_h1_firstDerivativeSource (W t) (q t)
  have hSm : StronglyMeasurable S :=
    stronglyMeasurable_h1_firstDerivativeSource hW hq hSrep
  let G (t : Icc (0 : ℝ) T) := P t (q t)
  let H (t : Icc (0 : ℝ) T) := P t (S t)
  have hHm : StronglyMeasurable H :=
    stronglyMeasurable_h1_pullback hXm (fun t ↦ hP t (S t)) hSm
  have hHbound (t : Icc (0 : ℝ) T) : ‖H t‖ ≤ C * (12 * (B : ℝ) * ‖q t‖) :=
    (hnorm t (S t)).1.trans <| mul_le_mul_of_nonneg_left
      ((hSnorm t).trans (by gcongr; exact hWnorm t)) hC
  obtain ⟨D, hD, hqnorm⟩ := hqbound
  let Hext (s : ℝ) := H (projIcc 0 T hT s)
  have hHint : IntegrableOn Hext (Icc (0 : ℝ) T) volume := by
    apply (integrableOn_const (C := C * (12 * (B : ℝ) * D))
      (hs := measure_Icc_lt_top.ne)).mono'
      ((hHm.comp_measurable continuous_projIcc.measurable).aestronglyMeasurable.restrict)
    filter_upwards with s
    exact (hHbound _).trans (by gcongr; exact hqnorm _)
  have hInt (t : Icc (0 : ℝ) T) : IntervalIntegrable Hext volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le t.property.1).mpr
      (hHint.mono_set (Icc_subset_Icc_right t.property.2))
  have hGint (t : Icc (0 : ℝ) T) : G t = ∫ s in 0..(t : ℝ), Hext s := by
    apply realLineRepresentative_injective
    funext a
    change realLineRepresentative (P t (q t)) a = _
    rw [hP]
    change realLineRepresentative (q t) (X a t) = _
    rw [heq]
    have hEval := (realLineRepresentativeEvalCLM a).intervalIntegral_comp_comm (hInt t)
    change _ = realLineRepresentativeEvalCLM a (∫ s in 0..(t : ℝ), Hext s)
    rw [← hEval]
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) T := (uIcc_subset_Icc ⟨le_rfl, hT⟩ t.property) hs
    simp only [Hext, H, projIcc_of_mem hT hsI]
    change _ = realLineRepresentative (P ⟨s, hsI⟩ (S ⟨s, hsI⟩)) a
    rw [hP, hSrep]
  have hqG (t : Icc (0 : ℝ) T) : ‖q t‖ ≤ C * ‖G t‖ := by
    have hid : Q t (G t) = q t := by
      apply realLineRepresentative_injective
      funext x
      rw [hQ]
      change realLineRepresentative (P t (q t)) (Y x t) = _
      rw [hP]
      change realLineRepresentative (q t) (X (Y x t) t) = _
      rw [hchar.flow_inverse x t t.property]
    exact hid ▸ (hnorm t (G t)).2
  let K := C * (12 * (B : ℝ)) * C
  have hHG (t : Icc (0 : ℝ) T) : ‖H t‖ ≤ K * ‖G t‖ := (hHbound t).trans <| by
    calc _ ≤ C * (12 * (B : ℝ) * (C * ‖G t‖)) := by gcongr; exact hqG t
      _ = _ := by ring
  have hGzero : ∀ t, G t = 0 := by
    have hzero := eq_zero_on_of_eq_intervalIntegral_of_norm_le hT
      (hInt ⟨T, hT, le_rfl⟩)
      (u := fun s ↦ G (projIcc 0 T hT s))
      (K := K)
      (fun t ht ↦ by simpa only [projIcc_of_mem hT ht] using hGint ⟨t, ht⟩)
      (fun t ht ↦ by
        simpa only [Hext, projIcc_of_mem hT ht] using hHG ⟨t, ht⟩)
    intro t
    simpa only [projIcc_of_mem hT t.property] using hzero t t.property
  exact fun t ↦ norm_le_zero_iff.mp (by simpa only [hGzero t, norm_zero, mul_zero] using hqG t)


end DeGregorio.Iteration
