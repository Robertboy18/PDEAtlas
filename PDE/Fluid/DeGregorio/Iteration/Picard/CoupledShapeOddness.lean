/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.CoupledShapeRepresentative
public import PDE.Fluid.DeGregorio.Characteristics.Rescaled.Oddness
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Parity
public import PDE.Analysis.MeasureTheory.Lp.Primitive.Parity

/-!
# Oddness of the coupled H² solution on the closed slab

Reflection and the coupled interior energy estimate use spatial C¹ velocity
slices. The constructed continuous traces extend the comparison to both
endpoints. Oddness of the Hilbert input is a conclusion.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution PDE.Common DeGregorio
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
  {F : C(Icc (0 : ℝ) T,
    supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}

/-- The coupled solution inherits odd vorticity from its datum on the entire
closed interval. -/
theorem IsHkFrozenOutput.odd_vorticity_on_Icc
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hodd : Function.Odd w₀)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Function.Odd (fun x ↦ w x t) := by
  let fields : Fields := ⟨w, hkCurveHilbertVelocity hT F⟩
  let other := DeGregorio.reflectedFields fields
  let L := max R 0 + 1
  have hL : 0 < L := (le_max_right R 0).trans_lt (lt_add_one _)
  have hRL : R < L := (le_max_left R 0).trans_lt (lt_add_one _)
  have hwtime (x : ℝ) : ContinuousOn (w x) (Icc 0 T) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (h.continuous.comp (continuous_const.prodMk continuous_id))
  have hsupp (s : ℝ) (hs : s ∈ Icc 0 T) (x : ℝ) (hx : x ∉ Ioo (-L) L) :
      other.vorticity x s = 0 ∧ fields.vorticity x s = 0 := by
    have hRx : R < |x| := hRL.trans_le (le_of_not_gt fun ha ↦ hx (abs_lt.mp ha))
    exact ⟨by
      change -w (-x) s = 0
      rw [h.support (-x) s hs (by simpa only [abs_neg] using hRx), neg_zero],
      h.support x s hs hRx⟩
  have htrace : ContinuousOn (differenceEnergy other fields L) (Icc 0 T) := by
    apply continuousOn_integral_sq_Icc_of_traces
      (f := fun x s ↦ other.vorticity x s - fields.vorticity x s) (C := 4 * (B : ℝ))
    · intro s hs
      have hc := (h.contDiff_vorticity_on_Icc hs).continuous
      exact (hc.comp continuous_neg).neg.sub hc
    · intro x
      exact (hwtime (-x)).neg.sub (hwtime x)
    · intro s hs x
      change |-w (-x) s - w x s| ≤ _
      have hb := abs_sub (-w (-x) s) (w x s)
      rw [abs_neg] at hb
      have hneg := (h.spatial_bounds ⟨s, hs⟩ (-x)).1
      have hpos := (h.spatial_bounds ⟨s, hs⟩ x).1
      simp only [Real.norm_eq_abs] at hneg hpos
      linarith
  have hinitial : differenceEnergy other fields L 0 = 0 := by
    have hi (x : ℝ) : other.vorticity x 0 = fields.vorticity x 0 := by
      simp only [fields, other, DeGregorio.reflectedFields, h.initial, hodd x, neg_neg]
    simp only [differenceEnergy, hi, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero]
  have henergy := differenceEnergy_eq_zero_of_same_initialData_interior
    (fields := other) (other := fields) (contDiffOn_neg_reflect_slab h.classical)
    h.classical (fun s _ ↦ ((h.contDiff_velocity s).comp contDiff_neg).neg)
    (fun s _ ↦ h.contDiff_velocity s) h.isClassicalSolutionOn.reflectedFields
    h.isClassicalSolutionOn hL.le (by positivity : 0 ≤ 2 * (B : ℝ))
    (fun s hs ↦ hsupp s (Ioo_subset_Icc_self hs)) (by
      intro s _
      simp only [fields, other, DeGregorio.reflectedFields, neg_zero,
        hkCurveHilbertVelocity, l2Primitive, intervalIntegral.integral_same]) (by
      intro s hs x _
      have hb := h.spatial_bounds ⟨s, Ioo_subset_Icc_self hs⟩ x
      change |deriv (fun y ↦ (DeGregorio.reflectedFields fields).velocity y s) x| ≤ _ ∧ _
      rw [deriv_reflectedFields_velocity]
      change |deriv (fun y ↦ hkCurveHilbertVelocity hT F y s) (-x)| ≤ _ ∧ _
      rw [(h.velocity_derivative (-x) s).deriv]
      exact ⟨h.coefficient_bound (-x) s, hb⟩) htrace hinitial
  have hpoint := eq_zero_on_Icc_of_integral_sq_eq_zero
    (neg_lt_self hL) (((h.contDiff_vorticity_on_Icc ht).continuous.comp
      continuous_neg).neg.sub (h.contDiff_vorticity_on_Icc ht).continuous) (henergy t ht)
  intro x
  by_cases hx : x ∈ Icc (-L) L
  · have he := sub_eq_zero.mp (hpoint x hx)
    change -w (-x) t = w x t at he
    exact neg_eq_iff_eq_neg.mp he
  · have hz := hsupp t ht x (fun hi ↦ hx ⟨hi.1.le, hi.2.le⟩)
    change -w (-x) t = 0 ∧ w x t = 0 at hz
    simpa only [hz.2, neg_zero] using neg_eq_zero.mp hz.1

/-- The output's oddness makes the spectral input odd and hence gives
an odd normalized velocity and an even coefficient, also at the endpoints. -/
theorem IsHkFrozenOutput.odd_velocity_even_coefficient_on_Icc
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hodd : Function.Odd w₀)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Function.Odd (fun x ↦ hkCurveHilbertVelocity hT F x t) ∧
      Function.Even (fun x ↦ c x t) := by
  have hwodd := h.odd_vorticity_on_Icc hodd ht
  have hp := isHilbertPair_realHilbertTransformL2
    (oneDimensionalPushforwardL2 (F (projIcc 0 T hT t)).val)
  rw [projIcc_of_mem hT ht] at hp
  have hpair := hp.congr_ae (h.representative ⟨t, ht⟩) EventuallyEq.rfl
  refine ⟨?_, (h.hilbert_pair_self_on_Icc ht).even_of_ae_odd
    (.of_forall hwodd) (h.coefficient_continuous.comp
      (continuous_id.prodMk continuous_const))⟩
  change Function.Odd (l2Primitive (realHilbertTransformL2
    (oneDimensionalPushforwardL2 (F (projIcc 0 T hT t)).val)))
  rw [projIcc_of_mem hT ht]
  exact odd_l2Primitive_of_ae_even _ (hpair.ae_even_of_ae_odd (.of_forall hwodd))

end DeGregorio.Iteration
