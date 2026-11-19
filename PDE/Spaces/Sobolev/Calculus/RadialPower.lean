/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module
public import PDE.Analysis.MeasureTheory.Lp.RadialPower.Cutoff
public import PDE.DistributionTheory.TestFunction.CompactCutoff
public import PDE.Spaces.Sobolev.Calculus.Composition.Lipschitz
public import PDE.Spaces.Sobolev.Calculus.IsolatedPoint
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Sobolev membership of truncated singular radial powers

On `ℝ^(n+1)` with `n ≥ 1`, the function `φ(x) ‖x‖^a`, with `φ` a compactly supported `C¹`
cutoff, lies in `W^{1,p}` for finite `p ≥ 1` when both `‖x‖^a` and its gradient are
`p`-integrable near the origin, that is, `-a p < n + 1` and `-(a - 1) p < n + 1`. For `a < 0`
the truncation `max (‖x‖^a - 1) 0` lies in `W^{1,p}` under the second condition. The weak
derivatives are obtained by removing the origin with the ACL converse.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

/-- A compactly cut off radial power determines an actual Sobolev element.
The weak derivatives are obtained by removing the origin through the ACL converse. -/
theorem exists_w1p_mul_norm_rpow
    {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {φ : ℝ^(n + 1) → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    {a : ℝ} (ha : -a * p.toReal < (n + 1 : ℕ))
    (ha' : -(a - 1) * p.toReal < (n + 1 : ℕ)) :
    ∃ U : W^{1,p}(ℝ^(n + 1)),
      baseRepresentative U =ᵐ[volume] (fun x ↦ φ x * ‖x‖ ^ a) := by
  let f : ℝ^(n + 1) → ℝ := fun x ↦ φ x * ‖x‖ ^ a
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hd : 1 ≤ Module.finrank ℝ (ℝ^(n + 1)) := by simp
  have hLp : MemLp f p volume := hφ.continuous.memLp_mul_norm_rpow_of_hasCompactSupport
    hφc hd hp0 hp (by simpa using ha)
  have hD : MemLp (fderiv ℝ f) p volume :=
    hφ.memLp_fderiv_mul_norm_rpow_of_hasCompactSupport hφc hd hp0 hp
      (by simpa using ha) (by simpa using ha')
  have hc : HasCompactSupport f := hφc.mul_right
  have hfi : Integrable f := memLp_one_iff_integrable.mp
    (hLp.mono_exponent_of_measure_support_ne_top
      (fun _ hx ↦ image_eq_zero_of_notMem_tsupport hx) hc.measure_lt_top.ne Fact.out)
  have hpartial (i : Fin (n + 1)) : MemLp (∂[i] f) p volume := by
    refine hD.norm.mono' (measurable_fderiv_apply_const ℝ f
      (EuclideanSpace.single i (1 : ℝ))).aestronglyMeasurable ?_
    apply Filter.Eventually.of_forall
    intro x
    simpa [partialDeriv] using
      (fderiv ℝ f x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
  have hweak (i : Fin (n + 1)) : HasWeakDerivativeOn univ [i] f (∂[i] f) := by
    have : NeZero n := ⟨(Fact.out : 0 < n).ne'⟩
    refine hasWeakDerivativeOn_partialDeriv_of_contDiffAt_off_point 0 ?_
      (hfi.locallyIntegrable.locallyIntegrableOn univ) i ?_
    · intro x hx
      exact hφ.contDiffAt.mul
        ((contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx))
    · exact (memLp_one_iff_integrable.mp
        ((hpartial i).mono_exponent_of_measure_support_ne_top
          (fun _ hx ↦ image_eq_zero_of_notMem_tsupport hx)
          (hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))).measure_lt_top.ne
          Fact.out)).locallyIntegrable.locallyIntegrableOn univ
  have hb : MemLp f p (domainMeasure (n + 1) univ) := by simpa using hLp
  have hrow (i : Fin (n + 1)) : MemLp (∂[i] f) p (domainMeasure (n + 1) univ) := by
    simpa using hpartial i
  obtain ⟨U, hU, _⟩ := exists_of_weakDerivative_coordinates
    (hb.toLp f) (fun i ↦ (hrow i).toLp (∂[i] f))
    (fun i ↦ (hweak i).congr_ae hb.coeFn_toLp.symm (hrow i).coeFn_toLp.symm)
  refine ⟨U, ?_⟩
  change (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → ℝ) =ᵐ[volume] f
  rw [hU]
  simpa using hb.coeFn_toLp

/-- Negative radial powers truncated at level one lie in `W¹ᵖ` when their
classical first derivative has locally integrable `p`th power. -/
theorem exists_w1p_posPart_norm_rpow_sub_one
    {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {a : ℝ} (ha : a < 0) (hd : -(a - 1) * p.toReal < (n + 1 : ℕ)) :
    ∃ U : W^{1,p}(ℝ^(n + 1)),
      baseRepresentative U =ᵐ[volume] (fun x ↦ max (‖x‖ ^ a - 1) 0) := by
  let : Fact (0 < n + 1) := ⟨Nat.succ_pos n⟩
  obtain ⟨φ, _, hφone, _, hφrange⟩ := TestFunction.exists_eq_one_on_compact
    (n := n + 1) (U := Metric.ball 0 2) (K := Metric.closedBall 0 1)
    Metric.isOpen_ball (isCompact_closedBall _ _)
    (Metric.closedBall_subset_ball (by norm_num))
  have hbase : -a * p.toReal < (n + 1 : ℕ) := by
    have := ENNReal.toReal_nonneg (a := p)
    nlinarith
  obtain ⟨U, hU⟩ := exists_w1p_mul_norm_rpow hp
    (φ.contDiff.of_le (by norm_num)) φ.hasCompactSupport hbase hd
  have hF : LipschitzWith 1 (fun z : ℝ ↦ max (z - 1) 0) := by
    simpa only [one_mul, Function.comp_def, sub_eq_add_neg] using
      Lp.lipschitzWith_pos_part.comp (isometry_add_right (-1 : ℝ)).lipschitzWith
  have hF0 : max ((0 : ℝ) - 1) 0 = 0 := by norm_num
  refine ⟨lipschitzComposition hF hF0 U, ?_⟩
  have hcomp := lipschitzComposition_base_ae hF hF0 U
  change baseRepresentative (lipschitzComposition hF hF0 U) =ᵐ[domainMeasure (n + 1) univ]
    (fun x ↦ max (baseRepresentative U x - 1) 0) at hcomp
  have hcomp' : baseRepresentative (lipschitzComposition hF hF0 U) =ᵐ[volume]
      (fun x ↦ max (baseRepresentative U x - 1) 0) := by simpa using hcomp
  filter_upwards [hcomp', hU] with x hx hUx
  rw [hx, hUx]
  by_cases hxin : ‖x‖ ≤ 1
  · have hxone : φ x = 1 := hφone x (by simpa using hxin)
    rw [hxone, one_mul]
  · have hr : ‖x‖ ^ a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hxin) ha.le
    have hcut : φ x * ‖x‖ ^ a ≤ 1 :=
      (mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _) (hφrange x).2).trans hr
    rw [max_eq_right (sub_nonpos.mpr hcut), max_eq_right (sub_nonpos.mpr hr)]

end SobolevSpace.GraphSpace
