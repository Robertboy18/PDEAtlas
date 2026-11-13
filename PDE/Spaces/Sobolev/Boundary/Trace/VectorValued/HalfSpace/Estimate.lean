/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Core
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
import PDE.Analysis.MeasureTheory.LpNorm
import PDE.Spaces.Sobolev.Boundary.Trace.HalfLine.FiniteExponent
import PDE.Spaces.Sobolev.Calculus.Differentiation.VectorValued.ClassicalToWeak
import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Normed-valued smooth trace estimates on the upper half-space

Integrating the normed half-line endpoint estimate in the tangential variables gives
the boundary `p`-energy bound for compactly supported `C¹` functions. The raw integral
estimate holds in every real normed codomain. For a Banach-valued Sobolev element with
such a representative, weak-derivative uniqueness identifies its normal derivative row
and gives a bound in the graph norm.

Every finite real exponent `p ≥ 1` and every boundary dimension are included. These
are smooth estimates; `Trace.VectorValued.HalfSpace.Operator` extends the boundary map
by density.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open GraphSpace SobolevSpace.Trace.HalfSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The boundary norm integral is bounded by the upper-half-space base and normal
derivative energies. Neither completeness of the target nor positive boundary
dimension is required. At `p = 1` the base term vanishes. -/
theorem smooth_boundary_integral_norm_rpow_le_upper_energy
    {f : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ y : ℝ^n, ‖normalSlice f y 0‖ ^ p) ≤
      (p - 1) * (∫ x in ℝ^(n + 1)₊, ‖f x‖ ^ p) +
        (∫ x in ℝ^(n + 1)₊, ‖(∂[Fin.last n] f) x‖ ^ p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hBoundary : Integrable (fun y : ℝ^n ↦ ‖normalSlice f y 0‖ ^ p) :=
    ((boundaryValue_continuous hf.continuous).norm.rpow_const
      (fun _ ↦ Or.inr hp_pos.le)).integrable_of_hasCompactSupport
        ((boundaryValue_hasCompactSupport hfc).norm.rpow_const hp_pos.ne')
  have hF : Integrable (fun z : ℝ^n × ℝ ↦ ‖normalSlice f z.1 z.2‖ ^ p)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
    ((normalSlice_product_continuous hf.continuous).norm.rpow_const
      (fun _ ↦ Or.inr hp_pos.le)).integrable_of_hasCompactSupport
        ((normalSlice_product_hasCompactSupport hfc).norm.rpow_const hp_pos.ne')
  have hG : Integrable (fun z : ℝ^n × ℝ ↦ ‖normalDerivativeInSplit f z‖ ^ p)
      ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) :=
    ((normalDerivativeInSplit_continuous hf).norm.rpow_const
      (fun _ ↦ Or.inr hp_pos.le)).integrable_of_hasCompactSupport
        ((normalDerivativeInSplit_hasCompactSupport hfc).norm.rpow_const hp_pos.ne')
  have hSlice (y : ℝ^n) :
      ‖normalSlice f y 0‖ ^ p ≤
        (p - 1) * (∫ t, ‖normalSlice f y t‖ ^ p ∂positiveNormalMeasure) +
          ∫ t, ‖normalDerivativeInSplit f (y, t)‖ ^ p ∂positiveNormalMeasure := by
    have h := SobolevSpace.Trace.HalfLine.endpoint_norm_rpow_le_integral_add_integral
      (normalSlice_contDiff hf y) (normalSlice_hasCompactSupport hfc y) hp
    simpa only [deriv_normalSlice hf y, positiveNormalMeasure] using h
  calc
    (∫ y : ℝ^n, ‖normalSlice f y 0‖ ^ p) ≤
        ∫ y : ℝ^n,
          ((p - 1) * (∫ t, ‖normalSlice f y t‖ ^ p ∂positiveNormalMeasure) +
            ∫ t, ‖normalDerivativeInSplit f (y, t)‖ ^ p ∂positiveNormalMeasure) :=
      integral_mono hBoundary
        ((hF.integral_prod_left.const_mul (p - 1)).add hG.integral_prod_left) hSlice
    _ = (p - 1) *
          (∫ z : ℝ^n × ℝ, ‖normalSlice f z.1 z.2‖ ^ p
            ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) +
          (∫ z : ℝ^n × ℝ, ‖normalDerivativeInSplit f z‖ ^ p
            ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) := by
      rw [integral_add (hF.integral_prod_left.const_mul (p - 1)) hG.integral_prod_left,
        integral_const_mul, integral_prod _ hF, integral_prod _ hG]
    _ = _ := by
      simpa only [normalSlice, normalDerivativeInSplit] using
        congrArg₂ (fun a b : ℝ ↦ (p - 1) * a + b)
          (integral_joinTangentialNormal_eq_integral_upper
            (fun x ↦ ‖f x‖ ^ p))
          (integral_joinTangentialNormal_eq_integral_upper
            (fun x ↦ ‖(∂[Fin.last n] f) x‖ ^ p))

/-- The boundary `Lp` norm is controlled by the Sobolev graph norm.
Only agreement of the base representative is assumed: the classical normal
derivative is identified by uniqueness of weak derivatives. -/
theorem norm_smoothBoundaryLp_le [CompleteSpace F] {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}((⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩ : Opens ℝ^(n + 1)); F))
    {f : ℝ^(n + 1) → F} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hbase : (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] f) :
    ‖smoothBoundaryLp (p := ENNReal.ofReal p) hf.continuous hfc‖ ≤
      p ^ (1 / p) * ‖U‖ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hLp (a : DerivIndex (n + 1) 1) :
      ‖U.val a‖ ^ p = ∫ x in ℝ^(n + 1)₊, ‖U.val a x‖ ^ p := by
    simpa only [ENNReal.toReal_ofReal hp_pos.le, domainMeasure, Opens.coe_mk] using
      Lp.norm_rpow_eq_integral (ENNReal.ofReal_ne_zero_iff.mpr hp_pos)
        ENNReal.ofReal_ne_top (U.val a)
  have hnormal := coordinate_ae_partialDeriv_of_contDiffOn U hf.contDiffOn
    hbase (Fin.last n)
  have hbaseEnergy :
      (∫ x in ℝ^(n + 1)₊, ‖f x‖ ^ p) = ‖U.val (baseIndex (n + 1) 1)‖ ^ p :=
    (integral_congr_ae (hbase.fun_comp fun z : F ↦ ‖z‖ ^ p)).symm.trans
      (hLp _).symm
  have hnormalEnergy :
      (∫ x in ℝ^(n + 1)₊, ‖(∂[Fin.last n] f) x‖ ^ p) =
        ‖U.val (singleDerivIndex (n + 1) (Fin.last n))‖ ^ p :=
    (integral_congr_ae (hnormal.fun_comp fun z : F ↦ ‖z‖ ^ p)).symm.trans
      (hLp _).symm
  have hboundary :
      ‖smoothBoundaryLp (p := ENNReal.ofReal p) hf.continuous hfc‖ ^ p =
        ∫ y : ℝ^n, ‖normalSlice f y 0‖ ^ p := by
    calc
      _ = ∫ y : ℝ^n,
          ‖smoothBoundaryLp (p := ENNReal.ofReal p) hf.continuous hfc y‖ ^ p := by
        simpa only [ENNReal.toReal_ofReal hp_pos.le] using
          Lp.norm_rpow_eq_integral (ENNReal.ofReal_ne_zero_iff.mpr hp_pos)
            ENNReal.ofReal_ne_top (smoothBoundaryLp hf.continuous hfc)
      _ = _ := integral_congr_ae
        ((smoothBoundaryLp_coeFn_ae hf.continuous hfc).fun_comp fun z : F ↦ ‖z‖ ^ p)
  have hbound :
      ‖smoothBoundaryLp (p := ENNReal.ofReal p) hf.continuous hfc‖ ^ p ≤ p * ‖U‖ ^ p := by
    calc
      _ ≤ (p - 1) * ‖U.val (baseIndex (n + 1) 1)‖ ^ p +
          ‖U.val (singleDerivIndex (n + 1) (Fin.last n))‖ ^ p := by
        rw [hboundary, ← hbaseEnergy, ← hnormalEnergy]
        exact smooth_boundary_integral_norm_rpow_le_upper_energy hf hfc hp
      _ ≤ (p - 1) * ‖U‖ ^ p + ‖U‖ ^ p :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) (norm_coordinate_le _ U) hp_pos.le)
            (sub_nonneg.mpr hp))
          (Real.rpow_le_rpow (norm_nonneg _) (norm_coordinate_le _ U) hp_pos.le)
      _ = p * ‖U‖ ^ p := by ring
  have hconstant : 0 ≤ p ^ (1 / p) := Real.rpow_nonneg hp_pos.le _
  apply (Real.rpow_le_rpow_iff (norm_nonneg _)
    (mul_nonneg hconstant (norm_nonneg U)) hp_pos).mp
  rw [Real.mul_rpow hconstant (norm_nonneg U)]
  have hc : (p ^ (1 / p)) ^ p = p := by
    rw [← Real.rpow_mul hp_pos.le, one_div_mul_cancel hp_pos.ne', Real.rpow_one]
  rw [hc]
  exact hbound

end SobolevSpace.VectorValued.Trace.HalfSpace
