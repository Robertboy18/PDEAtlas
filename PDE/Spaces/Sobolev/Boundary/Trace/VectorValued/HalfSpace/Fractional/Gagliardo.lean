/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Fractional.Estimate
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph
import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Energy

/-!
# Banach-valued fractional trace on a half-space

The Sobolev trace takes values in the intrinsic Gagliardo space of order `1 - 1/p`
for finite real `p > 1`. Its first graph coordinate is the physical `Lᵖ` trace.
The norm bound adds the physical and fractional energies before taking the p-th root.

The energy estimate comes from compact smooth density and the Banach-valued smooth estimate;
no smooth approximation or fractional regularity hypothesis is imposed on the input.
The target may be any real Banach space, and the zero-dimensional boundary is included.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open SobolevSpace.Fractional

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
/-- The physical finite-exponent trace satisfies the intrinsic Gagliardo
condition at order `1 - 1 / p`. -/
theorem memGagliardo_traceLp (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    MemGagliardo n (1 - 1 / p) Set.univ (traceLp n p hp.le u)
      (p := ENNReal.ofReal p) := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  rw [memGagliardo_iff_lintegral_lt_top _
    (ENNReal.ofReal_pos.mpr hp₀).ne' ENNReal.ofReal_ne_top]
  refine ⟨by simpa only [Measure.restrict_univ] using Lp.memLp (traceLp n p hp.le u), ?_⟩
  simpa only [gagliardoProductMeasure, Measure.restrict_univ,
    ENNReal.toReal_ofReal hp₀.le, sub_mul, one_mul, one_div, inv_mul_cancel₀ hp₀.ne',
    ← add_sub_assoc] using lintegral_traceLp_sub_rpow_div_lt_top n p hp u

private def traceValue (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    GagliardoSpace n (1 - 1 / p) Set.univ (p := ENNReal.ofReal p) (F := F) :=
  GagliardoSpace.ofFunction (traceLp n p hp.le u) (memGagliardo_traceLp n p hp u)

private theorem toLp_traceValue (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    GagliardoSpace.toLp n (1 - 1 / p) Set.univ (traceValue n p hp u) =
      Lp.restrictionCLMOfLE Measure.restrict_le_self (traceLp n p hp.le u) := by
  apply Lp.ext
  exact (GagliardoSpace.toLp_ofFunction_apply_ae (traceLp n p hp.le u)
    (memGagliardo_traceLp n p hp u)).trans
      (Lp.restrictionCLMOfLE_apply_ae Measure.restrict_le_self (traceLp n p hp.le u)).symm

private theorem norm_toLp_traceValue (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    ‖GagliardoSpace.toLp n (1 - 1 / p) Set.univ (traceValue n p hp u)‖ =
      ‖traceLp n p hp.le u‖ := by
  change ‖(memGagliardo_traceLp n p hp u).1.toLp (traceLp n p hp.le u)‖ = _
  rw [Lp.norm_toLp]
  simp only [Measure.restrict_univ, Lp.norm_def]

private theorem differenceQuotient_traceValue_energy (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    ‖GagliardoSpace.differenceQuotient n (1 - 1 / p) Set.univ
      (traceValue n p hp u)‖ₑ ^ p =
      ∫⁻ z : ℝ^n × ℝ^n,
        ‖traceLp n p hp.le u z.1 - traceLp n p hp.le u z.2‖ₑ ^ p /
          (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
        ∂((volume : Measure (ℝ^n)).prod volume) := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  let v := traceValue n p hp u
  have hdiff :
      (GagliardoSpace.differenceQuotient n (1 - 1 / p) Set.univ v : ℝ^n × ℝ^n → F)
        =ᵐ[gagliardoProductMeasure n Set.univ]
          fun z ↦ diffQuot n (1 - 1 / p) (traceLp n p hp.le u) z
            (p := ENNReal.ofReal p) :=
    (GagliardoSpace.differenceQuotient_apply_ae v).trans
      (diffQuot_congr_ae
        (GagliardoSpace.toLp_ofFunction_apply_ae (traceLp n p hp.le u)
          (memGagliardo_traceLp n p hp u)))
  have henergy :
      ‖GagliardoSpace.differenceQuotient n (1 - 1 / p) Set.univ v‖ₑ ^ p =
        ∫⁻ z : ℝ^n × ℝ^n,
          ‖traceLp n p hp.le u z.1 - traceLp n p hp.le u z.2‖ₑ ^ p /
            (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
          ∂((volume : Measure (ℝ^n)).prod volume) := by
    rw [Lp.enorm_def]
    have hpow := eLpNorm_nnreal_pow_eq_lintegral
      (p := p.toNNReal) (Real.toNNReal_pos.mpr hp₀).ne'
      (Lp.aestronglyMeasurable
        (GagliardoSpace.differenceQuotient n (1 - 1 / p) Set.univ v))
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal p hp₀.le] at hpow
    rw [hpow]
    have hdiff' := hdiff
    simp only [gagliardoProductMeasure, Measure.restrict_univ] at hdiff' ⊢
    apply lintegral_congr_ae
    filter_upwards [hdiff'] with z hz
    rw [hz]
    simpa only [ENNReal.toReal_ofReal hp₀.le, sub_mul, one_mul, one_div,
      inv_mul_cancel₀ hp₀.ne', ← add_sub_assoc] using
      enorm_diffQuot_rpow (n := n) (s := 1 - 1 / p) (traceLp n p hp.le u) z
        (ENNReal.ofReal_pos.mpr hp₀).ne' ENNReal.ofReal_ne_top
  exact henergy

omit [CompleteSpace F] in
private theorem norm_le_of_coordinate_energies (hp : 0 < p) (C : ℝ≥0)
    (v : GagliardoSpace n (1 - 1 / p) Set.univ (p := ENNReal.ofReal p) (F := F))
    (r : ℝ) (hr : 0 ≤ r)
    (hbase : ‖GagliardoSpace.toLp n (1 - 1 / p) Set.univ v‖ ^ p ≤ p * r ^ p)
    (hdiff : ‖GagliardoSpace.differenceQuotient n (1 - 1 / p) Set.univ v‖ ^ p ≤
      (C : ℝ) * r ^ p) :
    ‖v‖ ≤ (p + C) ^ (1 / p) * r := by
  have hnorm := GagliardoSpace.norm_rpow_eq ENNReal.ofReal_ne_top v
  rw [ENNReal.toReal_ofReal hp.le] at hnorm
  have hv : ‖v‖ ^ p ≤ (p + C) * r ^ p := by
    rw [hnorm, add_mul]
    exact add_le_add hbase hdiff
  apply (Real.rpow_le_rpow_iff (norm_nonneg v) (by positivity) hp).1
  calc
    ‖v‖ ^ p ≤ (p + C) * r ^ p := hv
    _ = ((p + C) ^ (1 / p) * r) ^ p := by
      rw [Real.mul_rpow (by positivity) hr, one_div,
        Real.rpow_inv_rpow (by positivity) hp.ne']

private theorem norm_traceValue_le_of_energy_bound (hp : 1 < p) (C : ℝ≥0)
    (hC : ∀ u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F),
      (∫⁻ z : ℝ^n × ℝ^n,
        ‖traceLp n p hp.le u z.1 - traceLp n p hp.le u z.2‖ₑ ^ p /
          (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
        ∂((volume : Measure (ℝ^n)).prod volume)) ≤
      (C : ℝ≥0∞) * ∑ i : Fin (n + 1), ‖∂[i] u‖ₑ ^ p)
    (u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    ‖traceValue n p hp u‖ ≤ (p + C) ^ (1 / p) * ‖u‖ := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  let v := traceValue n p hp u
  have hweak :
      ∑ i : Fin (n + 1), ‖∂[i] u‖ₑ ^ p ≤ ‖u‖ₑ ^ p := by
    simpa only [ENNReal.toReal_ofReal hp₀.le] using
      SobolevSpace.VectorValued.sum_enorm_partialDeriv_rpow_le ENNReal.ofReal_ne_top u
  have henergy_le :
      ‖GagliardoSpace.differenceQuotient n (1 - 1 / p) Set.univ v‖ₑ ^ p ≤
        (C : ℝ≥0∞) * ‖u‖ₑ ^ p := by
    rw [differenceQuotient_traceValue_energy]
    exact (hC u).trans (mul_le_mul_right hweak _)
  have hdiff_norm :
      ‖GagliardoSpace.differenceQuotient n (1 - 1 / p) Set.univ v‖ ^ p ≤
        (C : ℝ) * ‖u‖ ^ p := by
    have h := ENNReal.toReal_mono (by finiteness) henergy_le
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm,
      ENNReal.coe_toReal] using h
  have hbase_norm : ‖traceLp n p hp.le u‖ ^ p ≤ p * ‖u‖ ^ p := by
    calc
      ‖traceLp n p hp.le u‖ ^ p ≤ (p ^ (1 / p) * ‖u‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) (norm_traceLp_apply_le hp.le u) hp₀.le
      _ = p * ‖u‖ ^ p := by
        rw [Real.mul_rpow (by positivity) (norm_nonneg _), one_div,
          Real.rpow_inv_rpow hp₀.le hp₀.ne']
  apply norm_le_of_coordinate_energies n p hp₀ C v ‖u‖ (norm_nonneg u) _ hdiff_norm
  rw [norm_toLp_traceValue]
  exact hbase_norm

private theorem exists_norm_traceValue_le (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F),
      ‖traceValue n p hp u‖ ≤ (p + C) ^ (1 / p) * ‖u‖ := by
  obtain ⟨C, hC⟩ := exists_trace_fractional_bound (F := F) n p hp
  exact ⟨C, norm_traceValue_le_of_energy_bound n p hp C hC⟩

/-- The bounded trace into the intrinsic Gagliardo space of order `1 - 1 / p`.
Its first graph coordinate is the physical `Lᵖ` boundary trace. -/
def traceGagliardo (hp : 1 < p) :
    W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F) →L[ℝ]
      GagliardoSpace n (1 - 1 / p) Set.univ (p := ENNReal.ofReal p) (F := F) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun U ↦ GagliardoSpace.ofFunction (traceLp n p hp.le U)
        (memGagliardo_traceLp n p hp U)
      map_add' := by
        intro u v
        change traceValue n p hp (u + v) =
          traceValue n p hp u + traceValue n p hp v
        apply GagliardoSpace.toLp_injective (n := n) (s := 1 - 1 / p)
          (Ω := Set.univ) (p := ENNReal.ofReal p) (F := F)
        rw [map_add, toLp_traceValue, toLp_traceValue, toLp_traceValue, map_add, map_add]
      map_smul' := by
        intro c u
        change traceValue n p hp (c • u) = c • traceValue n p hp u
        apply GagliardoSpace.toLp_injective (n := n) (s := 1 - 1 / p)
          (Ω := Set.univ) (p := ENNReal.ofReal p) (F := F)
        rw [map_smul, toLp_traceValue, toLp_traceValue, map_smul, map_smul] }
    (by
      obtain ⟨C, hC⟩ := exists_norm_traceValue_le (F := F) n p hp
      exact ⟨(p + C) ^ (1 / p), hC⟩)

/-- The Gagliardo trace has the physical `traceLp` representative almost
everywhere on the boundary. -/
theorem toLp_traceGagliardo_apply_ae (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    (GagliardoSpace.toLp n (1 - 1 / p) Set.univ (traceGagliardo n p hp u) : ℝ^n → F)
      =ᵐ[volume] (traceLp n p hp.le u : ℝ^n → F) := by
  change (GagliardoSpace.toLp n (1 - 1 / p) Set.univ
    (GagliardoSpace.ofFunction (traceLp n p hp.le u) (memGagliardo_traceLp n p hp u)) :
      ℝ^n → F) =ᵐ[volume] _
  simpa only [Measure.restrict_univ] using
    GagliardoSpace.toLp_ofFunction_apply_ae (traceLp n p hp.le u)
      (memGagliardo_traceLp n p hp u)

/-- Projection of the Gagliardo trace is exactly the `Lᵖ` trace. Restriction
to `univ` transports between the two equal boundary measures. -/
@[simp]
theorem toLp_traceGagliardo (hp : 1 < p)
    (u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    GagliardoSpace.toLp n (1 - 1 / p) Set.univ (traceGagliardo n p hp u) =
      Lp.restrictionCLMOfLE Measure.restrict_le_self (traceLp n p hp.le u) := by
  exact toLp_traceValue n p hp u

/-- The physical projection commutes with the trace as an equality of
continuous linear maps. -/
theorem toLp_comp_traceGagliardo (hp : 1 < p) :
    (GagliardoSpace.toLp n (1 - 1 / p) Set.univ).comp (traceGagliardo (F := F) n p hp) =
      (Lp.restrictionCLMOfLE Measure.restrict_le_self).comp (traceLp n p hp.le) := by
  apply ContinuousLinearMap.ext
  intro u
  exact toLp_traceGagliardo n p hp u

/-- Any constant `C` in the fractional energy estimate gives the operator bound
`‖traceGagliardo‖ ≤ (p + C) ^ (1 / p)`. The physical trace contributes `p ‖u‖ ^ p` and the
difference energy contributes `C ‖u‖ ^ p` before the p-th root is taken. -/
theorem norm_traceGagliardo_le_of_energy_bound (hp : 1 < p) (C : ℝ≥0)
    (hC : ∀ u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F),
      (∫⁻ z : ℝ^n × ℝ^n,
        ‖traceLp n p hp.le u z.1 - traceLp n p hp.le u z.2‖ₑ ^ p /
          (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
        ∂((volume : Measure (ℝ^n)).prod volume)) ≤
      (C : ℝ≥0∞) * ∑ i : Fin (n + 1), ‖∂[i] u‖ₑ ^ p) :
    ‖traceGagliardo (F := F) n p hp‖ ≤ (p + C) ^ (1 / p) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_traceValue_le_of_energy_bound n p hp C hC)

/-- There is a constant `C` for the fractional energy estimate of
`exists_trace_fractional_bound` such that the same `C` bounds the trace operator by
`(p + C) ^ (1 / p)`. -/
theorem exists_norm_traceGagliardo_le (hp : 1 < p) :
    ∃ C : ℝ≥0,
      (∀ u : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
        SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F),
        (∫⁻ z : ℝ^n × ℝ^n,
          ‖traceLp n p hp.le u z.1 - traceLp n p hp.le u z.2‖ₑ ^ p /
            (ENNReal.ofReal ‖z.1 - z.2‖) ^ ((n : ℝ) + p - 1)
          ∂((volume : Measure (ℝ^n)).prod volume)) ≤
        (C : ℝ≥0∞) * ∑ i : Fin (n + 1), ‖∂[i] u‖ₑ ^ p) ∧
      ‖traceGagliardo (F := F) n p hp‖ ≤ (p + C) ^ (1 / p) := by
  obtain ⟨C, hC⟩ := exists_trace_fractional_bound (F := F) n p hp
  exact ⟨C, hC, norm_traceGagliardo_le_of_energy_bound n p hp C hC⟩

/-- Vanishing of the fractional trace is exactly vanishing of the physical trace. -/
theorem traceGagliardo_eq_zero_iff (hp : 1 < p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    traceGagliardo n p hp U = 0 ↔ traceLp n p hp.le U = 0 := by
  constructor
  · intro h
    apply Lp.ext
    have ha := toLp_traceGagliardo_apply_ae n p hp U
    rw [h, map_zero] at ha
    have hz := (Lp.coeFn_zero F (ENNReal.ofReal p)
      ((volume : Measure (ℝ^n)).restrict Set.univ)).filter_mono
        (ae_mono (show (volume : Measure (ℝ^n)) ≤ volume.restrict Set.univ by
          rw [Measure.restrict_univ]))
    exact ha.symm.trans (hz.trans (Lp.coeFn_zero F (ENNReal.ofReal p) volume).symm)
  · intro h
    apply GagliardoSpace.toLp_injective
    rw [toLp_traceGagliardo, h, map_zero, map_zero]

end SobolevSpace.VectorValued.Trace.HalfSpace
