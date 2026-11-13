/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.SectionNorm
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import PDE.Analysis.MeasureTheory.StronglyMeasurable.Distance
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Reconstruction from mixed Lp sections

A jointly measurable function with finite mixed norm determines a nested Bochner Lp
class. Separability of the spatial Lp space gives strong measurability of the section
map by testing distances. The resulting class has the prescribed spatial sections
almost everywhere and exactly the original mixed norm.
-/

@[expose] public section

open Filter TopologicalSpace
open scoped ENNReal MeasureTheory

namespace MeasureTheory

/-- A finite positive Lp norm forces extended nonnegative values to be finite almost everywhere. -/
theorem MemLp.ae_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hptop : p ≠ ∞)
    {f : α → ℝ≥0∞} (hfin : MemLp f p μ) : ∀ᵐ x ∂μ, f x < ∞ := by
  have hpow := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ hptop hfin
  simp only [enorm_eq_self] at hpow
  have hm := hfin.aestronglyMeasurable.aemeasurable.pow_const p.toReal
  filter_upwards [ae_lt_top' hm hpow.ne] with x hx
  by_contra h
  have heq : f x = ∞ := top_unique (not_lt.mp h)
  rw [heq, ENNReal.top_rpow_of_pos (ENNReal.toReal_pos hp₀ hptop)] at hx
  exact (lt_irrefl _ hx)

/-- Finite mixed norm reconstructs a Bochner class with the given spatial representatives.
Separability concerns only the spatial Lp space; neither measure has to be finite. -/
theorem exists_mixedLp_sections {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [SeparableSpace (Lp E p ν)]
    (hptop : p ≠ ∞) (hqtop : q ≠ ∞)
    {U : α × β → E} (hU : Measurable U)
    (hfin : MemLp (fun t ↦ eLpNorm (fun x ↦ U (t, x)) p ν) q μ) :
    ∃ u : Lp (Lp E p ν) q μ,
      (∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (u t : β → E)) ∧
      ‖u‖ₑ = eLpNorm (fun t ↦ eLpNorm (fun x ↦ U (t, x)) p ν) q μ := by
  classical
  have hp₀ : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
  have hq₀ : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ q))
  have hslices := hfin.ae_lt_top hq₀ hqtop
  let v (t : α) : Lp E p ν :=
    if ht : MemLp (fun x ↦ U (t, x)) p ν then ht.toLp (fun x ↦ U (t, x)) else 0
  have hvsec : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (v t : β → E) := by
    filter_upwards [hslices] with t ht
    change MemLp (fun x ↦ U (t, x)) p ν at ht
    dsimp only [v]
    rw [dite_eq_left ht]
    exact ht.coeFn_toLp.symm
  have hvmeas : AEStronglyMeasurable v μ := by
    apply aestronglyMeasurable_of_aemeasurable_dist
    intro w
    have hw : Measurable (fun z : α × β ↦ w z.2) :=
      (Lp.stronglyMeasurable w).measurable.comp measurable_snd
    have hd : AEMeasurable
        (fun t ↦ (eLpNorm (fun x ↦ U (t, x) - w x) p ν).toReal) μ :=
      ((hU.sub hw).eLpNorm_prod_right hp₀ hptop).ennreal_toReal.aemeasurable
    apply hd.congr
    filter_upwards [hvsec] with t ht
    rw [dist_eq_norm, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub (v t) w, ht] with x hsub hx
    rw [hsub, Pi.sub_apply, hx]
  have hvnorm : (fun t ↦ eLpNorm (fun x ↦ U (t, x)) p ν) =ᵐ[μ] fun t ↦ ‖v t‖ₑ := by
    filter_upwards [hvsec] with t ht
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae ht
  have hv : MemLp v q μ := hfin.congr_enorm hvmeas hvnorm
  refine ⟨hv.toLp v, ?_, ?_⟩
  · filter_upwards [hvsec, hv.coeFn_toLp] with t ht hvt
    rw [hvt]
    exact ht
  · rw [Lp.enorm_toLp, ← eLpNorm_enorm _ hvmeas]
    exact eLpNorm_congr_ae (EventuallyEq.symm hvnorm)

end MeasureTheory
