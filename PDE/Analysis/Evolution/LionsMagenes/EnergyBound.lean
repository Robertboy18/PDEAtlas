/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
public import PDE.Analysis.Evolution.Core.Gronwall

/-!
# Uniform pivot bounds and traces from a continuous dual equation

The Lions–Magenes energy identity supplies a Grönwall bound even when the
velocity only takes values in the energy dual. A continuous equation in that
dual also identifies the endpoint traces of the continuous pivot representative.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution.ContinuousPivotEvolutionOn

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {T : GelfandTriple (V := V) (H := H)}
  {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {a b : ℝ}

/-- A continuous dual equation valid almost everywhere determines the dual
of the pivot representative at every time, including both endpoints. -/
theorem pivotToDual_eqOn_of_ae_eq
    (E : ContinuousPivotEvolutionOn T u g a b) (hab : a < b)
    {r : ℝ → StrongDual ℝ V} (hr : ContinuousOn r (Icc a b))
    (heq : (fun t ↦ T.energyToDual (u t)) =ᵐ[volume.restrict (Ioc a b)] r) :
    EqOn (fun t ↦ T.pivotToDual (E.representative t)) r (Icc a b) := by
  have hrep : E.representative =ᵐ[volume.restrict (Icc a b)]
      fun t ↦ T.inclusion (u t) := by
    simpa only [uIcc_of_le hab.le] using E.ae_eq_inclusion
  have heq' : (fun t ↦ T.energyToDual (u t)) =ᵐ[volume.restrict (Icc a b)] r :=
    (ae_restrict_congr_set Ioc_ae_eq_Icc).mp heq
  apply Measure.eqOn_Icc_of_ae_eq volume hab.ne _ _ hr
  · filter_upwards [hrep, heq'] with t ht he
    simpa only [ht, GelfandTriple.energyToDual, ContinuousLinearMap.comp_apply] using he
  · exact T.pivotToDual.continuous.comp_continuousOn
      (by simpa only [uIcc_of_le hab.le] using E.continuousOn)

/-- A one-sided bound for the dual energy pairing yields a uniform bound for
the pivot norm. The source budget is integrated over the whole time interval. -/
theorem norm_sq_le_mul_exp_of_pairing_le
    (E : ContinuousPivotEvolutionOn T u g a b) (hab : a ≤ b)
    (hgu : IntervalIntegrable (fun t ↦ g t (u t)) volume a b)
    {r : ℝ → ℝ} (hr : IntervalIntegrable r volume a b)
    (hr_nonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ r t)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      2 * g t (u t) ≤ K * ‖T.inclusion (u t)‖ ^ 2 + r t) :
    ∀ t ∈ Icc a b,
      ‖E.representative t‖ ^ 2 ≤
        (‖E.representative a‖ ^ 2 + ∫ s in a..b, r s) *
          Real.exp (K * (t - a)) := by
  apply le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le hab
    (E.absolutelyContinuousOnInterval_norm_sq hgu) hr hr_nonneg hK
  have hderiv := E.ae_hasDerivWithinAt_norm_sq hgu
  have hderiv' := ae_restrict_of_ae (s := Ioc a b) hderiv
  have hrep : E.representative =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ T.inclusion (u t) := by
    simpa only [uIcc_of_le hab, restrict_Ioc_eq_restrict_Icc] using E.ae_eq_inclusion
  have hinterior : ∀ᵐ t ∂volume.restrict (Ioc a b), t ∈ Ioo a b := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hderiv', hrep, hbound, hinterior] with t hd he hb ht
  have ht' : t ∈ uIcc a b := by
    simpa only [uIcc_of_le hab] using Ioo_subset_Icc_self ht
  have hnhds : uIcc a b ∈ 𝓝 t := by
    rw [uIcc_of_le hab]
    exact mem_of_superset (isOpen_Ioo.mem_nhds ht) Ioo_subset_Icc_self
  rw [(hd ht').hasDerivAt hnhds |>.deriv, he]
  exact hb

end PDE.Analysis.Evolution.ContinuousPivotEvolutionOn
