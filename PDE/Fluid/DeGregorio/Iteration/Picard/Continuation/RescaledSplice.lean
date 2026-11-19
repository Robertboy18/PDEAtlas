/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.Splice
import PDE.Analysis.Calculus.PartialRegularity
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Splicing endpoint-normalized rescaled solutions

Two rescaled slabs with matching vorticity and velocity traces can be joined
at an ordinary classical time. The endpoint formula identifies their equal
rescaling rates. Closed continuity of the spatial derivatives determines the
one-sided time derivatives from the PDE, so derivative matching is a conclusion.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

namespace DeGregorio

/-- The time derivative prescribed by the equal-rate rescaled equation. -/
def equalRateTransportRHS (fields : Fields) (ρ : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (ρ t + deriv (fun y ↦ fields.velocity y t) x) * fields.vorticity x t -
    (ρ t * x + fields.velocity x t) * deriv (fun y ↦ fields.vorticity y t) x

/-- Closed spatial traces make the rescaled transport right-hand side continuous on the
closed slab. -/
theorem continuous_equalRateTransportRHS
    {fields : Fields} {ρ : ℝ → ℝ} {T : ℝ}
    (hw : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ fields.vorticity p.1 p.2))
    (hu : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ fields.velocity p.1 p.2))
    (hwx : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦
      deriv (fun y ↦ fields.vorticity y p.2) p.1))
    (hux : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦
      deriv (fun y ↦ fields.velocity y p.2) p.1))
    (hρ : ContinuousOn ρ (Icc 0 T)) :
    Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ equalRateTransportRHS fields ρ p.1 p.2) := by
  have hr := (continuousOn_iff_continuous_domRestrict.mp hρ).comp
    (continuous_snd : Continuous (Prod.snd : ℝ × Icc (0 : ℝ) T → Icc (0 : ℝ) T))
  exact ((hr.add hux).mul hw).sub (((hr.mul continuous_fst).add hu).mul hwx)

/-- The initial right derivative follows from the interior rescaled PDE and
the continuous closed transport trace. -/
theorem IsClassicalRescaledSolutionOn.hasDerivWithinAt_equalRate_initial
    {fields : Fields} {ρ : ℝ → ℝ} {T : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo 0 T)) (hT : 0 < T)
    (hw : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ fields.vorticity p.1 p.2))
    (hrhs : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦
      equalRateTransportRHS fields ρ p.1 p.2)) (x : ℝ) :
    HasDerivWithinAt (fields.vorticity x) (equalRateTransportRHS fields ρ x 0)
      (Ici 0) 0 := by
  have htime : ContinuousOn (fields.vorticity x) (Icc 0 T) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (hw.comp (continuous_const.prodMk continuous_id))
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioo 0 T)
    (fun t ht ↦ (hsol.regularity.vorticity_time_differentiableAt
      (x := x) ht).differentiableWithinAt)
    ((htime 0 ⟨le_rfl, hT.le⟩).mono Ioo_subset_Icc_self)
    (Ioo_mem_nhdsGT hT)
  have hc := hrhs.comp
    ((continuous_const (y := x)).prodMk (continuous_projIcc (h := hT.le)))
  have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [Function.comp_apply,
    projIcc_of_mem hT.le (left_mem_Icc.mpr hT.le)] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hT] with t ht
  simp only [Function.comp_apply, projIcc_of_mem hT.le (Ioo_subset_Icc_self ht)]
  simpa only [equalRateTransportRHS, one_mul] using
    (eq_sub_iff_add_eq.mpr (hsol.transport (x := x) ht)).symm

/-- The terminal left derivative is determined by the same rescaled
transport trace. -/
theorem IsClassicalRescaledSolutionOn.hasDerivWithinAt_equalRate_terminal
    {fields : Fields} {ρ : ℝ → ℝ} {T : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo 0 T)) (hT : 0 < T)
    (hw : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ fields.vorticity p.1 p.2))
    (hrhs : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦
      equalRateTransportRHS fields ρ p.1 p.2)) (x : ℝ) :
    HasDerivWithinAt (fields.vorticity x) (equalRateTransportRHS fields ρ x T)
      (Iic T) T := by
  have htime : ContinuousOn (fields.vorticity x) (Icc 0 T) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (hw.comp (continuous_const.prodMk continuous_id))
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Ioo 0 T)
    (fun t ht ↦ (hsol.regularity.vorticity_time_differentiableAt
      (x := x) ht).differentiableWithinAt)
    ((htime T ⟨hT.le, le_rfl⟩).mono Ioo_subset_Icc_self)
    (Ioo_mem_nhdsLT hT)
  have hc := hrhs.comp
    ((continuous_const (y := x)).prodMk (continuous_projIcc (h := hT.le)))
  have hlim := (hc.tendsto T).mono_left (nhdsWithin_le_nhds (s := Iio T))
  simp only [Function.comp_apply,
    projIcc_of_mem hT.le (right_mem_Icc.mpr hT.le)] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht
  simp only [Function.comp_apply, projIcc_of_mem hT.le (Ioo_subset_Icc_self ht)]
  simpa only [equalRateTransportRHS, one_mul] using
    (eq_sub_iff_add_eq.mpr (hsol.transport (x := x) ht)).symm

namespace Iteration

/-- Concatenation of the two equal rescaling rates. -/
def joinTimeRates {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (ρ σ : ℝ → ℝ) : ℝ → ℝ :=
  joinTimeSlabs hT hS (fun _ ↦ ρ) (fun _ ↦ σ) 0

/-- Endpoint-normalized rescaled slabs join to a classical rescaled solution on
`(0, T + S)`, including the joining time. Matching rates and one-sided time derivatives
are derived from the endpoint normalization and the PDE. -/
theorem isClassicalRescaledSolutionOn_join
    {left right : Fields} {ρ σ : ℝ → ℝ} {T S R : ℝ}
    (hT : 0 < T) (hS : 0 < S)
    (hleft : IsClassicalRescaledSolutionOn 1 left ρ ρ (Ioo 0 T))
    (hright : IsClassicalRescaledSolutionOn 1 right σ σ (Ioo 0 S))
    (hwleft : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ left.vorticity p.1 p.2))
    (hwright : Continuous (fun p : ℝ × Icc (0 : ℝ) S ↦ right.vorticity p.1 p.2))
    (huleft : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ left.velocity p.1 p.2))
    (huright : Continuous (fun p : ℝ × Icc (0 : ℝ) S ↦ right.velocity p.1 p.2))
    (hwxleft : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦
      deriv (fun y ↦ left.vorticity y p.2) p.1))
    (hwxright : Continuous (fun p : ℝ × Icc (0 : ℝ) S ↦
      deriv (fun y ↦ right.vorticity y p.2) p.1))
    (huxleft : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦
      deriv (fun y ↦ left.velocity y p.2) p.1))
    (huxright : Continuous (fun p : ℝ × Icc (0 : ℝ) S ↦
      deriv (fun y ↦ right.velocity y p.2) p.1))
    (hρ : ContinuousOn ρ (Icc 0 T)) (hσ : ContinuousOn σ (Icc 0 S))
    (hwleft' : ∀ t ∈ Icc 0 T, Differentiable ℝ (fun x ↦ left.vorticity x t))
    (hwright' : ∀ t ∈ Icc 0 S, Differentiable ℝ (fun x ↦ right.vorticity x t))
    (huleft' : ∀ t ∈ Icc 0 T, Differentiable ℝ (fun x ↦ left.velocity x t))
    (huright' : ∀ t ∈ Icc 0 S, Differentiable ℝ (fun x ↦ right.velocity x t))
    (hpair : IsHilbertPair (fun x ↦ left.vorticity x T)
      (deriv (fun x ↦ left.velocity x T)))
    (hwmatch : (fun x ↦ left.vorticity x T) = (fun x ↦ right.vorticity x 0))
    (humatch : (fun x ↦ left.velocity x T) = (fun x ↦ right.velocity x 0))
    (hρend : ρ T = -left.velocity R T / R)
    (hσstart : σ 0 = -right.velocity R 0 / R) :
    IsClassicalRescaledSolutionOn 1
      ⟨joinTimeSlabs hT.le hS.le left.vorticity right.vorticity,
        joinTimeSlabs hT.le hS.le left.velocity right.velocity⟩
      (joinTimeRates hT.le hS.le ρ σ) (joinTimeRates hT.le hS.le ρ σ)
      (Ioo 0 (T + S)) := by
  have hratematch : ρ T = σ 0 := by
    rw [hρend, hσstart, congrFun humatch R]
  have hwxmatch := congrArg deriv hwmatch
  have huxmatch := congrArg deriv humatch
  let J := joinTimeSlabs hT.le hS.le left.vorticity right.vorticity
  let U := joinTimeSlabs hT.le hS.le left.velocity right.velocity
  let C := joinTimeSlabs hT.le hS.le
    (fun x t ↦ deriv (fun y ↦ left.velocity y t) x)
    (fun x t ↦ deriv (fun y ↦ right.velocity y t) x)
  let A := joinTimeSlabs hT.le hS.le
    (fun x t ↦ deriv (fun y ↦ left.vorticity y t) x)
    (fun x t ↦ deriv (fun y ↦ right.vorticity y t) x)
  let q := equalRateTransportRHS left ρ
  let r := equalRateTransportRHS right σ
  let K := joinTimeSlabs hT.le hS.le q r
  have hmatch (x : ℝ) : left.vorticity x T = right.vorticity x 0 := congrFun hwmatch x
  have hqmatch (x : ℝ) : q x T = r x 0 := by
    dsimp only [q, r, equalRateTransportRHS]
    rw [hratematch, congrFun hwmatch x, congrFun humatch x,
      congrFun hwxmatch x, congrFun huxmatch x]
  have hqcont := continuous_equalRateTransportRHS hwleft huleft hwxleft huxleft hρ
  have hrcont := continuous_equalRateTransportRHS hwright huright hwxright huxright hσ
  have hA : Continuous (Function.uncurry A) :=
    continuous_joinTimeSlabs hT.le hS.le hwxleft hwxright (fun x ↦ congrFun hwxmatch x)
  have hK : Continuous (Function.uncurry K) :=
    continuous_joinTimeSlabs hT.le hS.le hqcont hrcont hqmatch
  have hspace (x t : ℝ) : HasDerivAt (fun y ↦ J y t) (A x t) x := by
    by_cases ht : t ≤ T
    · simpa only [J, A, joinTimeSlabs, ite_eq_left ht] using
        (hwleft' _ (projIcc 0 T hT.le t).property x).hasDerivAt
    · simpa only [J, A, joinTimeSlabs, ite_eq_right ht] using
        (hwright' _ (projIcc 0 S hS.le (t - T)).property x).hasDerivAt
  have hvelocity (x t : ℝ) : HasDerivAt (fun y ↦ U y t) (C x t) x := by
    by_cases ht : t ≤ T
    · simpa only [U, C, joinTimeSlabs, ite_eq_left ht] using
        (huleft' _ (projIcc 0 T hT.le t).property x).hasDerivAt
    · simpa only [U, C, joinTimeSlabs, ite_eq_right ht] using
        (huright' _ (projIcc 0 S hS.le (t - T)).property x).hasDerivAt
  have htime (x t : ℝ) (ht : t ∈ Ioo 0 (T + S)) : HasDerivAt (J x) (K x t) t := by
    rcases lt_trichotomy t T with hlt | heq | hgt
    · have hi : t ∈ Ioo 0 T := ⟨ht.1, hlt⟩
      have hformula : deriv (left.vorticity x) t = q x t := by
        simpa only [q, equalRateTransportRHS, one_mul] using
          eq_sub_iff_add_eq.mpr (hleft.transport (x := x) hi)
      rw [show K x t = q x t from
        joinTimeSlabs_eq_left hT.le hS.le q r x (Ioo_subset_Icc_self hi), ← hformula]
      exact (hleft.regularity.vorticity_time_differentiableAt hi).hasDerivAt.congr_of_eventuallyEq
        (joinTimeSlabs_eventuallyEq_left hT.le hS.le left.vorticity right.vorticity x hi)
    · subst t
      rw [show K x T = q x T from
        joinTimeSlabs_eq_left hT.le hS.le q r x ⟨hT.le, le_rfl⟩]
      apply hasDerivAt_joinTimeSlabs_join hT hS hmatch x (q x T)
        (hleft.hasDerivWithinAt_equalRate_terminal hT hwleft hqcont x)
      rw [hqmatch]
      exact hright.hasDerivWithinAt_equalRate_initial hS hwright hrcont x
    · have hi : t - T ∈ Ioo 0 S := ⟨sub_pos.mpr hgt, by linarith [ht.2]⟩
      have hformula : deriv (right.vorticity x) (t - T) = r x (t - T) := by
        simpa only [r, equalRateTransportRHS, one_mul] using
          eq_sub_iff_add_eq.mpr (hright.transport (x := x) hi)
      rw [show K x t = r x (t - T) from
        joinTimeSlabs_eq_right hT.le hS.le hqmatch x ⟨hgt.le, ht.2.le⟩, ← hformula]
      exact ((hright.regularity.vorticity_time_differentiableAt hi).hasDerivAt.comp_sub_const
        t T).congr_of_eventuallyEq
          (joinTimeSlabs_eventuallyEq_right hT.le hS.le hmatch x ⟨hgt, ht.2⟩)
  have hregular : ContDiffOn ℝ 1 (Function.uncurry J) (univ ×ˢ Ioo 0 (T + S)) :=
    contDiffOn_one_of_partial_derivatives (isOpen_univ.prod isOpen_Ioo)
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hA).continuousOn)
      (((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hK).continuousOn)
      (fun p _ ↦ (hspace p.1 p.2).hasFDerivAt) fun p hp ↦ (htime p.1 p.2 hp.2).hasFDerivAt
  have hKformula (x t : ℝ) : K x t =
      (joinTimeRates hT.le hS.le ρ σ t + C x t) * J x t -
        (joinTimeRates hT.le hS.le ρ σ t * x + U x t) * A x t := by
    by_cases ht : t ≤ T <;>
      simp only [K, C, J, U, A, joinTimeRates, joinTimeSlabs, ht, ↓reduceIte,
        q, r, equalRateTransportRHS]
  have hpairJ (t : ℝ) (ht : t ∈ Ioo 0 (T + S)) :
      IsHilbertPair (fun x ↦ J x t) (fun x ↦ C x t) := by
    rcases lt_trichotomy t T with hlt | rfl | hgt
    · have hi : t ∈ Icc 0 T := ⟨ht.1.le, hlt.le⟩
      simpa only [J, C, joinTimeSlabs, ite_eq_left hlt.le, projIcc_of_mem hT.le hi] using
        hleft.biotSavart ⟨ht.1, hlt⟩
    · simpa only [J, C, joinTimeSlabs, ite_eq_left le_rfl,
        projIcc_of_mem hT.le (right_mem_Icc.mpr hT.le)] using hpair
    · have hi : t - T ∈ Ioo 0 S := ⟨sub_pos.mpr hgt, by linarith [ht.2]⟩
      simpa only [J, C, joinTimeSlabs, ite_eq_right (not_le.mpr hgt),
        projIcc_of_mem hS.le (Ioo_subset_Icc_self hi)] using hright.biotSavart hi
  refine ⟨⟨fun ht ↦ (hregular.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      ⟨mem_univ _, ht⟩)).differentiableAt (by simp), fun _ ↦ (hvelocity _ _).differentiableAt⟩,
    ?_, fun t ht ↦ (hpairJ t ht).congr_right_ae (.of_forall fun x ↦ (hvelocity x t).deriv.symm)⟩
  intro x t ht
  change deriv (J x) t + (joinTimeRates hT.le hS.le ρ σ t * x + 1 * U x t) *
      deriv (fun y ↦ J y t) x =
    (joinTimeRates hT.le hS.le ρ σ t + deriv (fun y ↦ U y t) x) * J x t
  rw [(htime x t ht).deriv, (hspace x t).deriv, (hvelocity x t).deriv, one_mul, hKformula,
    sub_add_cancel]

end Iteration

end DeGregorio
