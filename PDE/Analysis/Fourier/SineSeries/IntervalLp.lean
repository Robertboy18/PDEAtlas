/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.IntervalReflection
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Square-integrable interval data on the Fourier circle

Zero extension followed by odd reflection embeds interval data into the circle.
Endpoint values have no role in this measure-theoretic construction.
-/

@[expose] public section

namespace PDE.Analysis.Fourier.SineSeries

open MeasureTheory Set AddCircle
open scoped ENNReal

/-- Continuous interval data belong to every `Lᵖ` class, including `L∞`.
No endpoint compatibility is needed for this measure-theoretic statement. -/
theorem memLp_interval_of_continuousOn {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (p : ℝ≥0∞) :
    MemLp g p (volume.restrict (Ioc 0 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  apply MemLp.of_bound ((hg.mono Ioc_subset_Icc_self).aestronglyMeasurable
    measurableSet_Ioc) C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x (Ioc_subset_Icc_self hx)

/-- The odd reflection of the zero extension from `(0, 1]`. -/
noncomputable def oddZeroExtension (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator g x - (Ioc (0 : ℝ) 1).indicator g (-x)

/-- Odd zero extension preserves square integrability. -/
theorem memLp_oddZeroExtension {g : ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    MemLp (oddZeroExtension g) 2 volume := by
  have hi : MemLp ((Ioc (0 : ℝ) 1).indicator g) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet).mpr hg
  exact hi.sub (hi.comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure ℝ)))

/-- The zero extension agrees with the initial data at positive interval points. -/
theorem oddZeroExtension_of_mem {g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    oddZeroExtension g x = g x := by
  have hn : -x ∉ Ioc (0 : ℝ) 1 := by
    intro h
    linarith [hx.1, h.1]
  simp [oddZeroExtension, hx, hn]

/-- Oddness is an exact identity for the zero extension. -/
theorem oddZeroExtension_neg (g : ℝ → ℝ) (x : ℝ) :
    oddZeroExtension g (-x) = -oddZeroExtension g x := by
  simp only [oddZeroExtension, neg_neg, neg_sub]

/-- Measurable odd interval data viewed as a function on the circle of length two. -/
noncomputable def oddIntervalFunction (g : ℝ → ℝ) : AddCircle (2 : ℝ) → ℂ :=
  AddCircle.liftIoc 2 (-1) (fun x ↦ (oddZeroExtension g x : ℂ))

/-- Odd interval reflection belongs to circle `L²` for normalized Haar measure. -/
theorem memLp_oddIntervalFunction {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    MemLp (oddIntervalFunction g) 2 haarAddCircle := by
  have h : MemLp (fun x ↦ (oddZeroExtension g x : ℂ)) 2 volume :=
    (memLp_oddZeroExtension hg).ofReal
  exact (h.restrict (Ioc (-1) (-1 + 2))).memLp_liftIoc.haarAddCircle

/-- The `L²` circle vector attached to arbitrary real interval `L²` data. -/
noncomputable def oddIntervalL2 (g : ℝ → ℝ)
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) : Lp ℂ 2 (haarAddCircle (T := (2 : ℝ))) :=
  (memLp_oddIntervalFunction hg).toLp (oddIntervalFunction g)

/-- The odd zero extension of interval `L²` data is integrable. Its support has finite
measure, even though the ambient line has infinite measure. -/
theorem integrable_oddZeroExtension {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    Integrable (oddZeroExtension g) volume := by
  have hi : Integrable ((Ioc (0 : ℝ) 1).indicator g) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (hg.integrable (by norm_num))
  exact hi.sub hi.comp_neg

private theorem integral_mul_oddZeroExtension {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1)))
    (K : ℝ → ℂ) (hK : Continuous K) :
    (∫ x in (-1 : ℝ)..1, K x * (oddZeroExtension g x : ℂ)) =
      ∫ x in (0 : ℝ)..1, (K x - K (-x)) * (g x : ℂ) := by
  have hi : Integrable (fun x ↦ (oddZeroExtension g x : ℂ)) volume :=
    (integrable_oddZeroExtension hg).ofReal
  have hprod (a b : ℝ) :
      IntervalIntegrable (fun x ↦ K x * (oddZeroExtension g x : ℂ)) volume a b :=
    hi.intervalIntegrable.continuousOn_mul hK.continuousOn
  have hpos : (∫ x in (0 : ℝ)..1, K x * (oddZeroExtension g x : ℂ)) =
      ∫ x in (0 : ℝ)..1, K x * (g x : ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only
    rw [oddZeroExtension_of_mem ⟨hx.1, hx.2.le⟩]
  have hneg : (∫ x in (-1 : ℝ)..0, K x * (oddZeroExtension g x : ℂ)) =
      ∫ x in (0 : ℝ)..1, -(K (-x) * (g x : ℂ)) := by
    rw [← show (∫ x in (0 : ℝ)..1, K (-x) * (oddZeroExtension g (-x) : ℂ)) =
      ∫ x in (-1 : ℝ)..0, K x * (oddZeroExtension g x : ℂ) from by
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg
            (f := fun x ↦ K x * (oddZeroExtension g x : ℂ)) (a := (0 : ℝ)) (b := 1))]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only
    rw [oddZeroExtension_neg, oddZeroExtension_of_mem ⟨hx.1, hx.2.le⟩,
      Complex.ofReal_neg, mul_neg]
  have hg' : IntervalIntegrable (fun x ↦ (g x : ℂ)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (hg.integrable (by norm_num)).ofReal
  rw [← intervalIntegral.integral_add_adjacent_intervals (hprod (-1) 0) (hprod 0 1),
    hneg, hpos, intervalIntegral.integral_neg]
  have hj : IntervalIntegrable (fun x ↦ K (-x) * (g x : ℂ)) volume 0 1 :=
    hg'.continuousOn_mul (hK.comp continuous_neg).continuousOn
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (hg'.continuousOn_mul hK.continuousOn) hj]
  ring

/-- Fourier coefficients of arbitrary interval `L²` data are the usual sine integrals
after odd reflection. Endpoint values and pointwise Fourier convergence are not used. -/
theorem fourierCoeff_oddIntervalL2 {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (k : ℤ) :
    fourierCoeff (oddIntervalL2 g hg) k =
      -Complex.I * (∫ x in (0 : ℝ)..1, g x * Real.sin ((k : ℝ) * Real.pi * x) : ℝ) := by
  unfold oddIntervalL2
  rw [fourierCoeff_congr_ae (memLp_oddIntervalFunction hg).coeFn_toLp,
    oddIntervalFunction, fourierCoeff_eq_intervalIntegral _ _ (-1)]
  simp only [show (-1 : ℝ) + 2 = 1 by norm_num, smul_eq_mul]
  have heq :
      (∫ x in (-1 : ℝ)..1, fourier (-k) (x : AddCircle (2 : ℝ)) *
        liftIoc 2 (-1) (fun y ↦ (oddZeroExtension g y : ℂ)) (x : AddCircle (2 : ℝ))) =
      ∫ x in (-1 : ℝ)..1, fourier (-k) (x : AddCircle (2 : ℝ)) *
        (oddZeroExtension g x : ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only
    rw [liftIoc_coe_apply (show x ∈ Ioc (-1 : ℝ) (-1 + 2) from
      ⟨hx.1, by linarith [hx.2]⟩)]
  rw [heq, integral_mul_oddZeroExtension hg
    (fun x ↦ fourier (-k) (x : AddCircle (2 : ℝ))) (by fun_prop)]
  simp_rw [fourier_sub_reflection]
  have hmul (x : ℝ) :
      -2 * Complex.I * (Real.sin ((k : ℝ) * Real.pi * x) : ℂ) * (g x : ℂ) =
        (-2 * Complex.I) * ((g x * Real.sin ((k : ℝ) * Real.pi * x) : ℝ) : ℂ) := by
    push_cast
    ring
  simp_rw [hmul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  simp only [Complex.real_smul]
  push_cast
  ring

end PDE.Analysis.Fourier.SineSeries
