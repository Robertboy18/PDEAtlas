/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.Rellich.Translation
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Spaces.Sobolev.Compactness.Rellich.Topology

/-!
# Finite-cell averaging on global L¹

This is the `L¹` counterpart of `Rellich.CellAverages` and `Rellich.Translation`, needed for the
endpoint `p = 1` of the Rellich–Kondrachov theorem. Averaging an `L¹(ℝ^n)` function over each cell
of a finite family is a finite-rank operator, and for a cell `s` of finite positive measure the
averaging error obeys

  `∫_s |f - ⨍_s f| ≤ |s|⁻¹ ∫_s ∫_s |f x - f y| dx dy`,

by the triangle inequality for integrals in place of the Jensen step used in `L²`. For
pairwise-disjoint cells covering the support of `f` the global error is the sum of the cellwise
errors. Writing the pairwise oscillation in translation coordinates via the measure-preserving shear
`(x, h) ↦ (x, x + h)` bounds the total oscillation over lattice cells of mesh `δ` by
`∫_{[-δ,δ]ⁿ} ‖τ_h f - f‖_{L¹} dh`. Combined with the `W^{1,1}` translation estimate this yields a
finite-rank approximation in the manner of the Kolmogorov–Riesz–Fréchet compactness criterion
(Brezis, Chapter 4), here for `L¹`.

## Main definitions and results

* `setIntegralL1CLM s`: integration over `s` as a bounded functional on
  `L¹(ℝ^n)`.
* `cellIndicatorL1`, `cellAverageL1`: the cell indicator and the rank-one
  averaging operator `f ↦ (⨍_s f) 𝟙_s`, factored through `ℝ`; it is compact
  (`cellAverageL1.isCompactOperator`) and represented almost everywhere by the
  cell mean (`cellAverageL1_apply_ae`).
* `finiteCellAverageL1` and its compactness, representative formula, and error
  identities `finiteCellAverageL1.norm_sub_eq_sum`,
  `finiteCellAverageL1.norm_sub_le_pairwise`.
* `abs_sub_cellAverage_le`, `setIntegral_abs_sub_cellAverage_le_pairwise`: the
  one-cell oscillation bounds.
* `norm_translateL1_sub_eq_integral`,
  `integral_pairwise_abs_eq_withinCellTranslations`,
  `sum_integral_gridCellTranslations_le_norm_translateL1_sub`,
  `sum_gridCell_pairwise_abs_le_integral_translateL1`: translation-coordinate
  forms of the oscillation and the grid bound.

## Implementation notes

In `L²` the cell average is the orthogonal rank-one operator
`⟨𝟙_s, ·⟩ 𝟙_s / |s|`.  Without an inner product we instead compose the
functional `setIntegralL1CLM s` with `toSpanSingleton` on the indicator, so
finite rank, and hence compactness, is explicit.  Cells of measure zero give
the zero operator; positivity is required only in the oscillation estimates.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 4, for the Kolmogorov–Riesz–Fréchet compactness criterion in `L^p`.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace RellichKondrachov

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ}

/-! ## The `W^{1,1} → L¹` endpoint

The Hilbert-space cell averages in `Rellich` use orthogonal rank-one
operators.  At the endpoint there is no inner product, so each cell average
is factored through the one-dimensional space `ℝ`.  This gives the
finite-rank part of the compactness proof in `L¹`.
-/

section EndpointL1

/-- Integration over a measurable subset, as a bounded functional on global
`L¹`.  The restriction map is part of the definition so the statement does
not require a finite ambient measure. -/
noncomputable def setIntegralL1CLM (s : Set (ℝ^n)) :
    DerivLp n 1 Set.univ →L[ℝ] ℝ :=
  (MeasureTheory.L1.integralCLM
      (α := ℝ^n) (E := ℝ)
      (μ := (domainMeasure n Set.univ).restrict s)).comp
    (MeasureTheory.LpToLpRestrictCLM
      (ℝ^n) ℝ ℝ (domainMeasure n Set.univ) 1 s)

/-- The bounded functional `setIntegralL1CLM s` is the set integral `∫_s f`. -/
@[simp]
theorem setIntegralL1CLM_apply
    (s : Set (ℝ^n)) (f : DerivLp n 1 Set.univ) :
    setIntegralL1CLM s f = ∫ x in s, f x := by
  rw [setIntegralL1CLM, ContinuousLinearMap.comp_apply,
    ← MeasureTheory.L1.integral_eq,
    MeasureTheory.L1.integral_eq_integral]
  simpa [domainMeasure] using
    (MeasureTheory.integral_congr_ae
      (MeasureTheory.LpToLpRestrictCLM_coeFn ℝ s f))

/-- The characteristic function of a finite-measure cell, bundled in global
`L¹`. -/
noncomputable def cellIndicatorL1
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hfinite : (domainMeasure n Set.univ) s ≠ ∞) :
    DerivLp n 1 Set.univ :=
  MeasureTheory.indicatorConstLp 1 hs hfinite (1 : ℝ)

/-- Replace a global `L¹` function on `s` by its integral average on `s` and
by zero off `s`.  It is written as a composition through `ℝ`, making its
finite rank explicit. -/
noncomputable def cellAverageL1
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hfinite : (domainMeasure n Set.univ) s ≠ ∞) :
    DerivLp n 1 Set.univ →L[ℝ] DerivLp n 1 Set.univ :=
  ((domainMeasure n Set.univ).real s)⁻¹ •
    (ContinuousLinearMap.toSpanSingleton ℝ
      (cellIndicatorL1 s hs hfinite)).comp
        (setIntegralL1CLM s)

/-- A one-cell `L¹` averaging operator is compact because it factors through
the locally compact one-dimensional space `ℝ`. -/
theorem cellAverageL1.isCompactOperator
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hfinite : (domainMeasure n Set.univ) s ≠ ∞) :
    IsCompactOperator (cellAverageL1 s hs hfinite) := by
  unfold cellAverageL1
  exact
    ((isCompactOperator_of_locallyCompactSpace_rng
      (ContinuousLinearMap.toSpanSingleton ℝ
        (cellIndicatorL1 s hs hfinite))).comp_clm
          (setIntegralL1CLM s)).smul
      (((domainMeasure n Set.univ).real s)⁻¹ : ℝ)

/-- One-cell `L¹` averaging is the normalized cell integral times the cell
indicator. -/
theorem cellAverageL1_apply
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hfinite : (domainMeasure n Set.univ) s ≠ ∞)
    (f : DerivLp n 1 Set.univ) :
    cellAverageL1 s hs hfinite f =
      (((domainMeasure n Set.univ).real s)⁻¹ *
        (∫ x in s, f x)) • cellIndicatorL1 s hs hfinite := by
  simp [cellAverageL1, setIntegralL1CLM_apply, smul_smul]

/-- The one-cell `L¹` average is represented almost everywhere by the
cellwise mean, extended by zero off the cell. -/
theorem cellAverageL1_apply_ae
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hfinite : (domainMeasure n Set.univ) s ≠ ∞)
    (f : DerivLp n 1 Set.univ) :
    ((cellAverageL1 s hs hfinite f :
        DerivLp n 1 Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
      s.indicator (fun _ ↦
        ((domainMeasure n Set.univ).real s)⁻¹ * (∫ x in s, f x)) := by
  rw [cellAverageL1_apply]
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul
      (((domainMeasure n Set.univ).real s)⁻¹ * (∫ x in s, f x))
      (cellIndicatorL1 s hs hfinite),
    MeasureTheory.indicatorConstLp_coeFn
      (p := (1 : ℝ≥0∞)) (hs := hs) (hμs := hfinite)
      (c := (1 : ℝ))] with x hsmul hx
  rw [hsmul]
  change
    (((domainMeasure n Set.univ).real s)⁻¹ * (∫ x in s, f x)) *
        cellIndicatorL1 s hs hfinite x = _
  rw [show cellIndicatorL1 s hs hfinite x =
      s.indicator (fun _ ↦ (1 : ℝ)) x by exact hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Averaging over a finite collection of measurable cells in global `L¹`. -/
noncomputable def finiteCellAverageL1
    {ι : Type*} (I : Finset ι) (cell : ι → Set (ℝ^n))
    (hcell : ∀ i, MeasurableSet (cell i))
    (hfinite : ∀ i, (domainMeasure n Set.univ) (cell i) ≠ ∞) :
    DerivLp n 1 Set.univ →L[ℝ] DerivLp n 1 Set.univ :=
  ∑ i ∈ I, cellAverageL1 (cell i) (hcell i) (hfinite i)

/-- A finite sum of one-cell `L¹` averaging operators is compact. -/
theorem finiteCellAverageL1.isCompactOperator
    {ι : Type*} (I : Finset ι) (cell : ι → Set (ℝ^n))
    (hcell : ∀ i, MeasurableSet (cell i))
    (hfinite : ∀ i, (domainMeasure n Set.univ) (cell i) ≠ ∞) :
    IsCompactOperator (finiteCellAverageL1 I cell hcell hfinite) := by
  unfold finiteCellAverageL1
  apply Rellich.isCompactOperator_finset_sum
  intro i _
  exact cellAverageL1.isCompactOperator
    (cell i) (hcell i) (hfinite i)

/-- Finite-cell `L¹` averaging is represented almost everywhere by the sum
of the cellwise means extended by zero. -/
theorem finiteCellAverageL1_apply_ae
    {ι : Type*} (I : Finset ι) (cell : ι → Set (ℝ^n))
    (hcell : ∀ i, MeasurableSet (cell i))
    (hfinite : ∀ i, (domainMeasure n Set.univ) (cell i) ≠ ∞)
    (f : DerivLp n 1 Set.univ) :
    ((finiteCellAverageL1 I cell hcell hfinite f :
        DerivLp n 1 Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
      fun x ↦ ∑ i ∈ I,
        (cell i).indicator (fun _ ↦
          ((domainMeasure n Set.univ).real (cell i))⁻¹ *
            ∫ y in cell i, f y) x := by
  classical
  induction I using Finset.induction with
  | empty =>
      simp only [finiteCellAverageL1, Finset.sum_empty]
      exact MeasureTheory.Lp.coeFn_zero ℝ (1 : ℝ≥0∞) (domainMeasure n Set.univ)
  | @insert i I hi ih =>
      have hop : finiteCellAverageL1 (insert i I) cell hcell hfinite f =
          cellAverageL1 (cell i) (hcell i) (hfinite i) f +
            finiteCellAverageL1 I cell hcell hfinite f := by
        simp [finiteCellAverageL1, hi]
      rw [hop]
      filter_upwards [MeasureTheory.Lp.coeFn_add (cellAverageL1 (cell i) (hcell i) (hfinite i) f)
          (finiteCellAverageL1 I cell hcell hfinite f),
        cellAverageL1_apply_ae (cell i) (hcell i) (hfinite i) f, ih] with x hadd hix hIx
      rw [hadd, Pi.add_apply, hix, hIx, Finset.sum_insert hi]

/-- Pointwise deviation from a cell average is bounded by the average
absolute pairwise oscillation. -/
theorem abs_sub_cellAverage_le
    (s : Set (ℝ^n))
    (hs0 : (domainMeasure n Set.univ) s ≠ 0)
    (hfinite : (domainMeasure n Set.univ) s ≠ ∞)
    (f : DerivLp n 1 Set.univ) (x : ℝ^n) :
    |f x - ((domainMeasure n Set.univ).real s)⁻¹ *
      (∫ y in s, f y ∂domainMeasure n Set.univ)| ≤
      ((domainMeasure n Set.univ).real s)⁻¹ *
        ∫ y in s, |f x - f y| ∂domainMeasure n Set.univ := by
  let μ := domainMeasure n Set.univ
  have hmpos : 0 < μ.real s := ENNReal.toReal_pos hs0 hfinite
  change |f x - (μ.real s)⁻¹ * (∫ y in s, f y ∂μ)| ≤ (μ.real s)⁻¹ * ∫ y in s, |f x - f y| ∂μ
  -- the deviation is the average of `f x - f y`, and `|∫ g| ≤ ∫ |g|`
  have hdev : f x - (μ.real s)⁻¹ * (∫ y in s, f y ∂μ) =
      (μ.real s)⁻¹ * ∫ y in s, (f x - f y) ∂μ := by
    rw [integral_sub (integrableOn_const hfinite) (L1.integrable_coeFn f).integrableOn,
      setIntegral_const, smul_eq_mul, mul_sub, inv_mul_cancel_left₀ hmpos.ne']
  rw [hdev, abs_mul, abs_of_nonneg (inv_nonneg.mpr hmpos.le)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hmpos.le)

/-- Absolute pairwise oscillation of a global `L¹` function is integrable on
the square of a finite-measure cell. -/
theorem integrableOn_pairwise_abs_sub
    (s : Set (ℝ^n))
    (hfinite : (domainMeasure n Set.univ) s ≠ ∞)
    (f : DerivLp n 1 Set.univ) :
    IntegrableOn (fun p : ℝ^n × ℝ^n ↦ |f p.1 - f p.2|)
      (s ×ˢ s)
      ((domainMeasure n Set.univ).prod (domainMeasure n Set.univ)) := by
  let μ := domainMeasure n Set.univ
  have : IsFiniteMeasure (μ.restrict s) :=
    MeasureTheory.isFiniteMeasure_restrict.2 hfinite
  have hf : Integrable (fun x ↦ f x) (μ.restrict s) :=
    (MeasureTheory.L1.integrable_coeFn f).integrableOn
  have hfst : Integrable (fun p : ℝ^n × ℝ^n ↦ f p.1)
      ((μ.restrict s).prod (μ.restrict s)) :=
    hf.comp_fst (μ.restrict s)
  have hsnd : Integrable (fun p : ℝ^n × ℝ^n ↦ f p.2)
      ((μ.restrict s).prod (μ.restrict s)) :=
    hf.comp_snd (μ.restrict s)
  change Integrable (fun p : ℝ^n × ℝ^n ↦ |f p.1 - f p.2|)
    ((μ.prod μ).restrict (s ×ˢ s))
  rw [← Measure.prod_restrict]
  exact (hfst.sub hsnd).norm

/-- The `L¹` error on one cell is bounded by its normalized pairwise
oscillation. -/
theorem setIntegral_abs_sub_cellAverage_le_pairwise
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hs0 : (domainMeasure n Set.univ) s ≠ 0)
    (hfinite : (domainMeasure n Set.univ) s ≠ ∞)
    (f : DerivLp n 1 Set.univ) :
    (∫ x in s,
      |f x - ((domainMeasure n Set.univ).real s)⁻¹ *
        (∫ y in s, f y ∂domainMeasure n Set.univ)|
        ∂domainMeasure n Set.univ) ≤
      ((domainMeasure n Set.univ).real s)⁻¹ *
        ∫ x in s, ∫ y in s, |f x - f y|
          ∂domainMeasure n Set.univ ∂domainMeasure n Set.univ := by
  let μ := domainMeasure n Set.univ
  have hpairProd : Integrable (fun p : ℝ^n × ℝ^n ↦ |f p.1 - f p.2|)
      ((μ.restrict s).prod (μ.restrict s)) := by
    rw [Measure.prod_restrict]
    simpa [μ, domainMeasure, IntegrableOn] using integrableOn_pairwise_abs_sub s hfinite f
  have hinner : Integrable (fun x ↦ ∫ y in s, |f x - f y| ∂μ) (μ.restrict s) := by
    simpa only using hpairProd.integral_prod_left
  change (∫ x in s, |f x - (μ.real s)⁻¹ * (∫ y in s, f y ∂μ)| ∂μ) ≤
    (μ.real s)⁻¹ * ∫ x in s, ∫ y in s, |f x - f y| ∂μ ∂μ
  exact (setIntegral_mono_on
    ((L1.integrable_coeFn f).integrableOn.sub (integrableOn_const hfinite)).norm
    (hinner.const_mul _) hs fun x _ ↦ abs_sub_cellAverage_le s hs0 hfinite f x).trans_eq
    (integral_const_mul _ _)

/-- For disjoint cells covering the support, the global `L¹` error of the
finite-cell average is the sum of its cellwise errors. -/
theorem finiteCellAverageL1.norm_sub_eq_sum
    {ι : Type*} (I : Finset ι) (cell : ι → Set (ℝ^n))
    (hcell : ∀ i, MeasurableSet (cell i))
    (hfinite : ∀ i, (domainMeasure n Set.univ) (cell i) ≠ ∞)
    (hdisjoint : Set.Pairwise (↑I : Set ι) (Disjoint on cell))
    (f : DerivLp n 1 Set.univ)
    (hsupport : ∀ᵐ x ∂domainMeasure n Set.univ,
      x ∉ ⋃ i ∈ I, cell i → f x = 0) :
    ‖finiteCellAverageL1 I cell hcell hfinite f - f‖ =
      ∑ i ∈ I, ∫ x in cell i,
        |f x - ((domainMeasure n Set.univ).real (cell i))⁻¹ *
          (∫ y in cell i, f y ∂domainMeasure n Set.univ)|
          ∂domainMeasure n Set.univ := by
  classical
  let μ := domainMeasure n Set.univ
  let P : DerivLp n 1 Set.univ := finiteCellAverageL1 I cell hcell hfinite f
  let U : Set (ℝ^n) := ⋃ i ∈ I, cell i
  let g : ℝ^n → ℝ := fun x ↦
    (∑ i ∈ I, (cell i).indicator (fun _ ↦ (μ.real (cell i))⁻¹ * ∫ y in cell i, f y ∂μ) x) - f x
  have hP : (P : ℝ^n → ℝ) =ᵐ[μ] fun x ↦
      ∑ i ∈ I, (cell i).indicator (fun _ ↦ (μ.real (cell i))⁻¹ * ∫ y in cell i, f y ∂μ) x := by
    simpa [P, μ] using finiteCellAverageL1_apply_ae I cell hcell hfinite f
  have hsub : ((P - f : DerivLp n 1 Set.univ) : ℝ^n → ℝ) =ᵐ[μ] g := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub P f, hP] with x hx hPx
    rw [hx, Pi.sub_apply, hPx]
  have hgInt : Integrable (fun x ↦ |g x|) μ :=
    (MeasureTheory.L1.integrable_coeFn (P - f)).norm.congr (hsub.fun_comp abs)
  have hgZero : ∀ᵐ x ∂μ, x ∉ U → g x = 0 := by
    filter_upwards [hsupport] with x hfx hxU
    simp only [g, hfx hxU, sub_zero]
    exact Finset.sum_eq_zero fun i hi ↦
      indicator_of_notMem (fun hxi ↦ hxU (mem_iUnion₂_of_mem hi hxi)) _
  calc
    ‖finiteCellAverageL1 I cell hcell hfinite f - f‖ = ∫ x, |g x| ∂μ := by
      change ‖P - f‖ = _
      rw [MeasureTheory.L1.norm_eq_integral_norm]
      simpa [Real.norm_eq_abs, Function.comp_def, μ] using
        MeasureTheory.integral_congr_ae (hsub.fun_comp abs)
    _ = ∫ x in U, |g x| ∂μ := by
      rw [← MeasureTheory.integral_indicator (Finset.measurableSet_biUnion I fun i _ ↦ hcell i)]
      exact MeasureTheory.integral_congr_ae (hgZero.mono fun x hx ↦
        ((indicator_apply_eq_self (s := U) (f := fun x ↦ |g x|)).2 fun hxU ↦ by
          rw [hx hxU, abs_zero]).symm)
    _ = ∑ i ∈ I, ∫ x in cell i, |g x| ∂μ :=
      MeasureTheory.integral_biUnion_finset I (fun i _ ↦ hcell i) hdisjoint
        fun _ _ ↦ hgInt.integrableOn
    _ = ∑ i ∈ I, ∫ x in cell i, |f x - (μ.real (cell i))⁻¹ * (∫ y in cell i, f y ∂μ)| ∂μ := by
      refine Finset.sum_congr rfl fun i hi ↦ setIntegral_congr_fun (hcell i) fun x hxi ↦ ?_
      -- on `cell i` only the `i`-th indicator survives, since the cells are disjoint
      have hsum : (∑ j ∈ I, (cell j).indicator
          (fun _ ↦ (μ.real (cell j))⁻¹ * ∫ y in cell j, f y ∂μ) x) =
          (μ.real (cell i))⁻¹ * ∫ y in cell i, f y ∂μ := by
        rw [Finset.sum_eq_single_of_mem i hi fun j hj hji ↦ indicator_of_notMem
          (disjoint_left.1 (hdisjoint (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hj) hji.symm) hxi) _,
          indicator_of_mem hxi]
      have hgx : g x = (μ.real (cell i))⁻¹ * (∫ y in cell i, f y ∂μ) - f x :=
        congrArg (· - f x) hsum
      rw [hgx, abs_sub_comm]

/-- The global finite-cell `L¹` error is bounded by normalized pairwise
oscillation on the cells. -/
theorem finiteCellAverageL1.norm_sub_le_pairwise
    {ι : Type*} (I : Finset ι) (cell : ι → Set (ℝ^n))
    (hcell : ∀ i, MeasurableSet (cell i))
    (hpositive : ∀ i ∈ I, (domainMeasure n Set.univ) (cell i) ≠ 0)
    (hfinite : ∀ i, (domainMeasure n Set.univ) (cell i) ≠ ∞)
    (hdisjoint : Set.Pairwise (↑I : Set ι) (Disjoint on cell))
    (f : DerivLp n 1 Set.univ)
    (hsupport : ∀ᵐ x ∂domainMeasure n Set.univ,
      x ∉ ⋃ i ∈ I, cell i → f x = 0) :
    ‖finiteCellAverageL1 I cell hcell hfinite f - f‖ ≤
      ∑ i ∈ I,
        ((domainMeasure n Set.univ).real (cell i))⁻¹ *
          ∫ x in cell i, ∫ y in cell i, |f x - f y|
            ∂domainMeasure n Set.univ ∂domainMeasure n Set.univ := by
  rw [finiteCellAverageL1.norm_sub_eq_sum
    I cell hcell hfinite hdisjoint f hsupport]
  apply Finset.sum_le_sum
  intro i hi
  exact setIntegral_abs_sub_cellAverage_le_pairwise
    (cell i) (hcell i) (hpositive i hi) (hfinite i) f

/-- A representative of the `L¹` translation defect `τ_h f - f`. -/
private theorem translateL1_sub_ae_eq (h : ℝ^n) (f : DerivLp n 1 Set.univ) :
    ((Rellich.translateLp 1 h f - f : DerivLp n 1 Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume] fun x ↦ f (x + h) - f x := by
  have htrans : ((Rellich.translateLp 1 h f : DerivLp n 1 Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume] fun x ↦ f (x + h) := by
    simpa [domainMeasure] using Rellich.translateLp_apply_ae (n := n) (p := (1 : ℝ≥0∞)) h f
  have hsub : ((Rellich.translateLp 1 h f - f : DerivLp n 1 Set.univ) : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume] (Rellich.translateLp 1 h f : ℝ^n → ℝ) - (f : ℝ^n → ℝ) := by
    simpa [domainMeasure] using MeasureTheory.Lp.coeFn_sub (Rellich.translateLp 1 h f) f
  filter_upwards [hsub, htrans] with x hsub hxtrans
  rw [hsub, Pi.sub_apply, hxtrans]

/-- Representative formula for the `L¹` norm of a translation defect. -/
theorem norm_translateL1_sub_eq_integral
    (h : ℝ^n) (f : DerivLp n 1 Set.univ) :
    ‖Rellich.translateLp 1 h f - f‖ =
      ∫ x : ℝ^n, |f (x + h) - f x| := by
  rw [MeasureTheory.L1.norm_eq_integral_norm]
  simpa [domainMeasure, Real.norm_eq_abs] using
    MeasureTheory.integral_congr_ae ((translateL1_sub_ae_eq h f).fun_comp fun z ↦ ‖z‖)

/-- One-cell pairwise `L¹` oscillation in translation coordinates. -/
theorem integral_pairwise_abs_eq_withinCellTranslations
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hfinite : (MeasureTheory.volume : Measure (ℝ^n)) s ≠ ∞)
    (f : DerivLp n 1 Set.univ) :
    (∫ x in s, ∫ y in s, |f x - f y|) =
      ∫ h : ℝ^n, ∫ x : ℝ^n,
        (s ×ˢ s).indicator
          (fun p : ℝ^n × ℝ^n ↦ |f p.1 - f p.2|)
          (x, x + h) := by
  let G : ℝ^n × ℝ^n → ℝ := fun p ↦ |f p.1 - f p.2|
  have hGon : IntegrableOn G (s ×ˢ s)
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) := by
    simpa [G, domainMeasure] using
      integrableOn_pairwise_abs_sub (n := n) s (by simpa [domainMeasure] using hfinite) f
  -- the shear `(x, h) ↦ (x, x + h)` preserves the product measure
  let shear : ℝ^n × ℝ^n → ℝ^n × ℝ^n := fun p ↦ (p.1, p.1 + p.2)
  have hpres : MeasurePreserving shear
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume)
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) := by
    simpa [shear] using MeasureTheory.measurePreserving_prod_add
      (MeasureTheory.volume : Measure (ℝ^n)) (MeasureTheory.volume : Measure (ℝ^n))
  calc
    (∫ x in s, ∫ y in s, |f x - f y|) =
        ∫ p : ℝ^n × ℝ^n, (s ×ˢ s).indicator G p
          ∂((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) := by
      rw [MeasureTheory.integral_indicator (hs.prod hs), MeasureTheory.setIntegral_prod _ hGon]
    _ = ∫ p : ℝ^n × ℝ^n, ((s ×ˢ s).indicator G) (shear p)
          ∂((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) :=
      (hpres.integral_comp (MeasurableEquiv.shearAddRight (ℝ^n)).measurableEmbedding _).symm
    _ = _ := by
      with_reducible_and_instances
        simpa [Function.comp_def, shear] using MeasureTheory.integral_prod_symm
          (((s ×ˢ s).indicator G) ∘ shear)
          (hpres.integrable_comp_of_integrable (hGon.integrable_indicator (hs.prod hs)))

/-- The outer integrand of the shear formula
`integral_pairwise_abs_eq_withinCellTranslations`, namely
`h ↦ ∫ 𝟙_{s×s}(x, x+h) |f x - f(x+h)| dx`, is integrable in `h`; this is the
Fubini hypothesis for exchanging the order of integration over the grid. -/
theorem integrable_integral_withinCellTranslations_abs
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hfinite : (MeasureTheory.volume : Measure (ℝ^n)) s ≠ ∞)
    (f : DerivLp n 1 Set.univ) :
    Integrable (fun h : ℝ^n ↦ ∫ x : ℝ^n,
      (s ×ˢ s).indicator
        (fun p : ℝ^n × ℝ^n ↦ |f p.1 - f p.2|)
        (x, x + h)) MeasureTheory.volume := by
  have hGon : IntegrableOn (fun p : ℝ^n × ℝ^n ↦ |f p.1 - f p.2|) (s ×ˢ s)
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) := by
    simpa [domainMeasure] using
      integrableOn_pairwise_abs_sub (n := n) s (by simpa [domainMeasure] using hfinite) f
  have hpres : MeasurePreserving (fun p : ℝ^n × ℝ^n ↦ (p.1, p.1 + p.2))
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume)
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) := by
    simpa using MeasureTheory.measurePreserving_prod_add
      (MeasureTheory.volume : Measure (ℝ^n)) (MeasureTheory.volume : Measure (ℝ^n))
  simpa [Function.comp_def] using (hpres.integrable_comp_of_integrable
    (hGon.integrable_indicator (hs.prod hs))).integral_prod_right

/-- At a fixed shift, disjoint within-cell oscillations are bounded by the
global `L¹` translation defect. -/
theorem sum_integral_gridCellTranslations_le_norm_translateL1_sub
    {δ : ℝ} (hδ : 0 < δ) (I : Finset (Fin n → ℤ))
    (f : DerivLp n 1 Set.univ) (h : ℝ^n) :
    (∑ k ∈ I, ∫ x : ℝ^n,
      (Rellich.euclideanGridCell (n := n) δ k ×ˢ
          Rellich.euclideanGridCell (n := n) δ k).indicator
        (fun p : ℝ^n × ℝ^n ↦ |f p.1 - f p.2|)
        (x, x + h)) ≤ ‖Rellich.translateLp 1 h f - f‖ := by
  let cell : (Fin n → ℤ) → Set (ℝ^n) := Rellich.euclideanGridCell (n := n) δ
  let A : (Fin n → ℤ) → Set (ℝ^n) := fun k ↦ cell k ∩ (fun x : ℝ^n ↦ x + h) ⁻¹' cell k
  let D : ℝ^n → ℝ := fun x ↦ |f x - f (x + h)|
  have hAmeas (k : Fin n → ℤ) : MeasurableSet (A k) :=
    (Rellich.measurableSet_euclideanGridCell (n := n) δ k).inter
      ((Rellich.measurableSet_euclideanGridCell (n := n) δ k).preimage
        (measurable_id.add measurable_const))
  have hAdisjoint : Set.Pairwise (↑I : Set (Fin n → ℤ)) (Disjoint on A) := fun k _ l _ hkl ↦
    (Rellich.disjoint_euclideanGridCell_of_ne (n := n) hδ hkl).mono inter_subset_left
      inter_subset_left
  have hD : Integrable D MeasureTheory.volume := by
    have hint : Integrable (fun x ↦ |((Rellich.translateLp 1 h f - f :
        DerivLp n 1 Set.univ) : ℝ^n → ℝ) x|) MeasureTheory.volume := by
      simpa [domainMeasure, Real.norm_eq_abs] using
        (MeasureTheory.L1.integrable_coeFn (Rellich.translateLp 1 h f - f)).norm
    exact hint.congr ((translateL1_sub_ae_eq h f).mono fun x hx ↦ by
      simp only [D]
      rw [hx, abs_sub_comm])
  calc
    _ = ∑ k ∈ I, ∫ x in A k, D x := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← MeasureTheory.integral_indicator (hAmeas k)]
      refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ cell k <;> by_cases hxh : x + h ∈ cell k <;> simp [A, D, cell, hx, hxh]
    _ = ∫ x in ⋃ k ∈ I, A k, D x := (MeasureTheory.integral_biUnion_finset I
      (fun k _ ↦ hAmeas k) hAdisjoint fun _ _ ↦ hD.integrableOn).symm
    _ ≤ ∫ x : ℝ^n, D x :=
      MeasureTheory.setIntegral_le_integral hD (.of_forall fun x ↦ abs_nonneg _)
    _ = ‖Rellich.translateLp 1 h f - f‖ := by
      rw [norm_translateL1_sub_eq_integral]
      exact MeasureTheory.integral_congr_ae (.of_forall fun x ↦ abs_sub_comm _ _)

/-- Total pairwise `L¹` oscillation over regular grid cells is controlled by
the translation modulus integrated over their common difference box. -/
theorem sum_gridCell_pairwise_abs_le_integral_translateL1
    {δ : ℝ} (hδ : 0 < δ) (I : Finset (Fin n → ℤ))
    (f : DerivLp n 1 Set.univ) :
    (∑ k ∈ I,
      ∫ x in Rellich.euclideanGridCell (n := n) δ k,
      ∫ y in Rellich.euclideanGridCell (n := n) δ k,
        |f x - f y|) ≤
      ∫ h in Rellich.euclideanDifferenceBox (n := n) δ,
        ‖Rellich.translateLp 1 h f - f‖ := by
  let cell : (Fin n → ℤ) → Set (ℝ^n) := Rellich.euclideanGridCell (n := n) δ
  let K : (Fin n → ℤ) → ℝ^n → ℝ := fun k h ↦ ∫ x : ℝ^n,
    (cell k ×ˢ cell k).indicator (fun p : ℝ^n × ℝ^n ↦ |f p.1 - f p.2|) (x, x + h)
  let T : ℝ^n → ℝ := fun h ↦ ‖Rellich.translateLp 1 h f - f‖
  have hcell (k : Fin n → ℤ) := Rellich.measurableSet_euclideanGridCell (n := n) δ k
  have hfin (k : Fin n → ℤ) : (MeasureTheory.volume : Measure (ℝ^n)) (cell k) ≠ ∞ := by
    simp [cell, Rellich.volume_euclideanGridCell]
  have hKint (k : Fin n → ℤ) : Integrable (K k) MeasureTheory.volume :=
    integrable_integral_withinCellTranslations_abs (n := n) (cell k) (hcell k) (hfin k) f
  have hbox := Rellich.measurableSet_euclideanDifferenceBox (n := n) δ
  have hTIndicator : Integrable ((Rellich.euclideanDifferenceBox (n := n) δ).indicator T)
      MeasureTheory.volume :=
    (((Rellich.continuous_translateLp (n := n) 1 (by norm_num) f).sub
      continuous_const).norm.continuousOn.integrableOn_compact
        (Rellich.isCompact_euclideanDifferenceBox (n := n) δ)).integrable_indicator hbox
  -- outside the difference box no shift keeps a point in its cell
  have hpoint (h : ℝ^n) :
      (∑ k ∈ I, K k h) ≤ (Rellich.euclideanDifferenceBox (n := n) δ).indicator T h := by
    by_cases hh : h ∈ Rellich.euclideanDifferenceBox (n := n) δ
    · rw [indicator_of_mem hh]
      exact sum_integral_gridCellTranslations_le_norm_translateL1_sub (n := n) hδ I f h
    · rw [indicator_of_notMem hh]
      refine (Finset.sum_eq_zero fun k _ ↦ MeasureTheory.integral_eq_zero_of_ae
        (.of_forall fun x ↦ indicator_of_notMem (fun hpair ↦ hh ?_) _)).le
      simpa using Rellich.sub_mem_euclideanDifferenceBox_of_mem_gridCell (n := n) hpair.1 hpair.2
  calc
    _ = ∑ k ∈ I, ∫ h : ℝ^n, K k h := Finset.sum_congr rfl fun k _ ↦
      integral_pairwise_abs_eq_withinCellTranslations (n := n) (cell k) (hcell k) (hfin k) f
    _ = ∫ h : ℝ^n, ∑ k ∈ I, K k h :=
      (MeasureTheory.integral_finsetSum I fun k _ ↦ hKint k).symm
    _ ≤ ∫ h : ℝ^n, (Rellich.euclideanDifferenceBox (n := n) δ).indicator T h :=
      MeasureTheory.integral_mono (MeasureTheory.integrable_finsetSum I fun k _ ↦ hKint k)
        hTIndicator hpoint
    _ = _ := MeasureTheory.integral_indicator hbox

end EndpointL1

end RellichKondrachov
end GraphSpace
end SobolevSpace
