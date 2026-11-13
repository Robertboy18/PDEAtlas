/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Positivity.Finset
import PDE.Analysis.MeasureTheory.LpNorm
import PDE.Spaces.Sobolev.Compactness.Rellich.Topology

/-!
# Finite-cell averaging in L²

Replacing an `L²` function by its mean value on each cell of a finite partition is a finite-rank,
hence compact, operator. The error committed on a single cell `s` of finite positive measure is
controlled by the pairwise oscillation of `f` over `s × s`:

  `∫_s |f - ⨍_s f|² ≤ |s|⁻¹ ∫_s ∫_s |f x - f y|² dx dy`,

which is Jensen's inequality applied to the average of `y ↦ f x - f y`. Summing over disjoint cells
covering the support of `f` gives the same bound for the global averaging error. This is the
finite-dimensional approximation step in our proof of the Rellich–Kondrachov theorem: the right-hand
side is later bounded by translation estimates in terms of the gradient, so that bounded sets in
`H¹` are approximated uniformly by a compact operator. The same mechanism, uniformly small
translations giving total boundedness, underlies the Kolmogorov–Riesz–Fréchet compactness criterion
in `L^p` (Brezis, Chapter 4); here cell averages are the approximating operators. Evans proves the
Rellich–Kondrachov theorem with mollifiers and the Arzelà–Ascoli theorem instead (§5.7, Theorem 1).

## Main definitions and results

* `cellIndicatorL2`, `cellAverageOperator`: the indicator of a cell as an `L²`
  vector, and the rank-one operator `f ↦ (⨍_s f) 𝟙_s`; it is compact
  (`cellAverageOperator.isCompactOperator`) and given almost everywhere by the
  cell mean (`cellAverageOperator_apply_ae`).
* `sq_setAverage_le_setAverage_sq`, `sub_setAverage_sq_le_setAverage_sub_sq`,
  `setIntegral_sub_setAverage_sq_le_pairwise`: the one-cell oscillation
  estimates.
* `finiteCellAverageOperator`: the sum of the one-cell operators over a finite
  index set; `finiteCellAverageOperator.isCompactOperator`.
* `finiteCellAverageOperator.norm_sub_sq_eq_sum`,
  `finiteCellAverageOperator.norm_sub_sq_le_pairwise`: for pairwise-disjoint
  cells covering the support of `f`, the squared `L²` error is the sum of the
  cellwise errors and is bounded by the normalized pairwise oscillations.

## Implementation notes

The measure space is arbitrary in this file; only measurability and finiteness
of the cells enter, together with s-finiteness of `μ` for the Fubini step in
the pairwise bounds.  Null cells give the zero operator, and the positivity
hypothesis `μ (cell i) ≠ 0` is needed only for the Jensen step.  The results
are specialised to Euclidean grid cells in `Rellich.EuclideanGrid`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 4, for the Kolmogorov–Riesz–Fréchet compactness criterion in `L^p`.
  <https://doi.org/10.1007/978-0-387-70914-7>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.7, Theorem 1, pp. 286-288, whose proof mollifies and
  applies the Arzelà–Ascoli theorem.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace Rellich

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

variable {n : ℕ}

section CellAverages

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The `L²` indicator vector of a measurable set of finite measure. -/
noncomputable def cellIndicatorL2 (s : Set α) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) : MeasureTheory.Lp ℝ 2 μ :=
  MeasureTheory.indicatorConstLp 2 hs hμs (1 : ℝ)

/-- Orthogonal averaging onto the constant functions supported on one cell.
For a null cell this is the zero operator. -/
noncomputable def cellAverageOperator (s : Set α) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) :
    MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ :=
  (μ.real s)⁻¹ • InnerProductSpace.rankOne ℝ
    (cellIndicatorL2 s hs hμs) (cellIndicatorL2 s hs hμs)

/-- Every one-cell averaging operator is compact. -/
theorem cellAverageOperator.isCompactOperator
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    IsCompactOperator (cellAverageOperator s hs hμs) := by
  unfold cellAverageOperator
  exact (isCompactOperator_rankOne_real
    (cellIndicatorL2 s hs hμs) (cellIndicatorL2 s hs hμs)).smul
      ((μ.real s)⁻¹ : ℝ)

/-- Pairing with a cell indicator is integration over that cell. -/
theorem inner_cellIndicatorL2_eq_setIntegral
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    ⟪cellIndicatorL2 s hs hμs, f⟫_ℝ = ∫ x in s, f x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, @inner ℝ ℝ _ (cellIndicatorL2 s hs hμs x) (f x) ∂μ) =
        ∫ x, s.indicator (fun y ↦ f y) x ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.indicatorConstLp_coeFn
        (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hx
      rw [show cellIndicatorL2 s hs hμs x = s.indicator (fun _ ↦ (1 : ℝ)) x by
        exact hx]
      by_cases hxs : x ∈ s <;> simp [hxs, RCLike.inner_apply]
    _ = ∫ x in s, f x ∂μ := MeasureTheory.integral_indicator hs

/-- Explicit formula for one-cell averaging. -/
theorem cellAverageOperator_apply
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    cellAverageOperator s hs hμs f =
      ((μ.real s)⁻¹ * (∫ x in s, f x ∂μ)) • cellIndicatorL2 s hs hμs := by
  simp [cellAverageOperator, InnerProductSpace.rankOne_apply,
    inner_cellIndicatorL2_eq_setIntegral, smul_smul]

/-- One-cell averaging written directly with the normalized set average. -/
theorem cellAverageOperator_apply_setAverage
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    cellAverageOperator s hs hμs f =
      (⨍ x in s, f x ∂μ) • cellIndicatorL2 s hs hμs := by
  rw [cellAverageOperator_apply, MeasureTheory.setAverage_eq]
  simp only [smul_eq_mul]

/-- The one-cell averaging operator is represented by the cellwise mean on
the cell and zero off the cell. -/
theorem cellAverageOperator_apply_ae
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    ((cellAverageOperator s hs hμs f : MeasureTheory.Lp ℝ 2 μ) : α → ℝ)
      =ᵐ[μ] s.indicator fun _ ↦ (μ.real s)⁻¹ * (∫ x in s, f x ∂μ) := by
  rw [cellAverageOperator_apply]
  filter_upwards [MeasureTheory.Lp.coeFn_smul
      ((μ.real s)⁻¹ * (∫ x in s, f x ∂μ)) (cellIndicatorL2 s hs hμs),
    MeasureTheory.indicatorConstLp_coeFn
      (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hsmul hx
  rw [hsmul]
  change ((μ.real s)⁻¹ * (∫ x in s, f x ∂μ)) *
      cellIndicatorL2 s hs hμs x = _
  rw [show cellIndicatorL2 s hs hμs x = s.indicator (fun _ ↦ (1 : ℝ)) x by
    exact hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Cauchy-Schwarz/Jensen for the average over an arbitrary measurable cell
of finite positive measure. -/
theorem sq_setAverage_le_setAverage_sq
    (s : Set α) (hs0 : μ s ≠ 0) (hμs : μ s ≠ ∞)
    (g : α → ℝ) (hg : IntegrableOn g s μ)
    (hgSq : IntegrableOn (fun x ↦ (g x) ^ 2) s μ) :
    (⨍ x in s, g x ∂μ) ^ 2 ≤ ⨍ x in s, (g x) ^ 2 ∂μ := by
  have hJ :=
    (show Even 2 by norm_num).convexOn_pow.map_set_average_le
      (μ := μ) (s := (Set.univ : Set ℝ)) (t := s) (f := g)
      (continuous_pow 2).continuousOn isClosed_univ hs0 hμs
      (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _)
      hg (by simpa [Function.comp_def] using hgSq)
  simpa [Function.comp_def] using hJ

/-- Pointwise deviation from a cell average is bounded by the average
pairwise squared oscillation on that cell. -/
theorem sub_setAverage_sq_le_setAverage_sub_sq
    (s : Set α) (hs0 : μ s ≠ 0) (hμs : μ s ≠ ∞)
    (f : MeasureTheory.Lp ℝ 2 μ) (x : α) :
    (f x - ⨍ y in s, f y ∂μ) ^ 2 ≤
      ⨍ y in s, (f x - f y) ^ 2 ∂μ := by
  have hf : IntegrableOn (fun y ↦ f y) s μ :=
    MeasureTheory.integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs
  have hconst : IntegrableOn (fun _ : α ↦ f x) s μ :=
    MeasureTheory.integrableOn_const hμs
  have hg : IntegrableOn (fun y ↦ f x - f y) s μ := hconst.sub hf
  have hsq : IntegrableOn (fun y ↦ (f x - f y) ^ 2) s μ := by
    have hconstSq : IntegrableOn (fun _ : α ↦ (f x) ^ 2) s μ :=
      MeasureTheory.integrableOn_const hμs
    have hlinear : IntegrableOn (fun y ↦ (2 * f x) * f y) s μ :=
      hf.const_mul (2 * f x)
    have hfSq : IntegrableOn (fun y ↦ (f y) ^ 2) s μ :=
      ((MeasureTheory.Lp.memLp f).integrable_sq).integrableOn
    have hexpand := (hconstSq.sub hlinear).add hfSq
    apply hexpand.congr
    exact Filter.Eventually.of_forall fun y ↦ by
      change (f x) ^ 2 - (2 * f x) * f y + (f y) ^ 2 = (f x - f y) ^ 2
      ring
  have havg :
      (⨍ y in s, f x - f y ∂μ) = f x - ⨍ y in s, f y ∂μ := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.integral_sub hconst hf, smul_sub,
      ← MeasureTheory.setAverage_eq, ← MeasureTheory.setAverage_eq,
      MeasureTheory.setAverage_const hs0 hμs]
  rw [← havg]
  exact sq_setAverage_le_setAverage_sq s hs0 hμs
    (fun y ↦ f x - f y) hg hsq

/-- Pairwise squared oscillation of an `L²` function is integrable on the
square of every finite-measure cell. -/
theorem L2_integrableOn_pairwise_sub_sq
    [SFinite μ]
    (s : Set α) (hμs : μ s ≠ ∞)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    IntegrableOn (fun p : α × α ↦ (f p.1 - f p.2) ^ 2)
      (s ×ˢ s) (μ.prod μ) := by
  have : IsFiniteMeasure (μ.restrict s) :=
    MeasureTheory.isFiniteMeasure_restrict.2 hμs
  have hf : Integrable (fun x ↦ f x) (μ.restrict s) :=
    MeasureTheory.integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs
  have hfSq : Integrable (fun x ↦ (f x) ^ 2) (μ.restrict s) :=
    ((MeasureTheory.Lp.memLp f).integrable_sq).integrableOn
  have hfstSq : Integrable (fun p : α × α ↦ (f p.1) ^ 2)
      ((μ.restrict s).prod (μ.restrict s)) :=
    hfSq.comp_fst (μ.restrict s)
  have hsndSq : Integrable (fun p : α × α ↦ (f p.2) ^ 2)
      ((μ.restrict s).prod (μ.restrict s)) :=
    hfSq.comp_snd (μ.restrict s)
  have hcross : Integrable (fun p : α × α ↦ (2 : ℝ) * (f p.1 * f p.2))
      ((μ.restrict s).prod (μ.restrict s)) :=
    (hf.mul_prod hf).const_mul 2
  have hexpand := (hfstSq.sub hcross).add hsndSq
  rw [IntegrableOn, ← Measure.prod_restrict]
  apply hexpand.congr
  exact Filter.Eventually.of_forall fun p ↦ by
    change (f p.1) ^ 2 - 2 * (f p.1 * f p.2) + (f p.2) ^ 2 =
      (f p.1 - f p.2) ^ 2
    ring

/-- Integrated cell-oscillation estimate: the squared error from replacing
an `L²` function by its cell average is controlled by the average pairwise
oscillation on that cell. -/
theorem setIntegral_sub_setAverage_sq_le_pairwise
    [SFinite μ]
    (s : Set α) (hs : MeasurableSet s) (hs0 : μ s ≠ 0) (hμs : μ s ≠ ∞)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    (∫ x in s, (f x - ⨍ y in s, f y ∂μ) ^ 2 ∂μ) ≤
      (μ.real s)⁻¹ *
        ∫ x in s, ∫ y in s, (f x - f y) ^ 2 ∂μ ∂μ := by
  let c : ℝ := ⨍ y in s, f y ∂μ
  have hf : IntegrableOn (fun x ↦ f x) s μ :=
    MeasureTheory.integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs
  have hfSq : IntegrableOn (fun x ↦ (f x) ^ 2) s μ :=
    ((MeasureTheory.Lp.memLp f).integrable_sq).integrableOn
  have hconstSq : IntegrableOn (fun _ : α ↦ c ^ 2) s μ :=
    MeasureTheory.integrableOn_const hμs
  have hlinear : IntegrableOn (fun x ↦ (2 * c) * f x) s μ :=
    hf.const_mul (2 * c)
  have hlhs : IntegrableOn (fun x ↦ (f x - c) ^ 2) s μ := by
    have hexpand := (hfSq.sub hlinear).add hconstSq
    apply hexpand.congr
    exact Filter.Eventually.of_forall fun x ↦ by
      change (f x) ^ 2 - (2 * c) * f x + c ^ 2 = (f x - c) ^ 2
      ring
  have hpair := L2_integrableOn_pairwise_sub_sq s hμs f
  have hpairProd : Integrable (fun p : α × α ↦ (f p.1 - f p.2) ^ 2)
      ((μ.restrict s).prod (μ.restrict s)) := by
    simpa only [IntegrableOn, Measure.prod_restrict] using hpair
  have hinner : Integrable
      (fun x ↦ ∫ y in s, (f x - f y) ^ 2 ∂μ) (μ.restrict s) := by
    simpa only using hpairProd.integral_prod_left
  have hrhs : IntegrableOn
      (fun x ↦ ⨍ y in s, (f x - f y) ^ 2 ∂μ) s μ := by
    have heq :
        (fun x ↦ ⨍ y in s, (f x - f y) ^ 2 ∂μ) =
          fun x ↦ (μ.real s)⁻¹ *
            ∫ y in s, (f x - f y) ^ 2 ∂μ := by
      funext x
      rw [MeasureTheory.setAverage_eq]
      rfl
    rw [heq]
    exact hinner.const_mul _
  calc
    (∫ x in s, (f x - ⨍ y in s, f y ∂μ) ^ 2 ∂μ)
        ≤ ∫ x in s, ⨍ y in s, (f x - f y) ^ 2 ∂μ ∂μ := by
      exact MeasureTheory.setIntegral_mono_on
        (by simpa [c] using hlhs) hrhs hs fun x _ ↦
          sub_setAverage_sq_le_setAverage_sub_sq s hs0 hμs f x
    _ = (μ.real s)⁻¹ *
          ∫ x in s, ∫ y in s, (f x - f y) ^ 2 ∂μ ∂μ := by
      simp_rw [MeasureTheory.setAverage_eq]
      simp only [smul_eq_mul]
      rw [MeasureTheory.integral_const_mul]

/-- Averaging over finitely many measurable cells. -/
noncomputable def finiteCellAverageOperator
    {ι : Type*} (I : Finset ι) (cell : ι → Set α)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hfinite : ∀ i, μ (cell i) ≠ ∞) :
    MeasureTheory.Lp ℝ 2 μ →L[ℝ] MeasureTheory.Lp ℝ 2 μ :=
  ∑ i ∈ I, cellAverageOperator (cell i) (hcell i) (hfinite i)

/-- A finite-cell averaging operator is compact. -/
theorem finiteCellAverageOperator.isCompactOperator
    {ι : Type*} (I : Finset ι) (cell : ι → Set α)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hfinite : ∀ i, μ (cell i) ≠ ∞) :
    IsCompactOperator (finiteCellAverageOperator I cell hcell hfinite) := by
  unfold finiteCellAverageOperator
  apply isCompactOperator_finset_sum
  intro i _
  exact cellAverageOperator.isCompactOperator
    (cell i) (hcell i) (hfinite i)

/-- Representative formula for finite-cell averaging. -/
theorem finiteCellAverageOperator_apply_ae
    {ι : Type*} (I : Finset ι) (cell : ι → Set α)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hfinite : ∀ i, μ (cell i) ≠ ∞)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    ((finiteCellAverageOperator I cell hcell hfinite f :
        MeasureTheory.Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ]
      fun x ↦ ∑ i ∈ I,
        (cell i).indicator (fun _ ↦ ⨍ y in cell i, f y ∂μ) x := by
  classical
  induction I using Finset.induction with
  | empty =>
      simp only [finiteCellAverageOperator, Finset.sum_empty]
      filter_upwards [MeasureTheory.Lp.coeFn_zero ℝ (2 : ℝ≥0∞) μ] with x hx
      exact hx
  | @insert i I hi ih =>
      have hop :
          finiteCellAverageOperator (insert i I) cell hcell hfinite f =
            cellAverageOperator (cell i) (hcell i) (hfinite i) f +
              finiteCellAverageOperator I cell hcell hfinite f := by
        simp [finiteCellAverageOperator, hi]
      rw [hop]
      filter_upwards [MeasureTheory.Lp.coeFn_add
          (cellAverageOperator (cell i) (hcell i) (hfinite i) f)
          (finiteCellAverageOperator I cell hcell hfinite f),
        cellAverageOperator_apply_ae (cell i) (hcell i) (hfinite i) f,
        ih] with x hadd hcellx hIx
      rw [hadd, Pi.add_apply, hcellx, hIx]
      simp only [Finset.sum_insert hi]
      rw [MeasureTheory.setAverage_eq]
      simp only [smul_eq_mul]

/-- For pairwise-disjoint cells covering the support of `f`, the squared
error of finite-cell averaging is the sum of the cellwise squared errors. -/
theorem finiteCellAverageOperator.norm_sub_sq_eq_sum
    {ι : Type*} (I : Finset ι) (cell : ι → Set α)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hfinite : ∀ i, μ (cell i) ≠ ∞)
    (hdisjoint : Set.Pairwise (↑I : Set ι) (Disjoint on cell))
    (f : MeasureTheory.Lp ℝ 2 μ)
    (hsupport : ∀ᵐ x ∂μ, x ∉ ⋃ i ∈ I, cell i → f x = 0) :
    ‖finiteCellAverageOperator I cell hcell hfinite f - f‖ ^ 2 =
      ∑ i ∈ I, ∫ x in cell i,
        (f x - ⨍ y in cell i, f y ∂μ) ^ 2 ∂μ := by
  classical
  let P : MeasureTheory.Lp ℝ 2 μ :=
    finiteCellAverageOperator I cell hcell hfinite f
  let U : Set α := ⋃ i ∈ I, cell i
  let g : α → ℝ := fun x ↦
    (∑ i ∈ I, (cell i).indicator
      (fun _ ↦ ⨍ y in cell i, f y ∂μ) x) - f x
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact Finset.measurableSet_biUnion I fun i _ ↦ hcell i
  have hP : (P : α → ℝ) =ᵐ[μ] fun x ↦
      ∑ i ∈ I, (cell i).indicator
        (fun _ ↦ ⨍ y in cell i, f y ∂μ) x := by
    simpa [P] using finiteCellAverageOperator_apply_ae I cell hcell hfinite f
  have hsub : ((P - f : MeasureTheory.Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ] g := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub P f, hP] with x hx hPx
    rw [hx, Pi.sub_apply, hPx]
  have hgInt : Integrable (fun x ↦ (g x) ^ 2) μ := by
    apply ((MeasureTheory.Lp.memLp (P - f)).integrable_sq).congr
    exact hsub.fun_comp fun z ↦ z ^ 2
  have hgZero : ∀ᵐ x ∂μ, x ∉ U → g x = 0 := by
    filter_upwards [hsupport] with x hfx hxU
    have hnot (i : ι) (hi : i ∈ I) : x ∉ cell i := by
      intro hxi
      exact hxU (by
        dsimp [U]
        exact Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem hi hxi))
    have hsum : (∑ i ∈ I, (cell i).indicator
        (fun _ ↦ ⨍ y in cell i, f y ∂μ) x) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact Set.indicator_of_notMem (hnot i hi) _
    simp [g, hsum, hfx hxU]
  calc
    ‖finiteCellAverageOperator I cell hcell hfinite f - f‖ ^ 2
        = ∫ x, (g x) ^ 2 ∂μ := by
      change ‖P - f‖ ^ 2 = _
      rw [MeasureTheory.Lp.norm_sq_eq_integral_sq]
      exact MeasureTheory.integral_congr_ae (hsub.fun_comp fun z ↦ z ^ 2)
    _ = ∫ x in U, (g x) ^ 2 ∂μ := by
      rw [← MeasureTheory.integral_indicator hUmeas]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hgZero] with x hx
      by_cases hxU : x ∈ U
      · simp [Set.indicator_of_mem hxU]
      · simp [Set.indicator_of_notMem hxU, hx hxU]
    _ = ∑ i ∈ I, ∫ x in cell i, (g x) ^ 2 ∂μ := by
      dsimp [U]
      exact MeasureTheory.integral_biUnion_finset I
        (fun i _ ↦ hcell i) hdisjoint
        (fun _ _ ↦ hgInt.integrableOn)
    _ = ∑ i ∈ I, ∫ x in cell i,
          (f x - ⨍ y in cell i, f y ∂μ) ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply MeasureTheory.setIntegral_congr_ae (hcell i)
      exact Filter.Eventually.of_forall fun x hxi ↦ by
        have hsum : (∑ j ∈ I, (cell j).indicator
            (fun _ ↦ ⨍ y in cell j, f y ∂μ) x) =
            ⨍ y in cell i, f y ∂μ := by
          rw [Finset.sum_eq_single i]
          · simp [Set.indicator_of_mem hxi]
          · intro j hj hji
            have hd : Disjoint (cell i) (cell j) :=
              hdisjoint (by simpa using hi) (by simpa using hj) hji.symm
            have hxj : x ∉ cell j := fun hxj ↦ Set.disjoint_left.1 hd hxi hxj
            simp [Set.indicator_of_notMem hxj]
          · exact fun hnot ↦ (hnot hi).elim
        change (g x) ^ 2 = _
        rw [show g x =
            (⨍ y in cell i, f y ∂μ) - f x by
          simp only [g]
          rw [hsum]]
        ring

/-- Global finite-cell averaging error bounded by normalized pairwise
oscillation on each cell. -/
theorem finiteCellAverageOperator.norm_sub_sq_le_pairwise
    [SFinite μ]
    {ι : Type*} (I : Finset ι) (cell : ι → Set α)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hpositive : ∀ i ∈ I, μ (cell i) ≠ 0)
    (hfinite : ∀ i, μ (cell i) ≠ ∞)
    (hdisjoint : Set.Pairwise (↑I : Set ι) (Disjoint on cell))
    (f : MeasureTheory.Lp ℝ 2 μ)
    (hsupport : ∀ᵐ x ∂μ, x ∉ ⋃ i ∈ I, cell i → f x = 0) :
    ‖finiteCellAverageOperator I cell hcell hfinite f - f‖ ^ 2 ≤
      ∑ i ∈ I, (μ.real (cell i))⁻¹ *
        ∫ x in cell i, ∫ y in cell i, (f x - f y) ^ 2 ∂μ ∂μ := by
  rw [finiteCellAverageOperator.norm_sub_sq_eq_sum
    I cell hcell hfinite hdisjoint f hsupport]
  apply Finset.sum_le_sum
  intro i hi
  exact setIntegral_sub_setAverage_sq_le_pairwise
    (cell i) (hcell i) (hpositive i hi) (hfinite i) f

end CellAverages

end Rellich
end GraphSpace
end SobolevSpace
