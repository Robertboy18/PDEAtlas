/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.Rellich.EuclideanGrid
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Translation estimates for Rellich compactness

Translation `τ_h u = u(· + h)` is a linear isometry of `L^p(ℝ^n)` because Lebesgue measure is
translation invariant, and for `p < ∞` the map `h ↦ τ_h u` is continuous into `L^p` (Brezis,
Chapter 4). We set up these translations on the global spaces `DerivLp n p Set.univ` and prove the
estimate that links them to the cell averages of `Rellich.CellAverages`: for a positive mesh `δ` and
any finite family of lattice cells,

  `∑ₖ ∫_{Qₖ} ∫_{Qₖ} |f x - f y|² dx dy ≤ ∫_{[-δ,δ]ⁿ} ‖τ_h f - f‖²_{L²} dh`.

The proof is an exact change of variables, not an analytic estimate: the shear
`(x, h) ↦ (x, x + h)` preserves product Lebesgue measure, so the pairwise
oscillation on `Qₖ × Qₖ` becomes an integral over translation vectors, and
translation vectors between two points of one cell lie in the difference box
`[-δ, δ]ⁿ`.  Disjointness of the cells then bounds the sum by the full
translation defect for each fixed `h`.

## Main definitions and results

* `translationContinuousMap h`, `translationMeasurePreserving`: translation as
  a continuous, measure-preserving self-map of `ℝ^n`.
* `translateLp p h`: translation as a linear isometry of `L^p(ℝ^n)`, with
  `translateLp_apply_ae`, `translateLp_zero`, `translateLp_add`,
  `translateLp_lpSMul` (compatibility with multiplication by an `L^∞`
  coefficient), and `continuous_translateLp` for `p ≠ ∞`.
* `norm_translateL2_sub_sq_eq_integral`: `‖τ_h u - u‖² = ∫ |u(x+h) - u(x)|²`.
* `integral_pairwise_eq_integral_withinCellTranslations`: the shear formula for
  one cell.
* `sum_integral_gridCellTranslations_le_norm_translateL2_sub_sq`,
  `sum_gridCell_pairwise_le_integral_norm_translateL2_sub_sq`: the grid
  oscillation bounds.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 4, for the continuity of translations in `L^p`, `p < ∞`.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace Rellich

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

variable {n : ℕ}

/-- Translation by `h`, as a continuous self-map of Euclidean space. -/
def translationContinuousMap (h : ℝ^n) : C(ℝ^n, ℝ^n) :=
  ⟨fun x ↦ x + h, continuous_id.add continuous_const⟩

/-- Evaluating the translation map: `translationContinuousMap h x = x + h`. -/
@[simp]
theorem translationContinuousMap_apply (h x : ℝ^n) :
    translationContinuousMap h x = x + h :=
  rfl

/-- Euclidean translations vary continuously in the compact-open topology. -/
theorem continuous_translationContinuousMap :
    Continuous (translationContinuousMap : ℝ^n → C(ℝ^n, ℝ^n)) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_snd.add continuous_fst

/-- Translation preserves the global domain measure used by the
`L²(ℝ^n)` abbreviation. -/
theorem translationMeasurePreserving (h : ℝ^n) :
    MeasurePreserving (translationContinuousMap h)
      (domainMeasure n Set.univ) (domainMeasure n Set.univ) := by
  simpa [translationContinuousMap, domainMeasure] using
    (MeasureTheory.measurePreserving_add_right
      (MeasureTheory.volume : Measure (ℝ^n)) h)

/-- Translation on global `Lᵖ(ℝ^n)`, as a linear isometry. -/
noncomputable def translateLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℝ^n) :
    DerivLp n p Set.univ →ₗᵢ[ℝ] DerivLp n p Set.univ :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
    (translationContinuousMap h)
    (translationMeasurePreserving (n := n) h)

/-- Euclidean translation preserves every global `Lᵖ` norm. -/
theorem norm_translateLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : ℝ^n) (u : DerivLp n p Set.univ) :
    ‖translateLp p h u‖ = ‖u‖ :=
  (translateLp (n := n) p h).norm_map u

/-- `Lᵖ` translation has the expected representative almost everywhere. -/
theorem translateLp_apply_ae (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : ℝ^n) (u : DerivLp n p Set.univ) :
    ((translateLp p h u : DerivLp n p Set.univ) : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
      fun x ↦ u (x + h) := by
  have hrep :
      ((translateLp p h u : DerivLp n p Set.univ) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Set.univ]
          ((u : ℝ^n → ℝ) ∘ fun x ↦ x + h) := by
    simpa [translateLp, translationContinuousMap] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving u
        (translationMeasurePreserving (n := n) h))
  filter_upwards [hrep] with x hx
  exact hx

/-! Translation is an additive action on global `Lᵖ`. -/

/-- Translation by zero is the identity on global `Lᵖ`. -/
@[simp]
theorem translateLp_zero (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DerivLp n p Set.univ) :
    translateLp p (0 : ℝ^n) u = u := by
  apply MeasureTheory.Lp.ext
  filter_upwards [translateLp_apply_ae (n := n) p (0 : ℝ^n) u] with x hx
  simpa using hx

/-- Successive global `Lᵖ` translations add their displacement vectors. -/
theorem translateLp_add (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a b : ℝ^n) (u : DerivLp n p Set.univ) :
    translateLp p a (translateLp p b u) =
      translateLp p (a + b) u := by
  apply MeasureTheory.Lp.ext
  have ha := translateLp_apply_ae (n := n) p a (translateLp p b u)
  have hab := translateLp_apply_ae (n := n) p (a + b) u
  have hb := translateLp_apply_ae (n := n) p b u
  have hpres : MeasurePreserving (translationContinuousMap a)
      (domainMeasure n Set.univ) (domainMeasure n Set.univ) :=
    translationMeasurePreserving (n := n) a
  have hbcomp :
      (fun x ↦ (translateLp p b u) (x + a))
        =ᵐ[domainMeasure n Set.univ]
          fun x ↦ u ((x + a) + b) := by
    simpa [Function.comp_def, translationContinuousMap] using
      hpres.quasiMeasurePreserving.ae_eq_comp hb
  filter_upwards [ha, hab, hbcomp] with x hleft hright hmiddle
  rw [hleft, hright, hmiddle, add_assoc]

/-- Translation commutes with multiplication of a global `L∞` coefficient
and a global `Lᵖ` field.  The proof transports the pointwise multiplication
identity through the measure-preserving translation, so it is valid for
`Lp` equivalence classes. -/
theorem translateLp_lpSMul (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : ℝ^n) (a : DerivLp n ∞ Set.univ) (u : DerivLp n p Set.univ) :
    translateLp p h (a • u) = translateLp ∞ h a • translateLp p h u := by
  apply MeasureTheory.Lp.ext
  have hmulShift :
      (fun x ↦ ((a • u : DerivLp n p Set.univ) : ℝ^n → ℝ) (x + h))
        =ᵐ[domainMeasure n Set.univ] fun x ↦ a (x + h) * u (x + h) := by
    simpa [Function.comp_def, translationContinuousMap] using
      (translationMeasurePreserving (n := n) h).quasiMeasurePreserving.ae_eq_comp
        (MeasureTheory.Lp.coeFn_lpSMul (p := ∞) (q := p) (r := p) a u)
  filter_upwards [translateLp_apply_ae (n := n) p h (a • u), translateLp_apply_ae (n := n) ∞ h a,
    translateLp_apply_ae (n := n) p h u, hmulShift, MeasureTheory.Lp.coeFn_lpSMul (p := ∞)
      (q := p) (r := p) (translateLp ∞ h a) (translateLp p h u)]
    with x hxleft hxa hxu hxshift hxright
  rw [hxleft, hxshift, hxright]
  exact congrArg₂ (· * ·) hxa.symm hxu.symm

/-- For each fixed global `Lᵖ` function with finite exponent, translation is
strongly continuous in the translation vector. -/
theorem continuous_translateLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : DerivLp n p Set.univ) :
    Continuous fun h : ℝ^n ↦ translateLp p h u :=
  continuous_const.compMeasurePreservingLp (continuous_translationContinuousMap (n := n))
    translationMeasurePreserving hp

/-- The translation defect has the expected representative. -/
theorem translateLp_sub_apply_ae (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : ℝ^n) (u : DerivLp n p Set.univ) :
    (((translateLp p h u - u : DerivLp n p Set.univ) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Set.univ] fun x ↦ u (x + h) - u x := by
  filter_upwards [MeasureTheory.Lp.coeFn_sub (translateLp p h u) u,
    translateLp_apply_ae (n := n) p h u] with x hsub htrans
  rw [hsub, Pi.sub_apply, htrans]

/-- Squared norm of a translation defect in representative form. -/
theorem norm_translateL2_sub_sq_eq_integral
    (h : ℝ^n) (u : DerivLp n 2 Set.univ) :
    ‖translateLp 2 h u - u‖ ^ 2 =
      ∫ x : ℝ^n, (u (x + h) - u x) ^ 2 := by
  rw [MeasureTheory.Lp.norm_sq_eq_integral_sq]
  simpa [domainMeasure] using MeasureTheory.integral_congr_ae
    ((translateLp_sub_apply_ae (n := n) 2 h u).fun_comp (· ^ 2))

/-- The squared representative difference under a fixed translation is
integrable on all of Euclidean space. -/
theorem integrable_translation_sub_sq (h : ℝ^n)
    (f : DerivLp n 2 Set.univ) :
    Integrable (fun x : ℝ^n ↦ (f (x + h) - f x) ^ 2)
      MeasureTheory.volume := by
  simpa [domainMeasure, Function.comp_def] using
    (MeasureTheory.Lp.memLp (translateLp 2 h f - f)).integrable_sq.congr
      ((translateLp_sub_apply_ae (n := n) 2 h f).fun_comp (· ^ 2))

/-- Pairwise oscillation on one measurable finite-volume cell, rewritten in
translation coordinates `(x,h) ↦ (x,x+h)`.  The shear is Lebesgue
measure-preserving, so this is an exact change of variables rather than an
analytic estimate. -/
theorem integral_pairwise_eq_integral_withinCellTranslations
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hfinite : (MeasureTheory.volume : Measure (ℝ^n)) s ≠ ∞)
    (f : DerivLp n 2 Set.univ) :
    (∫ x in s, ∫ y in s, (f x - f y) ^ 2) =
      ∫ h : ℝ^n, ∫ x : ℝ^n,
        (s ×ˢ s).indicator
          (fun p : ℝ^n × ℝ^n ↦ (f p.1 - f p.2) ^ 2)
          (x, x + h) := by
  let G : ℝ^n × ℝ^n → ℝ := fun p ↦ (f p.1 - f p.2) ^ 2
  have hGon : IntegrableOn G (s ×ˢ s)
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) := by
    simpa [G, domainMeasure] using L2_integrableOn_pairwise_sub_sq
      (μ := domainMeasure n Set.univ) s (by simpa [domainMeasure] using hfinite) f
  -- the shear `(x, h) ↦ (x, x + h)` preserves the product measure
  let shear : ℝ^n × ℝ^n → ℝ^n × ℝ^n := fun p ↦ (p.1, p.1 + p.2)
  have hpres : MeasurePreserving shear
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume)
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) := by
    simpa [shear] using MeasureTheory.measurePreserving_prod_add
      (MeasureTheory.volume : Measure (ℝ^n)) (MeasureTheory.volume : Measure (ℝ^n))
  calc
    (∫ x in s, ∫ y in s, (f x - f y) ^ 2) =
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

/-- The outer translation integral appearing in the one-cell shear formula
is integrable. -/
theorem integrable_integral_withinCellTranslations
    (s : Set (ℝ^n)) (hs : MeasurableSet s)
    (hfinite : (MeasureTheory.volume : Measure (ℝ^n)) s ≠ ∞)
    (f : DerivLp n 2 Set.univ) :
    Integrable (fun h : ℝ^n ↦ ∫ x : ℝ^n,
      (s ×ˢ s).indicator
        (fun p : ℝ^n × ℝ^n ↦ (f p.1 - f p.2) ^ 2)
        (x, x + h)) MeasureTheory.volume := by
  have hGon : IntegrableOn (fun p : ℝ^n × ℝ^n ↦ (f p.1 - f p.2) ^ 2) (s ×ˢ s)
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) := by
    simpa [domainMeasure] using L2_integrableOn_pairwise_sub_sq
      (μ := domainMeasure n Set.univ) s (by simpa [domainMeasure] using hfinite) f
  have hpres : MeasurePreserving (fun p : ℝ^n × ℝ^n ↦ (p.1, p.1 + p.2))
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume)
      ((MeasureTheory.volume : Measure (ℝ^n)).prod MeasureTheory.volume) := by
    simpa using MeasureTheory.measurePreserving_prod_add
      (MeasureTheory.volume : Measure (ℝ^n)) (MeasureTheory.volume : Measure (ℝ^n))
  simpa [Function.comp_def] using (hpres.integrable_comp_of_integrable
    (hGon.integrable_indicator (hs.prod hs))).integral_prod_right

/-- For a fixed shift, the sum of within-cell oscillations over pairwise
disjoint regular grid cells is bounded by the full `L²` translation defect. -/
theorem sum_integral_gridCellTranslations_le_norm_translateL2_sub_sq
    {δ : ℝ} (hδ : 0 < δ) (I : Finset (Fin n → ℤ))
    (f : DerivLp n 2 Set.univ) (h : ℝ^n) :
    (∑ k ∈ I, ∫ x : ℝ^n,
      (euclideanGridCell (n := n) δ k ×ˢ
          euclideanGridCell (n := n) δ k).indicator
        (fun p : ℝ^n × ℝ^n ↦ (f p.1 - f p.2) ^ 2)
        (x, x + h)) ≤ ‖translateLp 2 h f - f‖ ^ 2 := by
  let cell : (Fin n → ℤ) → Set (ℝ^n) := euclideanGridCell (n := n) δ
  let A : (Fin n → ℤ) → Set (ℝ^n) := fun k ↦ cell k ∩ (fun x : ℝ^n ↦ x + h) ⁻¹' cell k
  let D : ℝ^n → ℝ := fun x ↦ (f x - f (x + h)) ^ 2
  have hAmeas (k : Fin n → ℤ) : MeasurableSet (A k) :=
    (measurableSet_euclideanGridCell (n := n) δ k).inter
      ((measurableSet_euclideanGridCell (n := n) δ k).preimage
        (measurable_id.add measurable_const))
  have hAdisjoint : Set.Pairwise (↑I : Set (Fin n → ℤ)) (Disjoint on A) := fun k _ l _ hkl ↦
    (disjoint_euclideanGridCell_of_ne (n := n) hδ hkl).mono inter_subset_left
      inter_subset_left
  have hD : Integrable D MeasureTheory.volume :=
    (integrable_translation_sub_sq (n := n) h f).congr (.of_forall fun x ↦ by ring)
  calc
    _ = ∑ k ∈ I, ∫ x in A k, D x := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← MeasureTheory.integral_indicator (hAmeas k)]
      refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ cell k <;> by_cases hxh : x + h ∈ cell k <;> simp [A, D, cell, hx, hxh]
    _ = ∫ x in ⋃ k ∈ I, A k, D x := (MeasureTheory.integral_biUnion_finset I
      (fun k _ ↦ hAmeas k) hAdisjoint fun _ _ ↦ hD.integrableOn).symm
    _ ≤ ∫ x : ℝ^n, D x :=
      MeasureTheory.setIntegral_le_integral hD (.of_forall fun x ↦ sq_nonneg _)
    _ = ‖translateLp 2 h f - f‖ ^ 2 := by
      rw [norm_translateL2_sub_sq_eq_integral]
      exact MeasureTheory.integral_congr_ae (.of_forall fun x ↦ by ring)

/-- The total pairwise oscillation over finitely many regular grid cells is
controlled by the translation modulus integrated over the common difference
box. -/
theorem sum_gridCell_pairwise_le_integral_norm_translateL2_sub_sq
    {δ : ℝ} (hδ : 0 < δ) (I : Finset (Fin n → ℤ))
    (f : DerivLp n 2 Set.univ) :
    (∑ k ∈ I, ∫ x in euclideanGridCell (n := n) δ k,
      ∫ y in euclideanGridCell (n := n) δ k, (f x - f y) ^ 2) ≤
      ∫ h in euclideanDifferenceBox (n := n) δ,
        ‖translateLp 2 h f - f‖ ^ 2 := by
  let cell : (Fin n → ℤ) → Set (ℝ^n) := euclideanGridCell (n := n) δ
  let K : (Fin n → ℤ) → ℝ^n → ℝ := fun k h ↦ ∫ x : ℝ^n,
    (cell k ×ˢ cell k).indicator (fun p : ℝ^n × ℝ^n ↦ (f p.1 - f p.2) ^ 2) (x, x + h)
  let T : ℝ^n → ℝ := fun h ↦ ‖translateLp 2 h f - f‖ ^ 2
  have hcell (k : Fin n → ℤ) := measurableSet_euclideanGridCell (n := n) δ k
  have hfin (k : Fin n → ℤ) : (MeasureTheory.volume : Measure (ℝ^n)) (cell k) ≠ ∞ := by
    simp [cell, volume_euclideanGridCell]
  have hKint (k : Fin n → ℤ) : Integrable (K k) MeasureTheory.volume :=
    integrable_integral_withinCellTranslations (n := n) (cell k) (hcell k) (hfin k) f
  have hbox := measurableSet_euclideanDifferenceBox (n := n) δ
  have hTIndicator : Integrable ((euclideanDifferenceBox (n := n) δ).indicator T)
      MeasureTheory.volume :=
    ((((continuous_translateLp (n := n) 2 (by norm_num) f).sub
      continuous_const).norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_euclideanDifferenceBox (n := n) δ)).integrable_indicator hbox
  -- outside the difference box no shift keeps a point in its cell
  have hpoint (h : ℝ^n) :
      (∑ k ∈ I, K k h) ≤ (euclideanDifferenceBox (n := n) δ).indicator T h := by
    by_cases hh : h ∈ euclideanDifferenceBox (n := n) δ
    · rw [indicator_of_mem hh]
      exact sum_integral_gridCellTranslations_le_norm_translateL2_sub_sq (n := n) hδ I f h
    · rw [indicator_of_notMem hh]
      refine (Finset.sum_eq_zero fun k _ ↦ MeasureTheory.integral_eq_zero_of_ae
        (.of_forall fun x ↦ indicator_of_notMem (fun hpair ↦ hh ?_) _)).le
      simpa using sub_mem_euclideanDifferenceBox_of_mem_gridCell (n := n) hpair.1 hpair.2
  calc
    _ = ∑ k ∈ I, ∫ h : ℝ^n, K k h := Finset.sum_congr rfl fun k _ ↦
      integral_pairwise_eq_integral_withinCellTranslations (n := n) (cell k) (hcell k) (hfin k) f
    _ = ∫ h : ℝ^n, ∑ k ∈ I, K k h :=
      (MeasureTheory.integral_finsetSum I fun k _ ↦ hKint k).symm
    _ ≤ ∫ h : ℝ^n, (euclideanDifferenceBox (n := n) δ).indicator T h :=
      MeasureTheory.integral_mono (MeasureTheory.integrable_finsetSum I fun k _ ↦ hKint k)
        hTIndicator hpoint
    _ = _ := MeasureTheory.integral_indicator hbox

end Rellich
end GraphSpace
end SobolevSpace
