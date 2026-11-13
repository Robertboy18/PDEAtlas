/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Compactness.Rellich.Translation
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupport
import PDE.Spaces.Sobolev.Compactness.Rellich.SmoothTranslation
import PDE.Spaces.Sobolev.Compactness.Rellich.Topology
import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator

/-!
# Rellich compactness via zero extension

We prove Rellich compactness for `H¹₀(Ω) → L²(Ω)` on bounded measurable sets, and for
`H¹(Ω) → L²(Ω)` under the `Boundary.C1ExtensionAtlas` hypothesis (Evans, §5.7, Theorem 1 and the
Remark after it).

## Main results

* `zeroExtendedBaseL2`: the map `H¹₀(Ω) → L²(ℝ^n)`, `u ↦ ũ`, and its
  representative `zeroExtendedBaseL2_apply_ae`.
* `translationDefectCLM.norm_le`: `‖τ_h ũ - ũ‖ ≤ |h| ‖u‖`.
* `euclideanGridAverageOperator.norm_sub_le`: the finite-rank approximation
  estimate for zero-extended fields.
* `zeroExtendedBaseL2.isCompactOperator`: compactness of `u ↦ ũ` for bounded
  measurable `Ω`.
* `baseCoordinateL2_isCompactOperator_of_c1Domain`: compactness of
  `H¹(Ω) → L²(Ω)` under `Boundary.C1ExtensionAtlas`.
* `baseCoordCLM.isCompactOperator_of_bounded`: compactness of the concrete
  inclusion `H¹₀(Ω) → L²(Ω)` for bounded measurable `Ω`, by factoring it as
  zero extension followed by restriction
  (`baseCoordCLM.eq_restrict_comp_zeroExtendedBaseL2`).

## How it works

For `u ∈ H¹₀(Ω)` we extend the base coordinate by zero to `ℝ^n`. The compactness proof uses finite
grid averages, where Evans uses mollifiers and the Arzelà–Ascoli theorem. Two uniform facts hold on
norm-bounded sets: the extensions vanish outside one fixed ball, and their translation defects obey
`‖τ_h ũ - ũ‖_{L²} ≤ |h| ‖u‖`, obtained from the smooth estimate of `Rellich.SmoothTranslation` by
density. Averaging over a finite lattice grid of mesh `δ` covering that ball is a finite-rank
operator (`Rellich.EuclideanGrid`), and by the oscillation bounds of `Rellich.CellAverages` and
`Rellich.Translation` its error is at most a constant times `√n · δ` uniformly on the unit ball of
`H¹₀(Ω)`. A uniform limit of compact operators is compact. For `H¹(Ω)` under
`Boundary.C1ExtensionAtlas` we extend to `H¹(ℝ^n)`, cut off to a ball `B ⊇ closure Ω`, apply the
`H¹₀(B)` result, and restrict back to `Ω`.

## Implementation notes

Boundedness of `Ω` enters only through the existence of one ball outside of
which all zero extensions vanish; no regularity of `∂Ω` is used for the `H¹₀`
statements. The `C¹` statement takes the chart-and-cutoff data as a typeclass
hypothesis; `HasC1GraphBoundary.c1ExtensionAtlas` constructs such data for a
bounded open set with `C¹` graph boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.7, Theorem 1, pp. 286-288, and the Remark after it,
  p. 289, for `W^{1,p}_0(U) ⊂⊂ L^p(U)` without regularity of `∂U`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace
namespace GraphSpace
namespace Rellich

open MeasureTheory Set Function
open scoped ENNReal Topology InnerProductSpace RealInnerProductSpace

variable {n : ℕ}

section ZeroExtension

variable {Ω : Set (ℝ^n)}

/-- The zero-extended `L²` representative of an `H¹₀(Ω)` function. -/
noncomputable def zeroExtendedBaseL2 (hΩmeas : MeasurableSet Ω) :
    H¹₀(Ω) →L[ℝ] DerivLp n 2 Set.univ :=
  (wkpBaseCoordinateCLM
    (n := n) (m := 1) (p := 2) (Ω := Set.univ)).comp
      (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩmeas)

/-- Translation defect of the zero-extended base coordinate. -/
noncomputable def translationDefectCLM (hΩmeas : MeasurableSet Ω) (h : ℝ^n) :
    H¹₀(Ω) →L[ℝ] DerivLp n 2 Set.univ :=
  (translateLp 2 h).toContinuousLinearMap.comp
      (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas) -
    zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas

/-- The translation defect of `u` is `τ_h ũ - ũ`, where `ũ` is the zero-extended
base coordinate. -/
@[simp]
theorem translationDefectCLM_apply (hΩmeas : MeasurableSet Ω)
    (h : ℝ^n) (u : H¹₀(Ω)) :
    translationDefectCLM (n := n) (Ω := Ω) hΩmeas h u =
      translateLp 2 h (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u) -
        zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u :=
  rfl

/-- Unfolding `zeroExtendedBaseL2`: it is the base coordinate of the zero
extension `ZeroTrace.zeroExtendH10 u ∈ H¹(ℝ^n)`. -/
@[simp]
theorem zeroExtendedBaseL2_apply (hΩmeas : MeasurableSet Ω)
    (u : H¹₀(Ω)) :
    zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u =
      (((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u : W^{1,2}(ℝ^n)) :
        WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)) :=
  rfl

/-- Zero extension followed by projection to the base coordinate is
contractive from `H¹₀(Ω)` to global `L²`. -/
theorem zeroExtendedBaseL2.norm_le
    (hΩmeas : MeasurableSet Ω) (u : H¹₀(Ω)) :
    ‖zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u‖ ≤ ‖u‖ := by
  calc
    ‖zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u‖
        ≤ ‖((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u : W^{1,2}(ℝ^n)) :
          WkpAmbientOn n 1 2 Set.univ)‖ := by
      change
        ‖(((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u : W^{1,2}(ℝ^n)) :
          WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))‖ ≤
        ‖((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u : W^{1,2}(ℝ^n)) :
          WkpAmbientOn n 1 2 Set.univ)‖
      exact PiLp.norm_apply_le _ (baseIndex n 1)
    _ = ‖ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩmeas u‖ := rfl
    _ = ‖u‖ := ZeroTrace.norm_zeroExtendH10 hΩmeas u

/-- The zero-extended base coordinate is represented by the literal indicator
of the original Sobolev function. -/
theorem zeroExtendedBaseL2_apply_ae (hΩmeas : MeasurableSet Ω)
    (u : H¹₀(Ω)) :
    ((zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ) =ᵐ[MeasureTheory.volume]
      Ω.indicator fun x ↦
        (((((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) :
          DerivLp n 2 Ω) : ℝ^n → ℝ) x) := by
  simpa [zeroExtendedBaseL2_apply, domainMeasure] using
    ZeroTrace.zeroExtendH10_coordinate_apply_ae
      (n := n) (Ω := Ω) hΩmeas u (baseIndex n 1)

/-- If `Ω` is bounded, every zero-extended base coordinate vanishes almost
everywhere outside one ball depending only on `Ω`.  This is the uniform
tightness half of the Rellich compactness argument. -/
theorem zeroExtendedBaseL2.ae_eq_zero_outside_ball
    (hΩmeas : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ R : ℝ, ∀ u : H¹₀(Ω),
      ∀ᵐ x ∂ (MeasureTheory.volume : Measure (ℝ^n)),
        x ∉ Metric.ball (0 : ℝ^n) R →
          (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u :
            DerivLp n 2 Set.univ) x = 0 := by
  obtain ⟨R, hR⟩ := hΩbounded.subset_ball (0 : ℝ^n)
  refine ⟨R, fun u ↦ ?_⟩
  filter_upwards [zeroExtendedBaseL2_apply_ae (n := n) (Ω := Ω) hΩmeas u] with x hx
  intro hxBall
  rw [hx]
  exact Set.indicator_of_notMem (fun hxΩ ↦ hxBall (hR hxΩ)) _

/-- On a bounded domain, choose one ball containing the zero extensions.
For each positive grid scale, every zero-extended `H¹₀` base coordinate
vanishes almost everywhere outside the ball's finite grid cover. The ball
is independent of the scale; the grid cells depend on it. This plays the role of step 2 of
Evans's proof of §5.7, Theorem 1, where the extended functions have support in one bounded open
set. -/
theorem zeroExtendedBaseL2.exists_euclideanGridSupport
    (hΩmeas : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ R : ℝ, ∀ {δ : ℝ}, 0 < δ → ∀ u : H¹₀(Ω),
      ∀ᵐ x ∂ (MeasureTheory.volume : Measure (ℝ^n)),
        x ∉ ⋃ k ∈ euclideanGridIndicesForBall (n := n) δ R,
            euclideanGridCell (n := n) δ k →
          (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u :
            DerivLp n 2 Set.univ) x = 0 := by
  obtain ⟨R, hR⟩ := zeroExtendedBaseL2.ae_eq_zero_outside_ball
    (n := n) (Ω := Ω) hΩmeas hΩbounded
  refine ⟨R, fun {δ} hδ u ↦ ?_⟩
  filter_upwards [hR u] with x hx
  intro hxGrid
  apply hx
  intro hxBall
  exact hxGrid (ball_subset_iUnion_euclideanGridCell (n := n) hδ hxBall)

/-- Every fixed zero-extended `H¹₀` function is strongly continuous under
global `L²` translations. -/
theorem zeroExtendedBaseL2.continuous_translate
    (hΩmeas : MeasurableSet Ω) (u : H¹₀(Ω)) :
    Continuous fun h : ℝ^n ↦
      translateLp 2 h (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u) :=
  continuous_translateLp 2 (by norm_num) _

/-- The `H¹₀` translation estimate `‖τ_h ũ - ũ‖_{L²} ≤ |h| ‖u‖` for `u ∈ H¹₀(Ω)` and `h ∈ ℝ^n`,
`ũ` the zero extension, obtained from the smooth result by density. This is the uniform
translation control used by the grid approximation `euclideanGridAverageOperator.norm_sub_le`. -/
theorem translationDefectCLM.norm_le
    (hΩmeas : MeasurableSet Ω) (h : ℝ^n)
    (u : H¹₀(Ω)) :
    ‖translationDefectCLM (n := n) (Ω := Ω) hΩmeas h u‖ ≤
      ‖h‖ * ‖u‖ := by
  refine DenseRange.induction_on (denseRange_testFunctionToH10Linear (n := n) (Ω := Ω)) u
    (isClosed_le (translationDefectCLM (n := n) (Ω := Ω) hΩmeas h).continuous.norm
      (continuous_const.mul continuous_norm)) fun φΩ ↦ ?_
  have hzero := ZeroTrace.zeroExtendH10_testFunction_eq (n := n) (Ω := Ω) hΩmeas φΩ
  change ‖translateLp 2 h (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := univ)
      (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩmeas (testFunctionToH10 (n := n) (Ω := Ω) φΩ))) -
    wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := univ)
      (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩmeas (testFunctionToH10 (n := n) (Ω := Ω) φΩ))‖ ≤
    ‖h‖ * ‖testFunctionToH10 (n := n) (Ω := Ω) φΩ‖
  rw [← ZeroTrace.norm_zeroExtendH10 hΩmeas, hzero]
  simpa [wkpBaseCoordinateCLM, wkpCoordinateCLM] using
    norm_translateL2_sub_globalTestFunction_le φΩ.1 h

/-- Integrated translation control over the box of within-cell shifts.
This is the quantitative input for the finite-grid proof of the
`H¹₀(Ω) → L²(Ω)` Rellich theorem. -/
theorem translationDefectCLM.integral_norm_sq_le
    (hΩmeas : MeasurableSet Ω) {δ : ℝ} (hδ : 0 < δ)
    (u : H¹₀(Ω)) :
    (∫ h in euclideanDifferenceBox (n := n) δ,
        ‖translationDefectCLM (n := n) (Ω := Ω) hΩmeas h u‖ ^ 2) ≤
      (2 * δ) ^ n * ((n : ℝ) * δ ^ 2 * ‖u‖ ^ 2) := by
  have hbox := isCompact_euclideanDifferenceBox (n := n) δ
  have hcont : Continuous fun h ↦ ‖translationDefectCLM (n := n) (Ω := Ω) hΩmeas h u‖ ^ 2 :=
    ((zeroExtendedBaseL2.continuous_translate hΩmeas u).sub continuous_const).norm.pow 2
  calc (∫ h in euclideanDifferenceBox (n := n) δ,
        ‖translationDefectCLM (n := n) (Ω := Ω) hΩmeas h u‖ ^ 2)
      ≤ ∫ _ in euclideanDifferenceBox (n := n) δ, (n : ℝ) * δ ^ 2 * ‖u‖ ^ 2 := by
        refine setIntegral_mono_on (hcont.continuousOn.integrableOn_compact hbox)
          (integrableOn_const hbox.measure_lt_top.ne)
          (measurableSet_euclideanDifferenceBox (n := n) δ) fun h hh ↦ ?_
        calc ‖translationDefectCLM (n := n) (Ω := Ω) hΩmeas h u‖ ^ 2 ≤ (‖h‖ * ‖u‖) ^ 2 := by
              gcongr
              exact translationDefectCLM.norm_le hΩmeas h u
          _ = ‖h‖ ^ 2 * ‖u‖ ^ 2 := mul_pow _ _ _
          _ ≤ _ := by
              gcongr
              exact norm_sq_le_of_mem_euclideanDifferenceBox (n := n) hh
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_euclideanDifferenceBox,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

/-- Quantitative finite-rank grid approximation of a zero-extended
`H¹₀` function.  The factor `2^n n` comes from the ratio between the
within-cell difference box and one grid cell, together with
`|h|² ≤ n δ²`.

In the bounded-domain `H¹₀ → L²` case, it replaces the mollification and Arzelà–Ascoli steps
of Evans's proof of §5.7, Theorem 1. -/
theorem euclideanGridAverageOperator.norm_sub_sq_le
    (hΩmeas : MeasurableSet Ω) {δ : ℝ} (hδ : 0 < δ) (R : ℝ)
    (u : H¹₀(Ω))
    (hsupport : ∀ᵐ x ∂(MeasureTheory.volume : Measure (ℝ^n)),
      x ∉ ⋃ k ∈ euclideanGridIndicesForBall (n := n) δ R,
          euclideanGridCell (n := n) δ k →
        (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u :
          DerivLp n 2 Set.univ) x = 0) :
    ‖euclideanGridAverageOperator (n := n) δ R
        (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u) -
      zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u‖ ^ 2 ≤
      (2 : ℝ) ^ n * (n : ℝ) * δ ^ 2 * ‖u‖ ^ 2 := by
  let I := euclideanGridIndicesForBall (n := n) δ R
  let cell : (Fin n → ℤ) → Set (ℝ^n) := euclideanGridCell (n := n) δ
  let f := zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u
  have herr := finiteCellAverageOperator.norm_sub_sq_le_pairwise
    (μ := domainMeasure n Set.univ) I cell
    (fun k ↦ measurableSet_euclideanGridCell (n := n) δ k)
    (fun k hk ↦ by
      simpa [domainMeasure, cell] using
        volume_euclideanGridCell_ne_zero (n := n) hδ k)
    (fun k ↦ by simp [domainMeasure, cell, volume_euclideanGridCell])
    (by simpa [cell] using
      (pairwiseDisjoint_euclideanGridCell (n := n) hδ I))
    f (by simpa [domainMeasure, I, cell, f] using hsupport)
  calc
    ‖euclideanGridAverageOperator (n := n) δ R f - f‖ ^ 2 ≤
        ∑ k ∈ I, ((domainMeasure n Set.univ).real (cell k))⁻¹ *
          ∫ x in cell k, ∫ y in cell k, (f x - f y) ^ 2 := by
      simpa [euclideanGridAverageOperator, I, cell, f] using herr
    _ = (δ ^ n)⁻¹ *
        ∑ k ∈ I, ∫ x in cell k, ∫ y in cell k, (f x - f y) ^ 2 := by
      simp_rw [show ∀ k : Fin n → ℤ,
          (domainMeasure n Set.univ).real (cell k) = δ ^ n by
        intro k
        simpa [domainMeasure, cell] using
          volumeReal_euclideanGridCell (n := n) hδ k]
      rw [Finset.mul_sum]
    _ ≤ (δ ^ n)⁻¹ *
        ∫ h in euclideanDifferenceBox (n := n) δ,
          ‖translateLp 2 h f - f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_gridCell_pairwise_le_integral_norm_translateL2_sub_sq hδ I f)
        (by positivity)
    _ ≤ (δ ^ n)⁻¹ * ((2 * δ) ^ n * ((n : ℝ) * δ ^ 2 * ‖u‖ ^ 2)) := by
      gcongr
      exact translationDefectCLM.integral_norm_sq_le hΩmeas hδ u
    _ = (2 : ℝ) ^ n * (n : ℝ) * δ ^ 2 * ‖u‖ ^ 2 := by
      rw [mul_pow, mul_comm (2 ^ n : ℝ), mul_assoc (δ ^ n),
        inv_mul_cancel_left₀ (pow_ne_zero _ hδ.ne')]
      ring

/-- Unsquared form of the finite-rank grid approximation estimate. -/
theorem euclideanGridAverageOperator.norm_sub_le
    (hΩmeas : MeasurableSet Ω) {δ : ℝ} (hδ : 0 < δ) (R : ℝ)
    (u : H¹₀(Ω))
    (hsupport : ∀ᵐ x ∂(MeasureTheory.volume : Measure (ℝ^n)),
      x ∉ ⋃ k ∈ euclideanGridIndicesForBall (n := n) δ R,
          euclideanGridCell (n := n) δ k →
        (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u :
          DerivLp n 2 Set.univ) x = 0) :
    ‖euclideanGridAverageOperator (n := n) δ R
        (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u) -
      zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u‖ ≤
      Real.sqrt ((2 : ℝ) ^ n * (n : ℝ)) * δ * ‖u‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  exact euclideanGridAverageOperator.norm_sub_sq_le hΩmeas hδ R u hsupport

/-- **Rellich compactness for zero-trace functions.** If `Ω` is measurable and bounded,
zero extension followed by the base-coordinate projection is a compact map
`H¹₀(Ω) → L²(ℝ^n)`.

This is the case `p = 2` of the Remark after Evans §5.7, Theorem 1 (p. 289), that
`W^{1,p}_0(U) ⊂⊂ L^p(U)` without regularity of `∂U`, here for a bounded measurable set.
Membership in `H¹₀` supplies an isometric zero extension, so no boundary regularity enters. -/
theorem zeroExtendedBaseL2.isCompactOperator
    (hΩmeas : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω) :
    IsCompactOperator
      (zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas) := by
  let F := zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas
  let S : Set (DerivLp n 2 Set.univ) := F '' Metric.closedBall (0 : H¹₀(Ω)) 1
  obtain ⟨R, hR⟩ := zeroExtendedBaseL2.exists_euclideanGridSupport hΩmeas hΩbounded
  -- grid averages at scale `ε / (K + 1)` approximate `S` uniformly within `ε`
  have htot : TotallyBounded S := by
    refine totallyBounded_of_uniform_compact_approximation S
      (Metric.isBounded_closedBall.image F) fun ε hε ↦ ?_
    set K : ℝ := Real.sqrt ((2 : ℝ) ^ n * (n : ℝ))
    have hδ : 0 < ε / (K + 1) := by positivity
    refine ⟨euclideanGridAverageOperator (n := n) (ε / (K + 1)) R,
      euclideanGridAverageOperator.isCompactOperator (n := n) _ R, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    calc _ ≤ K * (ε / (K + 1)) * ‖u‖ :=
          euclideanGridAverageOperator.norm_sub_le hΩmeas hδ R u (hR hδ u)
      _ ≤ K * (ε / (K + 1)) :=
          mul_le_of_le_one_right (by positivity) (mem_closedBall_zero_iff.mp hu)
      _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
      _ = ε := mul_div_cancel₀ _ (by positivity)
  refine (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image F).2
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos, ?_⟩
  exact htot.closure.isCompact_of_isClosed isClosed_closure

/-- Uniform translation continuity on every norm-bounded subset of
`H¹₀(Ω)`, with an explicit modulus independent of the function. -/
theorem translationDefectCLM.uniform_on_norm_bounded
    (hΩmeas : MeasurableSet Ω) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : H¹₀(Ω), ‖u‖ ≤ C →
      ∀ h : ℝ^n, ‖h‖ < δ →
        ‖translationDefectCLM (n := n) (Ω := Ω) hΩmeas h u‖ < ε := by
  let D := C + 1
  have hD : 0 < D := by dsimp [D]; linarith
  let δ := ε / D
  have hδ : 0 < δ := div_pos hε hD
  refine ⟨δ, hδ, fun u hu h hh ↦ ?_⟩
  calc
    ‖translationDefectCLM (n := n) (Ω := Ω) hΩmeas h u‖
        ≤ ‖h‖ * ‖u‖ := translationDefectCLM.norm_le hΩmeas h u
    _ ≤ ‖h‖ * C := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ ≤ ‖h‖ * D := mul_le_mul_of_nonneg_left (by dsimp [D]; linarith) (norm_nonneg _)
    _ < δ * D := mul_lt_mul_of_pos_right hh hD
    _ = ε := by simp [δ, ne_of_gt hD]

end ZeroExtension

section Boundary.C1ExtensionAtlas

variable {Ω : Set (ℝ^n)}

variable [Fact (0 < n)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- **Rellich compactness** for `H¹(Ω) → L²(Ω)` under the operational
`Boundary.C1ExtensionAtlas` hypothesis.
The order-zero inclusion

`H¹(Ω) → L²(Ω)`

is compact when `Ω` carries the operational chart-and-cutoff data used by the
extension theorem.  Deriving this hypothesis from the standard assertion that
`Ω` has `C¹` boundary is a separate geometric step.

The proof factors the inclusion in four steps.  `Extension.C1.extensionCLM`
sends `H¹(Ω)` boundedly into `H¹(ℝ^n)` and agrees with the original base
function almost everywhere on `Ω`.  Multiplying by a smooth compactly supported
cutoff equal to one on `closure Ω` and restricting to a ball `B` containing its
support lands continuously in `H¹₀(B)`.  The bounded-domain Rellich theorem for
`H¹₀(B)` makes zero extension followed by the base-coordinate map compact, and
precomposition keeps it compact.  Finally restriction `L²(ℝ^n) → L²(Ω)` is
bounded, and since the cutoff is one on `Ω` the composite is the order-zero
inclusion. -/
theorem baseCoordinateL2_isCompactOperator_of_c1Domain :
    IsCompactOperator
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := 2) (Ω := Ω)) := by
  obtain ⟨ψ, -, hψone, -, -⟩ := TestFunction.exists_eq_one_on_compact (n := n) isOpen_univ
    hΩ.bounded.isCompact_closure (subset_univ _)
  obtain ⟨R, hψB⟩ := ψ.hasCompactSupport.isCompact.isBounded.subset_ball (0 : ℝ^n)
  let B : Set (ℝ^n) := Metric.ball 0 R
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hΩB : Ω ⊆ B := fun x hx ↦ hψB <| subset_tsupport _ <| show ψ.toFun x ≠ 0 by
    rw [hψone x (subset_closure hx)]
    exact one_ne_zero
  let ext := Extension.C1.extensionCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω)
  -- multiply the global extension by `ψ` and restrict to `B`: this lands in `H¹₀(B)`
  let localizedGlobalH1 : H¹(Ω) →L[ℝ] W^{1,2}(ℝ^n) :=
    (cutoffCLM (n := n) (p := (2 : ℝ≥0∞)) (Ω := univ) ψ).comp ext
  let localizedOnB : H¹(Ω) →L[ℝ] H¹(B) :=
    (restrictCLM (n := n) (k := 1) (p := (2 : ℝ≥0∞)) hBopen.measurableSet (subset_univ B)).comp
      localizedGlobalH1
  let localizedH10 : H¹(Ω) →L[ℝ] H¹₀(B) :=
    localizedOnB.codRestrict (h10SubmoduleOn (n := n) (Ω := B)).toSubmodule fun u ↦ by
      let f : ℝ^n → ℝ := fun x ↦ ψ.toFun x * ((ext u : WkpAmbientOn n 1 2 univ) (baseIndex n 1)) x
      have hbase : (((((localizedGlobalH1 u : W^{1,2}(ℝ^n)) : WkpAmbientOn n 1 2 univ)
          (baseIndex n 1) : DerivLp n 2 univ) : ℝ^n → ℝ)) =ᵐ[volume] f := by
        simpa [localizedGlobalH1, f, domainMeasure] using
          cutoffCLM_base_apply_ae (n := n) (p := (2 : ℝ≥0∞)) (Ω := univ) ψ (ext u)
      simpa [localizedOnB] using restrict_mem_H10_of_tsupport_subset hBopen (localizedGlobalH1 u) f
        hbase ψ.hasCompactSupport.mul_right (tsupport_mul_subset_left.trans hψB)
  -- the compact middle map: the bounded-ball Rellich operator after the localized extension
  let compactGlobal : H¹(Ω) →L[ℝ] DerivLp n 2 univ :=
    (zeroExtendedBaseL2 (n := n) (Ω := B) hBopen.measurableSet).comp localizedH10
  let restrictΩ := restrictDerivLp (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) (Ωbig := univ)
    (subset_univ Ω)
  -- restricting back to `Ω`, where `ψ = 1`, gives the base-coordinate map
  have heq : wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω) =
      restrictΩ.comp compactGlobal := by
    ext u
    have hzero : ((compactGlobal u : DerivLp n 2 univ) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        B.indicator fun x ↦ (((((localizedH10 u : H¹(B)) : WkpAmbientOn n 1 2 B)
          (baseIndex n 1) : DerivLp n 2 B) : ℝ^n → ℝ) x) := by
      filter_upwards [ae_restrict_of_ae (s := Ω)
        (zeroExtendedBaseL2_apply_ae (n := n) (Ω := B) hBopen.measurableSet (localizedH10 u))]
        with x hx
      simpa [compactGlobal, domainMeasure] using hx
    have hlocal : (((((localizedH10 u : H¹(B)) : WkpAmbientOn n 1 2 B) (baseIndex n 1) :
        DerivLp n 2 B) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
          fun x ↦ ((localizedGlobalH1 u : WkpAmbientOn n 1 2 univ) (baseIndex n 1)) x := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩB
        (restrictCLM_apply_ae (n := n) (k := 1) (p := (2 : ℝ≥0∞)) hBopen.measurableSet
          (subset_univ B) (localizedGlobalH1 u) (baseIndex n 1))] with x hx
      rw [show (localizedH10 u : H¹(B)) = localizedOnB u from rfl]
      simpa [localizedOnB] using hx
    have hcutoff : (((((localizedGlobalH1 u : W^{1,2}(ℝ^n)) : WkpAmbientOn n 1 2 univ)
        (baseIndex n 1) : DerivLp n 2 univ) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
          fun x ↦ ψ.toFun x * ((ext u : WkpAmbientOn n 1 2 univ) (baseIndex n 1)) x := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (subset_univ Ω)
        (cutoffCLM_base_apply_ae (n := n) (p := (2 : ℝ≥0∞)) (Ω := univ) ψ (ext u))] with x hx
      simpa [localizedGlobalH1, domainMeasure] using hx
    filter_upwards [restrictDerivLp_apply_ae (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) (Ωbig := univ)
        (subset_univ Ω) (compactGlobal u), hzero, hlocal, hcutoff,
      Extension.C1.extensionCLM_agree_ae (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) u,
      ae_restrict_mem hΩ.isOpen.measurableSet] with x hfinal hzeroX hlocalX hcutoffX hagreeX hxΩ
    rw [show (restrictΩ.comp compactGlobal u : DerivLp n 2 Ω) x =
        (compactGlobal u : DerivLp n 2 univ) x from hfinal, hzeroX, indicator_of_mem (hΩB hxΩ),
      hlocalX, hcutoffX, hψone x (subset_closure hxΩ), one_mul]
    simpa [baseRepresentative] using hagreeX.symm
  rw [heq]
  exact ((zeroExtendedBaseL2.isCompactOperator (n := n) (Ω := B) hBopen.measurableSet
    Metric.isBounded_ball).comp_clm localizedH10).clm_comp restrictΩ

end Boundary.C1ExtensionAtlas

end Rellich

open MeasureTheory Set Function
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The ordinary `H¹₀(Ω) → L²(Ω)` base-coordinate map factors as zero
extension to `ℝ^n`, followed by restriction back to `Ω`. -/
theorem baseCoordCLM.eq_restrict_comp_zeroExtendedBaseL2
    (hΩmeas : MeasurableSet Ω) :
    baseCoordCLM (n := n) (Ω := Ω) =
      (restrictDerivLp (n := n) (p := (2 : ℝ≥0∞))
        (Ω := Ω) (Ωbig := Set.univ) (Set.subset_univ Ω)).comp
        (Rellich.zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas) := by
  ext u
  have hrestrict := restrictDerivLp_apply_ae
    (n := n) (p := (2 : ℝ≥0∞)) (Ω := Ω) (Ωbig := Set.univ)
    (Set.subset_univ Ω)
    (Rellich.zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u)
  have hzeroGlobal := Rellich.zeroExtendedBaseL2_apply_ae
    (n := n) (Ω := Ω) hΩmeas u
  have hzero :
      ((Rellich.zeroExtendedBaseL2 (n := n) (Ω := Ω) hΩmeas u :
          DerivLp n 2 Set.univ) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        Ω.indicator fun x ↦
          (((((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)
            (baseIndex n 1) : DerivLp n 2 Ω) : ℝ^n → ℝ) x) := by
    have hzeroΩ := MeasureTheory.ae_restrict_of_ae (s := Ω) hzeroGlobal
    filter_upwards [hzeroΩ] with x hx
    simpa [domainMeasure] using hx
  filter_upwards [hrestrict, hzero,
    MeasureTheory.ae_restrict_mem hΩmeas] with x hres hzero hxΩ
  rw [ContinuousLinearMap.comp_apply, hres, hzero,
    Set.indicator_of_mem hxΩ]
  rfl

/-- Rellich compactness of the concrete embedding `H¹₀(Ω) → L²(Ω)` on a
bounded measurable domain. -/
theorem baseCoordCLM.isCompactOperator_of_bounded
    (hΩmeas : MeasurableSet Ω) (hΩbounded : Bornology.IsBounded Ω) :
    IsCompactOperator (baseCoordCLM (n := n) (Ω := Ω)) := by
  rw [baseCoordCLM.eq_restrict_comp_zeroExtendedBaseL2
    (n := n) (Ω := Ω) hΩmeas]
  exact (Rellich.zeroExtendedBaseL2.isCompactOperator
    (n := n) (Ω := Ω) hΩmeas hΩbounded).clm_comp
      (restrictDerivLp (n := n) (p := (2 : ℝ≥0∞))
        (Ω := Ω) (Ωbig := Set.univ) (Set.subset_univ Ω))

end GraphSpace
end SobolevSpace
