/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.Density

/-!
# Localization for singular weighted Sobolev density

Smooth approximation for an unbounded or singular row weight cannot in general be obtained by
applying the unweighted mollification theorem directly. The usual argument localizes a Sobolev
graph, compares the target weight on the localized region with a bounded reference weight,
mollifies there, and controls the error outside that region separately.

We record the bookkeeping of that argument, not its analytic content. The local comparison is a
domination of row measures, converted into a quantitative jet estimate by
`dist_toDerivativeL2Rows_of_measure_le_smul`. The error outside the localized region enters as a
hypothesis, `EventuallyDistLeWeightedDistAdd`, asserting directly that the `w`-distance from the
approximants to the localized graph is eventually at most the dominated-weight distance plus a
tolerance. The final predicate `HasLocallyComparableExhaustion` bundles these data existentially,
with every witness chosen per graph element and per accuracy.

## Main results

* `dist_localizedDerivativeL2Rows_le`: transfer of a jet distance from a bounded reference
  weight to a dominated target weight, at the cost of the operator norm of the change of weights.
* `exists_testFunction_localizedDerivativeL2Rows_dist_lt`: test-function approximation in any
  weight dominated by a bounded reference weight, from `globalApproximation_derivativeL2Rows`.
* `exists_testFunction_dist_lt_of_localized_measure_comparison`: the `ε/3` assembly of
  localization, reference convergence, and the distance comparison.
* `HasLocallyComparableExhaustion.hasSmoothCoreOn`: the predicate implies `HasSmoothCoreOn`.

## Implementation notes

`HasLocallyComparableExhaustion w` is logically equivalent to plain approximation of every
realizable weighted graph by eligible test functions in the `w`-norm, which is the hypothesis of
`HasSmoothCoreOn.of_graph_approximation`. The witnesses `q = v = 0`, `V = U`, and any sequence
`φ` approximating `U` in the `w`-norm satisfy every clause, because convergence in the
reference weight `v = 0` takes place in the zero space and is trivial. The localization structure
therefore carries no logical content on its own: an application must still prove `w`-norm
approximation, and the predicate only fixes the shape in which that proof is organized. We do
not establish the predicate for any singular weight, and convergence in a bounded reference norm
does not by itself imply convergence in a singular weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open TopologicalSpace
open scoped Distributions ENNReal Topology Sobolev

namespace SobolevSpace
namespace Weighted

variable {n k : ℕ}

/-- Eventually along the sequence `φ`, each `φ m` is `w`-eligible and its `w`-distance to `V` is
at most its `q`-distance to `V` plus `δ`, where the `q`-distance is computed after changing
weights from the bounded reference `v` to the dominated weight `q`.

The statement bounds the full `w`-distance. In an application the `w`-distance is split into a
part controlled by the `q`-distance and a remainder over the region discarded by a localization,
and `δ` absorbs the remainder. -/
def EventuallyDistLeWeightedDistAdd
    (w q v : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (B C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hB : ∀ a, B a ≠ ∞) (hC : ∀ a, C a ≠ ∞)
    (hv : ∀ a,
      (domainMeasure n Set.univ).withDensity (v a) ≤
        B a • domainMeasure n Set.univ)
    (hqv : ∀ a,
      (domainMeasure n Set.univ).withDensity (q a) ≤
        C a • (domainMeasure n Set.univ).withDensity (v a))
    (V : W^{k,2}(ℝ^n))
    (hVw : CoordinatesMemL2WithDensities w V)
    (φ : ℕ → 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (δ : ℝ) : Prop :=
  ∀ᶠ m in Filter.atTop,
    ∃ hφw : CoordinatesMemL2WithDensities w
        (GraphSpace.globalTestFunctionToWkpOnLinear
          (n := n) (k := k) (p := 2) (Ω := Set.univ) (φ m)),
      dist
          (toDerivativeL2Rows w
            (GraphSpace.globalTestFunctionToWkpOnLinear
              (n := n) (k := k) (p := 2) (Ω := Set.univ) (φ m)) hφw)
          (toDerivativeL2Rows w V hVw) ≤
        dist
            (l2RowsCLMOfMeasureLeSmul
              (domainMeasure n Set.univ) q v C hC hqv
              (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv
                (GraphSpace.globalTestFunctionToWkpOnLinear
                  (n := n) (k := k) (p := 2) (Ω := Set.univ) (φ m))))
            (l2RowsCLMOfMeasureLeSmul
              (domainMeasure n Set.univ) q v C hC hqv
              (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv V)) + δ

/-- Quantitative transfer of a Sobolev-jet distance from a bounded reference weight to a
localized target weight. -/
theorem dist_localizedDerivativeL2Rows_le
    (q v : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (B C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hB : ∀ a, B a ≠ ∞) (hC : ∀ a, C a ≠ ∞)
    (hv : ∀ a,
      (domainMeasure n Set.univ).withDensity (v a) ≤
        B a • domainMeasure n Set.univ)
    (hqv : ∀ a,
      (domainMeasure n Set.univ).withDensity (q a) ≤
        C a • (domainMeasure n Set.univ).withDensity (v a))
    (U V : W^{k,2}(ℝ^n)) :
    dist
        (l2RowsCLMOfMeasureLeSmul
          (domainMeasure n Set.univ) q v C hC hqv
          (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv U))
        (l2RowsCLMOfMeasureLeSmul
          (domainMeasure n Set.univ) q v C hC hqv
          (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv V)) ≤
      ‖l2RowsCLMOfMeasureLeSmul
          (domainMeasure n Set.univ) q v C hC hqv‖ *
        dist (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv U)
          (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv V) := by
  simpa only [derivativeL2RowsCLMOfMeasureLeSmul_apply,
    l2RowsCLMOfMeasureLeSmul_toDerivativeL2Rows] using
      dist_toDerivativeL2Rows_of_measure_le_smul
        q v C hC hqv U V
          (coordinatesMemL2WithDensities_of_measure_le_smul v B hB hv U)
          (coordinatesMemL2WithDensities_of_measure_le_smul v B hB hv V)

/-- Cutoff and mollification in a bounded reference weight give arbitrary accuracy after changing
to any row weight dominated by that reference weight. -/
theorem exists_testFunction_localizedDerivativeL2Rows_dist_lt
    (mollifier : Approximation.Mollifier n)
    (q v : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (B C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hB : ∀ a, B a ≠ ∞) (hC : ∀ a, C a ≠ ∞)
    (hv : ∀ a,
      (domainMeasure n Set.univ).withDensity (v a) ≤
        B a • domainMeasure n Set.univ)
    (hqv : ∀ a,
      (domainMeasure n Set.univ).withDensity (q a) ≤
        C a • (domainMeasure n Set.univ).withDensity (v a))
    (V : W^{k,2}(ℝ^n)) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      dist
          (l2RowsCLMOfMeasureLeSmul
            (domainMeasure n Set.univ) q v C hC hqv
            (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv
              (GraphSpace.globalTestFunctionToWkpOnLinear
                (n := n) (k := k) (p := 2) (Ω := Set.univ) φ)))
          (l2RowsCLMOfMeasureLeSmul
            (domainMeasure n Set.univ) q v C hC hqv
            (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv V)) < ε := by
  obtain ⟨f, hf, hcompact, hconv⟩ :=
    globalApproximation_derivativeL2Rows mollifier v B hB hv V
  let A := ‖l2RowsCLMOfMeasureLeSmul
    (domainMeasure n Set.univ) q v C hC hqv‖
  by_cases hA : A = 0
  · let φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
      ⟨f 0, hf 0, hcompact 0, Set.subset_univ _⟩
    refine ⟨φ, lt_of_le_of_lt ?_ hε⟩
    have hdist := dist_localizedDerivativeL2Rows_le
      q v B C hB hC hv hqv
      (GraphSpace.globalTestFunctionToWkpOnLinear
        (n := n) (k := k) (p := 2) (Ω := Set.univ) φ) V
    simpa [A, hA] using hdist
  · have hApos : 0 < A := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA)
    have htol : 0 < ε / A := div_pos hε hApos
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (ε / A) htol
    let φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
      ⟨f N, hf N, hcompact N, Set.subset_univ _⟩
    refine ⟨φ, lt_of_le_of_lt
      (dist_localizedDerivativeL2Rows_le
        q v B C hB hC hv hqv
        (GraphSpace.globalTestFunctionToWkpOnLinear
          (n := n) (k := k) (p := 2) (Ω := Set.univ) φ) V) ?_⟩
    have href :
        dist
            (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv
              (GraphSpace.globalTestFunctionToWkpOnLinear
                (n := n) (k := k) (p := 2) (Ω := Set.univ) φ))
            (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv V) < ε / A := by
      simpa [φ, GraphSpace.globalTestFunctionToWkpOnLinear,
        GraphSpace.globalTestFunctionToWkpOn] using hN N le_rfl
    calc
      ‖l2RowsCLMOfMeasureLeSmul
          (domainMeasure n Set.univ) q v C hC hqv‖ *
          dist
            (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv
              (GraphSpace.globalTestFunctionToWkpOnLinear
                (n := n) (k := k) (p := 2) (Ω := Set.univ) φ))
            (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv V)
          < A * (ε / A) := by
            simpa only [A] using mul_lt_mul_of_pos_left href hApos
      _ = ε := by field_simp

/-- A localized graph can be approximated in a singular global row norm when the localized weight
is dominated by a bounded reference weight and the `w`-distance is eventually controlled by
the dominated-weight distance (`EventuallyDistLeWeightedDistAdd`).

The reference convergence and the distance comparison concern the same test-function sequence.
The bounded-reference mollification theorem supplies reference convergence, but support and
decay estimates for the chosen sequence depend on the application. -/
theorem exists_testFunction_dist_lt_of_localized_measure_comparison
    (w q v : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (B C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hB : ∀ a, B a ≠ ∞) (hC : ∀ a, C a ≠ ∞)
    (hv : ∀ a,
      (domainMeasure n Set.univ).withDensity (v a) ≤
        B a • domainMeasure n Set.univ)
    (hqv : ∀ a,
      (domainMeasure n Set.univ).withDensity (q a) ≤
        C a • (domainMeasure n Set.univ).withDensity (v a))
    (U : coordinatesMemL2WithDensitiesSubmodule (Ω := Set.univ) w)
    (V : W^{k,2}(ℝ^n))
    (hVw : CoordinatesMemL2WithDensities w V)
    (φ : ℕ → 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (happrox : Filter.Tendsto
      (fun m ↦ derivativeL2RowsCLMOfMeasureLeSmul v B hB hv
        (GraphSpace.globalTestFunctionToWkpOnLinear
          (n := n) (k := k) (p := 2) (Ω := Set.univ) (φ m)))
      Filter.atTop (𝓝 (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv V)))
    (ε : ℝ) (hε : 0 < ε)
    (hlocalize :
      dist (toDerivativeL2Rows w V hVw)
          (toDerivativeL2Rows w U U.property) < ε / 3)
    (tail : EventuallyDistLeWeightedDistAdd w q v B C hB hC hv hqv V hVw φ (ε / 3)) :
    ∃ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
      (hφw : CoordinatesMemL2WithDensities w
        (GraphSpace.globalTestFunctionToWkpOnLinear
          (n := n) (k := k) (p := 2) (Ω := Set.univ) φ)),
      dist
          (toDerivativeL2Rows w
            (GraphSpace.globalTestFunctionToWkpOnLinear
              (n := n) (k := k) (p := 2) (Ω := Set.univ) φ) hφw)
          (toDerivativeL2Rows w U U.property) < ε := by
  have hthird : 0 < ε / 3 := div_pos hε (by norm_num)
  have hconv := ((l2RowsCLMOfMeasureLeSmul
    (domainMeasure n Set.univ) q v C hC hqv).continuous.tendsto
      (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv V)).comp happrox
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (ε / 3) hthird
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp tail
  let φ₀ := φ (max N M)
  have hqdist := hN (max N M) (le_max_left _ _)
  obtain ⟨hφw, htail⟩ := hM (max N M) (le_max_right _ _)
  refine ⟨φ₀, hφw, ?_⟩
  refine (dist_triangle _ (toDerivativeL2Rows w V hVw) _).trans_lt ?_
  calc
    dist
          (toDerivativeL2Rows w
            (GraphSpace.globalTestFunctionToWkpOnLinear
              (n := n) (k := k) (p := 2) (Ω := Set.univ) φ₀) hφw)
          (toDerivativeL2Rows w V hVw) +
        dist (toDerivativeL2Rows w V hVw)
          (toDerivativeL2Rows w U U.property)
        ≤ (ε / 3 + ε / 3) +
          dist (toDerivativeL2Rows w V hVw)
            (toDerivativeL2Rows w U U.property) := by
              exact add_le_add
                (htail.trans (add_le_add_left hqdist.le _)) le_rfl
    _ < (ε / 3 + ε / 3) + ε / 3 := by gcongr
    _ = ε := by ring

/-- For every realizable weighted graph `U` and accuracy `ε` there are: a graph `V` within `ε/3`
of `U` in the `w`-norm, a bounded reference weight `v` with a dominated weight `q`, and a
sequence of test functions converging to `V` in the `v`-norm whose `w`-distance to `V` is
eventually at most the `q`-distance plus `ε/3` (`EventuallyDistLeWeightedDistAdd`).

All witnesses, including the comparison constants `B` and `C`, are chosen per `U` and `ε`. Since
`q = v = 0` and `V = U` are admissible, the predicate is equivalent to approximation of every
realizable weighted graph by eligible test functions in the `w`-norm, arranged in the shape
of the localize-compare-mollify argument. -/
def HasLocallyComparableExhaustion
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) : Prop :=
  ∀
      (U : coordinatesMemL2WithDensitiesSubmodule (Ω := Set.univ) w)
      (ε : ℝ), 0 < ε →
      ∃ (q v : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
        (B C : GraphSpace.DerivIndex n k → ℝ≥0∞)
        (V : W^{k,2}(ℝ^n))
        (hVw : CoordinatesMemL2WithDensities w V)
        (φ : ℕ → 𝓓((⊤ : Opens (ℝ^n)), ℝ))
        (hB : ∀ a, B a ≠ ∞)
        (hC : ∀ a, C a ≠ ∞)
        (hv : ∀ a, (domainMeasure n Set.univ).withDensity (v a) ≤
          B a • domainMeasure n Set.univ)
        (hqv : ∀ a, (domainMeasure n Set.univ).withDensity (q a) ≤
          C a • (domainMeasure n Set.univ).withDensity (v a)),
        Filter.Tendsto
          (fun m ↦ derivativeL2RowsCLMOfMeasureLeSmul v B hB hv
            (GraphSpace.globalTestFunctionToWkpOnLinear
              (n := n) (k := k) (p := 2) (Ω := Set.univ) (φ m)))
          Filter.atTop (𝓝 (derivativeL2RowsCLMOfMeasureLeSmul v B hB hv V)) ∧
        dist (toDerivativeL2Rows w V hVw)
          (toDerivativeL2Rows w U U.property) < ε / 3 ∧
        EventuallyDistLeWeightedDistAdd w q v B C hB hC hv hqv V hVw φ (ε / 3)

/-- A locally comparable exhaustion supplies a test function close to any realizable weighted
Sobolev graph. -/
theorem HasLocallyComparableExhaustion.exists_testFunction_dist_lt
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hlocal : HasLocallyComparableExhaustion w)
    (U : coordinatesMemL2WithDensitiesSubmodule (Ω := Set.univ) w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
      (hφw : CoordinatesMemL2WithDensities w
        (GraphSpace.globalTestFunctionToWkpOnLinear
          (n := n) (k := k) (p := 2) (Ω := Set.univ) φ)),
      dist
          (toDerivativeL2Rows w
            (GraphSpace.globalTestFunctionToWkpOnLinear
              (n := n) (k := k) (p := 2) (Ω := Set.univ) φ) hφw)
          (toDerivativeL2Rows w U U.property) < ε := by
  obtain ⟨q, v, B, C, V, hVw, φ, hB, hC, hv, hqv, happrox, hclose, htail⟩ :=
    hlocal U ε hε
  exact exists_testFunction_dist_lt_of_localized_measure_comparison
    w q v B C hB hC hv hqv U V hVw φ happrox ε hε hclose htail

/-- `HasLocallyComparableExhaustion w` implies `HasSmoothCoreOn w`: eligible test functions are
dense in the completed weighted jet space. Since the hypothesis is equivalent to `w`-norm
approximation of realizable graphs, this is `HasSmoothCoreOn.of_graph_approximation`
restated, not an independent density theorem for singular weights. -/
theorem HasLocallyComparableExhaustion.hasSmoothCoreOn
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hlocal : HasLocallyComparableExhaustion w) :
    HasSmoothCoreOn (Ω := Set.univ) w := by
  apply HasSmoothCoreOn.of_graph_approximation
  intro U ε hε
  obtain ⟨φ, hφw, hdist⟩ :=
    hlocal.exists_testFunction_dist_lt U ε hε
  exact ⟨⟨φ, hφw⟩, hdist⟩

/-- For positive order-zero weight, closability and a locally comparable exhaustion make the
eligible test functions a core of the closed singular weighted derivative operator. -/
theorem HasLocallyComparableExhaustion.weightedJetOperator_closure_hasSmoothCore
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hlocal : HasLocallyComparableExhaustion w)
    (hw : AEMeasurable
      (w (GraphSpace.baseIndex n k)) (domainMeasure n Set.univ))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Set.univ,
      0 < w (GraphSpace.baseIndex n k) x)
    (hclosable : (weightedJetOperator (Ω := Set.univ) w).IsClosable) :
    (weightedJetOperator (Ω := Set.univ) w).closure.HasCore
      (smoothWeightedJetOperator (Ω := Set.univ) w).domain :=
  SobolevSpace.Weighted.weightedJetOperator_closure_hasSmoothCore
    isOpen_univ hw hw_pos hlocal.hasSmoothCoreOn hclosable

end Weighted
end SobolevSpace
