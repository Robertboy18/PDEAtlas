/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import PDE.Common.Euclidean
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Compactly supported test-function cutoffs

Given a compact set `K` inside an open set `U` of a finite-dimensional real normed space,
there is a smooth function `ψ` with `0 ≤ ψ ≤ 1`, `tsupport ψ ⊆ U`, and `ψ = 1` on a
neighbourhood of `K`. This is the smooth Urysohn lemma that underlies partitions of unity and
localization arguments in distribution theory; see Hörmander, Chapter I.

Mathlib's smooth separation theorem supplies a function equal to `1` near `K` and vanishing
outside a compact neighbourhood contained in `U`. We view it as a test function, retaining
the support, neighbourhood, and range guarantees.

## Main results

* `exists_eq_one_on_compact_finiteDimensional`: the cutoff as an element of the
  test-function space `𝓓((⊤ : Opens E), ℝ)` together with the four properties above.
* `exists_eq_one_on_compact`: the same statement specialized to `ℝ^n`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Classics in
  Mathematics, Springer, 2003, Chapter I, "Test Functions".
  <https://doi.org/10.1007/978-3-642-61497-2_2>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace TestFunction

open Set
open scoped Topology BigOperators

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth cutoff supported in an open set and equal to `1` near a compact subset of a
finite-dimensional real normed space. -/
theorem exists_eq_one_on_compact_finiteDimensional {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ψ : 𝓓((⊤ : Opens E), ℝ),
      tsupport ψ.toFun ⊆ U ∧
      (∀ x ∈ K, ψ.toFun x = 1) ∧
      (∀ x ∈ K, ψ.toFun =ᶠ[𝓝 x] 1) ∧
      (∀ x, ψ.toFun x ∈ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf1, hf0, hfRange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ E) hK.isClosed hKL (n := (⊤ : ℕ∞))
  have hfSupport : tsupport f ⊆ L :=
    closure_minimal (Function.support_subset_iff'.mpr hf0) hL.isClosed
  refine ⟨TestFunction.mk f (contMDiff_iff_contDiff.mp f.contMDiff)
    (HasCompactSupport.of_support_subset_isCompact hL
      ((subset_tsupport f).trans hfSupport)) (subset_univ _),
    hfSupport.trans hLU, hf1.self_of_nhdsSet, ?_, hfRange⟩
  exact fun x hx ↦ hf1.filter_mono (nhds_le_nhdsSet hx)

/-- A smooth cutoff supported in an open Euclidean set and equal to `1` near a compact subset. -/
theorem exists_eq_one_on_compact {n : ℕ} {U K : Set (ℝ^n)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      tsupport ψ.toFun ⊆ U ∧
      (∀ x ∈ K, ψ.toFun x = 1) ∧
      (∀ x ∈ K, ψ.toFun =ᶠ[𝓝 x] 1) ∧
      (∀ x, ψ.toFun x ∈ Set.Icc (0 : ℝ) 1) :=
  exists_eq_one_on_compact_finiteDimensional hU hK hKU

end TestFunction
