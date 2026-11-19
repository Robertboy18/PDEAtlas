/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution

/-!
# Restricting distributions to fixed compact supports

The test-function space `𝓓(E)` is the inductive limit of the Fréchet spaces `𝓓_K(E)` of smooth
functions supported in a compact set `K`, and a distribution is a linear functional whose
restriction to every `𝓓_K(E)` is continuous. Continuity on a Fréchet space defined by the
countable family of derivative seminorms means a bound by finitely many of them: for each `K`
there are `k` and `C` with

`‖⟨T, φ⟩‖ ≤ C · max_{j ≤ k} sup_x ‖D^j φ(x)‖` for all `φ ∈ 𝓓_K(E)`.

The smallest such `k` is the order of `T` on `K`; we prove existence of the bound without
minimizing `k`. See Hörmander, Chapter II, or Rudin, *Functional Analysis*.

## Main results

* `restrictToSupportedInCLM`: the restriction of `T` to `𝓓_K(E)` as a continuous linear map.
* `exists_norm_restrictToSupportedIn_le`: a bound by a finite supremum of derivative seminorms.
* `exists_norm_restrictToSupportedIn_le_supSeminorm`: the same bound with a single cumulative
  seminorm `ContDiffMapSupportedIn.supSeminorm ℝ E ℝ ⊤ K k`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Classics in
  Mathematics, Springer, 2003, Chapter II, "Definition and Basic Properties of Distributions".
  <https://doi.org/10.1007/978-3-642-61497-2_3>
* W. Rudin, *Functional Analysis*, 2nd ed., International Series in Pure and Applied
  Mathematics, McGraw-Hill, 1991.
-/

@[expose] public section

open Set TopologicalSpace
open scoped CompactConvergenceCLM Distributions

noncomputable section

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The continuous restriction of a distribution to test functions supported in `K`. -/
def restrictToSupportedInCLM
    (T : 𝓓'((⊤ : Opens E), G)) (K : Compacts E) :
    𝓓_{K}(E, ℝ) →L[ℝ] G :=
  ((ContinuousLinearMap.toUniformConvergenceCLM
      (RingHom.id ℝ) G {S : Set 𝓓((⊤ : Opens E), ℝ) | IsCompact S}).symm T).comp
    (TestFunction.ofSupportedInCLM ℝ (subset_univ _))

/-- The restriction to `𝓓_K` acts by evaluating `T` on the test function `φ`, viewed as an
element of the full LF space. -/
@[simp]
theorem restrictToSupportedInCLM_apply
    (T : 𝓓'((⊤ : Opens E), G)) (K : Compacts E)
    (φ : 𝓓_{K}(E, ℝ)) :
    restrictToSupportedInCLM T K φ =
      T (TestFunction.ofSupportedIn (subset_univ _) φ) :=
  rfl

/-- A distribution is controlled by finitely many derivative seminorms on each fixed support
stage. -/
theorem exists_norm_restrictToSupportedIn_le
    (T : 𝓓'((⊤ : Opens E), G)) (K : Compacts E) :
    ∃ (s : Finset ℕ) (C : NNReal), C ≠ 0 ∧
      ∀ φ : 𝓓_{K}(E, ℝ),
        ‖restrictToSupportedInCLM T K φ‖ ≤
          C * (s.sup (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) φ := by
  let q : Seminorm ℝ 𝓓_{K}(E, ℝ) :=
    (normSeminorm ℝ G).comp (restrictToSupportedInCLM T K).toLinearMap
  have hq : Continuous q := by
    change Continuous fun φ : 𝓓_{K}(E, ℝ) ↦ ‖restrictToSupportedInCLM T K φ‖
    fun_prop
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous
      (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K) q hq
  refine ⟨s, C, hC, fun φ ↦ ?_⟩
  exact hbound φ

/-- A distribution is controlled by one cumulative derivative seminorm on each fixed support
stage. -/
theorem exists_norm_restrictToSupportedIn_le_supSeminorm
    (T : 𝓓'((⊤ : Opens E), G)) (K : Compacts E) :
    ∃ (k : ℕ) (C : NNReal), C ≠ 0 ∧
      ∀ φ : 𝓓_{K}(E, ℝ),
        ‖restrictToSupportedInCLM T K φ‖ ≤
          C * ContDiffMapSupportedIn.supSeminorm ℝ E ℝ ⊤ K k φ := by
  obtain ⟨s, C, hC, hbound⟩ := exists_norm_restrictToSupportedIn_le T K
  refine ⟨s.sup id, C, hC, fun φ ↦ (hbound φ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  exact Seminorm.le_def.mp
    (Finset.sup_mono (Finset.subset_Iic_sup_id s)) φ

end Distribution
