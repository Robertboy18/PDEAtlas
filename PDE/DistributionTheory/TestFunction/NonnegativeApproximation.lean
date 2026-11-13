/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction
public import PDE.Spaces.Sobolev.Approximation.Mollification.FiniteJets

/-!
# Nonnegative smooth approximation of finite-regularity tests

A positive mollifier preserves nonnegativity. Shrinking its radius inside a compact
support collar gives smooth tests in the original open set, with one common compact
support and uniform convergence of every available jet.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace TestFunction

open SobolevSpace SobolevSpace.Approximation

variable {n m : ℕ} {U : Opens (ℝ^n)}

/-- Compact Cᵐ tests admit smooth tests in the same domain; positivity is preserved.
Their supports lie in one interior compact set and their available jets converge uniformly. -/
theorem exists_smooth_jet_approximation_preserving_nonneg
    (φ : 𝓓^{m}(U, ℝ)) :
    ∃ (K : Set (ℝ^n)) (a : ℕ → 𝓓(U, ℝ)),
      IsCompact K ∧ K ⊆ U ∧ tsupport φ ⊆ K ∧
      (∀ j, tsupport (a j) ⊆ K ∧ ((∀ x, 0 ≤ φ x) → ∀ x, 0 ≤ a j x)) ∧
      ∀ indices : List (Fin n), indices.length ≤ m →
        TendstoUniformly (fun j ↦ iteratedPartialDeriv indices (a j))
          (iteratedPartialDeriv indices φ) atTop := by
  obtain ⟨μ, _, _, _, _⟩ := exists_radial_mollifier n
  obtain ⟨δ, hδ, hδU⟩ :=
    φ.hasCompactSupport.isCompact.exists_cthickening_subset_open U.isOpen φ.tsupport_subset
  obtain ⟨R, hR⟩ := μ.compactSupport.isCompact.isBounded.subset_closedBall (0 : ℝ^n)
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hεpos : ∀ j, 0 < ε j := fun j ↦
    one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one)
  have hεle : ∀ j, ε j ≤ 1 := fun j ↦
    (div_le_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one)).mpr
      (le_add_of_nonneg_left (Nat.cast_nonneg j))
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hscale : ∀ᶠ j in atTop, ε j * R < δ := by
    have hlim : Tendsto (fun j ↦ ε j * R) atTop (𝓝 0) := by
      simpa using hε0.mul_const R
    exact hlim.eventually (Iio_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hscale
  let K := Metric.cthickening δ (tsupport φ)
  have hK : IsCompact K := φ.hasCompactSupport.isCompact.cthickening
  have hsupp (j : ℕ) : tsupport (mollify μ (ε (j + N)) φ) ⊆ K :=
    closure_minimal
      (support_mollify_subset_cthickening μ (hεpos _) hR
        (hN _ (Nat.le_add_left _ _)) φ) Metric.isClosed_cthickening
  let a : ℕ → 𝓓(U, ℝ) := fun j ↦
    TestFunction.mk (mollify μ (ε (j + N)) φ)
      (mollify_contDiff_of_pos μ (hεpos _) φ φ.contDiff.continuous.locallyIntegrable)
      (HasCompactSupport.of_support_subset_isCompact hK
        ((subset_tsupport _).trans (hsupp j))) ((hsupp j).trans hδU)
  refine ⟨K, a, hK, hδU, Metric.self_subset_cthickening _, ?_, ?_⟩
  · intro j
    refine ⟨hsupp j, fun hφ x ↦ ?_⟩
    exact integral_nonneg fun y ↦ mul_nonneg (scaled_nonneg μ (hεpos _) y) (hφ (x - y))
  · intro indices hindices
    exact iteratedPartialDeriv_mollify_tendstoUniformly
      μ φ.contDiff φ.hasCompactSupport (fun j ↦ ε (j + N))
      (fun j ↦ hεpos _) (fun j ↦ hεle _)
      (hε0.comp (tendsto_add_atTop_nat N)) indices hindices


/-- Nonnegative compact Cᵐ tests admit nonnegative smooth tests in the same domain.
Their supports lie in one interior compact set and their available jets converge uniformly. -/
theorem exists_nonneg_smooth_jet_approximation
    (φ : 𝓓^{m}(U, ℝ)) (hφ : ∀ x, 0 ≤ φ x) :
    ∃ (K : Set (ℝ^n)) (a : ℕ → 𝓓(U, ℝ)),
      IsCompact K ∧ K ⊆ U ∧ tsupport φ ⊆ K ∧
      (∀ j, tsupport (a j) ⊆ K ∧ ∀ x, 0 ≤ a j x) ∧
      ∀ indices : List (Fin n), indices.length ≤ m →
        TendstoUniformly (fun j ↦ iteratedPartialDeriv indices (a j))
          (iteratedPartialDeriv indices φ) atTop := by
  obtain ⟨K, a, hK, hKU, hφK, haK, hconv⟩ :=
    exists_smooth_jet_approximation_preserving_nonneg φ
  exact ⟨K, a, hK, hKU, hφK, fun j ↦ ⟨(haK j).1, (haK j).2 hφ⟩, hconv⟩

end TestFunction
