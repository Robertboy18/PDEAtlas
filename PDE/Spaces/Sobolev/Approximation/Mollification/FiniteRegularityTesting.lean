/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.FiniteJets
import PDE.Analysis.Integration.CompactSupportLimit
import PDE.DistributionTheory.TestFunction.NonnegativeApproximation

/-!
# Finite-regularity tests for weak derivatives

Mollification approximates a compact Cᵐ test in every available jet, with eventual support
in one compact subset of the original open domain. Local integrability then extends the
distributional integration-by-parts identity from smooth tests to these finite-regularity tests.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace SobolevSpace

variable {n m : ℕ}

/-- Compact Cᵐ tests admit smooth approximations whose jets converge uniformly and whose
supports eventually lie in one compact subset of the same open domain. -/
theorem Approximation.exists_testFunction_jet_approximation
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) {φ : ℝ^n → ℝ}
    (hφ : ContDiff ℝ m φ) (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    ∃ (K : Set (ℝ^n)) (a : ℕ → 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      IsCompact K ∧ K ⊆ Ω ∧ tsupport φ ⊆ K ∧
      (∀ᶠ j in atTop, tsupport (a j).toFun ⊆ K) ∧
      ∀ indices : List (Fin n), indices.length ≤ m →
        TendstoUniformly (fun j ↦ iteratedPartialDeriv indices (a j).toFun)
          (iteratedPartialDeriv indices φ) atTop := by
  let ψ : 𝓓^{m}(⟨Ω, hΩ⟩, ℝ) :=
    TestFunction.mk φ hφ hφc hφΩ
  obtain ⟨K, a, hK, hKΩ, hφK, haK, hconv⟩ :=
    TestFunction.exists_smooth_jet_approximation_preserving_nonneg ψ
  let b : ℕ → 𝓓((⊤ : Opens (ℝ^n)), ℝ) := fun j ↦
    TestFunction.mk (a j) (a j).contDiff (a j).hasCompactSupport (subset_univ _)
  exact ⟨K, b, hK, hKΩ, hφK,
    Eventually.of_forall (fun j ↦ (haK j).1), hconv⟩

private theorem tendsto_integral_mul_of_uniform
    {Ω K : Set (ℝ^n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {f ψ : ℝ^n → ℝ} (hf : LocallyIntegrableOn f Ω volume)
    (hψ : Continuous ψ) (hψK : tsupport ψ ⊆ K)
    {a : ℕ → ℝ^n → ℝ} (ha : ∀ j, Continuous (a j))
    (haK : ∀ᶠ j in atTop, tsupport (a j) ⊆ K)
    (hconv : TendstoUniformly a ψ atTop) :
    Tendsto (fun j ↦ ∫ x, f x * a j x ∂domainMeasure n Ω) atTop
      (𝓝 (∫ x, f x * ψ x ∂domainMeasure n Ω)) := by
  simp_rw [mul_comm (f _)]
  apply tendsto_integral_smul_of_uniformOn_compact hK
  · simpa only [IntegrableOn, domainMeasure, Measure.restrict_restrict_of_subset hKΩ] using
      hf.integrableOn_compact_subset hKΩ hK
  · exact hψ
  · exact ha
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport fun h ↦ hx (hψK h)
  · filter_upwards [haK] with j hj x hx
    exact image_eq_zero_of_notMem_tsupport fun h ↦ hx (hj h)
  · exact hconv.tendstoUniformlyOn

/-- A weak derivative can be tested against a compact Cᵐ function when the derivative word
has length at most `m`. The test support must lie inside the open domain. -/
theorem HasWeakDerivativeOn.integral_identity_of_contDiff
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) {indices : List (Fin n)}
    {f g : ℝ^n → ℝ} (h : HasWeakDerivativeOn Ω indices f g)
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ m φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) (hindices : indices.length ≤ m) :
    (∫ x, f x * iteratedPartialDeriv indices φ x ∂domainMeasure n Ω) =
      (-1) ^ indices.length * (∫ x, g x * φ x ∂domainMeasure n Ω) := by
  obtain ⟨K, a, hK, hKΩ, hφK, haK, hconv⟩ :=
    Approximation.exists_testFunction_jet_approximation hΩ hφ hφc hφΩ
  have hleft := tendsto_integral_mul_of_uniform hK hKΩ h.locallyIntegrable_f
    (PDE.contDiff_iteratedPartialDeriv_of_le hφ indices hindices).continuous
    ((tsupport_iteratedPartialDeriv_subset_tsupport indices φ).trans hφK)
    (fun j ↦ (PDE.contDiff_top_iteratedPartialDeriv (a j).contDiff indices).continuous)
    (haK.mono fun j hj ↦
      (tsupport_iteratedPartialDeriv_subset_tsupport indices (a j).toFun).trans hj)
    (hconv indices hindices)
  have hbase : TendstoUniformly (fun j ↦ (a j).toFun) φ atTop := by
    simpa only [iteratedPartialDeriv] using hconv [] (Nat.zero_le m)
  have hright := (tendsto_integral_mul_of_uniform hK hKΩ h.locallyIntegrable_g
    hφ.continuous hφK (fun j ↦ (a j).contDiff.continuous) haK hbase).const_mul
      ((-1 : ℝ) ^ indices.length)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [haK] with j hj
  exact (h (a j) (hj.trans hKΩ)).symm

end SobolevSpace
