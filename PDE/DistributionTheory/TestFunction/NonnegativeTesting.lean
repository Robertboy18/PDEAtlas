/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.CompactSupportLimit
public import PDE.DistributionTheory.TestFunction.NonnegativeApproximation

/-!
# Extending distributional inequalities to C¹ tests

For locally integrable coefficients, an inequality against nonnegative smooth tests
also holds against nonnegative compact C¹ tests. Positive mollification supplies the
approximants and one common interior compact support.
-/

@[expose] public section

open PDE (partialDeriv)

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace TestFunction

variable {n : ℕ} {U : Opens (ℝ^n)}

/-- Smooth nonnegative testing suffices for a first-order distributional inequality
with two locally integrable coefficients. -/
theorem nonneg_integral_mul_partialDeriv_of_smooth
    {f g : ℝ^n → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hg : LocallyIntegrableOn g U volume) (i j : Fin n)
    (h : ∀ a : 𝓓(U, ℝ), (∀ x, 0 ≤ a x) →
      0 ≤ ∫ x, f x * (∂[i] ⇑a) x + g x * (∂[j] ⇑a) x)
    (φ : 𝓓^{1}(U, ℝ)) (hφ : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, f x * (∂[i] ⇑φ) x + g x * (∂[j] ⇑φ) x := by
  obtain ⟨K, a, hK, hKU, hφK, haK, hconv⟩ :=
    exists_nonneg_smooth_jet_approximation φ hφ
  let b : ℕ → 𝓓^{1}(U, ℝ) := fun k ↦
    .mk (a k) ((a k).contDiff.of_le (by simp))
      (a k).hasCompactSupport (a k).tsupport_subset
  have hlim (v : ℝ^n → ℝ) (hv : LocallyIntegrableOn v U volume) (r : Fin n) :
      Tendsto (fun k ↦ ∫ x, v x * (∂[r] ⇑(a k)) x) atTop
        (𝓝 (∫ x, v x * (∂[r] ⇑φ) x)) := by
    simp_rw [mul_comm _ (partialDeriv _ _ _)]
    apply tendsto_integral_smul_of_uniformOn_compact hK
      (hv.integrableOn_compact_subset hKU hK) (φ.continuous_partialDeriv r)
      (fun k ↦ (b k).continuous_partialDeriv r)
    · exact fun x hx ↦ φ.partialDeriv_eq_zero_of_notMem_tsupport
        (fun hxφ ↦ hx (hφK hxφ)) r
    · exact Eventually.of_forall fun k x hx ↦ (b k).partialDeriv_eq_zero_of_notMem_tsupport
        (fun hxa ↦ hx ((haK k).1 hxa)) r
    · convert (hconv [r] (by simp)).tendstoUniformlyOn (s := K) using 1
      · rfl
      · rfl
  have hsum := (hlim f hf i).add (hlim g hg j)
  have heq (k : ℕ) :
      (∫ x, f x * (∂[i] ⇑(a k)) x + g x * (∂[j] ⇑(a k)) x) =
        (∫ x, f x * (∂[i] ⇑(a k)) x) +
          ∫ x, g x * (∂[j] ⇑(a k)) x :=
    integral_add ((b k).integrable_mul_partialDeriv hf i)
      ((b k).integrable_mul_partialDeriv hg j)
  rw [← integral_add (φ.integrable_mul_partialDeriv hf i)
    (φ.integrable_mul_partialDeriv hg j)] at hsum
  exact ge_of_tendsto hsum (Eventually.of_forall fun k ↦ by
    rw [← heq]
    exact h (a k) (haK k).2)

end TestFunction
