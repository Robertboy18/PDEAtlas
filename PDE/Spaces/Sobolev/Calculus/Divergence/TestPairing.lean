/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Divergence.Functional
public import PDE.Spaces.Sobolev.Localization.Cutoff.Coordinates

/-!
# Classical test integrals and weak flux pairings

A square-integrable vector flux acts continuously on the derivative
coordinates of `H¹₀`. On smooth tests this action is the ordinary integral
against the classical gradient. No derivative of the flux is needed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The classical finite coordinate integral equals the flux pairing. -/
theorem integral_flux_test_eq_sum_inner (q : Fin n → DerivLp n 2 Ω)
    (φ : TestFunctionOn n Ω) :
    (∫ x, ∑ i : Fin n, q i x * (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) =
      ∑ i : Fin n, ⟪q i, derivCoordCLM i (testFunctionToH10 φ)⟫ := by
  have hterm (i : Fin n) : Integrable
      (fun x ↦ q i x * (∂[i] φ.1.toFun) x) (domainMeasure n Ω) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (q i)
      (derivCoordCLM i (testFunctionToH10 φ))).congr
    filter_upwards [derivCoordCLM_testFunction_apply_ae i φ] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hterm i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [derivCoordCLM_testFunction_apply_ae i φ] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Equality of the classical test integrals gives equality of the
coordinate pairings, with the sign convention `-div q = f`. -/
theorem weakDivergence_test_pairing_of_integral
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (φ : TestFunctionOn n Ω)
    (h : (∫ x, ∑ i : Fin n, q i x * (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) =
      ∫ x, f x * φ.1.toFun x ∂domainMeasure n Ω) :
    (∑ i, ⟪q i, derivCoordCLM i (testFunctionToH10 φ)⟫) =
      ⟪f, baseCoordCLM (testFunctionToH10 φ)⟫ := by
  rw [← integral_flux_test_eq_sum_inner, inner_base_testFunction_eq_integral]
  exact h

end SobolevSpace.GraphSpace
