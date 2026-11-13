/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Divergence.TestPairing

/-!
# Local representatives in weak divergence tests

A test supported in a smaller region only sees the flux and load on its
support. This lets an equation in a coordinate chart act on a global Sobolev
test without imposing an equation on the extensions outside the chart.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω V : Set (ℝ^n)}

/-- Local integral representatives suffice for the weak equation on a
test supported in the local region. -/
theorem weakDivergence_test_pairing_of_restricted_integral
    (hΩ : MeasurableSet Ω) (hVΩ : V ⊆ Ω)
    (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (φ : TestFunctionOn n Ω) (hφV : tsupport φ.1.toFun ⊆ V)
    (Q : ℝ^n → Fin n → ℝ) (F : ℝ^n → ℝ)
    (hq : ∀ᵐ x ∂volume.restrict V, x ∈ tsupport φ.1.toFun →
      ∀ i : Fin n, q i x = Q x i)
    (hf : ∀ᵐ x ∂volume.restrict V, x ∈ tsupport φ.1.toFun → f x = F x)
    (hlocal : (∫ x in V, ∑ i : Fin n, Q x i * (∂[i] φ.1.toFun) x) =
      ∫ x in V, F x * φ.1.toFun x) :
    (∑ i, ⟪q i, derivCoordCLM i (testFunctionToH10 φ)⟫) =
      ⟪f, baseCoordCLM (testFunctionToH10 φ)⟫ := by
  have hd (x : ℝ^n) (hx : x ∉ tsupport φ.1.toFun) (i : Fin n) :
      (∂[i] φ.1.toFun) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun h ↦ hx (tsupport_iteratedPartialDeriv_subset_tsupport [i] φ.1.toFun h)
  apply weakDivergence_test_pairing_of_integral
  change (∫ x in Ω, ∑ i : Fin n, q i x * (∂[i] φ.1.toFun) x) =
    ∫ x in Ω, f x * φ.1.toFun x
  have hleft :
      (∫ x in Ω, ∑ i : Fin n, q i x * (∂[i] φ.1.toFun) x) =
        ∫ x in V, ∑ i : Fin n, Q x i * (∂[i] φ.1.toFun) x := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ hVΩ
      (fun x hx ↦ by
        have hxφ : x ∉ tsupport φ.1.toFun := fun h ↦ hx.2 (hφV h)
        simp only [hd x hxφ, mul_zero, Finset.sum_const_zero])]
    apply integral_congr_ae
    filter_upwards [hq] with x hx
    by_cases hxφ : x ∈ tsupport φ.1.toFun
    · simp only [hx hxφ]
    · simp only [hd x hxφ, mul_zero, Finset.sum_const_zero]
  have hright : (∫ x in Ω, f x * φ.1.toFun x) =
      ∫ x in V, F x * φ.1.toFun x := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ hVΩ
      (fun x hx ↦ by
        have hz := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx.2 (hφV h))
        rw [hz, mul_zero])]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    by_cases hxφ : x ∈ tsupport φ.1.toFun
    · rw [hx hxφ]
    · rw [image_eq_zero_of_notMem_tsupport hxφ, mul_zero, mul_zero]
  exact hleft.trans (hlocal.trans hright.symm)

end SobolevSpace.GraphSpace
