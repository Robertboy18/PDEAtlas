/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.HigherOrder.FluxDifferentiation
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.Spaces.Sobolev.Calculus.Divergence.Functional

/-!
# Local flux identities for the nonlinear bootstrap

Compactly supported tests express the divergence equation without imposing
global integrability on higher derivatives. On each interior subdomain where
the flux belongs to L², density recovers the usual H¹₀ pairing. Differentiating
the flux differentiates the test and uses commutation of its smooth partials.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev InnerProductSpace

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} {Ω V : Set ℝ^n}

/-- The flux pairs to zero with gradients of smooth tests supported in the domain.
For locally integrable fluxes, this expresses zero distributional divergence. The
regularity is supplied separately below, through continuity or an `L²` realization.
The integrals use the ambient measure. -/
def HasZeroWeakDivergenceOn (Ω : Set ℝ^n) (Q : Fin n → ℝ^n → ℝ) : Prop :=
  ∀ φ : TestFunctionOn n Ω,
    (∑ i, ∫ x, Q i x * (∂[i] φ.1.toFun) x) = 0

private theorem integral_flux_test_eq_restrict
    (Q : ℝ^n → ℝ) (φ : TestFunctionOn n Ω) (i : Fin n) :
    (∫ x, Q x * (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) =
      ∫ x, Q x * (∂[i] φ.1.toFun) x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hs := (tsupport_fderiv_apply_subset ℝ (f := φ.1.toFun)
    (EuclideanSpace.single i (1 : ℝ))).trans φ.2
  have hz : (∂[i] φ.1.toFun) x = 0 := by
    by_contra hne
    exact hx (hs (subset_tsupport _ hne))
  rw [hz, mul_zero]

/-- A local flux identity restricts to every smaller domain. -/
theorem HasZeroWeakDivergenceOn.mono {Q : Fin n → ℝ^n → ℝ}
    (hQ : HasZeroWeakDivergenceOn Ω Q) (hVΩ : V ⊆ Ω) :
    HasZeroWeakDivergenceOn V Q :=
  fun φ ↦ hQ ⟨φ.1, φ.2.trans hVΩ⟩

/-- Equality of fluxes on the domain preserves their weak divergence. -/
theorem HasZeroWeakDivergenceOn.congr {Q R : Fin n → ℝ^n → ℝ}
    (hΩ : IsOpen Ω)
    (hQ : HasZeroWeakDivergenceOn Ω Q)
    (hQR : ∀ i, EqOn (Q i) (R i) Ω) :
    HasZeroWeakDivergenceOn Ω R := by
  intro φ
  rw [← hQ φ]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_flux_test_eq_restrict, ← integral_flux_test_eq_restrict]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  exact congrArg (fun t : ℝ ↦ t * (∂[i] φ.1.toFun) x) ((hQR i hx).symm)

/-- An L² realization of a local flux identity satisfies the full H¹₀ equation. -/
theorem HasZeroWeakDivergenceOn.pairing {Q : Fin n → ℝ^n → ℝ}
    (hQ : HasZeroWeakDivergenceOn Ω Q)
    (q : Fin n → DerivLp n 2 Ω)
    (hq : ∀ i, (q i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] Q i)
    (v : H¹₀(Ω)) :
    (∑ i, ⟪q i, derivCoordCLM i v⟫_ℝ) = 0 := by
  have ht (φ : TestFunctionOn n Ω) :
      (∑ i, ⟪q i, derivCoordCLM i (testFunctionToH10 φ)⟫_ℝ) = 0 := by
    rw [← hQ φ]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_deriv_testFunction_data_eq_integral, ← integral_flux_test_eq_restrict]
    apply integral_congr_ae
    filter_upwards [hq i] with x hx
    rw [hx]
  simpa only [inner_zero_left] using weakDivergence_pairing_of_testFunctions q 0
    (fun φ ↦ by simpa only [inner_zero_left] using ht φ) v

/-- Conversely, an L² weak flux equation gives the local test identity. -/
theorem hasZeroWeakDivergenceOn_of_pairing
    (q : Fin n → DerivLp n 2 Ω) {Q : Fin n → ℝ^n → ℝ}
    (hq : ∀ i, (q i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] Q i)
    (hweak : ∀ v : H¹₀(Ω), (∑ i, ⟪q i, derivCoordCLM i v⟫_ℝ) = 0) :
    HasZeroWeakDivergenceOn Ω Q := by
  intro φ
  rw [← hweak (testFunctionToH10 φ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_deriv_testFunction_data_eq_integral, ← integral_flux_test_eq_restrict]
  apply integral_congr_ae
  filter_upwards [hq i] with x hx
  rw [hx]

/-- Differentiating a C¹ divergence-free flux preserves its distributional equation.
No second derivative of the flux is required. -/
theorem HasZeroWeakDivergenceOn.partialDeriv
    (hΩ : IsOpen Ω) {Q : Fin n → ℝ^n → ℝ}
    (hQ : HasZeroWeakDivergenceOn Ω Q)
    (hreg : ∀ i, ContDiffOn ℝ 1 (Q i) Ω) (k : Fin n) :
    HasZeroWeakDivergenceOn Ω (fun i ↦ ∂[k] (Q i)) := by
  intro φ
  let ψ := φ.iteratedPartialDeriv [k]
  have ht := hQ ψ
  have hp (i : Fin n) :
      (∫ x, Q i x * (∂[i] ψ.1.toFun) x) =
        -(∫ x, (∂[k] (Q i)) x * (∂[i] φ.1.toFun) x) := by
    rw [← integral_flux_test_eq_restrict, ← integral_flux_test_eq_restrict]
    have hw := hasWeakDerivativeOn_of_contDiffAt_one hΩ
      (fun x hx ↦ (hreg i).contDiffAt (hΩ.mem_nhds hx)) k
    have hc : ∂[i] ψ.1.toFun = ∂[k] (φ.iteratedPartialDeriv [i]).1.toFun := by
      have h := iteratedPartialDeriv_congr_perm_smooth φ.1.contDiff
        (List.Perm.swap i k [])
      change ∂[i] (φ.iteratedPartialDeriv [k]).1.toFun = _
      rw [TestFunctionOn.iteratedPartialDeriv_toFun,
        TestFunctionOn.iteratedPartialDeriv_toFun]
      simpa only [iteratedPartialDeriv, TestFunction.toFun_eq_coe] using h.symm
    rw [hc]
    simpa only [TestFunctionOn.iteratedPartialDeriv_toFun, iteratedPartialDeriv,
      List.length_cons, List.length_nil, Nat.zero_add, pow_one, neg_one_mul] using
      hw (φ.iteratedPartialDeriv [i]).1 (φ.iteratedPartialDeriv [i]).2
  simp_rw [hp] at ht
  simpa only [Finset.sum_neg_distrib, neg_eq_zero] using ht

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
