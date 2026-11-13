/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension

/-!
# First derivative coordinates of compact cutoff extension

The finite Leibniz expansion for cutoff extension reduces in first order to
the usual product rule. On a neighborhood where the cutoff equals one, the
extension therefore preserves the original derivative representative.
-/

@[expose] public noncomputable section

open PDE (partialDeriv iteratedPartialDeriv)

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff

open MeasureTheory Set GraphSpace
open scoped ENNReal Topology

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {V Ω : Set (ℝ^n)}

/-- The first derivative of compact cutoff extension satisfies the
two-term product rule almost everywhere on the larger domain. -/
theorem extendByCutoff_derivative_ae (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ V)
    (U : W^{1,p}(V)) (i : Fin n) :
    ⇑((extendByCutoff hV hVΩ κ hκ U).val (singleDerivIndex n i))
      =ᵐ[domainMeasure n Ω] fun x ↦
        (∂[i] κ.toFun) x * baseRepresentative U x +
          κ.toFun x * U.val (singleDerivIndex n i) x := by
  have h := extendByCutoff_coordinate_ae hV hVΩ κ hκ U (singleDerivIndex n i)
  rw [singleDerivIndex_toList, List.reverse_singleton] at h
  filter_upwards [h] with x hx
  rw [hx]
  simp [weakLeibnizExpansion, derivativeSplits, iteratedPartialDeriv,
    wkpWordRepresentative, derivIndexOfList_singleton, firstDerivIndex_one,
    baseRepresentative, add_comm]

/-- Extension preserves derivatives at almost every point of a set on which
the cutoff is locally constant one. No openness of that set is needed. -/
theorem extendByCutoff_derivative_ae_on_core (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ V)
    (U : W^{1,p}(V)) (i : Fin n) {K : Set (ℝ^n)}
    (hcore : ∀ x ∈ K, κ.toFun =ᶠ[𝓝 x] 1) :
    ∀ᵐ x ∂domainMeasure n Ω, x ∈ K →
      (extendByCutoff hV hVΩ κ hκ U).val (singleDerivIndex n i) x =
        U.val (singleDerivIndex n i) x := by
  filter_upwards [extendByCutoff_derivative_ae hV hVΩ κ hκ U i] with x hx hxK
  have hvalue : κ.toFun x = 1 := (hcore x hxK).eq_of_nhds
  have hderiv : (∂[i] κ.toFun) x = 0 := by
    unfold partialDeriv
    rw [(hcore x hxK).fderiv_eq]
    simp
  simp only [hx, hderiv, hvalue, zero_mul, one_mul, zero_add]

end SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff
