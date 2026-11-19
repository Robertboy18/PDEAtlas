/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.DomainLipschitz
public import PDE.Spaces.Sobolev.GraphSpace.Local.Definitions
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Locality
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Lipschitz composition of local Sobolev functions

A scalar Lipschitz map preserves `W^{1,p}_loc` for every `1 ≤ p ≤ ∞`.
On a relatively compact subdomain, its constant offset is integrable and
the open-domain chain rule applies. Uniqueness identifies the local derivative
coordinates with any supplied weak derivative; locality then gives the chain
rule on the original domain.

Neither the function nor its weak derivatives need to be globally integrable.
The domain may be unbounded and its boundary need not be regular.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal NNReal

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Set (ℝ^n)} {u g : ℝ^n → ℝ} {F : ℝ → ℝ} {C : ℝ≥0}

/-- Scalar Lipschitz composition preserves local first-order Sobolev
membership, including both exponent endpoints. The map need not fix zero. -/
theorem IsLocallyWkpOn.comp_lipschitz
    (hu : IsLocallyWkpOn 1 p Ω u) (hF : LipschitzWith C F) :
    IsLocallyWkpOn 1 p Ω (F ∘ u) := by
  intro V hV hcompact hVΩ
  obtain ⟨U, hU⟩ := hu V hV hcompact hVΩ
  have : IsFiniteMeasure (domainMeasure n V) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono subset_closure).trans_lt hcompact.measure_lt_top).ne
  refine ⟨lipschitzCompositionOn hV hF U, ?_⟩
  exact (lipschitzCompositionOn_base_ae hV hF U).trans (hU.fun_comp F)

/-- The weak chain rule for a local Sobolev function. Any weak
derivative of the input determines the derivative of the composition,
without a global `Lᵖ` hypothesis on either function. -/
theorem IsLocallyWkpOn.hasWeakDerivativeOn_comp_lipschitz
    (hu : IsLocallyWkpOn 1 p Ω u) (hΩ : IsOpen Ω) (hF : LipschitzWith C F)
    (i : Fin n) (hweak : HasWeakDerivativeOn Ω [i] u g) :
    HasWeakDerivativeOn Ω [i] (F ∘ u) (fun x ↦ deriv F (u x) * g x) := by
  have hlocal (V : Set (ℝ^n)) (hV : IsOpen V)
      (hcompact : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
      HasWeakDerivativeOn V [i] (F ∘ u) (fun x ↦ deriv F (u x) * g x) := by
    obtain ⟨U, hU⟩ := hu V hV hcompact hVΩ
    change baseRepresentative U =ᵐ[domainMeasure n V] u at hU
    have hd : HasWeakDerivativeOn V [i] (baseRepresentative U)
        (U.val (singleDerivIndex n i)) := by
      simpa only [baseRepresentative, singleDerivIndex_toList] using
        U.property (singleDerivIndex n i)
    have hrow := (hd.congr_ae hU Filter.EventuallyEq.rfl).unique_ae hV
      (hweak.mono hV.measurableSet (subset_closure.trans hVΩ))
    apply (hasWeakDerivativeOn_comp_lipschitz_on hV hF U i).congr_ae (hU.fun_comp F)
    filter_upwards [hU, hrow] with x hx hdx
    simp only [hx, hdx]
  have hneighborhood (x : Ω) := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := x.val)) hΩ (singleton_subset_iff.mpr x.property)
  choose V hV hxV hVΩ hcompact using hneighborhood
  refine hasWeakDerivativeOn_single_of_open_cover V hV ?_ i ?_
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩ (mem_singleton x)⟩
  · intro x
    exact hlocal (V x) (hV x) (hcompact x) (hVΩ x)

end SobolevSpace.GraphSpace
