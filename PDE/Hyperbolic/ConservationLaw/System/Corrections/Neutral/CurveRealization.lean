/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered

import PDE.Analysis.Calculus.Coordinates.Curve.Chart
import PDE.Hyperbolic.ConservationLaw.System.Corrections.Neutral.Realization

/-!
# Compact neutral corrections along a transverse curve arc

A local transverse chart is chosen before the compact bilinear family, complete
curve, isolating open set and positive tolerance. The neutral correction
theorem then realizes the full curve jet with arbitrarily small value and first
derivative, preserving strict hyperbolicity and every genuinely nonlinear family
globally.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis

/-- Choose one open time neighborhood for compact neutral corrections of the
supplied globally strictly hyperbolic and genuinely nonlinear flux.

Neutrality is expressed in the same ordered eigenbasis of the Jacobian at each point of the time
support. The complete curve agrees with the local curve on this neighborhood, and its visits to the
isolating open set occur only there. The correction realizes the full second jet at every time and
is arbitrarily small in value and first derivative. The chart is derived from transversality. -/
theorem exists_compact_neutral_tube_realization
    {m : ℕ} (f : ℝ^m → ℝ^m) (hf : ContDiff ℝ 3 f)
    (hhyper : ∀ x, IsStrictlyHyperbolicAt f x)
    (hgn : ∀ i, IsGenuinelyNonlinearFamily f i)
    {γ : ℝ → ℝ^m} {I : Set ℝ} {t₀ : ℝ}
    (ell : ℝ^m →L[ℝ] ℝ) (hI : IsOpen I) (ht₀ : t₀ ∈ I)
    (hγ : ContDiffOn ℝ ∞ γ I) (htrans : ell (deriv γ t₀) ≠ 0) :
    ∃ J : Set ℝ, IsOpen J ∧ t₀ ∈ J ∧ J ⊆ I ∧
      ∀ B : ℝ → ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ^m,
        ContDiff ℝ ∞ B → HasCompactSupport B → tsupport B ⊆ J →
        (∀ s ∈ J, ∀ v w, B s v w = B s w v) →
        (∀ s ∈ J, ∀ v, B s (deriv γ s) v = 0) →
        (∀ t ∈ tsupport B,
          ∃ (b : Module.Basis (Fin m) ℝ (ℝ^m)) (eig : Fin m → ℝ),
            StrictMono eig ∧ (∀ i, fderiv ℝ f (γ t) (b i) = eig i • b i) ∧
              ∀ i, b.repr (B t (b i) (b i)) i = 0) →
        ∀ q : ℝ → ℝ^m, EqOn q γ J →
        ∀ U : Set (ℝ^m), IsOpen U → γ '' tsupport B ⊆ U → q ⁻¹' U ⊆ J →
        ∀ η : ℝ, 0 < η →
        ∃ P : ℝ^m → ℝ^m, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
          tsupport P ⊆ U ∧
          (∀ s : ℝ, P (q s) = 0 ∧ fderiv ℝ P (q s) = 0 ∧
            fderiv ℝ (fderiv ℝ P) (q s) = B s) ∧
          (∀ x : ℝ^m, ‖P x‖ < η ∧ ‖fderiv ℝ P x‖ < η) ∧
          (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
            ∀ i, IsGenuinelyNonlinearFamily (f + P) i := by
  obtain ⟨e, J, hJ, htJ, hJI, he, _, _, hγtarget, htmap, ht, hz, hcoord, _, _, hmod⟩ :=
    exists_smooth_transverse_curve_chart ell hI ht₀ hγ htrans
  have he_source : EqOn e (fun p ↦ γ p.1 + (p.2 : ℝ^m)) e.source := fun p _ ↦ congrFun he p
  refine ⟨J, hJ, htJ, hJI, ?_⟩
  intro B hB hBcompact hBsupport hsym hker hneutral q hq U hU hsupportU hisolate η hη
  have hγcompact : ContinuousOn γ (tsupport B) := hγ.continuousOn.mono (hBsupport.trans hJI)
  exact exists_actual_neutral_tube_correction f hf hhyper hgn ell e γ J he_source
    hγtarget htmap ht hz hcoord hmod B hB hBcompact hBsupport hsym hker
    hγcompact hneutral q hq U hU hsupportU hisolate η hη

end PDE.Hyperbolic.ConservationLaw.System
