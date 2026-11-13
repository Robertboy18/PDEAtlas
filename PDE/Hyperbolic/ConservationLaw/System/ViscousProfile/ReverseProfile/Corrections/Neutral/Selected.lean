/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/


module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Corrections.Neutral.Integrated
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.FirstOrder

import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Corrections.Neutral.Inputs

/-!
# Global neutral corrections for the retained selected clock

The shared selected-input theorem derives the smooth ordered frame, physical
speed variation and global baseline hyperbolicity and genuine nonlinearity.
The neutral integrated-correction theorem then constructs the global correction
with arbitrarily small value and first derivative, preserving all canonical
genuinely nonlinear families and strict hyperbolicity.

The supplied flow, terminal event, coefficient slice, time, index pair,
fundamental solution and projection remain fixed. One common frame, completed
orbit, isolating neighborhood and time bump precede every signed target and
positive tolerance. The original closed branch retains its exact signed integral.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The retained selected clock admits globally smooth compact corrections
with arbitrary signed integrated Hessian response and arbitrarily small value
and first derivative. The corrected flux is globally strictly hyperbolic and
all its canonical characteristic families are genuinely nonlinear.

The supplied normalized vectors extend to one ordered frame with smooth
dual coordinates. All geometric witnesses are fixed before target and tolerance;
the complete orbit and original closed branch have the same exact response. -/
theorem exists_selected_clock_neutral_integrated_correction {δ A B H tAnchor tStar : ℝ}
    {c : Fin 3 → ℝ} {b : (Fin 3 → ℝ) × ℝ → ℝ} {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ} {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))} (hδ : 0 < δ)
    (hδsmall : δ < 1 / 4) (hAB : A ^ 2 < B ^ 2) (hb : ContDiff ℝ ∞ b)
    (hbsupport : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10)) (hΨ : ContDiff ℝ ∞ Ψ)
    (hselected : ((δ, c), (0, 0)) ∈ N) (hinitial : ∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3))
    (hode : ∀ θ ∈ N, ∀ s ∈ Icc (0 : ℝ) H, HasDerivAt (fun u ↦ Ψ (u, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y)) (Ψ (s, θ)) - θ.2.1 •
      Ψ (s, θ)) s)
    (hevent : ∀ θ ∈ N, T θ ∈ Ioo (0 : ℝ) H ∧ Ψ (T θ, θ) 1 = 0) (i j : Fin 3) (hij : i ≠ j) :
    let θ0 := ((δ, c), ((0 : ℝ), (0 : ℝ)))
    let e := T θ0
    let b0 : ℝ → ℝ := fun y ↦ b (c, y)
    let f := concreteGatedFlux δ (clockFeedback A B) b0
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, θ0)
    let W := prescribedClockFullVariation Ψ (δ, c) (1, 0)
    let rStar := GatedFlux.rightEigenvector (fastLogCosh δ) MiddleClock.g cutoff
      (clockFeedback A B) b0 (γ tStar)
    tStar ∈ Ioo (0 : ℝ) e →
    205 < γ tStar 1 → 2 < γ tStar 2 → (γ tStar 2) ^ 2 < A ^ 2 →
    0 < γ e 2 → γ e 0 / γ e 2 = 1 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar i), ⇑(W tStar)] ≠ 0 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar j), ⇑(W tStar)] ≠ 0 →
    (∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ deriv γ tStar = ∑ k, a k • rStar k) →
    ∀ (S : Evolution.FundamentalSolution
      (fun t ↦ fderiv ℝ f (γ t)) tAnchor (Icc (0 : ℝ) e))
      (L : (ℝ^3) →L[ℝ] (ℝ^2)),
      LinearMap.ker L.toLinearMap = Submodule.span ℝ ({f (γ e)} : Set (ℝ^3)) →
      ∃ (V : Set ℝ) (r : ℝ → Module.Basis (Fin 3) ℝ (ℝ^3))
        (J : Set ℝ) (q : ℝ → ℝ^3) (U : Set (ℝ^3)) (l u : ℝ) (χ : ℝ → ℝ),
        IsOpen V ∧ tStar ∈ V ∧ (∀ k, r tStar k = rStar k) ∧
        (∀ k, ContDiffOn ℝ ∞ (fun t ↦ r t k) V ∧
          ContDiffOn ℝ ∞ (fun t ↦ characteristicSpeed f k (γ t)) V) ∧
        ContDiffOn ℝ ∞
          (fun p : ℝ × (ℝ^3) ↦ ((r p.1).repr p.2 : Fin 3 → ℝ)) (V ×ˢ univ) ∧
        (∀ t ∈ V, StrictMono (fun k ↦ characteristicSpeed f k (γ t)) ∧
          ∀ k, fderiv ℝ f (γ t) (r t k) = characteristicSpeed f k (γ t) • r t k ∧
            (r tStar).equivFun (r t k) k = 1) ∧
        (∀ k, (r tStar).repr (f (γ tStar)) k ≠ 0) ∧
        IsOpen J ∧ tStar ∈ J ∧ J ⊆ V ∩ Ioo (0 : ℝ) e ∧
        IsViscousProfile f 0 0 0 q ∧ ContDiff ℝ ∞ q ∧
        (∀ t, HasDerivAt q (f (q t)) t) ∧
        EqOn q γ (Icc (0 : ℝ) H) ∧
        EqOn q (fun t ↦ GatedFlux.reversal (γ (e + e - t))) (Icc e (e + e)) ∧
        Function.Injective q ∧ (∀ t, q t ≠ 0) ∧
        IsOpen U ∧ 0 < l ∧ l < tStar ∧ tStar < u ∧ u < e ∧
        Icc l u ⊆ J ∧ MapsTo γ (Icc l u) U ∧ q ⁻¹' U ⊆ J ∧
        (∀ t ∈ Icc (0 : ℝ) e, GatedFlux.reversal (γ t) ∉ U) ∧
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo l u ∧
        (∀ t, 0 ≤ χ t) ∧ (∫ t, χ t) = 1 ∧
        ∀ target : ℝ^2, ∀ η : ℝ, 0 < η → ∃ P : (ℝ^3) → ℝ^3,
          ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ tsupport P ⊆ U ∧
          (∀ t, P (q t) = 0 ∧ fderiv ℝ P (q t) = 0 ∧
            (∀ v, fderiv ℝ (fderiv ℝ P) (q t) (deriv q t) v = 0) ∧
            ∀ k, (r t).repr
              (fderiv ℝ (fderiv ℝ P) (q t) (r t k) (r t k)) k = 0) ∧
          (∀ t, L (S.propagator e t
            (fderiv ℝ (fderiv ℝ P) (q t) (W t) (W t))) = χ t • target) ∧
          Integrable (fun t ↦ L (S.propagator e t
            (fderiv ℝ (fderiv ℝ P) (q t) (W t) (W t)))) ∧
          (∫ t in (0 : ℝ)..e, L (S.propagator e t
            (fderiv ℝ (fderiv ℝ P) (q t) (W t) (W t)))) = target ∧
          (∫ t in (0 : ℝ)..e, L (S.propagator e t
            (fderiv ℝ (fderiv ℝ P) (γ t) (W t) (W t)))) = target ∧
          (∀ x, ‖P x‖ < η ∧ ‖fderiv ℝ P x‖ < η) ∧
          (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
          ∀ k, IsGenuinelyNonlinearFamily (f + P) k := by
  intro θ0 e b0 f γ W rStar htStar hy hzInner hzOuter hz hρ hi hj hexp S L hL
  obtain ⟨hb0, hsupportClosed, _, hhyper, hgn, _, hW,
      hγODE, hγzero, he, hmiddle, hA, V, r, hV, htV, hrStar,
      hsmooth, hdual, hspectral', hcoordinates, hi', hj'⟩ :=
    exists_selected_clock_neutral_correction_inputs
      hδ hδsmall hAB hb hbsupport hΨ hselected hinitial hode hevent
      i j htStar hy hzInner hzOuter hi hj hexp
  obtain ⟨J, q, U, l, u, χ, hcorrection⟩ := exists_prescribed_clock_neutral_integrated_correction
      hδ.le hA hAB hsupportClosed hb0 hhyper hgn he.2 htStar
      hγODE hγzero hmiddle hz hρ S L hL r W hV htV
      (fun t ht ↦ ⟨fun k ↦ characteristicSpeed f k (γ t),
        (hspectral' t ht).1, fun k ↦ ((hspectral' t ht).2 k).1⟩)
      i j hij (hsmooth i).1 (hsmooth j).1 hW.contDiffOn hi' hj' (fun k _ _ ↦ hcoordinates k)
  exact ⟨V, r, J, q, U, l, u, χ, hV, htV, hrStar, hsmooth, hdual, hspectral',
    hcoordinates, hcorrection⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
