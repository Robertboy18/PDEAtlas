/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Cubic.Construction
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.JetDerivative

import PDE.Analysis.ODE.Interpolation.CubicResidual
import PDE.Hyperbolic.ConservationLaw.System.Corrections.Neutral.CompactTolerance

/-!
# Cubic corrections preserving characteristic families

The generic compact correction can be made small enough to retain strict
hyperbolicity and genuine nonlinearity. Applying it to a localized strip residual
produces one corrected flux for every time and speed in the smaller strip.

The residual and interpolation constructors retain global amplitude zeros,
coordinate-zero jets, and the full order-two bound. Their analytic constructions
come from the general results in `PDE.Analysis`.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Preserve amplitude zeros as well as all canonical characteristic families.
The characteristic tolerance is chosen on the fixed compact support of `A`.
The global pointwise zero implication uses the product construction; the
neighborhood equality used for characteristic preservation still comes from
being outside the topological support, not from a pointwise zero. -/
theorem exists_localized_small_cubic_correction_preserving_zeros_and_families {d : ℕ}
    {f : ℝ^d → ℝ^d} {m : ℝ^d → ℝ} {A : ℝ^d → ℝ^d} (hf : ContDiff ℝ ∞ f)
    (hhyper : ∀ x, IsStrictlyHyperbolicAt f x) (hgn : ∀ i, IsGenuinelyNonlinearFamily f i)
    (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m) (hA : ContDiff ℝ ∞ A)
    (hAc : HasCompactSupport A) (εcap : ℝ) (hcap : 0 < εcap) {η : ℝ} (hη : 0 < η) :
    ∃ (ε : ℝ) (P : ℝ^d → ℝ^d),
      0 < ε ∧ ε < εcap ∧ ε ≤ 1 ∧ ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ tsupport A ∩ {x | |m x| ≤ 2 * ε} ∧
      (∀ x, |m x| ≤ ε → P x = (m x) ^ 3 • A x) ∧
      (∀ x, A x = 0 → P x = 0) ∧
      (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P x‖ < η) ∧
      (∀ x, m x = 0 → ∀ n ≤ 2, iteratedFDeriv ℝ n P x = 0) ∧
      (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
      ∀ i, IsGenuinelyNonlinearFamily (f + P) i := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf2.fderiv_right le_rfl
  have hjet := (forall_hasOrderedGenuinelyNonlinearEigenbasis_fderiv_iff hf2).mpr ⟨hhyper, hgn⟩
  obtain ⟨δ, hδ, htolerance⟩ :=
    ContinuousLinearMap.exists_pos_tolerance_of_compact_neutral_family (Fin d)
      (K := tsupport A) (A := fderiv ℝ f) (H := fderiv ℝ (fderiv ℝ f))
      (B := fun _ ↦ 0) hAc hDf.continuous.continuousOn
      (hDf.continuous_fderiv one_ne_zero).continuousOn continuousOn_const
      (fun x _ ↦ by
        obtain ⟨b, eig, horder, hdiag, hnonzero⟩ := hjet x
        exact ⟨b, eig, horder, hdiag, fun i ↦ ⟨hnonzero i, by simp⟩⟩)
  obtain ⟨ε, P, hε, hεcap, hεone, hP, hPc, hsupport, hexact, hPzero, hsmall, hzero⟩ :=
    PDE.Analysis.exists_localized_small_compact_cubic_correction_preserving_zeros
      hm hmc hA hAc εcap hcap (lt_min hη hδ)
  have hP2 : ContDiff ℝ 2 P := hP.of_le (by simp)
  have hDP : ContDiff ℝ 1 (fderiv ℝ P) := hP2.fderiv_right le_rfl
  have hfirst : fderiv ℝ (f + P) = fderiv ℝ f + fderiv ℝ P := funext fun x ↦
    fderiv_add (hf2.differentiable two_ne_zero x) (hP2.differentiable two_ne_zero x)
  have hsecond (x : ℝ^d) : fderiv ℝ (fderiv ℝ (f + P)) x =
        fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ P) x := by
    rw [hfirst]
    exact fderiv_add (hDf.differentiable one_ne_zero x) (hDP.differentiable one_ne_zero x)
  have hgood : (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
      ∀ i, IsGenuinelyNonlinearFamily (f + P) i := by
    refine (forall_hasOrderedGenuinelyNonlinearEigenbasis_fderiv_iff (hf2.add hP2)).mp fun x ↦ ?_
    change ContinuousLinearMap.HasOrderedGenuinelyNonlinearEigenbasis (Fin d)
      (fderiv ℝ (f + P) x) (fderiv ℝ (fderiv ℝ (f + P)) x)
    by_cases hx : x ∈ tsupport P
    · apply htolerance x (hsupport hx).1 0 ⟨le_rfl, zero_le_one⟩
      · rw [hfirst, Pi.add_apply, add_sub_cancel_left]
        simpa only [norm_iteratedFDeriv_one] using
          (hsmall 1 (by norm_num) x).trans_le (min_le_right η δ)
      · change ‖fderiv ℝ (fderiv ℝ (f + P)) x - (fderiv ℝ (fderiv ℝ f) x +
            (0 : ℝ) • (0 : ℝ^d →L[ℝ] ℝ^d →L[ℝ] ℝ^d))‖ < δ
        have hbound := (hsmall 2 le_rfl x).trans_le (min_le_right η δ)
        rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at hbound
        convert hbound using 2
        rw [hsecond]
        ext v w
        simp
    · -- Outside the support the fluxes agree on a neighborhood, hence so do both jets.
      have hsame : f + P =ᶠ[𝓝 x] f := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        rw [Pi.add_apply, show P y = 0 from hy, add_zero]
      rw [hsame.fderiv_eq, (hsame.fderiv (𝕜 := ℝ)).fderiv_eq]
      exact hjet x
  exact ⟨ε, P, hε, hεcap, hεone, hP, hPc, hsupport, hexact, hPzero,
    fun n hn x ↦ (hsmall n hn x).trans_le (min_le_left η δ), hzero, hgood⟩

/-- Realize the residual by one state correction, preserving all pulled-back
residual zeros regardless of the chosen scale. The amplitude and coordinate
are fixed before the cap and tolerance. The correction retains its full
order-two bound, support control, coordinate-zero jets, and all characteristic
families; the corrected ODE holds on the smaller strip as before. -/
theorem exists_state_cubic_residual_realization_preserving_zeros {d : ℕ} {f : ℝ^d → ℝ^d}
    {w R : ℝ × ℝ → ℝ^d} {coord : ℝ^d → (ℝ × ℝ) × ℝ} {K : Set ℝ} {Ω : Set (ℝ × ℝ)} {U : Set (ℝ^d)}
    {r : ℝ} (hf : ContDiff ℝ ∞ f) (hhyper : ∀ x, IsStrictlyHyperbolicAt f x)
    (hgn : ∀ i, IsGenuinelyNonlinearFamily f i) (hw : ContDiff ℝ ∞ w) (hK : IsCompact K)
    (hcoord : ContDiff ℝ ∞ coord) (hcoordc : HasCompactSupport coord) (hU : IsOpen U)
    (hΩ : IsOpen Ω) (hr : 0 < r) (hstate : MapsTo w (K ×ˢ Icc (-r) r) U)
    (hdomain : K ×ˢ Icc (-r) r ⊆ Ω) (hrecover : ∀ p ∈ K ×ˢ Icc (-r) r, coord (w p) = (p, 0))
    (hR : ContDiffOn ℝ ∞ R Ω)
    (hresidual : ∀ p ∈ Ω,
      HasDerivAt (fun t ↦ w (t, p.2)) (f (w p) - p.2 • w p + p.2 ^ 3 • R p) p.1) :
    ∃ A : ℝ^d → ℝ^d, ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
      tsupport A ⊆ U ∩ (fun x ↦ (coord x).1) ⁻¹' Ω ∧
      (∀ p ∈ K ×ˢ Icc (-r) r, A (w p) = R p) ∧
      (∀ x, R ((coord x).1) = 0 → A x = 0) ∧
      ∀ εcap : ℝ, 0 < εcap → ∀ η : ℝ, 0 < η →
        ∃ (ε : ℝ) (P : ℝ^d → ℝ^d),
          0 < ε ∧ ε < εcap ∧ ε < r ∧ ε ≤ 1 ∧
          ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
          tsupport P ⊆ tsupport A ∩ {x | |(coord x).1.2| ≤ 2 * ε} ∧
          (∀ x, A x = 0 → P x = 0) ∧
          (∀ x, R ((coord x).1) = 0 → P x = 0) ∧
          (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P x‖ < η) ∧
          (∀ x, (coord x).1.2 = 0 → ∀ n ≤ 2, iteratedFDeriv ℝ n P x = 0) ∧
          (∀ t ∈ K, ∀ μ : ℝ, |μ| ≤ ε → P (w (t, μ)) = μ ^ 3 • R (t, μ)) ∧
          (∀ t ∈ K, ∀ μ : ℝ, |μ| ≤ ε →
            HasDerivAt (fun s ↦ w (s, μ)) ((f + P) (w (t, μ)) - μ • w (t, μ)) t) ∧
          (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
          ∀ i, IsGenuinelyNonlinearFamily (f + P) i := by
  obtain ⟨A, hA, hAc, hAsupport, hAstrip, hAzero⟩ :=
    PDE.Analysis.exists_compact_amplitude_of_strip_coordinates_preserving_zeros
      hw.continuous hK hcoord hU hΩ hR hstate hdomain hrecover
  let m : ℝ^d → ℝ := fun x ↦ (coord x).1.2
  have hm : ContDiff ℝ ∞ m := hcoord.fst.snd
  have hmc : HasCompactSupport m := hcoordc.comp_left (g := fun p : (ℝ × ℝ) × ℝ ↦ p.1.2) rfl
  refine ⟨A, hA, hAc, hAsupport, hAstrip, hAzero, fun εcap hcap η hη ↦ ?_⟩
  obtain ⟨ε, P, hε, hεbound, hεone, hP, hPc, hsupport, hexact, hPzero, hsmall,
      hzero, hhyperP, hgnP⟩ := exists_localized_small_cubic_correction_preserving_zeros_and_families
      hf hhyper hgn hm hmc hA hAc (min εcap r) (lt_min hcap hr) hη
  have hεr : ε < r := hεbound.trans_le (min_le_right εcap r)
  have hrealize (t : ℝ) (ht : t ∈ K) (μ : ℝ) (hμ : |μ| ≤ ε) :
      P (w (t, μ)) = μ ^ 3 • R (t, μ) := by
    have hp : (t, μ) ∈ K ×ˢ Icc (-r) r := ⟨ht, abs_le.mp (hμ.trans hεr.le)⟩
    have hmstrip : m (w (t, μ)) = μ := congrArg (fun q ↦ q.1.2) (hrecover (t, μ) hp)
    rw [hexact (w (t, μ)) (by rwa [hmstrip]), hmstrip, hAstrip (t, μ) hp]
  refine ⟨ε, P, hε, hεbound.trans_le (min_le_left εcap r), hεr, hεone, hP, hPc, hsupport,
    hPzero, (fun x hx ↦ hPzero x (hAzero x hx)), hsmall, hzero, hrealize,
    fun t ht μ hμ ↦ ?_, hhyperP, hgnP⟩
  refine (hresidual (t, μ) (hdomain ⟨ht, abs_le.mp (hμ.trans hεr.le)⟩)).congr_deriv ?_
  change f (w (t, μ)) - μ • w (t, μ) + μ ^ 3 • R (t, μ) = (f + P) (w (t, μ)) - μ • w (t, μ)
  rw [Pi.add_apply, hrealize t ht μ hμ]
  abel

/-- Realize an interpolation residual while retaining its pointwise zeros in
state space. In particular, its constant-cutoff collar identity can be combined with the global
residual-zero implication. -/
theorem exists_state_cubic_interpolation_realization_preserving_zeros {d : ℕ} {f : ℝ^d → ℝ^d}
    {u v a w : ℝ × ℝ → ℝ^d} {θ : ℝ → ℝ} {coord : ℝ^d → (ℝ × ℝ) × ℝ} {K : Set ℝ} {Ω : Set (ℝ × ℝ)}
    {U : Set (ℝ^d)} {r : ℝ} (hf : ContDiff ℝ ∞ f) (hhyper : ∀ x, IsStrictlyHyperbolicAt f x)
    (hgn : ∀ i, IsGenuinelyNonlinearFamily f i) (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hθ : ContDiff ℝ ∞ θ) (hfactor : ∀ p ∈ Ω, v p - u p = p.2 ^ 3 • a p)
    (hodeU : ∀ p ∈ Ω, HasDerivAt (fun t ↦ u (t, p.2)) (f (u p) - p.2 • u p) p.1)
    (hodeV : ∀ p ∈ Ω, HasDerivAt (fun t ↦ v (t, p.2)) (f (v p) - p.2 • v p) p.1)
    (hw : ContDiff ℝ ∞ w) (hw_eq : w = fun p ↦ u p + θ p.1 • (v p - u p)) (hK : IsCompact K)
    (hcoord : ContDiff ℝ ∞ coord) (hcoordc : HasCompactSupport coord) (hU : IsOpen U)
    (hΩ : IsOpen Ω) (hr : 0 < r) (hstate : MapsTo w (K ×ˢ Icc (-r) r) U)
    (hdomain : K ×ˢ Icc (-r) r ⊆ Ω) (hrecover : ∀ p ∈ K ×ˢ Icc (-r) r, coord (w p) = (p, 0)) :
    ∃ R : ℝ × ℝ → ℝ^d, ContDiffOn ℝ ∞ R Ω ∧
      (∀ p ∈ Ω, HasDerivAt (fun t ↦ w (t, p.2))
        (f (w p) - p.2 • w p + p.2 ^ 3 • R p) p.1) ∧
      (∀ p ∈ Ω, (θ p.1 = 0 ∨ θ p.1 = 1) → deriv θ p.1 = 0 → R p = 0) ∧
      ∃ A : ℝ^d → ℝ^d, ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
        tsupport A ⊆ U ∩ (fun x ↦ (coord x).1) ⁻¹' Ω ∧
        (∀ p ∈ K ×ˢ Icc (-r) r, A (w p) = R p) ∧
        (∀ x, R ((coord x).1) = 0 → A x = 0) ∧
        ∀ εcap : ℝ, 0 < εcap → ∀ η : ℝ, 0 < η →
          ∃ (ε : ℝ) (P : ℝ^d → ℝ^d),
            0 < ε ∧ ε < εcap ∧ ε < r ∧ ε ≤ 1 ∧
            ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
            tsupport P ⊆ tsupport A ∩ {x | |(coord x).1.2| ≤ 2 * ε} ∧
            (∀ x, A x = 0 → P x = 0) ∧
            (∀ x, R ((coord x).1) = 0 → P x = 0) ∧
            (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P x‖ < η) ∧
            (∀ x, (coord x).1.2 = 0 → ∀ n ≤ 2, iteratedFDeriv ℝ n P x = 0) ∧
            (∀ t ∈ K, ∀ μ : ℝ, |μ| ≤ ε → P (w (t, μ)) = μ ^ 3 • R (t, μ)) ∧
            (∀ t ∈ K, ∀ μ : ℝ, |μ| ≤ ε →
              HasDerivAt (fun s ↦ w (s, μ)) ((f + P) (w (t, μ)) - μ • w (t, μ)) t) ∧
            (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
            ∀ i, IsGenuinelyNonlinearFamily (f + P) i := by
  obtain ⟨R, hR, hresidual, hcollar⟩ :=
    PDE.Analysis.ODE.exists_contDiffOn_cubic_interpolation_residual
      hf hu hv ha hθ hfactor hodeU hodeV
  have hresidualW : ∀ p ∈ Ω, HasDerivAt (fun t ↦ w (t, p.2))
      (f (w p) - p.2 • w p + p.2 ^ 3 • R p) p.1 := by
    simpa only [hw_eq] using hresidual
  exact ⟨R, hR, hresidualW, hcollar, exists_state_cubic_residual_realization_preserving_zeros
      hf hhyper hgn hw hK hcoord hcoordc hU hΩ hr hstate hdomain hrecover hR hresidualW⟩

end PDE.Hyperbolic.ConservationLaw.System
