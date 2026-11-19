/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Reflection

import PDE.Analysis.Evolution.ODE.Regularity
import PDE.Hyperbolic.ConservationLaw.System.Corrections.Neutral.CurveRealization
import PDE.Hyperbolic.ConservationLaw.System.Corrections.Neutral.IntegratedFamily
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Reference.ArcIsolation

/-!
# Neutral compact corrections along a selected clock connection

The fixed concrete flux is globally strictly hyperbolic and genuinely nonlinear.
The supplied frame is an ordered eigenbasis of its Jacobian near the
selected time. A supplied zero-speed branch with terminal ratio one determines
its complete connection and an isolated arc. The chart neighborhood, completed
orbit, spatial neighborhood, inner time interval and normalized bump are chosen
before every signed projected target and positive tolerance.

The integrated bilinear family is neutral in this same eigenbasis. The compact
neutral realization theorem produces a global smooth correction, arbitrarily small
in value and first derivative, while preserving global strict hyperbolicity and
all canonical genuinely nonlinear families. The all-time curve jets and the
signed integral on the original closed branch remain exact.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped ContDiff Topology Matrix

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

/-- One selected zero-speed clock match admits globally neutral compact corrections
with arbitrary signed projected Hessian integral and arbitrarily small value and
first derivative. The common geometric witnesses and normalized bump precede
both the target and tolerance. Only the two used eigenbasis columns and `W`
need local smoothness; the ordered eigenbasis hypothesis is pointwise.
The supplied `S`, `L`, `W` and basis are retained.

The complete orbit agrees with the original branch on closed `[0,H]`. Its
all-time zero lower jets, tangent annihilation and dual-frame diagonal identities
are retained, and the last integral uses the original finite branch literally.
Global strict hyperbolicity and genuine nonlinearity hold for the new flux `f + P`. -/
theorem exists_prescribed_clock_neutral_integrated_correction {δ A B e H tAnchor tStar : ℝ}
    {b : ℝ → ℝ} {γ : ℝ → ℝ^3} (hδ : 0 ≤ δ) (hA : 1 ≤ A ^ 2) (hAB : A ^ 2 < B ^ 2)
    (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10)) (hb : ContDiff ℝ ∞ b)
    (hhyper : ∀ x, IsStrictlyHyperbolicAt (concreteGatedFlux δ (clockFeedback A B) b) x)
    (hgn : ∀ k, IsGenuinelyNonlinearFamily (concreteGatedFlux δ (clockFeedback A B) b) k)
    (heH : e < H) (htStar : tStar ∈ Ioo (0 : ℝ) e)
    (hγ : ∀ t ∈ Icc (0 : ℝ) H, HasDerivAt γ (concreteGatedFlux δ (clockFeedback A B) b (γ t)) t)
    (hγzero : γ 0 = !₂[0, 0, 1]) (hmiddle : γ e 1 = 0) (hz : 0 < γ e 2) (hρ : γ e 0 / γ e 2 = 1)
    (S : Evolution.FundamentalSolution (fun t ↦ fderiv ℝ (concreteGatedFlux δ (clockFeedback A B) b)
      (γ t)) tAnchor (Icc (0 : ℝ) e))
    (L : (ℝ^3) →L[ℝ] (ℝ^2))
    (hL : LinearMap.ker L.toLinearMap =
      Submodule.span ℝ ({concreteGatedFlux δ (clockFeedback A B) b (γ e)} : Set (ℝ^3)))
    (r : ℝ → Module.Basis (Fin 3) ℝ (ℝ^3)) (W : ℝ → ℝ^3) {V : Set ℝ} (hV : IsOpen V)
    (htV : tStar ∈ V)
    (hrEigen : ∀ t ∈ V, ∃ eig : Fin 3 → ℝ, StrictMono eig ∧ ∀ k,
      fderiv ℝ (concreteGatedFlux δ (clockFeedback A B) b) (γ t) (r t k) = eig k • r t k)
    (i j : Fin 3) (hij : i ≠ j) (hiSmooth : ContDiffOn ℝ ∞ (fun t ↦ r t i) V)
    (hjSmooth : ContDiffOn ℝ ∞ (fun t ↦ r t j) V) (hW : ContDiffOn ℝ ∞ W V)
    (hi : Matrix.det
      ![⇑(concreteGatedFlux δ (clockFeedback A B) b (γ tStar)), ⇑(r tStar i), ⇑(W tStar)] ≠ 0)
    (hj : Matrix.det
      ![⇑(concreteGatedFlux δ (clockFeedback A B) b (γ tStar)), ⇑(r tStar j), ⇑(W tStar)] ≠ 0)
    (hcoeff : ∀ k, k ≠ i → k ≠ j →
      (r tStar).repr (concreteGatedFlux δ (clockFeedback A B) b (γ tStar)) k ≠ 0) :
    let f := concreteGatedFlux δ (clockFeedback A B) b
    ∃ (J : Set ℝ) (q : ℝ → ℝ^3) (U : Set (ℝ^3)) (l u : ℝ) (χ : ℝ → ℝ),
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
          ∀ m, (r t).repr
            (fderiv ℝ (fderiv ℝ P) (q t) (r t m) (r t m)) m = 0) ∧
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
  classical
  intro f
  have he : 0 < e := htStar.1.trans htStar.2
  have hf : ContDiff ℝ ∞ f := contDiff_concreteGatedFlux δ (contDiff_clockFeedback A B) hb
  have hbranch : ∀ t ∈ Icc (0 : ℝ) e, HasDerivAt γ (f (γ t)) t :=
    fun t ht ↦ hγ t ⟨ht.1, ht.2.trans heH.le⟩
  have hγSmooth : ContDiffOn ℝ ∞ γ (Ioo (0 : ℝ) e) :=
    Evolution.contDiffOn_of_hasDerivAt (n := ⊤) (f := fun _ x ↦ f x)
      isOpen_Ioo (hf.comp contDiff_snd).contDiffOn (fun t ht ↦ hbranch t ⟨ht.1.le, ht.2.le⟩)
  -- The omitted nonzero coordinate supplies the chart's transverse covector.
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  let ell : (ℝ^3) →L[ℝ] ℝ := ((r tStar).coord k).toContinuousLinearMap
  have htrans : ell (deriv γ tStar) ≠ 0 := show (r tStar).repr (deriv γ tStar) k ≠ 0 from
    (hbranch tStar ⟨htStar.1.le, htStar.2.le⟩).deriv ▸ hcoeff k hki hkj
  obtain ⟨J, hJ, htJ, hJV, hrealize⟩ :=
    exists_compact_neutral_tube_realization f (hf.of_le (by simp)) hhyper hgn
      ell (hV.inter isOpen_Ioo) ⟨htV, htStar⟩ (hγSmooth.mono (fun _ ht ↦ ht.2)) htrans
  obtain ⟨q, U, l, u, hprofile, hqSmooth, hqODE, hqγ, hreflected, hinj, hqne,
      hU, _, hl0, hlt, htu, hue, hinnerJ, hinnerU, hnoReturn, _, hrevU⟩ :=
    exists_isolated_arc_of_prescribed_clock_zero_speed_match
      hδ hA hAB hbsupp hb heH htStar hγ hγzero hmiddle hz hρ hJ htJ
  have hJH : J ⊆ Icc (0 : ℝ) H := fun _ ht ↦ ⟨(hJV ht).2.1.le, (hJV ht).2.2.le.trans heH.le⟩
  have hqJ : EqOn q γ J := fun _ ht ↦ hqγ (hJH ht)
  have hinnerV : Ioo l u ⊆ V := fun _ ht ↦ (hJV (hinnerJ ⟨ht.1.le, ht.2.le⟩)).1
  have hisolate : q ⁻¹' U ⊆ J := fun t ht ↦ (hnoReturn t ht).1
  -- Restrict the time neighborhood before selecting the common normalized bump.
  obtain ⟨lB, uB, χ, _, hBJ, hχ, hχcompact, hχsupport, hχnonneg, hχintegral, _, hfamily⟩ :=
    GNNeutralHessian.exists_integrated_bilinearCorrection_of_autonomous
      (Ω := univ) htStar isOpen_univ hf.contDiffOn (fun _ _ ↦ mem_univ _)
      hbranch S L hL r W isOpen_Ioo ⟨hlt, htu⟩ i j hij
      (hiSmooth.mono hinnerV) (hjSmooth.mono hinnerV) (hW.mono hinnerV) hi hj hcoeff
  have hχinner : tsupport χ ⊆ Ioo l u := fun _ ht ↦ (hBJ (hχsupport ht)).1
  refine ⟨J, q, U, l, u, χ, hJ, htJ, hJV, hprofile, hqSmooth, hqODE, hqγ,
    hreflected, hinj, hqne, hU, hl0, hlt, htu, hue, hinnerJ, hinnerU, hisolate,
    hrevU, hχ, hχcompact, hχinner, hχnonneg, hχintegral, fun target η hη ↦ ?_⟩
  let C : ℝ → (ℝ^3) →L[ℝ] (ℝ^3) →L[ℝ] (ℝ^3) := fun t ↦
    GNNeutralHessian.bilinearCorrection (f (γ t)) (r t i) (r t j) (W t)
      (L.comp (S.propagator e t)) (χ t • target)
  obtain ⟨hC, hCcompact, hCsupport, hCfacts, hCint, hCintegral⟩ := hfamily target
  have hCinner : tsupport C ⊆ Icc l u := fun t ht ↦ Ioo_subset_Icc_self (hBJ (hCsupport ht)).1
  have hCsupportJ : tsupport C ⊆ J := hCinner.trans hinnerJ
  -- The algebraic diagonal zeros belong to the supplied ordered eigenbasis.
  obtain ⟨P, hP, hPcompact, hPsupport, hjet, hsmall, hPhyper, hPgn⟩ :=
    hrealize C hC hCcompact hCsupportJ (fun t _ ↦ (hCfacts t).1) (fun t _ ↦ (hCfacts t).2.1)
      (fun t ht ↦ ⟨r t, (hrEigen t (hJV (hCsupportJ ht)).1).imp fun _ h ↦
        ⟨h.1, h.2, (hCfacts t).2.2.1⟩⟩)
      q hqJ U hU (image_subset_iff.mpr fun t ht ↦ hinnerU (hCinner ht)) hisolate η hη
  have hresponse : (fun t ↦ L (S.propagator e t (fderiv ℝ (fderiv ℝ P) (q t) (W t) (W t)))) =
      fun t ↦ L (S.propagator e t (C t (W t) (W t))) := funext fun t ↦ by rw [(hjet t).2.2]
  have hqIntegral : (∫ t in (0 : ℝ)..e, L (S.propagator e t
      (fderiv ℝ (fderiv ℝ P) (q t) (W t) (W t)))) = target := by rw [hresponse]; exact hCintegral
  refine ⟨P, hP, hPcompact, hPsupport,
    fun t ↦ ⟨(hjet t).1, (hjet t).2.1, fun v ↦ ?_, fun m ↦ (hjet t).2.2 ▸ (hCfacts t).2.2.1 m⟩,
    fun t ↦ (hjet t).2.2 ▸ (hCfacts t).2.2.2, hresponse ▸ hCint, hqIntegral, ?_,
    hsmall, hPhyper, hPgn⟩
  · rw [(hjet t).2.2]
    by_cases ht : t ∈ J
    · rw [(hqODE t).deriv, hqγ (hJH ht)]
      change C t (f (γ t)) v = 0
      rw [← show deriv γ t = f (γ t) from (hγ t (hJH ht)).deriv]
      exact (hCfacts t).2.1 v
    · simp only [image_eq_zero_of_notMem_tsupport (fun hs ↦ ht (hCsupportJ hs)), zero_apply]
  · rw [← hqIntegral]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le he.le] at ht
    simp only [hqγ ⟨ht.1, ht.2.trans heH.le⟩]

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
