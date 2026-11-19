/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental
public import PDE.Analysis.ODE.SmoothDependence.FiniteInterval.AnchoredEvent

import PDE.Analysis.Calculus.Prod.ParameterDerivative
import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Propagator.Uniqueness
import PDE.Analysis.ODE.SmoothDependence.Variation.MovingEvent
import PDE.Analysis.ODE.SmoothDependence.Variation.Response

/-!
# Moving-event response relative to a retained flow

The old family and its event are supplied before the correction. Only the
corrected family and event are constructed, using the entire initial speed
section of the retained family at the supplied anchor. The response therefore
uses the retained first variation and the supplied fundamental solution.

The anchor may lie on either side of the event or at either slab endpoint.
The signed integral runs from that anchor to the reference event time.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Evolution
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Construct the corrected flow from the retained family's initial speed section.
Vanishing lower jets of the correction preserve the complete reference and the
first speed variation on the closed slab. The moving-point difference has zero
first derivative and the full projected second response with coefficient one.

The old flow, event, and propagator remain the supplied witnesses. The old event
needs only local `C²` regularity. No initial speed derivative is required to vanish,
and there is no ordering assumption between the anchor and the event time. -/
theorem exists_retained_flow_movingEvent_secondSpeedVariation_response
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (q : ℝ → E) (hq : ∀ t, HasDerivAt q (f (q t)) t)
    {lo hi c e s₀ : ℝ} (hc : c ∈ Icc lo hi)
    (F : ℝ → ℝ → E) (hF : ContDiff ℝ ∞ F.uncurry)
    (I₀ : Set ℝ) (hI₀ : IsOpen I₀) (h0I₀ : (0 : ℝ) ∈ I₀)
    (hFbase : EqOn (fun t ↦ F t 0) q (Icc lo hi))
    (hFode : ∀ μ ∈ I₀, ∀ t ∈ Icc lo hi,
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (τ : ℝ → ℝ) (hτ : ContDiffOn ℝ 2 τ I₀) (hτ0 : τ 0 = e)
    (ell : E →L[ℝ] ℝ)
    (hτsection : ∀ μ ∈ I₀, τ μ ∈ Ioo lo hi ∧ ell (F (τ μ) μ) = ell (q e))
    (htransverse : ell (f (q e)) ≠ 0)
    (S : FundamentalSolution (fun t ↦ fderiv ℝ f (q t)) s₀ (Icc lo hi))
    (L : E →L[ℝ] V) (hL : L (f (q e)) = 0)
    (P : E → E) (hP : ContDiff ℝ ∞ P)
    (hPzero : ∀ t, P (q t) = 0) (hDPzero : ∀ t, fderiv ℝ P (q t) = 0) :
    ∃ (G : ℝ → ℝ → E) (υ : ℝ → ℝ) (I : Set ℝ),
      let R : ℝ → E := fun μ ↦ G (υ μ) μ - F (τ μ) μ
      let Δ : E := deriv (deriv (G e)) 0 - deriv (deriv (F e)) 0
      ContDiff ℝ ∞ G.uncurry ∧ IsOpen I ∧ (0 : ℝ) ∈ I ∧ I ⊆ I₀ ∧
      (∀ μ, G c μ = F c μ) ∧ EqOn (fun t ↦ G t 0) q (Icc lo hi) ∧
      (∀ μ ∈ I, ∀ t ∈ Icc lo hi,
        HasDerivAt (fun s ↦ G s μ) (f (G t μ) + P (G t μ) - μ • G t μ) t) ∧
      ContDiffOn ℝ ∞ υ I ∧ υ 0 = e ∧
      (∀ μ ∈ I, υ μ ∈ Ioo lo hi ∧ ell (G (υ μ) μ) = ell (q e)) ∧
      EqOn (fun t ↦ deriv (G t) 0) (fun t ↦ deriv (F t) 0) (Icc lo hi) ∧
      deriv υ 0 = deriv τ 0 ∧ R 0 = 0 ∧ HasDerivAt R 0 0 ∧
      HasDerivAt (deriv R) (Δ - (ell Δ / ell (f (q e))) • f (q e)) 0 ∧
      L (deriv (deriv R) 0) =
        ∫ s in c..e, L (S.propagator e s
          (fderiv ℝ (fderiv ℝ P) (q s) (deriv (F s) 0) (deriv (F s) 0))) := by
  have he : e ∈ Ioo lo hi := by simpa only [hτ0] using (hτsection 0 h0I₀).1
  have heClosed : e ∈ Icc lo hi := Ioo_subset_Icc_self he
  -- the corrected flow and its event, built from the retained initial speed section
  obtain ⟨Φ, υ, I₁, hΦ, hI₁, h0I₁, hGinit, hΦbase, hΦode, hυ, hυ0, hυsection, _⟩ :=
    exists_anchored_flux_flow_event (fun x ↦ f x + P x) (hf.add hP) q
      (fun t ↦ by simpa only [hPzero t, add_zero] using hq t)
      (F c) (hF.comp (contDiff_const.prodMk contDiff_id)) hc he (hFbase hc) ell
      (by simpa only [hPzero e, add_zero] using htransverse)
  let G : ℝ → ℝ → E := fun t μ ↦ Φ (t, μ)
  let I : Set ℝ := I₀ ∩ I₁
  have hG : ContDiff ℝ ∞ G.uncurry := hΦ
  have hGbase : EqOn (fun t ↦ G t 0) q (Icc lo hi) := hΦbase
  have hI : IsOpen I := hI₀.inter hI₁
  have h0I : (0 : ℝ) ∈ I := ⟨h0I₀, h0I₁⟩
  have hGode (μ : ℝ) (hμ : μ ∈ I) (t : ℝ) (ht : t ∈ Icc lo hi) :
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) + P (G t μ) - μ • G t μ) t :=
    hΦode μ hμ.2 t ht
  have hυI : ContDiffOn ℝ ∞ υ I := hυ.mono inter_subset_right
  have hτ2 : ContDiffAt ℝ 2 τ 0 := hτ.contDiffAt (hI₀.mem_nhds h0I₀)
  have hυ2 : ContDiffAt ℝ 2 υ 0 := (hυI.contDiffAt (hI.mem_nhds h0I)).of_le (by simp)
  have hF3 : ContDiff ℝ 3 F.uncurry := hF.of_le (by simp)
  have hG3 : ContDiff ℝ 3 G.uncurry := hG.of_le (by simp)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hP2 : ContDiff ℝ 2 P := hP.of_le (by simp)
  have hodeF (t : ℝ) (ht : t ∈ Icc lo hi) : ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t :=
    eventually_of_mem (hI.mem_nhds h0I) fun μ hμ ↦ hFode μ hμ.1 t ht
  have hodeG (t : ℝ) (ht : t ∈ Icc lo hi) : ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) + P (G t μ) - μ • G t μ) t :=
    eventually_of_mem (hI.mem_nhds h0I) fun μ hμ ↦ hGode μ hμ t ht
  have hinit : G c =ᶠ[𝓝 (0 : ℝ)] F c := .of_forall hGinit
  have hjet (t : ℝ) (ht : t ∈ Icc lo hi) : P (F t 0) = 0 ∧ fderiv ℝ P (F t 0) = 0 := by
    rw [show F t 0 = q t from hFbase ht]
    exact ⟨hPzero t, hDPzero t⟩
  obtain ⟨_, _, hfirst, _⟩ := exists_projected_secondSpeedVariation_response_of_mem_Icc hc
    hF3 hG3 hf2 hP2 hodeF hodeG hinit hjet L
  obtain ⟨S₁, htimes, hsecond, hintegral⟩ :=
    exists_projected_movingEvent_secondSpeedVariation_response_of_mem_Icc hc he
      hF3 hG3 hf2 hP2 hodeF hodeG hinit hjet hτ2 hυ2 hτ0 hυ0 ell
      (eventually_of_mem (hI.mem_nhds h0I) fun μ hμ ↦ (hτsection μ hμ.1).2)
      (eventually_of_mem (hI.mem_nhds h0I) fun μ hμ ↦ (hυsection μ hμ.2).2)
      (by simpa only [hFbase heClosed] using htransverse) L
      (by simpa only [hFbase heClosed] using hL)
  -- the first derivative of the moving-point difference vanishes
  have heventDeriv {Q : ℝ → ℝ → E} {σ : ℝ → ℝ}
      (hQ : ContDiff ℝ ∞ Q.uncurry) (hσ : ContDiffAt ℝ 2 σ 0) (hσ0 : σ 0 = e)
      (hv : HasDerivAt (fun t ↦ Q t 0) (f (q e)) e) :
      HasDerivAt (fun μ ↦ Q (σ μ) μ) (deriv (Q e) 0 + deriv σ 0 • f (q e)) 0 := by
    have hmove : HasDerivAt (fun μ ↦ Q (σ μ) μ)
        (deriv (Q e) 0 + fderiv ℝ (fun t ↦ Q t 0) e (deriv σ 0)) 0 :=
      PDE.Analysis.hasDerivAt_moving_point (U := fun μ t ↦ Q t μ)
        (((hQ.comp (contDiff_snd.prodMk contDiff_fst)).differentiable (by simp)) (0, e))
        (hσ.differentiableAt (by simp)).hasDerivAt hσ0
    simpa only [fderiv_eq_smul_deriv, hv.deriv] using hmove
  have hvelF : HasDerivAt (fun t ↦ F t 0) (f (q e)) e := by
    simpa only [hFbase heClosed, zero_smul, sub_zero] using hFode 0 h0I₀ e heClosed
  have hvelG : HasDerivAt (fun t ↦ G t 0) (f (q e)) e := by
    simpa only [hGbase heClosed, hPzero e, add_zero, zero_smul, sub_zero] using
      hGode 0 h0I e heClosed
  have hRfirst : HasDerivAt (fun μ ↦ G (υ μ) μ - F (τ μ) μ) 0 0 := by
    simpa only [hfirst heClosed, htimes, sub_self] using
      (heventDeriv hG hυ2 hυ0 hvelG).fun_sub (heventDeriv hF hτ2 hτ0 hvelF)
  refine ⟨G, υ, I, hG, hI, h0I, inter_subset_left, hGinit, hGbase, hGode, hυI, hυ0,
    fun μ hμ ↦ hυsection μ hμ.2, hfirst, htimes, ?_, hRfirst, ?_, ?_⟩
  · simp only [hυ0, hτ0, hGbase heClosed, hFbase heClosed, sub_self]
  · simpa only [hFbase heClosed] using hsecond
  -- the propagator of the retained coefficient is the supplied one
  have hprop (s : ℝ) (hs : s ∈ Icc lo hi) : S₁.propagator e s = S.propagator e s :=
    (S₁.congr fun t ht ↦ congrArg (fderiv ℝ f) (hFbase ht)).propagator_eq_on_Icc S hs heClosed
  refine hintegral.trans (intervalIntegral.integral_congr fun s hs ↦ ?_)
  have hsClosed : s ∈ Icc lo hi := uIcc_subset_Icc hc heClosed hs
  simp only [hprop s hsClosed, hFbase hsClosed]

end PDE.Analysis.ODE
