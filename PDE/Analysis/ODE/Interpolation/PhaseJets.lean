/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

import PDE.Analysis.Calculus.LocalExtension
import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Duhamel.Identification
import PDE.Analysis.ODE.SmoothDependence.Variation
import PDE.Analysis.ODE.SmoothDependence.Variation.SecondOrder

/-!
# Propagation of equal speed jets for phase-aligned solution strips

Two supplied strips solve the same autonomous field with affine speed damping.
Their zero-speed curves coincide, and only their first two ordinary speed
jets agree at one time anchor. These jets then agree throughout the closed
interval, in both directions from the anchor.

The strips need smoothness only on an open product containing the slab at
speed zero. A compactly supported representative of each local germ permits
reuse of the existing second-variation formula. Linear uniqueness is used
twice with one fundamental solution; no equality of the initial speed germs
is required or concluded.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluate the production parameter-variation formula for affine damping. -/
private theorem hasDerivAt_firstSpeedVariation_sub_smul_of_contDiffAt
    {F : ℝ → ℝ → E} {f : E → E} {t : ℝ}
    (hF : ContDiffAt ℝ 2 F.uncurry (t, 0)) (hf : ContDiff ℝ 2 f)
    (hode : ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t) :
    HasDerivAt (fun s ↦ deriv (F s) 0)
      (fderiv ℝ f (F t 0) (deriv (F t) 0) - F t 0) t := by
  let field : ℝ × E → E := fun z ↦ f z.2 - z.1 • z.2
  have hstate : HasFDerivAt (fun z : ℝ × E ↦ z.2)
      (ContinuousLinearMap.snd ℝ ℝ E) (0, F t 0) := hasFDerivAt_snd
  have hspeed : HasFDerivAt (fun z : ℝ × E ↦ z.1)
      (ContinuousLinearMap.fst ℝ ℝ E) (0, F t 0) := hasFDerivAt_fst
  have hfield :=
    ((hf.differentiable (by norm_num) (F t 0)).hasFDerivAt.comp (0, F t 0)
      hstate).fun_sub (hspeed.fun_smul hstate)
  have h := hasDerivAt_parameterVariation_of_contDiffAt (F := F) (v := field)
    (t := t) (p := 0) hF hfield.differentiableAt hode (1 : ℝ)
  apply h.congr_deriv
  simpa only [field, Function.comp_def, fderiv_apply_one_eq_deriv, sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, zero_apply, zero_smul, one_smul, zero_add] using
    congrArg (fun D : (ℝ × E) →L[ℝ] E ↦ D (1, deriv (F t) 0)) hfield.fderiv

/-- Localize the family germ, reuse the checked second-variation formula, and
transfer both ordinary speed jets and the ordinary time derivative back. -/
private theorem hasDerivAt_secondSpeedVariation_sub_smul_of_contDiffAt
    {F : ℝ → ℝ → E} {f : E → E} {t : ℝ}
    (hF : ContDiffAt ℝ 3 F.uncurry (t, 0)) (hf : ContDiff ℝ 2 f)
    (hode : ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t) :
    HasDerivAt (fun s ↦ deriv (deriv (F s)) 0)
      (fderiv ℝ f (F t 0) (deriv (deriv (F t)) 0) +
        fderiv ℝ (fderiv ℝ f) (F t 0) (deriv (F t) 0) (deriv (F t) 0) -
        (2 : ℝ) • deriv (F t) 0) t := by
  obtain ⟨Q, hQ, _, heq⟩ := hF.exists_contDiff_compactSupport_eventuallyEq
  let R : ℝ → ℝ → E := fun s μ ↦ Q (s, μ)
  have hR : ContDiff ℝ 3 R.uncurry := hQ
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp
    (show {z : ℝ × ℝ | F z.1 z.2 = Q z} ∈ 𝓝 (t, 0) from heq)
  have hFR {s μ : ℝ} (hs : s ∈ U) (hμ : μ ∈ V) : F s μ = R s μ :=
    hUV (show (s, μ) ∈ U ×ˢ V from ⟨hs, hμ⟩)
  have htU : t ∈ U := mem_of_mem_nhds hU
  have hslice (s : ℝ) (hs : s ∈ U) : F s =ᶠ[𝓝 (0 : ℝ)] R s :=
    eventually_of_mem hV fun _ ↦ hFR hs
  have hRode : ∀ᶠ μ in 𝓝 (0 : ℝ),
      HasDerivAt (fun s ↦ R s μ) (f (R t μ) - μ • R t μ) t := by
    filter_upwards [hode, hV] with μ hμ hμV
    simpa only [hFR htU hμV] using
      hμ.congr_of_eventuallyEq (eventually_of_mem hU fun _ hs ↦ (hFR hs hμV).symm)
  have hsecondGerm : (fun s ↦ deriv (deriv (F s)) 0) =ᶠ[𝓝 t]
      (fun s ↦ deriv (deriv (R s)) 0) :=
    eventually_of_mem hU fun s hs ↦ (hslice s hs).deriv.deriv_eq
  simpa only [← (hslice t htU).self_of_nhds, ← (hslice t htU).deriv_eq,
    ← hsecondGerm.self_of_nhds, zero_smul, sub_zero] using
    (hasDerivAt_secondSpeedVariation_sub_smul hR hf hRode).congr_of_eventuallyEq hsecondGerm

variable [CompleteSpace E]

/-- Equal speed jets of orders one and two at one anchor propagate along two
supplied solution strips with the same zero-speed curve and the same field
`f - μ • id`. All displayed jets are ordinary scalar derivatives.

The anchor may lie at either endpoint, and the interval may be a singleton.
Joint smoothness is required only on the displayed open product. The actual
ordinary time equations are supplied at every closed-slab time. No initial
speed-germ equality, variation equation, or global smoothness of either strip
is assumed. -/
theorem eqOn_speedJets_of_same_field
    {F G : ℝ → ℝ → E} {f : E → E} {q : ℝ → E}
    {I J : Set ℝ} {a b c : ℝ}
    (hI : IsOpen I) (hJ : IsOpen J) (hinterval : Icc a b ⊆ I)
    (hzero : (0 : ℝ) ∈ J)
    (hF : ContDiffOn ℝ ∞ F.uncurry (I ×ˢ J))
    (hG : ContDiffOn ℝ ∞ G.uncurry (I ×ˢ J)) (hf : ContDiff ℝ 2 f)
    (hodeF : ∀ t ∈ Icc a b, ∀ μ ∈ J,
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (hodeG : ∀ t ∈ Icc a b, ∀ μ ∈ J,
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) - μ • G t μ) t)
    (hFzero : EqOn (fun t ↦ F t 0) q (Icc a b))
    (hGzero : EqOn (fun t ↦ G t 0) q (Icc a b))
    (hc : c ∈ Icc a b)
    (hfirst : deriv (F c) 0 = deriv (G c) 0)
    (hsecond : deriv (deriv (F c)) 0 = deriv (deriv (G c)) 0) :
    EqOn (fun t ↦ F t 0) (fun t ↦ G t 0) (Icc a b) ∧
      EqOn (fun t ↦ deriv (F t) 0) (fun t ↦ deriv (G t) 0) (Icc a b) ∧
      EqOn (fun t ↦ deriv (deriv (F t)) 0)
        (fun t ↦ deriv (deriv (G t)) 0) (Icc a b) := by
  have hbase : EqOn (fun t ↦ F t 0) (fun t ↦ G t 0) (Icc a b) := fun t ht ↦
    (hFzero ht).trans (hGzero ht).symm
  have hspeed {Q : ℝ → ℝ → E} (hQ : ContDiffOn ℝ ∞ Q.uncurry (I ×ˢ J)) :
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ ↦ deriv (Q z.1) z.2) (I ×ˢ J) := by
    have h : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ ↦ fderiv ℝ (Q z.1) z.2) (I ×ˢ J) :=
      hQ.fderiv_snd hJ (by simp)
    simpa only [fderiv_apply_one_eq_deriv] using h.clm_apply (contDiffOn_const (c := (1 : ℝ)))
  have hregularity (Q : ℝ → ℝ → E)
      (hQ : ContDiffOn ℝ ∞ Q.uncurry (I ×ˢ J)) :
      ContinuousOn (fun t ↦ Q t 0) (Icc a b) ∧
        ContinuousOn (fun t ↦ deriv (Q t) 0) (Icc a b) ∧
        ContinuousOn (fun t ↦ deriv (deriv (Q t)) 0) (Icc a b) :=
    ⟨(hQ.contDiffOn_prodMk_left hzero).continuousOn.mono hinterval,
      ((hspeed hQ).contDiffOn_prodMk_left hzero).continuousOn.mono hinterval,
      ((hspeed (Q := fun s μ ↦ deriv (Q s) μ) (hspeed hQ)).contDiffOn_prodMk_left
        hzero).continuousOn.mono hinterval⟩
  obtain ⟨hFcont, hWF, hZF⟩ := hregularity F hF
  obtain ⟨_, hWG, hZG⟩ := hregularity G hG
  have hlocal {Q : ℝ → ℝ → E}
      (hQ : ContDiffOn ℝ ∞ Q.uncurry (I ×ˢ J)) {t : ℝ} (ht : t ∈ Icc a b) :
      ContDiffAt ℝ 3 Q.uncurry (t, 0) :=
    (hQ.contDiffAt (prod_mem_nhds (hI.mem_nhds (hinterval ht))
      (hJ.mem_nhds hzero))).of_le (by simp)
  let A : ℝ → E →L[ℝ] E := fun t ↦ fderiv ℝ f (F t 0)
  have hA : ContinuousOn A (Icc a b) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous.comp_continuousOn hFcont
  let S : PDE.Analysis.Evolution.FundamentalSolution A c (Icc a b) :=
    PDE.Analysis.Evolution.fundamentalSolutionIcc hA ⟨c, hc⟩
  -- One arbitrary-anchor linear uniqueness argument, reused for both differences.
  have hzeroSolution {u v : ℝ → E} (hu : ContinuousOn u (Icc a b))
      (hv : ContinuousOn v (Icc a b))
      (hdu : ∀ t ∈ Icc a b, HasDerivAt (fun s ↦ u s - v s) (A t (u t - v t)) t)
      (huv : u c = v c) : EqOn u v (Icc a b) := fun t ht ↦ by
    have h := S.eq_propagator_add_integral_of_hasDerivWithinAt
      (z := fun s ↦ u s - v s) (r := fun _ ↦ (0 : E)) (hu.sub hv) continuousOn_const
      (fun s hs ↦ by simpa only [add_zero] using
        (hdu s (Ioo_subset_Icc_self hs)).hasDerivWithinAt) hc ht
    simpa only [huv, sub_self, map_zero, intervalIntegral.integral_zero, add_zero,
      sub_eq_zero] using h
  have hodeF' (t : ℝ) (ht : t ∈ Icc a b) := eventually_of_mem (hJ.mem_nhds hzero) (hodeF t ht)
  have hodeG' (t : ℝ) (ht : t ∈ Icc a b) := eventually_of_mem (hJ.mem_nhds hzero) (hodeG t ht)
  have hfirstOn : EqOn (fun t ↦ deriv (F t) 0) (fun t ↦ deriv (G t) 0) (Icc a b) :=
    hzeroSolution hWF hWG (fun t ht ↦ by
      refine ((hasDerivAt_firstSpeedVariation_sub_smul_of_contDiffAt
        ((hlocal hF ht).of_le (by norm_num)) hf (hodeF' t ht)).fun_sub
        (hasDerivAt_firstSpeedVariation_sub_smul_of_contDiffAt
          ((hlocal hG ht).of_le (by norm_num)) hf (hodeG' t ht))).congr_deriv ?_
      dsimp only [A]
      rw [show G t 0 = F t 0 from (hbase ht).symm, map_sub]
      abel) hfirst
  refine ⟨hbase, hfirstOn, hzeroSolution hZF hZG (fun t ht ↦ ?_) hsecond⟩
  refine ((hasDerivAt_secondSpeedVariation_sub_smul_of_contDiffAt (hlocal hF ht) hf
    (hodeF' t ht)).fun_sub (hasDerivAt_secondSpeedVariation_sub_smul_of_contDiffAt
      (hlocal hG ht) hf (hodeG' t ht))).congr_deriv ?_
  dsimp only [A]
  rw [show G t 0 = F t 0 from (hbase ht).symm,
    show deriv (G t) 0 = deriv (F t) 0 from (hfirstOn ht).symm, map_sub]
  abel

end PDE.Analysis.ODE
