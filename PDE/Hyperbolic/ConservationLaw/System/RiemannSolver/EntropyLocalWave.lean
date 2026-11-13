/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.ElementaryWave
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Rarefaction
public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyProduction
public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyRarefaction
import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Compression

/-!
# Entropy admissible realizations of local elementary transformations

Negative Hugoniot branches use their convex-entropy production estimate.
The local integral flow gives entropy equality for contacts and, after
inverting its characteristic speed, for rarefaction fans. These profiles
retain the elementary witnesses and uniform propagation bounds.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

private theorem exists_bounded_entropy_elementary_discontinuity {m : ℕ} {flux : ℝ^m → ℝ^m}
    {fields : Fin m → CharacteristicField flux} {k : Fin m} {left right : ℝ^m} {σ lo hi K : ℝ}
    (hRH : RankineHugoniot flux left right σ)
    (hproduction : ∀ E : ConvexEntropyPair flux, E.entropyFlux right - E.entropyFlux left ≤
      σ * (E.entropy right - E.entropy left))
    (helem : IsElementaryWave fields k left right (planarShock left right σ)) (hlo : lo ≤ σ)
    (hhi : σ ≤ hi) (hleft : ‖left‖ ≤ K) (hright : ‖right‖ ≤ K) :
    ∃ u : ℝ^2 → ℝ^m,
      IsElementaryWave fields k left right u ∧
      IsEntropyWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
      (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
      (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
      (∀ p : ℝ^2, 0 < p 0 → p 1 < lo * p 0 → u p = left) ∧
      (∀ p : ℝ^2, 0 < p 0 → hi * p 0 ≤ p 1 → u p = right) := by
  refine ⟨planarShock left right σ, helem,
    ((isEntropyWeakSolution_planarShock_iff).mpr ⟨hRH, hproduction⟩).mono_domain le_top,
    measurable_planarShock left right σ,
    fun p _ ↦ (norm_planarShock_le_max left right σ p).trans (max_le hleft hright),
    fun _ hc p ↦ planarShock_smul_of_pos hc left right σ p,
    fun p ht hp ↦ planarShock_apply_of_mem (hp.trans_le (mul_le_mul_of_nonneg_right hlo ht.le)),
    fun p ht hp ↦ planarShock_apply_of_not_mem
      (not_lt.mpr ((mul_le_mul_of_nonneg_right hhi ht.le).trans hp))⟩

/-- Realize a local elementary transformation by bounded self-similar weak
waves satisfying every convex entropy inequality and preserving the precise
elementary witness. On a genuinely nonlinear
branch the transformation has the positively oriented characteristic tangent
and agrees with the supplied local flow for positive strengths. -/
theorem eventually_exists_bounded_entropy_elementary_wave {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 1 flux) (fields : Fin m → CharacteristicField flux) (k : Fin m) (gn : Prop)
    {R T : ℝ × ℝ^m → ℝ^m} {speed : ℝ × ℝ^m → ℝ} {q₀ : ℝ^m} {lo hi : ℝ}
    (heig : ContDiffAt ℝ 1 (fields k).speed q₀) (hT : ContDiffAt ℝ 1 T (0, q₀))
    (hR : ContDiffAt ℝ 1 R (0, q₀)) (hTzero : ∀ q, T (0, q) = q)
    (hRzero : ∀ᶠ q in 𝓝 q₀, R (0, q) = q)
    (htan : HasDerivAt (fun s ↦ T (s, q₀)) ((fields k).rightEigenvector q₀) 0)
    (helementary : ∀ p, IsElementaryConnection fields k p.2 (T p))
    (hbranch : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), (¬gn ∨ 0 < p.1) → T p = R p)
    (hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      HasDerivAt (fun t ↦ R (t, p.2)) ((fields k).rightEigenvector (R p)) p.1)
    (hshock : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), gn → p.1 ≤ 0 → RankineHugoniot flux p.2 (T p) (speed p) ∧
      ∀ E : ConvexEntropyPair flux, E.entropyFlux (T p) - E.entropyFlux p.2 ≤
      speed p * (E.entropy (T p) - E.entropy p.2))
    (hpositive : gn → 0 < fderiv ℝ (fields k).speed q₀ ((fields k).rightEigenvector q₀))
    (hdegenerate : ¬gn → (fields k).IsLinearlyDegenerate)
    (hwindow : (fields k).speed q₀ ∈ Ioo lo hi) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∃ u : ℝ^2 → ℝ^m,
      IsElementaryWave fields k p.2 (T p) u ∧
      IsEntropyWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
      (∀ z : ℝ^2, 0 < z 0 → ‖u z‖ ≤ ‖q₀‖ + 1) ∧
      (∀ c : ℝ, 0 < c → ∀ z, u (c • z) = u z) ∧
      (∀ z : ℝ^2, 0 < z 0 → z 1 < lo * z 0 → u z = p.2) ∧
      (∀ z : ℝ^2, 0 < z 0 → hi * z 0 ≤ z 1 → u z = T p) := by
  classical
  let C := fields k
  have hR₀ := hRzero.self_of_nhds
  have hTnorm : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ‖T p‖ ≤ ‖q₀‖ + 1 := Eventually.mono
    (hT.continuousAt.norm (Iio_mem_nhds (by simpa only [hTzero] using lt_add_one ‖q₀‖)))
    fun _ hp ↦ le_of_lt hp
  have hqnorm : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), ‖p.2‖ ≤ ‖q₀‖ + 1 := Eventually.mono
    (continuousAt_snd.norm (Iio_mem_nhds (lt_add_one ‖q₀‖))) fun _ hp ↦ le_of_lt hp
  have hspeedLeft : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), C.speed p.2 ∈ Ioo lo hi :=
    (heig.continuousAt.comp continuousAt_snd) (Ioo_mem_nhds hwindow.1 hwindow.2)
  have hspeedRight : ∀ᶠ p in 𝓝 (0, q₀), C.speed (T p) ∈ Ioo lo hi := by
    have heigT : ContinuousAt C.speed (T (0, q₀)) := by
      simpa only [hTzero] using heig.continuousAt
    exact (heigT.comp hT.continuousAt) (by
      simpa only [Function.comp_def, hTzero] using Ioo_mem_nhds hwindow.1 hwindow.2)
  by_cases hgn : gn
  · obtain ⟨δT, hδT, hmonoT⟩ :=
      exists_uniform_speed_expansion heig hT (hTzero q₀) htan (hpositive hgn)
    obtain ⟨P, hP⟩ := exists_uniform_rarefaction_profile C heig hR hRzero hflow (hpositive hgn).ne'
    have htanR : HasDerivAt (fun s ↦ R (s, q₀)) (C.rightEigenvector q₀) 0 := by
      simpa only [hR₀] using hflow.self_of_nhds
    obtain ⟨δR, hδR, hmonoR⟩ := exists_uniform_speed_expansion heig hR hR₀ htanR (hpositive hgn)
    have hspeedReg : ContDiffAt ℝ 1 (fun p ↦ C.speed (R p)) (0, q₀) :=
      (show ContDiffAt ℝ 1 C.speed (R (0, q₀)) by simpa only [hR₀] using heig).comp (0, q₀) hR
    obtain ⟨δ, hδ, hball'⟩ := Metric.mem_nhds_iff.mp
      (((hR.eventually (by simp)).and (hflow.and hP)).and
        (hspeedReg.eventually (by simp)))
    have hball {p : ℝ × ℝ^m} (hp : p ∈ ball ((0 : ℝ), q₀) δ) := (hball' hp).1
    have hz : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), R (0, p.2) = p.2 := (continuousAt_snd :
        ContinuousAt (Prod.snd : ℝ × ℝ^m → ℝ^m) (0, q₀)).tendsto.eventually hRzero
    filter_upwards [hTnorm, hqnorm, hspeedLeft, hspeedRight, hbranch, hz, hshock,
      ball_mem_nhds ((0 : ℝ), q₀) hδT, ball_mem_nhds ((0 : ℝ), q₀) hδR,
      ball_mem_nhds ((0 : ℝ), q₀) hδ]
      with p hTp hqp hspeedL hspeedR hbranchp hzp hshockp hpT hpR hpδ
    by_cases hs0 : p.1 = 0
    · rw [show T p = p.2 by rw [show p = (0, p.2) from Prod.ext hs0 rfl, hTzero]]
      exact ⟨fun _ ↦ p.2, .same p.2, isEntropyWeakSolution_const forwardHalfSpace p.2,
        measurable_const, fun _ _ ↦ hqp, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩
    rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hpT hpR hpδ
    rcases lt_or_gt_of_ne hs0 with hs | hs
    · have hdecrease : C.speed (T p) < C.speed p.2 := by
        simpa only [hTzero] using hmonoT p.2 hpT.2 hpT.1 ⟨neg_lt_zero.mpr hδT, hδT⟩ hs
      obtain ⟨σ, hσ⟩ := (helementary p).exists_laxShock_of_speed_lt hdecrease
      have hjump : T p ≠ p.2 := fun h ↦ (ne_of_lt hdecrease) (congrArg C.speed h)
      have hσeq := RankineHugoniot.unique_speed hjump hσ.1 (hshockp hgn hs.le).1
      exact exists_bounded_entropy_elementary_discontinuity hσ.1
        (fun E ↦ hσeq.symm ▸ (hshockp hgn hs.le).2 E) (.shock σ hσ)
        (hspeedR.1.trans hσ.2.1).le (hσ.2.2.1.trans hspeedL.2).le hqp hTp
    · have hTR := hbranchp (Or.inr hs)
      have hmem {s : ℝ} (hs' : s ∈ Ioo (-δ) δ) : (s, p.2) ∈ ball ((0 : ℝ), q₀) δ := by
        rw [← ball_prod_same, Real.ball_zero_eq_Ioo]
        exact ⟨hs', hpδ.2⟩
      have hPp := (hball (hmem hpδ.1)).2.2
      have horder : C.speed p.2 < C.speed (R p) := by
        simpa only [hzp] using hmonoR p.2 hpR.2 ⟨neg_lt_zero.mpr hδR, hδR⟩ hpR.1 hs
      obtain ⟨u, hu, hmu, hbu, hsu, hlu, hru, hinside⟩ :=
        exists_bounded_weak_rarefaction hflux horder.le
          (fun ξ hξ ↦ (hPp.2.2 ξ (Icc_subset_uIcc hξ)).1)
          (fun ξ hξ ↦ (hPp.2.2 ξ (Icc_subset_uIcc hξ)).2.2.1)
          hPp.1 hPp.2.1 (fun ξ hξ ↦ (hPp.2.2 ξ (Icc_subset_uIcc hξ)).2.2.2)
      have hentropy : SatisfiesEntropyInequality flux forwardHalfSpace u :=
        satisfiesEntropyInequality_rarefaction_of_profile hflux horder.le
          (fun ξ hξ ↦ (hPp.2.2 ξ (Icc_subset_uIcc hξ)).1)
          (fun ξ hξ ↦ (hPp.2.2 ξ (Icc_subset_uIcc hξ)).2.2.1)
          hPp.1 hPp.2.1 (fun p _ hp ↦ hlu p hp) hru hinside
      have hθmem {r θ : ℝ} (hr : p.1 ∈ Ioo (-r) r) (hθ : θ ∈ Icc 0 1) : θ * p.1 ∈ Ioo (-r) r :=
        ⟨by linarith [mul_nonneg hθ.1 hs.le, hr.2],
          (mul_le_of_le_one_left hs.le hθ.2).trans_lt hr.2⟩
      have hmono : StrictMonoOn (fun θ : ℝ ↦ C.speed (R (θ * p.1, p.2))) (Icc 0 1) :=
        fun _ ha _ hb hab ↦ hmonoR p.2 hpR.2 (hθmem hpR.1 ha) (hθmem hpR.1 hb)
          (mul_lt_mul_of_pos_right hab hs)
      have helem : IsElementaryWave fields k p.2 (R p) u := by
        refine .rarefaction (fun s ↦ R (s, p.2)) p.1 (Ioo (-δ) δ) isOpen_Ioo
          (by rw [uIcc_of_le hs.le]; exact Icc_subset_Ioo (neg_lt_zero.mpr hδ) hpδ.1.2)
          (fun s hs' ↦ ((hball (hmem hs')).1.comp s
            (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt)
          hzp (fun s hs' ↦ (hball (hmem hs')).2.1.hasDerivWithinAt) rfl hmono
          (fun s hs' ↦ ?_) (fun z _ hx ↦ hlu z hx) hru fun θ hθ t ht ↦ ?_
        · exact ((hball' (hmem hs')).2.comp s
            (contDiffAt_id.prodMk contDiffAt_const)).continuousAt.continuousWithinAt
        let ξ := C.speed (R (θ * p.1, p.2))
        have hξL : C.speed p.2 ≤ ξ := by
          simpa only [zero_mul, hzp] using hmono.monotoneOn (left_mem_Icc.mpr zero_le_one) hθ hθ.1
        rcases hθ.2.lt_or_eq with hθ1 | rfl
        · have hξR : ξ < C.speed (R p) := by
            simpa only [one_mul] using hmono hθ (right_mem_Icc.mpr zero_le_one) hθ1
          change u (AffineInterface.interface ξ t) = _
          rw [hinside _ ht (mul_le_mul_of_nonneg_right hξL ht.le) (mul_lt_mul_of_pos_right hξR ht)]
          change P (ξ * t / t, p.2) = _
          rw [mul_div_cancel_right₀ ξ ht.ne']
          exact (hball (hmem (hθmem hpδ.1 hθ))).2.2.2.1
        · simpa only [one_mul] using
            hru (AffineInterface.interface (C.speed (R p)) t) ht (by simp)
      refine ⟨u, hTR.symm ▸ helem, ⟨hu, hentropy⟩, hmu, hbu, hsu,
        fun z ht hx ↦ hlu z (hx.trans_le (mul_le_mul_of_nonneg_right hspeedL.1.le ht.le)),
        fun z ht hx ↦ ?_⟩
      rw [hTR] at hspeedR ⊢
      exact hru z ht ((mul_le_mul_of_nonneg_right hspeedR.2.le ht.le).trans hx)
  · have hld := hdegenerate hgn
    obtain ⟨δ, hδ, hcontact⟩ := exists_uniform_contact_of_local_flow
      C.flux_differentiable hR.continuousAt hRzero hflow (Eventually.of_forall fun q ↦
        ⟨hld.1 q, hld.2 q, (C.eigenvector q).apply_eq_smul⟩)
    have hRHnear : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
        RankineHugoniot flux p.2 (R p) (C.speed p.2) := by
      filter_upwards [ball_mem_nhds ((0 : ℝ), q₀) hδ] with p hp
      rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hp
      exact (hcontact p.2 hp.2 p.1 hp.1).2
    have hentropy := eventually_contact_entropy_of_rankineHugoniot hR hRzero hRHnear
    filter_upwards [hTnorm, hqnorm, hspeedLeft, hbranch, hentropy,
      ball_mem_nhds ((0 : ℝ), q₀) hδ] with p hTp hqp hspeedL hbranchp hep hp
    have hTR := hbranchp (Or.inl hgn)
    rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hp
    obtain ⟨hspeed, hRH⟩ := hcontact p.2 hp.2 p.1 hp.1
    rw [hTR] at hTp ⊢
    exact exists_bounded_entropy_elementary_discontinuity hRH (fun E ↦ (hep E.toEntropyPair).le)
      (.contact (C.speed p.2) ⟨hRH, rfl, hspeed.symm⟩) hspeedL.1.le hspeedL.2.le hqp hTp

end PDE.Hyperbolic.ConservationLaw.System
