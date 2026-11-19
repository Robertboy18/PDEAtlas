/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.PlanarShock
public import PDE.Analysis.Calculus.ImplicitRay.Transversality
import Mathlib.Analysis.Convex.Deriv
import CAS.ExactTactic

/-!
# Entropy production along Hugoniot curves

Differentiating the Rankine–Hugoniot relation expresses the derivative of
`[q] - σ[η]` as the shock-speed derivative times the convexity remainder
based at the right state. Increasing shock speed therefore gives entropy
dissipation on the negative-strength branch. Constant-speed branches have
zero entropy production. Only `C¹` compatible entropy pairs are needed.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

variable {m : ℕ} {flux : ℝ^m → ℝ^m}

/-- The tangent plane to a differentiable convex entropy lies below its graph. -/
theorem ConvexEntropyPair.relative_remainder_nonneg
    (E : ConvexEntropyPair flux) (left right : ℝ^m) :
    0 ≤ fderiv ℝ E.entropy right (right - left) - (E.entropy right - E.entropy left) := by
  have hc := E.entropy_convex.comp_affineMap (AffineMap.lineMap right left)
  have hd : HasDerivAt (E.entropy ∘ AffineMap.lineMap right left)
      (fderiv ℝ E.entropy right (left - right)) (0 : ℝ) := by
    simpa only [AffineMap.lineMap_apply_zero] using (E.entropy_contDiff.differentiable_one
        (AffineMap.lineMap right left (0 : ℝ))).hasFDerivAt.comp_hasDerivAt
          (0 : ℝ) AffineMap.hasDerivAt_lineMap
  have h := hc.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hd
  simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at h
  rw [show left - right = -(right - left) from (neg_sub _ _).symm, map_neg] at h
  linarith

/-- For a strictly convex differentiable entropy, the tangent remainder is
positive between distinct states. -/
theorem ConvexEntropyPair.relative_remainder_pos (E : ConvexEntropyPair flux)
    (hstrict : StrictConvexOn ℝ univ E.entropy) {left right : ℝ^m} (hne : left ≠ right) :
    0 < fderiv ℝ E.entropy right (right - left) - (E.entropy right - E.entropy left) := by
  let midpoint : ℝ^m := (1 / 2 : ℝ) • left + (1 / 2 : ℝ) • right
  have hmid : E.entropy midpoint < (1 / 2 : ℝ) * E.entropy left + (1 / 2 : ℝ) * E.entropy right :=
    hstrict.2 (mem_univ left) (mem_univ right) hne (by norm_num) (by norm_num) (by norm_num)
  have h := E.relative_remainder_nonneg midpoint right
  rw [show right - midpoint = (1 / 2 : ℝ) • (right - left) by simp only [midpoint]; module,
    map_smul, smul_eq_mul] at h
  linarith

/-- Differentiated Hugoniot relations give the exact derivative of entropy
production. -/
theorem EntropyPair.hasDerivAt_shock_production (E : EntropyPair flux) {S : ℝ → ℝ^m} {speed : ℝ → ℝ}
    {left tangent : ℝ^m} {s a : ℝ} (hS : HasDerivAt S tangent s) (hspeed : HasDerivAt speed a s)
    (hRH : ∀ᶠ t in 𝓝 s, RankineHugoniot flux left (S t) (speed t)) :
    HasDerivAt (fun t ↦ E.entropyFlux (S t) - E.entropyFlux left - speed t *
      (E.entropy (S t) - E.entropy left))
      (a * (fderiv ℝ E.entropy (S s) (S s - left) - (E.entropy (S s) - E.entropy left))) s := by
  have hF := ((E.flux_differentiable (S s)).hasFDerivAt.comp_hasDerivAt s hS).sub_const (flux left)
  have hR := hspeed.smul (hS.sub_const left)
  have heq := hF.unique (hR.congr_of_eventuallyEq hRH)
  have hη := (E.entropy_contDiff.differentiable_one (S s)).hasFDerivAt.comp_hasDerivAt s hS
  have hq := (E.entropyFlux_contDiff.differentiable_one (S s)).hasFDerivAt.comp_hasDerivAt s hS
  refine ((hq.sub_const (E.entropyFlux left)).sub
    (hspeed.mul (hη.sub_const (E.entropy left)))).congr_deriv ?_
  rw [E.fderiv_entropyFlux_apply, heq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  cas

/-- A Hugoniot curve with nondecreasing speed dissipates every convex entropy
on its negative-strength branch. The curve and speed need only be `C¹`. -/
theorem ConvexEntropyPair.shock_production_nonpos (E : ConvexEntropyPair flux) {S : ℝ → ℝ^m}
    {speed : ℝ → ℝ} {left : ℝ^m} {a : ℝ} (ha : a ≤ 0) (hzero : S 0 = left)
    (hS : ∀ s ∈ Icc a 0, DifferentiableAt ℝ S s)
    (hspeed : ∀ s ∈ Icc a 0, DifferentiableAt ℝ speed s) (hmono : MonotoneOn speed (Icc a 0))
    (hRH : ∀ s ∈ Icc a 0, RankineHugoniot flux left (S s) (speed s)) :
    E.entropyFlux (S a) - E.entropyFlux left ≤ speed a * (E.entropy (S a) - E.entropy left) := by
  let f := fun s ↦ E.entropyFlux (S s) - E.entropyFlux left -
    speed s * (E.entropy (S s) - E.entropy left)
  have hcont : ContinuousOn f (Icc a 0) := fun s hs ↦
    (((E.entropyFlux_contDiff.continuous.continuousAt.comp
      (hS s hs).continuousAt).sub continuousAt_const).sub ((hspeed s hs).continuousAt.mul
        ((E.entropy_contDiff.continuous.continuousAt.comp
          (hS s hs).continuousAt).sub continuousAt_const))).continuousWithinAt
  have hd (s : ℝ) (hs : s ∈ interior (Icc a 0)) : HasDerivAt f
        (deriv speed s * (fderiv ℝ E.entropy (S s) (S s - left) -
          (E.entropy (S s) - E.entropy left))) s :=
    E.toEntropyPair.hasDerivAt_shock_production (hS s (interior_subset hs)).hasDerivAt
      (hspeed s (interior_subset hs)).hasDerivAt
      (eventually_of_mem (mem_interior_iff_mem_nhds.mp hs) hRH)
  have hnonneg (s : ℝ) (hs : s ∈ interior (Icc a 0)) : 0 ≤ deriv speed s := by
    rw [← derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hs)]
    exact hmono.derivWithin_nonneg
  have hfm : MonotoneOn f (Icc a 0) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hcont
      (fun s hs ↦ (hd s hs).hasDerivWithinAt)
      (fun s hs ↦ mul_nonneg (hnonneg s hs) (E.relative_remainder_nonneg left (S s)))
  simpa only [f, hzero, sub_self, mul_zero, sub_zero, sub_nonpos] using
    hfm ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩ ha

/-- Positive shock-speed derivative at zero gives entropy dissipation uniformly
in strength and left state. The neighborhood is independent of the entropy pair. -/
theorem eventually_shock_entropy_of_positive_speed_deriv {S : ℝ × ℝ^m → ℝ^m} {speed : ℝ × ℝ^m → ℝ}
    {q₀ : ℝ^m} {a : ℝ} (hS : ContDiffAt ℝ 1 S (0, q₀)) (hspeed : ContDiffAt ℝ 1 speed (0, q₀))
    (hzero : ∀ᶠ q in 𝓝 q₀, S (0, q) = q)
    (hRH : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), RankineHugoniot flux p.2 (S p) (speed p))
    (hd : HasDerivAt (fun s ↦ speed (s, q₀)) a 0) (ha : 0 < a) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), p.1 ≤ 0 → ∀ E : ConvexEntropyPair flux,
      E.entropyFlux (S p) - E.entropyFlux p.2 ≤ speed p * (E.entropy (S p) - E.entropy p.2) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    ((hS.eventually (by simp)).and ((hspeed.eventually (by simp)).and hRH))
  obtain ⟨ε, hε, hmono⟩ :=
    PDE.Analysis.Calculus.exists_uniform_strictMonoOn_of_hasDerivAt hspeed hd ha
  have hz := (continuousAt_snd :
    ContinuousAt (Prod.snd : ℝ × ℝ^m → ℝ^m) (0, q₀)).tendsto.eventually hzero
  filter_upwards [ball_mem_nhds ((0 : ℝ), q₀) hδ,
    ball_mem_nhds ((0 : ℝ), q₀) hε, hz] with p hp hpε hzp hs E
  rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hp hpε
  have hsegment {s : ℝ} (hsp : s ∈ Icc p.1 0) : (s, p.2) ∈ ball ((0 : ℝ), q₀) δ := by
    rw [← ball_prod_same, Real.ball_zero_eq_Ioo]
    exact ⟨⟨hp.1.1.trans_le hsp.1, hsp.2.trans_lt hδ⟩, hp.2⟩
  exact E.shock_production_nonpos (S := fun s ↦ S (s, p.2)) (speed := fun s ↦ speed (s, p.2)) hs hzp
    (fun s hsp ↦ ((hball (hsegment hsp)).1.comp s
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt_one)
    (fun s hsp ↦ ((hball (hsegment hsp)).2.1.comp s
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt_one)
    ((hmono p.2 hpε.2).monotoneOn.mono (Icc_subset_Ioo hpε.1.1 hε))
    fun s hsp ↦ (hball (hsegment hsp)).2.2

/-- A connected constant-speed Hugoniot branch has zero production for every
compatible entropy pair. This includes the constructed contact curves. -/
theorem EntropyPair.contact_production_eq_zero (E : EntropyPair flux) {R : ℝ → ℝ^m} {left : ℝ^m}
    {speed s : ℝ} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I) (h0 : 0 ∈ I) (hs : s ∈ I)
    (hzero : R 0 = left) (hR : ∀ t ∈ I, DifferentiableAt ℝ R t)
    (hRH : ∀ t ∈ I, RankineHugoniot flux left (R t) speed) :
    E.entropyFlux (R s) - E.entropyFlux left = speed * (E.entropy (R s) - E.entropy left) := by
  let f := fun t ↦ E.entropyFlux (R t) - E.entropyFlux left -
    speed * (E.entropy (R t) - E.entropy left)
  have hd (t : ℝ) (ht : t ∈ I) : HasDerivAt f 0 t := by
    simpa only [zero_mul] using E.hasDerivAt_shock_production
      (hR t ht).hasDerivAt (hasDerivAt_const t speed) (eventually_of_mem (hI.mem_nhds ht) hRH)
  simpa only [f, hzero, sub_self, mul_zero, sub_zero, sub_eq_zero] using
    hI.is_const_of_deriv_eq_zero hconn
      (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (hd t ht).deriv) hs h0

/-- Constant-speed Hugoniot relations along a regular local family imply
entropy equality uniformly in strength and left state. -/
theorem eventually_contact_entropy_of_rankineHugoniot {R : ℝ × ℝ^m → ℝ^m} {speed : ℝ^m → ℝ}
    {q₀ : ℝ^m} (hR : ContDiffAt ℝ 1 R (0, q₀)) (hzero : ∀ᶠ q in 𝓝 q₀, R (0, q) = q)
    (hRH : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), RankineHugoniot flux p.2 (R p) (speed p.2)) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ E : EntropyPair flux, E.entropyFlux (R p) - E.entropyFlux p.2 =
      speed p.2 * (E.entropy (R p) - E.entropy p.2) := by
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.mem_nhds_iff.mp ((hR.eventually (by simp)).and hRH)
  have hz := (continuousAt_snd :
    ContinuousAt (Prod.snd : ℝ × ℝ^m → ℝ^m) (0, q₀)).tendsto.eventually hzero
  filter_upwards [ball_mem_nhds ((0 : ℝ), q₀) hδ, hz] with p hp hzp E
  rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hp
  have hmem {s : ℝ} (hs : s ∈ Ioo (-δ) δ) : (s, p.2) ∈ ball ((0 : ℝ), q₀) δ := by
    rw [← ball_prod_same, Real.ball_zero_eq_Ioo]
    exact ⟨hs, hp.2⟩
  exact E.contact_production_eq_zero (R := fun s ↦ R (s, p.2))
    isOpen_Ioo (convex_Ioo _ _).isPreconnected ⟨neg_lt_zero.mpr hδ, hδ⟩ hp.1 hzp
    (fun s hs ↦ ((hball (hmem hs)).1.comp s
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt_one) fun s hs ↦ (hball (hmem hs)).2

end PDE.Hyperbolic.ConservationLaw.System
