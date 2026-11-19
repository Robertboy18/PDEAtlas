/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Causality
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Testing
import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Propagation

/-!
# Backward-cone locality of physical Duhamel evolution

Forcings which agree inside a backward cone give identical displacement there.
Compact smooth terminal tests propagate backwards inside the cone; the
physical Duhamel testing identity therefore gives equal pairings. Local test
uniqueness identifies the L2 representatives. Restriction of the forcing
interval gives the conclusion at every time of a fixed closed interval.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set PDE PDE.Common Metric
open scoped ENNReal SchwartzMap

namespace WaveEquation.Fourier

/-- A compact terminal test inside a backward cone remains inside that cone
under the backward sine wave. -/
theorem realSolution_eq_zero_outside_backwardCone {n : ℕ} [Fact (0 < n)] (φ : 𝓢(ℝ^n, ℝ))
    (hφ : HasCompactSupport (φ : ℝ^n → ℝ)) (c : ℝ^n) {s b T : ℝ} (hsb : s ≤ b) (hTb : b < T)
    (hsub : tsupport (φ : ℝ^n → ℝ) ⊆ ball c (T - b)) {x : ℝ^n} (hx : x ∉ ball c (T - s)) :
    realSolution 0 φ (timeSpaceCons (b - s) x) = 0 := by
  have hR : ∃ R : ℝ, R < T - b ∧
      tsupport (φ : ℝ^n → ℝ) ⊆ closedBall c R := by
    by_cases he : (tsupport (φ : ℝ^n → ℝ)).Nonempty
    · obtain ⟨y, hy, hmax⟩ := hφ.exists_isMaxOn he
        ((continuous_id.dist continuous_const).continuousOn)
      exact ⟨dist y c, hsub hy, fun z hz ↦ hmax hz⟩
    · exact ⟨0, sub_pos.mpr hTb, fun y hy ↦ (he ⟨y, hy⟩).elim⟩
  obtain ⟨R, hR, hsupport⟩ := hR
  apply realSolution_eq_zero_of_radius_lt 0 φ c (sub_nonneg.mpr hsb) (fun _ _ ↦ rfl)
  · exact fun y hy ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ (not_le.mpr hy) (hsupport h))
  · have hx' : T - s ≤ dist x c := le_of_not_gt hx
    linarith

private theorem re_inner_duhamelL2_eq_of_forcing_eq {n : ℕ} [Fact (0 < n)] (a b T : ℝ) (hbT : b < T)
    (c : ℝ^n) (f g : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc a b)))
    {r q : ℝ → ℝ^n → ℝ}
    (hf : ∀ᵐ s ∂volume.restrict (Icc a b), (f s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (r s x : ℂ))
    (hg : ∀ᵐ s ∂volume.restrict (Icc a b), (g s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (q s x : ℂ))
    (heq : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ᵐ x ∂volume, x ∈ ball c (T - s) → r s x = q s x)
    (φ : 𝓢(ℝ^n, ℝ)) (hφ : HasCompactSupport (φ : ℝ^n → ℝ))
    (hφsub : tsupport (φ : ℝ^n → ℝ) ⊆ ball c (T - b)) :
    (inner ℂ ((φ.postcompCLM Complex.ofRealCLM).toLp 2 volume) (duhamelL2 a b b f)).re =
      (inner ℂ ((φ.postcompCLM Complex.ofRealCLM).toLp 2 volume) (duhamelL2 a b b g)).re := by
  rw [re_inner_duhamelL2_realSchwartz_eq_integral a b f φ hf,
    re_inner_duhamelL2_realSchwartz_eq_integral a b g φ hg]
  apply integral_congr_ae
  filter_upwards [heq, ae_restrict_mem measurableSet_Icc] with s hs hsb
  apply integral_congr_ae
  filter_upwards [hs] with x hx
  by_cases hxc : x ∈ ball c (T - s)
  · rw [hx hxc]
  · rw [realSolution_eq_zero_outside_backwardCone φ hφ c hsb.2 hbT hφsub hxc]
    simp only [mul_zero]

/-- L1L2 forcing which agrees inside a backward cone has identical physical
Duhamel displacement there. -/
theorem ae_re_duhamelL2_eq_on_ball_of_forcing_eq {n : ℕ} [Fact (0 < n)] (a b T : ℝ) (hbT : b < T)
    (c : ℝ^n) (f g : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc a b)))
    {r q : ℝ → ℝ^n → ℝ}
    (hf : ∀ᵐ s ∂volume.restrict (Icc a b), (f s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (r s x : ℂ))
    (hg : ∀ᵐ s ∂volume.restrict (Icc a b), (g s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (q s x : ℂ))
    (heq : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ᵐ x ∂volume, x ∈ ball c (T - s) → r s x = q s x) :
    ∀ᵐ x ∂volume, x ∈ ball c (T - b) → (duhamelL2 a b b f x).re = (duhamelL2 a b b g x).re := by
  have hfL : LocallyIntegrable (fun x ↦ (duhamelL2 a b b f x).re) volume :=
    ((Lp.memLp (duhamelL2 a b b f)).re).locallyIntegrable (by norm_num)
  have hgL : LocallyIntegrable (fun x ↦ (duhamelL2 a b b g x).re) volume :=
    ((Lp.memLp (duhamelL2 a b b g)).re).locallyIntegrable (by norm_num)
  have hz : ∀ᵐ x ∂volume, x ∈ ball c (T - b) →
      (duhamelL2 a b b f x).re - (duhamelL2 a b b g x).re = 0 := by
    apply isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hfL.sub hgL).locallyIntegrableOn _)
    intro ψ hψ hψc hψsub
    let φ : 𝓢(ℝ^n, ℝ) := hψc.toSchwartzMap hψ
    have hφ : HasCompactSupport (φ : ℝ^n → ℝ) := hψc
    have htest := re_inner_duhamelL2_eq_of_forcing_eq a b T hbT c f g hf hg heq φ hφ hψsub
    rw [re_inner_realSchwartz_eq_integral φ _ Filter.EventuallyEq.rfl,
      re_inner_realSchwartz_eq_integral φ _ Filter.EventuallyEq.rfl] at htest
    have hi := hfL.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    have hj := hgL.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    simp only [smul_eq_mul] at hi hj ⊢
    simp only [Pi.sub_apply, mul_sub]
    rw [integral_sub hi hj]
    exact sub_eq_zero.mpr htest
  filter_upwards [hz] with x hx hxc using sub_eq_zero.mp (hx hxc)

/-- Cone locality holds at every time of one fixed forcing interval, using
restriction of the same Bochner class to each proper prefix. -/
theorem ae_re_duhamelL2_eq_on_ball_of_forcing_eq_on_Icc {n : ℕ} [Fact (0 < n)] (a b T : ℝ)
    (hbT : b < T) (c : ℝ^n)
    (f g : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc a b))) {r q : ℝ → ℝ^n → ℝ}
    (hf : ∀ᵐ s ∂volume.restrict (Icc a b), (f s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (r s x : ℂ))
    (hg : ∀ᵐ s ∂volume.restrict (Icc a b), (g s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (q s x : ℂ))
    (heq : ∀ᵐ s ∂volume.restrict (Icc a b), ∀ᵐ x ∂volume, x ∈ ball c (T - s) → r s x = q s x) :
    ∀ t ∈ Icc a b, ∀ᵐ x ∂volume, x ∈ ball c (T - t) →
      (duhamelL2 a b t f x).re = (duhamelL2 a b t g x).re := by
  intro t ht
  have hμ : volume.restrict (Icc a t) ≤ volume.restrict (Icc a b) :=
    Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl
  let f' := Lp.restrictionCLMOfLE hμ f
  let g' := Lp.restrictionCLMOfLE hμ g
  have hf' : ∀ᵐ s ∂volume.restrict (Icc a t),
      (f' s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (r s x : ℂ) := by
    filter_upwards [Lp.restrictionCLMOfLE_apply_ae hμ f, ae_mono hμ hf] with s hs hsf using hs ▸ hsf
  have hg' : ∀ᵐ s ∂volume.restrict (Icc a t),
      (g' s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦ (q s x : ℂ) := by
    filter_upwards [Lp.restrictionCLMOfLE_apply_ae hμ g, ae_mono hμ hg] with s hs hsg using hs ▸ hsg
  have h := ae_re_duhamelL2_eq_on_ball_of_forcing_eq a t T (ht.2.trans_lt hbT)
    c f' g' hf' hg' (ae_mono hμ heq)
  have hDf : duhamelL2 a t t f' = duhamelL2 a b t f :=
    duhamelL2_restrict_right a b t t ht.2 le_rfl f
  have hDg : duhamelL2 a t t g' = duhamelL2 a b t g :=
    duhamelL2_restrict_right a b t t ht.2 le_rfl g
  rwa [hDf, hDg] at h

end WaveEquation.Fourier
