/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.PerturbedMild
public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileSemigroupSobolev

/-!
# Forward mild solutions of the profile evolution

Let `S` be the self-similar evolution around a profile on vector `Hᵏ⁺¹`, with generator
`L₀ - Π B` for the transport `B` from `Hᵏ⁺¹` to `Hᵏ`, and let `S(r) Π` be its gaining path from
vector `Hᵏ`, applied after the Leray projection. A path `U` in `Hᵏ⁺¹` that solves the forward
equation of the profile evolution with a forcing `F` in `Hᵏ`,

`U t = S (t - σ) (U σ) + ∫_σ^t S(t - r) (Π F r) dr`,

solves the forward equation of the free self-similar evolution `S₀` with the transport moved into
the forcing,

`U τ = S₀ (τ - σ) (U σ) + ∫_σ^τ Π S₀(τ - r) (F r - B (U r)) dr`,

where `Π S₀(r)` is the projected free gain from `Hᵏ` to `Hᵏ⁺¹`
(`eq_freeMild_of_profileMild`). After the top order is forgotten, both the evolution on `Hᵏ⁺¹`
and its gaining path solve Duhamel equations with the bounded kernel `Π S₀(r)` on `Hᵏ`; the
general statement is `PDE.Analysis.Evolution.eq_freeMild_of_perturbedMild`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open HeatEquation.WholeSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev

namespace NavierStokes.Selfsimilar

variable {b : Fin 3 → DerivLp 3 ∞ Set.univ} {c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ} {k : ℕ}
  (hk : ProfileCoefficientBounds k b c) (hk' : ProfileCoefficientBounds (k + 1) b c)

/-- At positive times the gaining path from `Hᵏ` of a field in `Hᵏ⁺¹` with the top order
forgotten is the evolution of the field on `Hᵏ⁺¹`. -/
theorem profileGain_vectorLower {s : ℝ} (hs : 0 < s) (u : VectorH 3 (k + 1)) :
    profileGain k b c hk s (vectorLower 3 k u) =
      profileSemigroup (k + 1) b c hk' s.toNNReal u := by
  apply vectorLower_injective 3 k
  have h := congrArg (fun L ↦ L (vectorLower 3 k u))
    (vectorLower_comp_profileGain hk (t := s.toNNReal) (Real.toNNReal_pos.mpr hs))
  simp only [ContinuousLinearMap.comp_apply, Real.coe_toNNReal _ hs.le] at h
  rw [h, profileSemigroup_level_compat hk' hk]

/-- The Duhamel formula of the evolution on `Hᵏ⁺¹` with the top order forgotten: the transport
acts on the evolution itself and the kernel is the projected free evolution on `Hᵏ`. -/
theorem vectorLower_profileSemigroup_duhamel {t : ℝ} (ht : 0 ≤ t) (u : VectorH 3 (k + 1)) :
    vectorLower 3 k (profileSemigroup (k + 1) b c hk' t.toNNReal u) =
      vectorSelfsimilarHeat 3 k t.toNNReal (vectorLower 3 k u) -
        ∫ s in (0 : ℝ)..t, leraySobolev 3 k (vectorSelfsimilarHeat 3 k (t - s).toNNReal
          (hk.transport (profileSemigroup (k + 1) b c hk' s.toNNReal u))) := by
  have h1 := profileSemigroup_level_compat hk' hk t.toNNReal u
  have h2 := profileSemigroup_duhamel_lower hk t.toNNReal (vectorLower 3 k u)
  rw [vectorSelfsimilarHeatSemigroup_apply, Real.coe_toNNReal _ ht] at h2
  have h3 : ∫ s in (0 : ℝ)..t, leraySobolev 3 k (vectorSelfsimilarHeat 3 k (t - s).toNNReal
        (hk.transport (profileGain k b c hk s (vectorLower 3 k u)))) =
      ∫ s in (0 : ℝ)..t, leraySobolev 3 k (vectorSelfsimilarHeat 3 k (t - s).toNNReal
        (hk.transport (profileSemigroup (k + 1) b c hk' s.toNNReal u))) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with s hs
    rw [uIoc_of_le ht] at hs
    rw [profileGain_vectorLower hk hk' hs.1]
  rw [h1, h2, h3]

/-- The Duhamel formula of the gaining path after the Leray projection, with the gained order
forgotten. -/
theorem vectorLower_profileGain_leraySobolev {r : ℝ} (hr : 0 < r) (x : VectorH 3 k) :
    vectorLower 3 k (profileGain k b c hk r (leraySobolev 3 k x)) =
      leraySobolev 3 k (vectorSelfsimilarHeat 3 k r.toNNReal x) -
        ∫ s in (0 : ℝ)..r, leraySobolev 3 k (vectorSelfsimilarHeat 3 k (r - s).toNNReal
          (hk.transport (profileGain k b c hk s (leraySobolev 3 k x)))) := by
  have h1 := congrArg (fun L ↦ L (leraySobolev 3 k x))
    (vectorLower_comp_profileGain hk (t := r.toNNReal) (Real.toNNReal_pos.mpr hr))
  simp only [ContinuousLinearMap.comp_apply, Real.coe_toNNReal _ hr.le] at h1
  have h2 := profileSemigroup_duhamel_lower hk r.toNNReal (leraySobolev 3 k x)
  rw [vectorSelfsimilarHeatSemigroup_apply, Real.coe_toNNReal _ hr.le,
    ← leraySobolev_vectorSelfsimilarHeat] at h2
  rw [h1, h2]

/-- **Forward mild solutions of the profile evolution are free forward mild solutions.** If `U`
is continuous on `[σ, τ]` in vector `Hᵏ⁺¹`, `F` is continuous on `[σ, τ]` in vector `Hᵏ`, and
`U t = S (t - σ) (U σ) + ∫_σ^t S(t - r) (Π F r) dr` for `t ∈ [σ, τ]`, with `S` the evolution on
`Hᵏ⁺¹` and `S(r)` its gaining path from `Hᵏ`, then
`U τ = S₀ (τ - σ) (U σ) + ∫_σ^τ Π S₀(τ - r) (F r - B (U r)) dr` with the free evolution `S₀` and
the transport `B`. -/
theorem eq_freeMild_of_profileMild {U : ℝ → VectorH 3 (k + 1)} {F : ℝ → VectorH 3 k}
    {σ τ : ℝ} (hστ : σ ≤ τ) (hUc : ContinuousOn U (Icc σ τ)) (hFc : ContinuousOn F (Icc σ τ))
    (hU : ∀ t ∈ Icc σ τ, U t = profileSemigroup (k + 1) b c hk' (t - σ).toNNReal (U σ) +
      ∫ r in σ..t, profileGain k b c hk (t - r) (leraySobolev 3 k (F r))) :
    U τ = vectorSelfsimilarHeat 3 (k + 1) (τ - σ).toNNReal (U σ) +
      ∫ r in σ..τ, projectedSelfsimilarHeatGainKernel 3 k (τ - r) (F r - hk.transport (U r)) := by
  -- bounds of the free evolution and of the gaining path on `[0, τ - σ]`
  obtain ⟨M₀, -, hM₀⟩ := (vectorSelfsimilarHeatSemigroup 3 k).exists_norm_le_on_Icc
    (τ - σ).toNNReal
  set Cg := transportGainConstant hk.transport *
    Real.exp (transportWeight hk.transport * (τ - σ)) * ‖leraySobolev 3 k‖ with hCg
  set C := max Cg (selfsimilarForwardGainConstant 3 k) with hC
  have hP : ∀ r ∈ Icc 0 (τ - σ),
      ‖(leraySobolev 3 k).comp (vectorSelfsimilarHeat 3 k r.toNNReal)‖ ≤
        ‖leraySobolev 3 k‖ * M₀ := fun r hr ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
    mul_le_mul_of_nonneg_left (ContinuousLinearMap.ext (vectorSelfsimilarHeatSemigroup_apply _) ▸
      hM₀ r.toNNReal ⟨zero_le, Real.toNNReal_le_toNNReal hr.2⟩) (norm_nonneg _)
  have hGb : ∀ r, 0 < r → r ≤ τ - σ →
      ‖(profileGain k b c hk r).comp (leraySobolev 3 k)‖ ≤ C * r ^ (-(1 / 2 : ℝ)) := by
    intro r hr hrT
    have hw := (transportWeight_pos hk.transport).le
    have hpow := Real.rpow_nonneg hr.le (-(1 / 2 : ℝ))
    have hC0 := transportGainConstant_nonneg hk.transport
    calc
      _ ≤ ‖profileGain k b c hk r‖ * ‖leraySobolev 3 k‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (transportGainConstant hk.transport * r ^ (-(1 / 2 : ℝ)) *
            Real.exp (transportWeight hk.transport * (τ - σ))) * ‖leraySobolev 3 k‖ := by
        gcongr
        exact (norm_profileGain_le hk hr).trans (by gcongr)
      _ = Cg * r ^ (-(1 / 2 : ℝ)) := by rw [hCg]; ring
      _ ≤ C * r ^ (-(1 / 2 : ℝ)) := by gcongr; exact le_max_left _ _
  have hΓb : ∀ r, 0 < r → r ≤ τ - σ →
      ‖projectedSelfsimilarHeatGainKernel 3 k r‖ ≤ C * r ^ (-(1 / 2 : ℝ)) := fun r hr _ ↦
    (norm_projectedSelfsimilarHeatGainKernel_le_selfsimilarForwardGainConstant (by norm_num)
      hr).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _))
  have hPc : Continuous fun p : ℝ × VectorH 3 k ↦
      (leraySobolev 3 k).comp (vectorSelfsimilarHeat 3 k p.1.toNNReal) p.2 :=
    (leraySobolev 3 k).continuous.comp (((vectorSelfsimilarHeatSemigroup 3 k).continuous_apply.comp
      (continuous_real_toNNReal.prodMap continuous_id)).congr fun p ↦
        vectorSelfsimilarHeatSemigroup_apply _ _)
  have hGc : ContinuousOn (fun p : ℝ × VectorH 3 k ↦
      (profileGain k b c hk p.1).comp (leraySobolev 3 k) p.2) (Ioi 0 ×ˢ univ) := by
    have h : ContinuousOn (fun p : ℝ × VectorH 3 k ↦
        profileGain k b c hk p.1 (leraySobolev 3 k p.2)) (Ioi 0 ×ˢ univ) :=
      (continuousOn_profileGain_apply_prod hk).comp
        (continuousOn_fst.prodMk ((leraySobolev 3 k).continuous.comp continuous_snd).continuousOn)
        fun p hp ↦ ⟨hp.1, mem_univ _⟩
    exact h.congr fun p _ ↦ ContinuousLinearMap.comp_apply _ _ _
  exact eq_freeMild_of_perturbedMild (vectorLower_injective 3 k) hk.transport
    (S := fun t ↦ profileSemigroup (k + 1) b c hk' t.toNNReal)
    (Z₁ := fun t ↦ vectorSelfsimilarHeat 3 (k + 1) t.toNNReal)
    (Z₀ := fun t ↦ vectorSelfsimilarHeat 3 k t.toNNReal)
    (P := fun t ↦ (leraySobolev 3 k).comp (vectorSelfsimilarHeat 3 k t.toNNReal))
    (G := fun r ↦ (profileGain k b c hk r).comp (leraySobolev 3 k))
    (Γ := projectedSelfsimilarHeatGainKernel 3 k) hστ
    (fun t _ u ↦ vectorLower_vectorSelfsimilarHeat _ u)
    (fun r hr x ↦ vectorLower_projectedSelfsimilarHeatGainKernel hr x)
    (fun t ht u ↦ vectorLower_profileSemigroup_duhamel hk hk' ht u)
    (fun r hr x ↦ vectorLower_profileGain_leraySobolev hk hr x) hPc hP hGc hGb
    continuousOn_projectedSelfsimilarHeatGainKernel_apply hΓb
    (((profileSemigroup (k + 1) b c hk').continuous_orbit (U σ)).comp
      continuous_real_toNNReal).continuousOn hUc hFc hU

end NavierStokes.Selfsimilar
