/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileSemigroup
public import PDE.Fluid.Incompressible.LerayProjection.TestField
public import PDE.Spaces.Sobolev.Calculus.Product.IntegrationByParts

/-!
# Tested weak form of the self-similar evolution around a profile

For a smooth compactly supported test field `φ` and `t > 0`, the evolution `S` around a profile with
bounded transport and stretching coefficients satisfies
`d/dt ⟪S(t)u, φ⟫ = ⟪S(t)u, L₀^† φ⟫ - ⟪Π B S(t)u, φ⟫`, where `L₀^† φ = Δφ - ½ ξ·∇φ - φ` is the formal
adjoint of the free self-similar generator and `B S(t)u` is the transport of the gaining path. With
bounded coefficients the transport term stays on the evolution, since moving it onto `φ` needs
derivatives of `b`. When the transport coefficients lie in `W^{1,∞}` it moves onto `φ`, and the
identity becomes `d/dt ⟪S(t)u, φ⟫ = ⟪S(t)u, L_U^† φ⟫` with `L_U^† φ` the formal adjoint of
`L_U = L₀ - Π B`.

## Main definitions

* `FreeTestedIdentity φ ψ`: the free evolution satisfies the tested identity for `φ`, with `ψ` in
  the place of `L₀^† φ`.
* `adjointTransport`: the formal adjoint `(B^† ψ)_j = -Σᵢ bᵢ ∂ᵢψⱼ - (Σᵢ ∂ᵢbᵢ) ψⱼ + Σᵢ cᵢⱼ ψᵢ` of the
  transport, for coefficients `bᵢ` that are the base functions of `B i ∈ W^{1,∞}`.
* `profileAdjoint`: the field `L_U^† φ = L₀^† φ - B^† Π φ`.

## Main results

* `profileSemigroup0_tested` and `hasDerivAt_profileSemigroup0_tested`: the tested identity in
  integrated and differentiated form.
* `hasDerivAt_profileSemigroup0_tested_of_divergenceFree`: for divergence-free `φ` the projection
  drops.
* `vectorL2Pairing_transport_eq`: `⟪B v, ψ⟫ = ⟪v, B^† ψ⟫` for `v, ψ ∈ H¹`.
* `hasDerivAt_profileSemigroup0_tested_adjoint`: `d/dt ⟪S(t)u, φ⟫ = ⟪S(t)u, L_U^† φ⟫`.

## How it works

The free evolution satisfies `FreeTestedIdentity` for `φ` and `L₀^† φ`:
`freeTestedIdentity_of_schwartz` proves it for Schwartz fields whose Fourier transforms are related
by the adjoint symbol, and `freeTestedIdentity_test` applies it to test fields. The profile
evolution is the free evolution minus a Duhamel integral of the free evolution of the projected
transport of the gaining path. Testing that integral against `φ`, we apply the free identity inside
it and swap the two time integrals over the triangle `0 < r ≤ s ≤ t`, where the integrand is
integrable by `integrableOn_profileTriangle`. This gives the integrated identity
`profileSemigroup0_tested_of_free`, and the fundamental theorem of calculus gives
`hasDerivAt_profileSemigroup0_tested_of_free`. For the adjoint form we use that the Leray projection
is self-adjoint, so `⟪Π B v, φ⟫ = ⟪B v, Π φ⟫` with `Π φ ∈ H¹`. Then `vectorL2Pairing_transport_eq`,
which is whole-space integration by parts against each `bᵢ ∈ W^{1,∞}` together with a transpose of
`c`, moves `B` onto `Π φ`, and the gaining path seen in `L²` is `S(t)u`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open HeatEquation.WholeSpace PDE.Analysis.Evolution SchwartzMap FourierTransform
open SobolevSpace.Fractional
open scoped ENNReal NNReal Sobolev BoundedContinuousFunction

namespace NavierStokes.Selfsimilar

section Tested

variable (b : Fin 3 → DerivLp 3 ∞ Set.univ) (c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ)
  (hk : ProfileCoefficientBounds 0 b c)

/-- The bounded transport of the coefficients `b` and `c`. -/
local notation "T₀" => (BoundedTransport.transport b c)

/-! ### The tested evolution identity -/

/-- The `L²` Duhamel formula with the projected free evolution after the transport as
kernel. -/
private theorem profileSemigroup0_eq_lower (t : ℝ≥0) (u : VectorH 3 0) :
    profileSemigroup0 b c hk t u = vectorSelfsimilarHeat 3 0 t u -
      ∫ r in (0 : ℝ)..t, transportLowerKernel T₀ (t - r)
        (profileGain0 b c r u) := by
  rw [profileSemigroup0_duhamel_l2, vectorSelfsimilarHeatSemigroup_apply]
  rfl

/-- The `L²` Duhamel formula at every nonnegative real time. -/
private theorem profileSemigroup0_toNNReal_eq {s : ℝ} (hs : 0 ≤ s) (u : VectorH 3 0) :
    profileSemigroup0 b c hk s.toNNReal u = vectorSelfsimilarHeat 3 0 s.toNNReal u -
      ∫ r in (0 : ℝ)..s, transportLowerKernel T₀ (s - r)
        (profileGain0 b c r u) := by
  rw [profileSemigroup0_eq_lower, Real.coe_toNNReal _ hs]

omit hk in
/-- The Duhamel integrand without gain along the gaining path is integrable on `[0, t]`. -/
private theorem intervalIntegrable_profileLowerKernel {t : ℝ} (ht : 0 ≤ t) (u : VectorH 3 0) :
    IntervalIntegrable (fun s ↦ transportLowerKernel T₀ (t - s) (profileGain0 b c s u))
      volume 0 t :=
  intervalIntegrable_transportLowerKernel _ ht u

omit hk in
/-- The kernel without gain is free evolution of the projected transport. -/
private theorem transportLowerKernel_eq_heat (ρ : ℝ) (v : VectorH 3 1) :
    transportLowerKernel T₀ ρ v = vectorSelfsimilarHeat 3 0
      ρ.toNNReal (leraySobolev 3 0 (BoundedTransport.transport b c v)) := by
  rw [transportLowerKernel_apply, leraySobolev_vectorSelfsimilarHeat]

/-- The free self-similar evolution satisfies the tested identity for the field `φ` with the
field `ψ`, which plays the role of the formal adjoint `L₀^† φ = Δφ - ½ ξ·∇φ - φ`. -/
def FreeTestedIdentity (φ ψ : VectorH 3 0) : Prop :=
  ∀ (g : VectorH 3 0) (t : ℝ≥0), vectorL2Pairing φ (vectorSelfsimilarHeat 3 0 t g) -
    vectorL2Pairing φ g =
      ∫ s in (0 : ℝ)..t, vectorL2Pairing ψ (vectorSelfsimilarHeat 3 0 s.toNNReal g)

/-- Vector fields with Schwartz components whose Fourier transforms are related by the adjoint
symbol satisfy the free tested identity. -/
theorem freeTestedIdentity_of_schwartz {φ ψ : VectorH 3 0} (Φ Ψ : Fin 3 → 𝓢(ℝ^3, ℂ))
    (hφ : ∀ j, baseL2 (φ j) = (Φ j).toLp 2) (hψ : ∀ j, baseL2 (ψ j) = (Ψ j).toLp 2)
    (hΨ : ∀ j k, (𝓕 (Ψ j) : 𝓢(ℝ^3, ℂ)) k =
      selfsimilarAdjointSymbol (⇑(𝓕 (Φ j) : 𝓢(ℝ^3, ℂ))) k) :
    FreeTestedIdentity φ ψ :=
  fun g t ↦ vectorSelfsimilarHeat_tested_of_schwartz Φ Ψ hφ hψ hΨ g t

omit hk in
theorem continuousOn_profileProjectedTransport (u : VectorH 3 0) :
    ContinuousOn (fun r ↦ leraySobolev 3 0 (BoundedTransport.transport b c (profileGain0 b c r u)))
      (Ioi 0) :=
  ((leraySobolev 3 0).comp T₀).continuous.comp_continuousOn
    (continuousOn_profileGain0_apply b c u)

omit hk in
theorem norm_profileProjectedTransport_le {r : ℝ} (hr : 0 < r) (u : VectorH 3 0) :
    ‖leraySobolev 3 0 (BoundedTransport.transport b c (profileGain0 b c r u))‖ ≤
      BoundedTransport.coefficientBound b c * ‖transportGainPath T₀ u‖ * r ^ (-(1 / 2 : ℝ)) *
        Real.exp (transportWeight T₀ * r) := by
  calc
    _ ≤ ‖BoundedTransport.transport b c (profileGain0 b c r u)‖ := norm_leraySobolev_le _
    _ ≤ BoundedTransport.coefficientBound b c * ‖profileGain0 b c r u‖ :=
      BoundedTransport.norm_transport_apply_le b c _
    _ ≤ BoundedTransport.coefficientBound b c * (‖transportGainPath T₀ u‖ * r ^ (-(1 / 2 : ℝ)) *
        Real.exp (transportWeight T₀ * r)) :=
      mul_le_mul_of_nonneg_left (norm_profileGain0_apply_le b c hr u)
        (BoundedTransport.coefficientBound_nonneg b c)
    _ = _ := by ring

omit hk in
theorem intervalIntegrable_pairing_profileProjectedTransport (φ : VectorH 3 0) {t : ℝ}
    (ht : 0 ≤ t) (u : VectorH 3 0) :
    IntervalIntegrable (fun r ↦ vectorL2Pairing φ
      (leraySobolev 3 0 (BoundedTransport.transport b c (profileGain0 b c r u)))) volume 0 t := by
  have hP := (vectorL2Pairing φ).continuous
  refine intervalIntegrable_of_continuousOn_Ioo ht
    (hP.comp_continuousOn ((continuousOn_profileProjectedTransport b c u).mono
      fun r hr ↦ hr.1))
    (g := fun r ↦ ‖vectorL2Pairing φ‖ * (BoundedTransport.coefficientBound b c *
      ‖transportGainPath T₀ u‖ * (r ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T₀ * r))))
    (((intervalIntegrable_rpow_neg_one_half 0 t).mul_continuousOn
      (g := fun r ↦ Real.exp (transportWeight T₀ * r)) (by fun_prop)).const_mul _ |>.const_mul _)
    ?_
  intro r hr
  calc
    _ ≤ ‖vectorL2Pairing φ‖ *
        ‖leraySobolev 3 0 (BoundedTransport.transport b c (profileGain0 b c r u))‖ :=
      (vectorL2Pairing φ).le_opNorm _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (ContinuousLinearMap.opNorm_nonneg _)
      calc
        _ ≤ _ := norm_profileProjectedTransport_le b c hr.1 u
        _ = _ := by ring

omit hk in
/-- The double Duhamel integrand is integrable on the triangle. -/
theorem integrableOn_profileTriangle (ψ : VectorH 3 0) (t : ℝ) (u : VectorH 3 0) :
    IntegrableOn (fun p : ℝ × ℝ ↦ if p.2 ≤ p.1 then
        vectorL2Pairing ψ (transportLowerKernel T₀ (p.1 - p.2) (profileGain0 b c p.2 u)) else 0)
      (Ioc 0 t ×ˢ Ioc 0 t) := by
  set K := selfsimilarGraphConstant 3 0 * ‖T₀‖ with hKdef
  have hK0 : 0 ≤ K := mul_nonneg (selfsimilarGraphConstant_nonneg 3 0) (norm_nonneg T₀)
  set C := ‖vectorL2Pairing ψ‖ * K * ‖transportGainPath T₀ u‖ * Real.exp (transportWeight T₀ * t)
  have hC : 0 ≤ C := by
    have := ContinuousLinearMap.opNorm_nonneg (vectorL2Pairing ψ)
    positivity
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hg : Integrable (fun z : ℝ × ℝ ↦ (1 : ℝ) * (C * z.2 ^ (-(1 / 2 : ℝ))))
      ((volume.restrict (Ioc (0 : ℝ) t)).prod (volume.restrict (Ioc (0 : ℝ) t))) :=
    (integrable_const (1 : ℝ)).mul_prod
      (((intervalIntegrable_rpow_neg_one_half 0 t).1).const_mul C)
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine hg.mono' ?_ ?_
  · have hγ : ContinuousOn (fun p : ℝ × ℝ ↦ profileGain0 b c p.2 u) (univ ×ˢ Ioi 0) :=
      (continuousOn_profileGain0_apply b c u).comp continuous_snd.continuousOn
        (fun p hp ↦ hp.2)
    have hpair : ContinuousOn (fun p : ℝ × ℝ ↦ (p.1 - p.2, profileGain0 b c p.2 u))
        (univ ×ˢ Ioi 0) :=
      (continuous_fst.sub continuous_snd).continuousOn.prodMk hγ
    have hK := ((vectorL2Pairing ψ).continuous.comp
      (continuous_transportLowerKernel_apply T₀)).comp_continuousOn hpair
    simp only [Function.comp_def] at hK
    have hmeas := (hK.mono (fun p (hp : p ∈ Ioc (0 : ℝ) t ×ˢ Ioc (0 : ℝ) t) ↦
        (⟨mem_univ _, hp.2.1⟩ : p ∈ univ ×ˢ Ioi (0 : ℝ)))).aestronglyMeasurable
      (μ := volume) (measurableSet_Ioc.prod measurableSet_Ioc)
    have hind := hmeas.indicator (measurableSet_le measurable_snd measurable_fst)
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    convert hind using 1
    funext p
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  · rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p
      ⟨_, hr, hrt⟩
    split_ifs with h
    · calc
        _ ≤ ‖vectorL2Pairing ψ‖ *
            ‖transportLowerKernel T₀ (p.1 - p.2) (profileGain0 b c p.2 u)‖ :=
          (vectorL2Pairing ψ).le_opNorm _
        _ ≤ ‖vectorL2Pairing ψ‖ * (K * (‖transportGainPath T₀ u‖ *
            p.2 ^ (-(1 / 2 : ℝ)) * Real.exp (transportWeight T₀ * p.2))) := by
          apply mul_le_mul_of_nonneg_left _ (ContinuousLinearMap.opNorm_nonneg _)
          exact ((transportLowerKernel T₀ _).le_of_opNorm_le
            (norm_transportLowerKernel_le _ _) _).trans
            (mul_le_mul_of_nonneg_left (norm_profileGain0_apply_le b c hr u) hK0)
        _ ≤ 1 * (C * p.2 ^ (-(1 / 2 : ℝ))) := by
          have hexp : Real.exp (transportWeight T₀ * p.2) ≤ Real.exp (transportWeight T₀ * t) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrt (transportWeight_pos T₀).le)
          have h2 := ContinuousLinearMap.opNorm_nonneg (vectorL2Pairing ψ)
          have h3 := Real.rpow_nonneg hr.le (-(1 / 2 : ℝ))
          have h4 := norm_nonneg (transportGainPath T₀ u)
          calc
            _ = (‖vectorL2Pairing ψ‖ * K * ‖transportGainPath T₀ u‖ *
                p.2 ^ (-(1 / 2 : ℝ))) * Real.exp (transportWeight T₀ * p.2) := by ring
            _ ≤ (‖vectorL2Pairing ψ‖ * K * ‖transportGainPath T₀ u‖ *
                p.2 ^ (-(1 / 2 : ℝ))) * Real.exp (transportWeight T₀ * t) :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
            _ = _ := by ring
    · rw [norm_zero]
      exact mul_nonneg zero_le_one (mul_nonneg hC (Real.rpow_nonneg hr.le _))

/-- The profile semigroup satisfies the tested identity whenever the free evolution does: for a
field `φ` with adjoint field `ψ`, `⟪S(t)u, φ⟫ - ⟪u, φ⟫ = ∫₀ᵗ (⟪S(s)u, ψ⟫ - ⟪Π B S(s)u, φ⟫) ds`,
where `B S(s)u` is the transport of the gaining path. -/
theorem profileSemigroup0_tested_of_free {φ ψ : VectorH 3 0} (hfree : FreeTestedIdentity φ ψ)
    (t : ℝ≥0) (u : VectorH 3 0) :
    vectorL2Pairing φ (profileSemigroup0 b c hk t u) - vectorL2Pairing φ u =
      ∫ s in (0 : ℝ)..t, (vectorL2Pairing ψ (profileSemigroup0 b c hk s.toNNReal u) -
        vectorL2Pairing φ (leraySobolev 3 0
          (BoundedTransport.transport b c (profileGain0 b c s u)))) := by
  rcases eq_zero_or_pos t with rfl | htpos
  · simp
  have ht : (0 : ℝ) ≤ t := t.coe_nonneg
  have ht' : (0 : ℝ) < t := htpos
  have hIK := intervalIntegrable_profileLowerKernel b c ht u
  have hIT := intervalIntegrable_pairing_profileProjectedTransport b c φ ht u
  have hcS : Continuous (fun s : ℝ ↦ vectorL2Pairing ψ (profileSemigroup0 b c hk s.toNNReal u)) :=
    (vectorL2Pairing ψ).continuous.comp
      (((profileSemigroup0 b c hk).continuous_orbit u).comp continuous_real_toNNReal)
  have hcS₀ : Continuous (fun s : ℝ ↦
      vectorL2Pairing ψ (vectorSelfsimilarHeat 3 0 s.toNNReal u)) :=
    (vectorL2Pairing ψ).continuous.comp
      ((continuous_vectorSelfsimilarHeat u).comp continuous_real_toNNReal)
  have hper : ∀ r ∈ uIcc (0 : ℝ) t,
      vectorL2Pairing φ (transportLowerKernel T₀ ((t : ℝ) - r) (profileGain0 b c r u)) =
        vectorL2Pairing φ (leraySobolev 3 0
          (BoundedTransport.transport b c (profileGain0 b c r u))) +
        ∫ σ in (0 : ℝ)..((t : ℝ) - r),
          vectorL2Pairing ψ (transportLowerKernel T₀ σ (profileGain0 b c r u)) := by
    intro r hr
    rw [uIcc_of_le ht] at hr
    have htr : 0 ≤ (t : ℝ) - r := sub_nonneg.mpr hr.2
    have h := hfree (leraySobolev 3 0 (BoundedTransport.transport b c (profileGain0 b c r u)))
      ((t : ℝ) - r).toNNReal
    rw [Real.coe_toNNReal _ htr] at h
    rw [transportLowerKernel_eq_heat, ← sub_eq_iff_eq_add', h]
    exact intervalIntegral.integral_congr fun σ _ ↦ by simp only [transportLowerKernel_eq_heat]
  have hI2 : IntervalIntegrable (fun r ↦ ∫ σ in (0 : ℝ)..((t : ℝ) - r),
      vectorL2Pairing ψ (transportLowerKernel T₀ σ (profileGain0 b c r u))) volume 0 t := by
    refine ((hIK.continuousLinearMap_comp (vectorL2Pairing φ)).sub hIT).congr fun r hr ↦ ?_
    rw [hper r (uIoc_subset_uIcc hr)]
    abel
  have hI3 : IntervalIntegrable (fun s ↦ ∫ r in (0 : ℝ)..s,
      vectorL2Pairing ψ (transportLowerKernel T₀ (s - r) (profileGain0 b c r u))) volume 0 t := by
    refine (hcS₀.sub hcS).intervalIntegrable 0 t |>.congr fun s hs ↦ ?_
    rw [uIoc_of_le ht] at hs
    change vectorL2Pairing ψ (vectorSelfsimilarHeat 3 0 s.toNNReal u) -
      vectorL2Pairing ψ (profileSemigroup0 b c hk s.toNNReal u) = _
    rw [profileSemigroup0_toNNReal_eq b c hk hs.1.le u, map_sub, sub_sub_cancel,
      ← (vectorL2Pairing ψ).intervalIntegral_comp_comm
        (intervalIntegrable_profileLowerKernel b c hs.1.le u)]
  have htri : (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s,
        vectorL2Pairing ψ (transportLowerKernel T₀ (s - r) (profileGain0 b c r u))) =
      ∫ r in (0 : ℝ)..t, ∫ σ in (0 : ℝ)..((t : ℝ) - r),
        vectorL2Pairing ψ (transportLowerKernel T₀ σ (profileGain0 b c r u)) := by
    rw [intervalIntegral_triangle_swap ht (integrableOn_profileTriangle b c ψ t u)]
    exact intervalIntegral.integral_congr fun r _ ↦ by
      simpa only [sub_self] using intervalIntegral.integral_comp_sub_right
        (fun σ ↦ vectorL2Pairing ψ (transportLowerKernel T₀ σ (profileGain0 b c r u))) r
        (a := r) (b := t)
  have eL : vectorL2Pairing φ (profileSemigroup0 b c hk t u) - vectorL2Pairing φ u =
      (∫ s in (0 : ℝ)..t, vectorL2Pairing ψ (vectorSelfsimilarHeat 3 0 s.toNNReal u)) -
        ((∫ r in (0 : ℝ)..t, vectorL2Pairing φ (leraySobolev 3 0
          (BoundedTransport.transport b c (profileGain0 b c r u)))) +
        ∫ r in (0 : ℝ)..t, ∫ σ in (0 : ℝ)..((t : ℝ) - r),
          vectorL2Pairing ψ (transportLowerKernel T₀ σ (profileGain0 b c r u))) := by
    rw [profileSemigroup0_eq_lower b c hk t u, map_sub,
      ← (vectorL2Pairing φ).intervalIntegral_comp_comm hIK,
      intervalIntegral.integral_congr hper, intervalIntegral.integral_add hIT hI2,
      ← hfree u t]
    abel
  have eR : (∫ s in (0 : ℝ)..t, (vectorL2Pairing ψ (profileSemigroup0 b c hk s.toNNReal u) -
        vectorL2Pairing φ (leraySobolev 3 0
          (BoundedTransport.transport b c (profileGain0 b c s u))))) =
      ((∫ s in (0 : ℝ)..t, vectorL2Pairing ψ (vectorSelfsimilarHeat 3 0 s.toNNReal u)) -
        ∫ r in (0 : ℝ)..t, ∫ σ in (0 : ℝ)..((t : ℝ) - r),
          vectorL2Pairing ψ (transportLowerKernel T₀ σ (profileGain0 b c r u))) -
        ∫ r in (0 : ℝ)..t, vectorL2Pairing φ (leraySobolev 3 0
          (BoundedTransport.transport b c (profileGain0 b c r u))) := by
    rw [intervalIntegral.integral_sub (hcS.intervalIntegrable 0 t) hIT, ← htri,
      ← intervalIntegral.integral_sub (hcS₀.intervalIntegrable 0 t) hI3]
    refine congrArg (· - _) (intervalIntegral.integral_congr fun s hs ↦ ?_)
    rw [uIcc_of_le ht] at hs
    change vectorL2Pairing ψ (profileSemigroup0 b c hk s.toNNReal u) =
      vectorL2Pairing ψ (vectorSelfsimilarHeat 3 0 s.toNNReal u) - ∫ r in (0 : ℝ)..s,
        vectorL2Pairing ψ (transportLowerKernel T₀ (s - r) (profileGain0 b c r u))
    rw [profileSemigroup0_toNNReal_eq b c hk hs.1 u, map_sub,
      ← (vectorL2Pairing ψ).intervalIntegral_comp_comm
        (intervalIntegrable_profileLowerKernel b c hs.1 u)]
  rw [eL, eR]
  ring

/-- The tested weak form of the profile semigroup, given the free tested identity: for `t > 0`,
`d/dt ⟪S(t)u, φ⟫ = ⟪S(t)u, ψ⟫ - ⟪Π B S(t)u, φ⟫`. -/
theorem hasDerivAt_profileSemigroup0_tested_of_free {φ ψ : VectorH 3 0}
    (hfree : FreeTestedIdentity φ ψ) (u : VectorH 3 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ vectorL2Pairing φ (profileSemigroup0 b c hk s.toNNReal u))
      (vectorL2Pairing ψ (profileSemigroup0 b c hk t.toNNReal u) -
        vectorL2Pairing φ (leraySobolev 3 0
          (BoundedTransport.transport b c (profileGain0 b c t u)))) t := by
  set f : ℝ → ℝ := fun s ↦ vectorL2Pairing ψ (profileSemigroup0 b c hk s.toNNReal u) -
    vectorL2Pairing φ (leraySobolev 3 0 (BoundedTransport.transport b c (profileGain0 b c s u)))
  have hcS : Continuous fun s : ℝ ↦ vectorL2Pairing ψ (profileSemigroup0 b c hk s.toNNReal u) :=
    (vectorL2Pairing ψ).continuous.comp
      (((profileSemigroup0 b c hk).continuous_orbit u).comp continuous_real_toNNReal)
  have hfc : ContinuousOn f (Ioi 0) :=
    hcS.continuousOn.sub ((vectorL2Pairing φ).continuous.comp_continuousOn
      (continuousOn_profileProjectedTransport b c u))
  have hint : IntervalIntegrable f volume 0 t := (hcS.intervalIntegrable 0 t).sub
    (intervalIntegrable_pairing_profileProjectedTransport b c φ ht.le u)
  have hderiv : HasDerivAt (fun s ↦ vectorL2Pairing φ u + ∫ r in (0 : ℝ)..s, f r) (f t) t := by
    have h := intervalIntegral.integral_hasDerivAt_right hint
      (hfc.stronglyMeasurableAtFilter isOpen_Ioi t ht) (hfc.continuousAt (Ioi_mem_nhds ht))
    simpa only [zero_add] using h.const_add (vectorL2Pairing φ u)
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  have h := profileSemigroup0_tested_of_free b c hk hfree s.toNNReal u
  rw [Real.coe_toNNReal _ hs.le] at h
  rw [← h]
  ring

/-! ### Smooth compactly supported test fields -/

omit hk in
/-- A smooth compactly supported test field `φ` and its formal adjoint
`L₀^† φ = Δφ - ½ ξ·∇φ - φ` satisfy the free tested identity. -/
theorem freeTestedIdentity_test (f : Fin 3 → ℝ^3 → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j))
    (hcs : ∀ j, HasCompactSupport (f j)) :
    FreeTestedIdentity (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
      (vectorOfMemLp (fun j ↦ selfsimilarAdjoint (f j))
        fun j ↦ memLp_selfsimilarAdjoint (hf j) (hcs j)) :=
  fun g t ↦ vectorSelfsimilarHeat_tested f hf hcs g t

/-- The tested weak form of the profile semigroup in integrated form: for a smooth compactly
supported test field `φ`, `⟪S(t)u, φ⟫ - ⟪u, φ⟫ = ∫₀ᵗ (⟪S(s)u, L₀^† φ⟫ - ⟪Π B S(s)u, φ⟫) ds`. -/
theorem profileSemigroup0_tested (f : Fin 3 → ℝ^3 → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j))
    (hcs : ∀ j, HasCompactSupport (f j)) (t : ℝ≥0) (u : VectorH 3 0) :
    vectorL2Pairing (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
        (profileSemigroup0 b c hk t u) -
      vectorL2Pairing (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j)) u =
      ∫ s in (0 : ℝ)..t, (vectorL2Pairing (vectorOfMemLp (fun j ↦ selfsimilarAdjoint (f j))
          fun j ↦ memLp_selfsimilarAdjoint (hf j) (hcs j)) (profileSemigroup0 b c hk s.toNNReal u) -
        vectorL2Pairing (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
          (leraySobolev 3 0 (BoundedTransport.transport b c (profileGain0 b c s u)))) :=
  profileSemigroup0_tested_of_free b c hk (freeTestedIdentity_test f hf hcs) t u

/-- The tested weak form of the profile semigroup: for a smooth compactly supported test field
`φ` and `t > 0`, `d/dt ⟪S(t)u, φ⟫ = ⟪S(t)u, L₀^† φ⟫ - ⟪Π B S(t)u, φ⟫`, where
`L₀^† φ = Δφ - ½ ξ·∇φ - φ` is the formal adjoint of the free self-similar generator and
`B S(t)u` is the transport of the gaining path. The coefficients are only bounded, so the
transport term stays on the evolution: moving it onto `φ` would need derivatives of `b`. -/
theorem hasDerivAt_profileSemigroup0_tested (f : Fin 3 → ℝ^3 → ℝ)
    (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hcs : ∀ j, HasCompactSupport (f j))
    (u : VectorH 3 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ vectorL2Pairing
        (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
        (profileSemigroup0 b c hk s.toNNReal u))
      (vectorL2Pairing (vectorOfMemLp (fun j ↦ selfsimilarAdjoint (f j))
          fun j ↦ memLp_selfsimilarAdjoint (hf j) (hcs j)) (profileSemigroup0 b c hk t.toNNReal u) -
        vectorL2Pairing (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
          (leraySobolev 3 0 (BoundedTransport.transport b c (profileGain0 b c t u)))) t :=
  hasDerivAt_profileSemigroup0_tested_of_free b c hk (freeTestedIdentity_test f hf hcs) u ht

/-- The tested weak form of the profile semigroup for a divergence-free test field `φ`:
for `t > 0`, `d/dt ⟪S(t)u, φ⟫ = ⟪S(t)u, L₀^† φ⟫ - ⟪B S(t)u, φ⟫`. -/
theorem hasDerivAt_profileSemigroup0_tested_of_divergenceFree (f : Fin 3 → ℝ^3 → ℝ)
    (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hcs : ∀ j, HasCompactSupport (f j))
    (hdiv : ∀ x, ∑ i, (PDE.partialDeriv i (f i)) x = 0) (u : VectorH 3 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ vectorL2Pairing
        (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
        (profileSemigroup0 b c hk s.toNNReal u))
      (vectorL2Pairing (vectorOfMemLp (fun j ↦ selfsimilarAdjoint (f j))
          fun j ↦ memLp_selfsimilarAdjoint (hf j) (hcs j)) (profileSemigroup0 b c hk t.toNNReal u) -
        vectorL2Pairing (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
          (BoundedTransport.transport b c (profileGain0 b c t u))) t := by
  have h := hasDerivAt_profileSemigroup0_tested b c hk f hf hcs u ht
  rwa [vectorL2Pairing_leraySobolev_of_eq
    (leraySobolev_vectorOfMemLp_of_divergenceFree f hf hcs hdiv)] at h

end Tested

/-! ### The formal adjoint -/

section Adjoint

variable (B : Fin 3 → W^{1,∞}(ℝ^3)) (c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ)

/-- The formal adjoint of the transport `v ↦ Σᵢ bᵢ ∂ᵢ v + c v` on `H¹` fields, for transport
coefficients `bᵢ` that are the base functions of `B i ∈ W^{1,∞}`:
`(B^† ψ)_j = -Σᵢ bᵢ ∂ᵢψⱼ - (Σᵢ ∂ᵢbᵢ) ψⱼ + Σᵢ cᵢⱼ ψᵢ`. It is the transport with the
coefficients `-b` and `cᵀ - (Σᵢ ∂ᵢbᵢ) I`. -/
def adjointTransport : VectorH 3 1 →L[ℝ] VectorH 3 0 :=
  BoundedTransport.transport (fun i ↦ -wkpBaseCoordinateCLM (B i)) fun j i ↦
    c i j - if j = i then ∑ l, wkpCoordinateCLM (singleDerivIndex 3 l) (B l) else 0

/-- Integration by parts moves the transport onto an `H¹` field: `⟪B v, ψ⟫ = ⟪v, B^† ψ⟫` for
`v, ψ ∈ H¹`, when the transport coefficients `bᵢ` are the base functions of `B i ∈ W^{1,∞}`. -/
theorem vectorL2Pairing_transport_eq {b : Fin 3 → DerivLp 3 ∞ Set.univ}
    (hB : ∀ i, wkpBaseCoordinateCLM (B i) = b i) (ψ v : VectorH 3 1) :
    vectorL2Pairing (vectorLower 3 0 ψ) (BoundedTransport.transport b c v) =
      vectorL2Pairing (adjointTransport B c ψ) (vectorLower 3 0 v) := by
  set d := ∑ l, wkpCoordinateCLM (singleDerivIndex 3 l) (B l) with hd
  have hsum_smul (w : DerivLp 3 2 Set.univ) :
      d • w = ∑ l, wkpCoordinateCLM (singleDerivIndex 3 l) (B l) • w := by
    let L : DerivLp 3 ∞ Set.univ →+ DerivLp 3 2 Set.univ :=
      AddMonoidHom.mk' (fun a ↦ a • w) fun a₁ a₂ ↦ Lp.smul_add a₁ a₂ w
    exact map_sum L _ Finset.univ
  have hibp (i j : Fin 3) :
      inner ℝ (wkpBaseCoordinateCLM (ψ j))
          (b i • wkpCoordinateCLM (singleDerivIndex 3 i) (v j)) =
        inner ℝ (-wkpBaseCoordinateCLM (B i) • wkpCoordinateCLM (singleDerivIndex 3 i) (ψ j))
            (wkpBaseCoordinateCLM (v j)) -
          inner ℝ (wkpCoordinateCLM (singleDerivIndex 3 i) (B i) • wkpBaseCoordinateCLM (ψ j))
            (wkpBaseCoordinateCLM (v j)) := by
    have h : inner ℝ (wkpBaseCoordinateCLM (B i) •
          wkpCoordinateCLM (singleDerivIndex 3 i) (v j)) (wkpBaseCoordinateCLM (ψ j)) +
        inner ℝ (wkpBaseCoordinateCLM (B i) • wkpCoordinateCLM (singleDerivIndex 3 i) (ψ j))
          (wkpBaseCoordinateCLM (v j)) =
        -inner ℝ (wkpCoordinateCLM (singleDerivIndex 3 i) (B i) • wkpBaseCoordinateCLM (v j))
          (wkpBaseCoordinateCLM (ψ j)) :=
      inner_mul_deriv_add_inner_mul_deriv_univ (B i) i (v j) (ψ j)
    have e1 : inner ℝ (wkpBaseCoordinateCLM (ψ j))
        (b i • wkpCoordinateCLM (singleDerivIndex 3 i) (v j)) =
        inner ℝ (wkpBaseCoordinateCLM (B i) • wkpCoordinateCLM (singleDerivIndex 3 i) (v j))
          (wkpBaseCoordinateCLM (ψ j)) := by
      rw [real_inner_comm, hB i]
    have e2 : inner ℝ (-wkpBaseCoordinateCLM (B i) •
        wkpCoordinateCLM (singleDerivIndex 3 i) (ψ j)) (wkpBaseCoordinateCLM (v j)) =
        -inner ℝ (wkpBaseCoordinateCLM (B i) • wkpCoordinateCLM (singleDerivIndex 3 i) (ψ j))
          (wkpBaseCoordinateCLM (v j)) := by
      rw [Lp.neg_smul, inner_neg_left]
    have e3 : inner ℝ (wkpCoordinateCLM (singleDerivIndex 3 i) (B i) •
        wkpBaseCoordinateCLM (ψ j)) (wkpBaseCoordinateCLM (v j)) =
        inner ℝ (wkpCoordinateCLM (singleDerivIndex 3 i) (B i) • wkpBaseCoordinateCLM (v j))
          (wkpBaseCoordinateCLM (ψ j)) := by
      rw [inner_lpSMul_left_eq_right, real_inner_comm]
    rw [e1, e2, e3]
    linarith
  have hdiag (j : Fin 3) :
      ∑ i, inner ℝ ((if j = i then d else 0) • wkpBaseCoordinateCLM (ψ i))
        (wkpBaseCoordinateCLM (v j)) =
        inner ℝ (d • wkpBaseCoordinateCLM (ψ j)) (wkpBaseCoordinateCLM (v j)) := by
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun i _ hij ↦ by
      rw [ite_eq_right (Ne.symm hij), Lp.zero_smul, inner_zero_left], ite_eq_left rfl]
  have hcoef (i j : Fin 3) :
      inner ℝ ((c i j - if j = i then d else 0) • wkpBaseCoordinateCLM (ψ i))
        (wkpBaseCoordinateCLM (v j)) =
        inner ℝ (c i j • wkpBaseCoordinateCLM (ψ i)) (wkpBaseCoordinateCLM (v j)) -
          inner ℝ ((if j = i then d else 0) • wkpBaseCoordinateCLM (ψ i))
            (wkpBaseCoordinateCLM (v j)) := by
    rw [sub_eq_add_neg, Lp.smul_add, Lp.neg_smul, inner_add_left, inner_neg_left, ← sub_eq_add_neg]
  have hdiv (j : Fin 3) :
      ∑ i, inner ℝ (wkpCoordinateCLM (singleDerivIndex 3 i) (B i) • wkpBaseCoordinateCLM (ψ j))
        (wkpBaseCoordinateCLM (v j)) =
        inner ℝ (d • wkpBaseCoordinateCLM (ψ j)) (wkpBaseCoordinateCLM (v j)) := by
    rw [hsum_smul, sum_inner]
  have hstretch : ∑ j, ∑ i, inner ℝ (wkpBaseCoordinateCLM (ψ j))
        (c j i • wkpBaseCoordinateCLM (v i)) =
      ∑ j, ∑ i, inner ℝ (c i j • wkpBaseCoordinateCLM (ψ i)) (wkpBaseCoordinateCLM (v j)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      (inner_lpSMul_left_eq_right _ _ _).symm
  simp only [vectorL2Pairing_apply, l2SobolevRow_apply, Lp.inner_euclideanTuple]
  change ∑ j, inner ℝ (wkpBaseCoordinateCLM (ψ j)) (BoundedTransport.scalarTransport b c j v) =
    ∑ j, inner ℝ (BoundedTransport.scalarTransport (fun i ↦ -wkpBaseCoordinateCLM (B i))
      (fun j i ↦ c i j - if j = i then d else 0) j ψ) (wkpBaseCoordinateCLM (v j))
  simp only [BoundedTransport.scalarTransport_apply, mulLpLeft_apply, inner_sum, sum_inner,
    inner_add_right, inner_add_left, Finset.sum_add_distrib, hibp, hcoef, Finset.sum_sub_distrib,
    hdiag, hdiv, hstretch]
  ring

/-- The formal adjoint `L_U^† φ = L₀^† φ - B^† Π φ` of the linearized self-similar operator
`L_U = L₀ - Π B` on a smooth compactly supported test field `φ`, with
`L₀^† φ = Δφ - ½ ξ·∇φ - φ` and the formal adjoint `B^†` of the transport, applied to the `H¹`
field `Π φ`. -/
def profileAdjoint (f : Fin 3 → ℝ^3 → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j))
    (hcs : ∀ j, HasCompactSupport (f j)) : VectorH 3 0 :=
  vectorOfMemLp (fun j ↦ selfsimilarAdjoint (f j))
      (fun j ↦ memLp_selfsimilarAdjoint (hf j) (hcs j)) -
    adjointTransport B c (leraySobolev 3 1 (testVectorH1 f hf hcs))

end Adjoint

/-- The tested weak form of the profile semigroup with the formal adjoint of the linearized
operator: when the transport coefficients `bᵢ` are the base functions of `B i ∈ W^{1,∞}`, for
every smooth compactly supported test field `φ` and `t > 0`,
`d/dt ⟪S(t)u, φ⟫ = ⟪S(t)u, L_U^† φ⟫` with `L_U^† φ = L₀^† φ - B^† Π φ`. -/
theorem hasDerivAt_profileSemigroup0_tested_adjoint (b : Fin 3 → DerivLp 3 ∞ Set.univ)
    (c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ) (hk : ProfileCoefficientBounds 0 b c)
    (B : Fin 3 → W^{1,∞}(ℝ^3)) (hB : ∀ i, wkpBaseCoordinateCLM (B i) = b i)
    (f : Fin 3 → ℝ^3 → ℝ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j))
    (hcs : ∀ j, HasCompactSupport (f j)) (u : VectorH 3 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ ↦ vectorL2Pairing
        (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
        (profileSemigroup0 b c hk s.toNNReal u))
      (vectorL2Pairing (profileAdjoint B c f hf hcs)
        (profileSemigroup0 b c hk t.toNNReal u)) t := by
  have h := hasDerivAt_profileSemigroup0_tested b c hk f hf hcs u ht
  have hlow : vectorLower 3 0 (profileGain0 b c t u) =
      profileSemigroup0 b c hk t.toNNReal u := by
    have := congrArg (fun L : VectorH 3 0 →L[ℝ] VectorH 3 0 ↦ L u)
      (vectorLower_comp_profileGain0 b c hk (Real.toNNReal_pos.mpr ht))
    simpa only [ContinuousLinearMap.comp_apply, Real.coe_toNNReal _ ht.le] using this
  have key : vectorL2Pairing (vectorOfMemLp f fun j ↦ memLp_of_test (hf j) (hcs j))
      (leraySobolev 3 0 (BoundedTransport.transport b c (profileGain0 b c t u))) =
      vectorL2Pairing (adjointTransport B c (leraySobolev 3 1 (testVectorH1 f hf hcs)))
        (profileSemigroup0 b c hk t.toNNReal u) := by
    rw [vectorL2Pairing_leraySobolev, ← vectorLower_testVectorH1 f hf hcs,
      ← vectorLower_leraySobolev, vectorL2Pairing_transport_eq B c hB, hlow]
  rw [key] at h
  rwa [profileAdjoint, vectorL2Pairing_sub_left]

end NavierStokes.Selfsimilar
