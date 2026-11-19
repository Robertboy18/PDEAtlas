/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.ForwardRegularity
public import PDE.Fluid.NavierStokes.Nonlinearity.ProfileTransport
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarForward

/-!
# Parabolic smoothing of forward mild solutions in similarity variables

Let `S₀` be the free self-similar heat evolution on vector `Hᵏ(ℝ³)` and `Π` the Leray
projection. A path `U` in vector `Hᵏ⁺¹`, continuous on `[σ, τ]`, is a forward mild solution if

`U t = S₀(t - σ) U σ + ∫ σ..t, Π S₀(t - s) (f s + A₀ s (U s)) ds`

for `σ < t ≤ τ`, where `A₀ s : Hᵏ⁺¹ → Hᵏ` is a bounded family losing one derivative and the
Duhamel integral gains it back. If `A₀ s` is the restriction of a bounded family
`A s : Hᵏ⁺² → Hᵏ⁺¹` and the forcing `f` is continuous in `Hᵏ⁺¹`, then `U` lies in `Hᵏ⁺²` at
times after `σ`, with the bound `C (t - σ)^(-1/2)`, and the lift solves the mild equation one
order higher from every later starting time. That equation is the hypothesis of the theorem at
the next order, so the theorem iterates, and the families of the next order may be built from
the regularity just gained.

The families may depend on time, so the theorem accepts a linearization around a
time-dependent field as an operator family, for example the transport by the solution itself
in the convection term, `A s v = -Π (U s · ∇ v)`, given at the two orders. The
convection `v ↦ (w · ∇) v` with a frozen coefficient `w ∈ Hᵐ`, `m ≥ 2`, is bounded from `Hᵐ⁺¹`
to `Hᵐ` (`NavierStokes.SobolevConvection.mixedConvection`). The profile transport
`v ↦ -Π (W · ∇ v + v · ∇ W)` with `W ∈ W^{k+2,∞}` is the constant case.

The forcing is taken one order above the Duhamel integrand. A forcing that is only continuous
with values in `Hᵏ` does not in general give a Duhamel integral in `Hᵏ⁺²`: maximal regularity
in spaces of continuous functions fails for the heat semigroup, by a theorem of Baillon. The
terms of a nonlinear equation that depend on the solution belong in the operator family, where
the Kato argument handles them.

## How it works

After a shift of time by `σ` we apply Kato's gain of regularity for forward mild solutions in its
abstract form, `PDE.Analysis.Evolution.exists_forwardMild_lift`, to the projected free gaining
kernels `projectedSelfsimilarHeatGainKernel 3 k` and `projectedSelfsimilarHeatGainKernel 3 (k + 1)`
and to the gaining free evolution `vectorSelfsimilarHeatGainKernel 3 (k + 1)`. Its hypotheses are
the bounds `C r^(-1/2)` of these three kernels
(`norm_projectedSelfsimilarHeatGainKernel_le_selfsimilarForwardGainConstant` and its two
companions), their compatibility with lowering the order, and the bounds and continuity of `A₀` and
`A`. Shifting the lift back in time gives the path `V` with the bound `C (t - σ)^(-1/2)` and the
mild equation from `σ`. The equation from a later time `σ'` follows by the semigroup property of the
free evolution (`PDE.Analysis.Evolution.eq_add_intervalIntegral_of_forwardMild`), once the new
forcing `f s + A s (V s)` is bounded by a multiple of `(s - σ)^(-1/2)`. The profile transport
theorem is the case of constant families.

## References

* J.-B. Baillon, "Caractère borné de certains générateurs de semi-groupes linéaires dans les espaces
  de Banach", *C. R. Acad. Sci. Paris Sér. A* 290 (1980), 757-760, Zbl 0436.47027.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open HeatEquation.WholeSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev

namespace NavierStokes.Selfsimilar

variable {k : ℕ}

/-! ### Gain of one order -/

/-- Parabolic smoothing of forward mild solutions. Let `U` be continuous on `[σ, τ]` in vector
`Hᵏ⁺¹(ℝ³)` and solve
`U t = S₀(t - σ) U σ + ∫ σ..t, Π S₀(t - s) (f s + A₀ s (U s)) ds` for `σ < t ≤ τ`, with a
forcing `f` continuous in `Hᵏ⁺¹` and bounded families `A₀ s : Hᵏ⁺¹ → Hᵏ`,
`A s : Hᵏ⁺² → Hᵏ⁺¹` with jointly continuous actions that agree after forgetting the top
order. Then `U` lies in `Hᵏ⁺²` at times after `σ`: there is a path `V` in `Hᵏ⁺²`, continuous
on `(σ, τ]` with `‖V t‖ ≤ C (t - σ)^(-1/2)`, whose lowering is `U`. It solves the mild
equation in `Hᵏ⁺²` with the gaining free evolution from `σ`, and with the free evolution from
every `σ' ∈ (σ, τ]`, which is the hypothesis of the next order.

The forcing lies one order above the Duhamel integrand, since continuity in `Hᵏ` alone does
not give the gained order; the parts of a nonlinear forcing that depend on the solution enter
through `A₀` and `A`. With `A s` the profile transport of a `W^{k+2,∞}` profile this is
`forwardMild_memSobolev_succ_profileTransport`. -/
theorem forwardMild_memSobolev_succ {σ τ a : ℝ}
    {A₀ : ℝ → VectorH 3 (k + 1) →L[ℝ] VectorH 3 k}
    {A : ℝ → VectorH 3 (k + 2) →L[ℝ] VectorH 3 (k + 1)}
    (hA₀c : ContinuousOn (fun p : ℝ × VectorH 3 (k + 1) ↦ A₀ p.1 p.2) (Icc σ τ ×ˢ univ))
    (hA₀ : ∀ s ∈ Icc σ τ, ‖A₀ s‖ ≤ a)
    (hAc : ContinuousOn (fun p : ℝ × VectorH 3 (k + 2) ↦ A p.1 p.2) (Icc σ τ ×ˢ univ))
    (hA : ∀ s ∈ Icc σ τ, ‖A s‖ ≤ a)
    (hlow : ∀ s ∈ Icc σ τ, ∀ v, vectorLower 3 k (A s v) = A₀ s (vectorLower 3 (k + 1) v))
    {f U : ℝ → VectorH 3 (k + 1)} (hfc : ContinuousOn f (Icc σ τ))
    (hUc : ContinuousOn U (Icc σ τ))
    (hU : ∀ t ∈ Ioc σ τ, U t = vectorSelfsimilarHeat 3 (k + 1) (t - σ).toNNReal (U σ) +
      ∫ s in σ..t, projectedSelfsimilarHeatGainKernel 3 k (t - s)
        (vectorLower 3 k (f s) + A₀ s (U s))) :
    ∃ V : ℝ → VectorH 3 (k + 2), ContinuousOn V (Ioc σ τ) ∧
      (∃ C, ∀ t ∈ Ioc σ τ, ‖V t‖ ≤ C * (t - σ) ^ (-(1 / 2 : ℝ))) ∧
      (∀ t ∈ Ioc σ τ, vectorLower 3 (k + 1) (V t) = U t) ∧
      (∀ t ∈ Ioc σ τ, V t = vectorSelfsimilarHeatGainKernel 3 (k + 1) (t - σ) (U σ) +
        ∫ s in σ..t, projectedSelfsimilarHeatGainKernel 3 (k + 1) (t - s) (f s + A s (V s))) ∧
      ∀ σ' ∈ Ioc σ τ, ∀ t ∈ Icc σ' τ,
        V t = vectorSelfsimilarHeat 3 (k + 2) (t - σ').toNNReal (V σ') +
          ∫ s in σ'..t, projectedSelfsimilarHeatGainKernel 3 (k + 1) (t - s)
            (f s + A s (V s)) := by
  rcases le_or_gt τ σ with hτσ | hστ
  · have hempty : ∀ t ∈ Ioc σ τ, False := fun t ht ↦ (ht.1.trans_le ht.2).not_ge hτσ
    exact ⟨0, continuousOn_const, ⟨0, fun t ht ↦ (hempty t ht).elim⟩,
      fun t ht ↦ (hempty t ht).elim, fun t ht ↦ (hempty t ht).elim,
      fun σ' hσ' ↦ (hempty σ' hσ').elim⟩
  have ha : 0 ≤ a := (ContinuousLinearMap.opNorm_nonneg _).trans (hA σ ⟨le_rfl, hστ.le⟩)
  have hK₀b : ∀ r, 0 < r → ‖projectedSelfsimilarHeatGainKernel 3 k r‖ ≤
      selfsimilarForwardGainConstant 3 k * r ^ (-(1 / 2 : ℝ)) := fun _ ↦
    norm_projectedSelfsimilarHeatGainKernel_le_selfsimilarForwardGainConstant (by norm_num)
  have hK₁b : ∀ r, 0 < r → ‖projectedSelfsimilarHeatGainKernel 3 (k + 1) r‖ ≤
      selfsimilarForwardGainConstant 3 k * r ^ (-(1 / 2 : ℝ)) := fun _ ↦
    norm_projectedSelfsimilarHeatGainKernel_succ_le_selfsimilarForwardGainConstant (by norm_num)
  have hΓb : ∀ r, 0 < r → ‖vectorSelfsimilarHeatGainKernel 3 (k + 1) r‖ ≤
      selfsimilarForwardGainConstant 3 k * r ^ (-(1 / 2 : ℝ)) := fun _ ↦
    norm_vectorSelfsimilarHeatGainKernel_succ_le_selfsimilarForwardGainConstant (by norm_num)
  -- Shift time by `σ`.
  have hshift : ∀ s ∈ Icc 0 (τ - σ), s + σ ∈ Icc σ τ := fun s hs ↦
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hA₀c' : ContinuousOn (fun p : ℝ × VectorH 3 (k + 1) ↦ A₀ (p.1 + σ) p.2)
      (Icc 0 (τ - σ) ×ˢ univ) :=
    hA₀c.comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn
      fun p hp ↦ ⟨hshift p.1 hp.1, mem_univ _⟩
  have hAc' : ContinuousOn (fun p : ℝ × VectorH 3 (k + 2) ↦ A (p.1 + σ) p.2)
      (Icc 0 (τ - σ) ×ˢ univ) :=
    hAc.comp ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn
      fun p hp ↦ ⟨hshift p.1 hp.1, mem_univ _⟩
  have hfc' : ContinuousOn (fun s ↦ f (s + σ)) (Icc 0 (τ - σ)) :=
    hfc.comp (continuousOn_id.add continuousOn_const) hshift
  have hUc' : ContinuousOn (fun s ↦ U (s + σ)) (Icc 0 (τ - σ)) :=
    hUc.comp (continuousOn_id.add continuousOn_const) hshift
  have hU' : ∀ t ∈ Ioc 0 (τ - σ), U (t + σ) =
      vectorSelfsimilarHeat 3 (k + 1) t.toNNReal (U (0 + σ)) +
        forwardDuhamel (projectedSelfsimilarHeatGainKernel 3 k)
          (fun s ↦ vectorLower 3 k (f (s + σ)) + A₀ (s + σ) (U (s + σ))) t := by
    intro t ht
    have h := hU (t + σ) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [intervalIntegral_eq_forwardDuhamel_sub, add_sub_cancel_right] at h
    rwa [zero_add]
  obtain ⟨V, hVc, ⟨C, hC⟩, hV⟩ := exists_forwardMild_lift (vectorLower 3 (k + 1))
    (vectorLower 3 k) (K₀ := projectedSelfsimilarHeatGainKernel 3 k)
    (K₁ := projectedSelfsimilarHeatGainKernel 3 (k + 1))
    (S := fun r ↦ vectorSelfsimilarHeat 3 (k + 1) r.toNNReal)
    (Γ := vectorSelfsimilarHeatGainKernel 3 (k + 1)) (M := selfsimilarForwardGainConstant 3 k)
    continuousOn_projectedSelfsimilarHeatGainKernel_apply
    hK₀b
    continuousOn_projectedSelfsimilarHeatGainKernel_apply
    hK₁b
    (fun r x ↦ vectorLower_succ_projectedSelfsimilarHeatGainKernel r x)
    continuousOn_vectorSelfsimilarHeatGainKernel_apply
    hΓb
    (fun _ hr x ↦ vectorLower_vectorSelfsimilarHeatGainKernel hr x)
    hA₀c' (fun s hs ↦ hA₀ _ (hshift s hs)) hAc' (fun s hs ↦ hA _ (hshift s hs))
    (fun s hs v ↦ hlow _ (hshift s hs) v) hfc' hUc' hU'
  have hmem : ∀ t ∈ Ioc σ τ, t - σ ∈ Ioc 0 (τ - σ) := fun t ht ↦
    ⟨sub_pos.mpr ht.1, by linarith [ht.2]⟩
  rw [zero_add] at hV
  -- The forcing of the lifted equation, shifted to start at zero.
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc'
  have hGc : ContinuousOn (fun s ↦ f (s + σ) + A (s + σ) (V s)) (Ioc 0 (τ - σ)) :=
    (hfc'.mono Ioc_subset_Icc_self).add (hAc'.comp (continuousOn_id.prodMk hVc)
      fun s hs ↦ ⟨Ioc_subset_Icc_self hs, mem_univ _⟩)
  have hGb : ∀ s ∈ Ioc 0 (τ - σ), ‖f (s + σ) + A (s + σ) (V s)‖ ≤
      (max B 0 + a * max C 0) * s ^ (-(1 / 2 : ℝ)) * Real.exp (1 * s) := by
    intro s hs
    have hp := Real.rpow_nonneg hs.1.le (-(1 / 2 : ℝ))
    have he : 1 ≤ Real.exp (1 * s) := Real.one_le_exp (by linarith [hs.1])
    have hfb : ‖f (s + σ)‖ ≤ max B 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (1 * s) :=
      ((hB s (Ioc_subset_Icc_self hs)).trans (le_max_left _ _)).trans
        (le_mul_rpow_neg_one_half_mul_exp (le_max_right _ _) hs.1)
    have hVb : ‖V s‖ ≤ max C 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (1 * s) :=
      (hC s hs).trans <| (mul_le_mul_of_nonneg_right (le_max_left _ _) hp).trans
        (le_mul_of_one_le_right (mul_nonneg (le_max_right _ _) hp) he)
    calc
      _ ≤ ‖f (s + σ)‖ + ‖A (s + σ)‖ * ‖V s‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl ((A (s + σ)).le_opNorm _))
      _ ≤ max B 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (1 * s) +
          a * (max C 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (1 * s)) :=
        add_le_add hfb (mul_le_mul (hA _ (hshift s (Ioc_subset_Icc_self hs))) hVb
          (norm_nonneg _) ha)
      _ = _ := by ring
  have hgain : ∀ t ∈ Ioc σ τ, V (t - σ) =
      vectorSelfsimilarHeatGainKernel 3 (k + 1) (t - σ) (U σ) +
        ∫ s in σ..t, projectedSelfsimilarHeatGainKernel 3 (k + 1) (t - s)
          (f s + A s (V (s - σ))) := by
    intro t ht
    rw [(hV (t - σ) (hmem t ht)).2, intervalIntegral_eq_forwardDuhamel_sub]
    simp only [add_sub_cancel_right]
  refine ⟨fun t ↦ V (t - σ), hVc.comp (continuousOn_id.sub continuousOn_const) hmem,
    ⟨C, fun t ht ↦ hC _ (hmem t ht)⟩, fun t ht ↦ ?_, hgain, fun σ' hσ' t ht ↦ ?_⟩
  · rw [(hV (t - σ) (hmem t ht)).1, sub_add_cancel]
  · have h := eq_add_intervalIntegral_of_forwardMild
      (S := fun r ↦ vectorSelfsimilarHeat 3 (k + 2) r.toNNReal)
      continuousOn_projectedSelfsimilarHeatGainKernel_apply
      hK₁b
      (fun a ha b hb x ↦ vectorSelfsimilarHeat_projectedSelfsimilarHeatGainKernel ha hb x)
      (fun a ha b hb x ↦ vectorSelfsimilarHeat_vectorSelfsimilarHeatGainKernel ha hb x)
      hGc hGb (fun t ht ↦ (hV t ht).2) (sub_pos.mpr hσ'.1) (sub_le_sub_right ht.1 σ)
      (by linarith [ht.2])
    have hint := intervalIntegral.integral_comp_add_right (a := σ' - σ) (b := t - σ)
      (fun x ↦ projectedSelfsimilarHeatGainKernel 3 (k + 1) (t - x)
        (f x + A x (V (x - σ)))) σ
    simp only [sub_add_cancel, add_sub_cancel_right] at hint
    have hint' : ∫ s in (σ' - σ)..(t - σ), projectedSelfsimilarHeatGainKernel 3 (k + 1)
        (t - σ - s) (f (s + σ) + A (s + σ) (V s)) =
        ∫ s in σ'..t, projectedSelfsimilarHeatGainKernel 3 (k + 1) (t - s)
          (f s + A s (V (s - σ))) := by
      rw [← hint]
      exact intervalIntegral.integral_congr fun s _ ↦ by
        simp only [show t - (s + σ) = t - σ - s by ring]
    rwa [hint', show t - σ - (σ' - σ) = t - σ' by ring] at h

/-! ### The profile transport -/

/-- Parabolic smoothing for the profile transport. For a profile `W` with `k + 2` weak
derivatives in `L∞`, a forward mild solution in `Hᵏ⁺¹` of
`U t = S₀(t - σ) U σ + ∫ σ..t, Π S₀(t - s) (f s + L_W (U s)) ds` with
`L_W v = -Π (W · ∇ v + v · ∇ W)` and a forcing continuous in `Hᵏ⁺¹` lies in `Hᵏ⁺²` at times
after `σ`, with the conclusions of `forwardMild_memSobolev_succ` for the profile transport on
`Hᵏ⁺²`. -/
theorem forwardMild_memSobolev_succ_profileTransport {σ τ : ℝ}
    (W : Fin 3 → W^{k + 2,∞}(ℝ^3)) {f U : ℝ → VectorH 3 (k + 1)}
    (hfc : ContinuousOn f (Icc σ τ)) (hUc : ContinuousOn U (Icc σ τ))
    (hU : ∀ t ∈ Ioc σ τ, U t = vectorSelfsimilarHeat 3 (k + 1) (t - σ).toNNReal (U σ) +
      ∫ s in σ..t, projectedSelfsimilarHeatGainKernel 3 k (t - s)
        (vectorLower 3 k (f s) + SobolevConvection.profileTransport k
          (fun i ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (W i)) (U s))) :
    ∃ V : ℝ → VectorH 3 (k + 2), ContinuousOn V (Ioc σ τ) ∧
      (∃ C, ∀ t ∈ Ioc σ τ, ‖V t‖ ≤ C * (t - σ) ^ (-(1 / 2 : ℝ))) ∧
      (∀ t ∈ Ioc σ τ, vectorLower 3 (k + 1) (V t) = U t) ∧
      (∀ t ∈ Ioc σ τ, V t = vectorSelfsimilarHeatGainKernel 3 (k + 1) (t - σ) (U σ) +
        ∫ s in σ..t, projectedSelfsimilarHeatGainKernel 3 (k + 1) (t - s)
          (f s + SobolevConvection.profileTransport (k + 1) W (V s))) ∧
      ∀ σ' ∈ Ioc σ τ, ∀ t ∈ Icc σ' τ,
        V t = vectorSelfsimilarHeat 3 (k + 2) (t - σ').toNNReal (V σ') +
          ∫ s in σ'..t, projectedSelfsimilarHeatGainKernel 3 (k + 1) (t - s)
            (f s + SobolevConvection.profileTransport (k + 1) W (V s)) := by
  set T₀ := SobolevConvection.profileTransport k
    (fun i ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (W i))
  set T₁ := SobolevConvection.profileTransport (k + 1) W
  exact forwardMild_memSobolev_succ (A₀ := fun _ ↦ T₀) (A := fun _ ↦ T₁)
    (a := max ‖T₀‖ ‖T₁‖) (T₀.continuous.comp continuous_snd).continuousOn
    (fun _ _ ↦ le_max_left _ _) (T₁.continuous.comp continuous_snd).continuousOn
    (fun _ _ ↦ le_max_right _ _)
    (fun _ _ v ↦ SobolevConvection.vectorLowerOrderCLM_profileTransport (Nat.le_succ k) W v)
    hfc hUc hU

end NavierStokes.Selfsimilar
