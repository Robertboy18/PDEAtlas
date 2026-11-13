/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.ForwardSmoothing
public import Mathlib.Analysis.Convolution

/-!
# Forward mild solutions of perturbed evolutions

Let `Z₀` and `Z₁` be the free evolution on spaces `E₀` and `E₁`, with an injective map
`ι : E₁ → E₀` forgetting one order of regularity and `ι ∘ Z₁ t = Z₀ t ∘ ι`, and let `S` be the
evolution on `E₁` obtained by perturbing the generator with an operator `B : E₁ → E₀` that loses
the extra order. Then `S` solves the Duhamel equation

`ι (S t u) = Z₀ t (ι u) - ∫₀ᵗ P (t - s) (B (S s u)) ds`,

where `P r : E₀ → E₀` is the bounded free kernel, and its forcing kernel `G r : E₀ → E₁` solves
`ι (G r x) = P r x - ∫₀ʳ P (r - s) (B (G s x)) ds`. A path `U` that solves the forward equation of
the perturbed evolution,

`U t = S (t - σ) (U σ) + ∫_σ^t G (t - r) (F r) dr`,

then solves the forward equation of the free evolution with the perturbation moved into the
forcing,

`U τ = Z₁ (τ - σ) (U σ) + ∫_σ^τ Γ (τ - r) (F r - B (U r)) dr`,

where `Γ r : E₀ → E₁` is the free gaining kernel, `ι ∘ Γ r = P r`
(`eq_freeMild_of_perturbedMild`). The proof forgets the extra order, expands both Duhamel
equations, and exchanges the order of the iterated forward integral by Fubini's theorem on a
triangle (`intervalIntegral_forward_comp_swap`). Forgetting the order first leaves only the
singularity `(q - r)^{-1/2}` of `G` on the diagonal, and the product of an indicator of an
interval with an integrable function of `q - r` is integrable on the plane.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution

variable {E F X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A forward integrand `r ↦ K (t - r) (f r)` on `[σ, t]` is integrable when the kernel acts
jointly continuously at positive lag with the bound `C r^{-1/2}` on `(0, t - σ]` and the
forcing is continuous on `[σ, t]`. -/
theorem intervalIntegrable_forwardIntegrand_of_continuousOn {K : ℝ → X →L[ℝ] E} {f : ℝ → X}
    {σ t C : ℝ} (hσt : σ ≤ t)
    (hKc : ContinuousOn (fun p : ℝ × X ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → r ≤ t - σ → ‖K r‖ ≤ C * r ^ (-(1 / 2 : ℝ)))
    (hf : ContinuousOn f (Icc σ t)) :
    IntervalIntegrable (fun r ↦ K (t - r) (f r)) volume σ t := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hsing : IntervalIntegrable (fun r : ℝ ↦ (t - r) ^ (-(1 / 2 : ℝ))) volume σ t := by
    have h := (intervalIntegrable_rpow_neg_one_half 0 (t - σ)).comp_sub_left t
    simp only [sub_zero, sub_sub_cancel] at h
    exact h.symm
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hσt, integrableOn_Ioc_iff_integrableOn_Ioo]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hσt,
    integrableOn_Ioc_iff_integrableOn_Ioo] at hsing
  have hcont : ContinuousOn (fun r ↦ K (t - r) (f r)) (Ioo σ t) :=
    hKc.comp ((continuousOn_const.sub continuousOn_id).prodMk (hf.mono Ioo_subset_Icc_self))
      fun r hr ↦ ⟨sub_pos.mpr hr.2, mem_univ _⟩
  refine (hsing.const_mul (C * D)).mono' (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  calc ‖K (t - r) (f r)‖ ≤ C * (t - r) ^ (-(1 / 2 : ℝ)) * D :=
        (K (t - r)).le_of_opNorm_le_of_le (hK _ (sub_pos.mpr hr.2) (by linarith [hr.1]))
          (hD r (Ioo_subset_Icc_self hr))
    _ = C * D * (t - r) ^ (-(1 / 2 : ℝ)) := by ring

/-- **Iterated forward integrals.** Let `A q` act jointly continuously for `q ∈ [σ, τ]` with
`‖A q‖ ≤ M`, let `K r` act jointly continuously at positive lag with `‖K r‖ ≤ C r^{-1/2}` for
`0 < r ≤ τ - σ`, and let `f` be continuous on `[σ, τ]`. Then the order of the iterated forward
integral can be exchanged:
`∫_σ^τ ∫_r^τ A q (K (q - r) (f r)) dq dr = ∫_σ^τ A q (∫_σ^q K (q - r) (f r) dr) dq`. -/
theorem intervalIntegral_forward_comp_swap [CompleteSpace E] [CompleteSpace F]
    {A : ℝ → E →L[ℝ] F} {K : ℝ → X →L[ℝ] E} {f : ℝ → X} {σ τ M C : ℝ} (hστ : σ ≤ τ)
    (hAc : ContinuousOn (fun p : ℝ × E ↦ A p.1 p.2) (Icc σ τ ×ˢ univ))
    (hA : ∀ q ∈ Icc σ τ, ‖A q‖ ≤ M)
    (hKc : ContinuousOn (fun p : ℝ × X ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → r ≤ τ - σ → ‖K r‖ ≤ C * r ^ (-(1 / 2 : ℝ)))
    (hf : ContinuousOn f (Icc σ τ)) :
    ∫ r in σ..τ, ∫ q in r..τ, A q (K (q - r) (f r)) =
      ∫ q in σ..τ, A q (∫ r in σ..q, K (q - r) (f r)) := by
  rcases eq_or_lt_of_le hστ with hστ' | hστ'
  · subst hστ'
    simp
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA σ ⟨le_rfl, hστ⟩)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD σ ⟨le_rfl, hστ⟩)
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hK (τ - σ) (sub_pos.mpr hστ') le_rfl)
    exact nonneg_of_mul_nonneg_left h (Real.rpow_pos_of_pos (sub_pos.mpr hστ') _)
  set Ψ : ℝ → ℝ → F := fun q r ↦ A q (K (q - r) (f r)) with hΨ
  -- the inner integral of the right side
  have hinner : ∀ q ∈ uIcc σ τ,
      ∫ r in σ..q, Ψ q r = A q (∫ r in σ..q, K (q - r) (f r)) := by
    intro q hq
    rw [uIcc_of_le hστ] at hq
    refine (A q).intervalIntegral_comp_comm ?_
    refine intervalIntegrable_forwardIntegrand_of_continuousOn hq.1 hKc (fun r hr hrq ↦ hK r hr ?_)
      (hf.mono (Icc_subset_Icc le_rfl hq.2))
    linarith [hq.2]
  -- the triangle integrand is integrable
  have hint : IntegrableOn (fun p : ℝ × ℝ ↦ if p.2 < p.1 then Ψ p.1 p.2 else 0)
      (Ioc σ τ ×ˢ Ioc σ τ) := by
    set R := Ioc σ τ ×ˢ Ioc σ τ
    set T : Set (ℝ × ℝ) := {p | p.2 < p.1}
    have hT : MeasurableSet T := measurableSet_lt measurable_snd measurable_fst
    have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
    have hfun : (fun p : ℝ × ℝ ↦ if p.2 < p.1 then Ψ p.1 p.2 else 0) =
        T.indicator (fun p ↦ Ψ p.1 p.2) := by
      funext p
      simp only [T, Set.indicator_apply, Set.mem_ofPred_eq]
    -- measurability: continuity on the open part of the triangle
    have hcont : ContinuousOn (fun p : ℝ × ℝ ↦ Ψ p.1 p.2) (T ∩ R) := by
      have hin : ContinuousOn (fun p : ℝ × ℝ ↦ K (p.1 - p.2) (f p.2)) (T ∩ R) :=
        hKc.comp ((continuous_fst.sub continuous_snd).continuousOn.prodMk
          (hf.comp continuous_snd.continuousOn fun p hp ↦ Ioc_subset_Icc_self hp.2.2))
          fun p hp ↦ ⟨sub_pos.mpr hp.1, mem_univ _⟩
      exact hAc.comp (continuous_fst.continuousOn.prodMk hin)
        fun p hp ↦ ⟨Ioc_subset_Icc_self hp.2.1, mem_univ _⟩
    have hmeas : AEStronglyMeasurable (T.indicator (fun p ↦ Ψ p.1 p.2))
        (volume.restrict R) := by
      rw [aestronglyMeasurable_indicator_iff hT, Measure.restrict_restrict hT]
      exact hcont.aestronglyMeasurable (hT.inter hR)
    -- the dominating function `M C D · 1_{(σ, τ]}(r) (q - r)^{-1/2} 1_{(0, τ - σ]}(q - r)`
    set φ : ℝ → ℝ := (Ioc σ τ).indicator fun _ ↦ 1
    set ψ : ℝ → ℝ := (Ioc 0 (τ - σ)).indicator fun x ↦ x ^ (-(1 / 2 : ℝ))
    have hφ : Integrable φ := (integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (measure_Ioc_lt_top.ne))
    have hψ : Integrable ψ := (integrable_indicator_iff measurableSet_Ioc).mpr
      (intervalIntegrable_rpow_neg_one_half 0 (τ - σ)).1
    have hg := (hφ.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hψ).const_mul
      (M * (C * D))
    rw [← Measure.volume_eq_prod] at hg
    rw [IntegrableOn, hfun]
    refine (hg.integrableOn (s := R)).mono' hmeas ?_
    filter_upwards [ae_restrict_mem hR] with p hp
    simp only [ContinuousLinearMap.mul_apply']
    have hp2 : p.2 ∈ Ioc σ τ := hp.2
    by_cases hlt : p.2 < p.1
    · have hpos : 0 < p.1 - p.2 := sub_pos.mpr hlt
      have hle : p.1 - p.2 ≤ τ - σ := by linarith [hp.1.2, hp.2.1]
      rw [Set.indicator_of_mem (show p ∈ T from hlt)]
      simp only [φ, ψ, Set.indicator_of_mem hp2, Set.indicator_of_mem
        (show p.1 - p.2 ∈ Ioc 0 (τ - σ) from ⟨hpos, hle⟩), one_mul]
      calc ‖Ψ p.1 p.2‖ ≤ M * (C * (p.1 - p.2) ^ (-(1 / 2 : ℝ)) * D) :=
            (A p.1).le_of_opNorm_le_of_le (hA _ (Ioc_subset_Icc_self hp.1))
              ((K _).le_of_opNorm_le_of_le (hK _ hpos hle) (hD _ (Ioc_subset_Icc_self hp2)))
        _ = M * (C * D) * (p.1 - p.2) ^ (-(1 / 2 : ℝ)) := by ring
    · rw [Set.indicator_of_notMem (show p ∉ T from hlt), norm_zero]
      have hφ0 : 0 ≤ φ p.2 := Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
      have hψ0 : 0 ≤ ψ (p.1 - p.2) :=
        Set.indicator_nonneg (fun x hx ↦ Real.rpow_nonneg hx.1.le _) _
      positivity
  -- the diagonal is a null set, so the indicator of `r ≤ q` gives the same integrand
  have hdiag : (volume : Measure (ℝ × ℝ)) {p | p.2 = p.1} = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_eq_fun measurable_snd
      measurable_fst)]
    have hslice : ∀ x : ℝ, Prod.mk x ⁻¹' {p : ℝ × ℝ | p.2 = p.1} = {x} := fun x ↦ by
      ext y
      simp
    simp only [hslice, measure_singleton, lintegral_zero]
  have hint' : IntegrableOn (fun p : ℝ × ℝ ↦ if p.2 ≤ p.1 then Ψ p.1 p.2 else 0)
      (Ioc σ τ ×ˢ Ioc σ τ) := by
    refine hint.congr_fun_ae (ae_restrict_of_ae ?_)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hdiag] with p hp
    have hne : p.2 ≠ p.1 := hp
    by_cases hlt : p.2 < p.1
    · simp [hlt, hlt.le]
    · have hnle : ¬p.2 ≤ p.1 := fun hle ↦ hlt (lt_of_le_of_ne hle hne)
      simp [hlt, hnle]
  rw [← intervalIntegral_triangle_swap hστ hint']
  exact intervalIntegral.integral_congr hinner

section Perturbation

variable {E₀ E₁ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]

omit [CompleteSpace E₀] [CompleteSpace E₁] in
/-- A Duhamel integral from `0` to `τ - a` is the forward integral from `a` to `τ`. -/
private theorem intervalIntegral_duhamel_shift (P : ℝ → E₀ →L[ℝ] E₀) (B : E₁ →L[ℝ] E₀)
    (g : ℝ → E₁) (a τ : ℝ) :
    ∫ s in (0 : ℝ)..(τ - a), P (τ - a - s) (B (g s)) =
      ∫ q in a..τ, P (τ - q) (B (g (q - a))) := by
  simpa only [add_zero, add_sub_cancel, add_sub_cancel_left, sub_add_eq_sub_sub] using
    (intervalIntegral.integral_comp_add_left (fun q ↦ P (τ - q) (B (g (q - a)))) a
      (a := 0) (b := τ - a))

/-- **Perturbed forward mild solutions are free forward mild solutions.** Let `ι : E₁ → E₀` be
injective, let the free evolution satisfy `ι ∘ Z₁ t = Z₀ t ∘ ι`, let `Γ r` be its gaining kernel
with `ι ∘ Γ r = P r` at positive `r`, and let the perturbed evolution `S` and its forcing kernel
`G` solve `ι (S t u) = Z₀ t (ι u) - ∫₀ᵗ P (t - s) (B (S s u)) ds` and
`ι (G r x) = P r x - ∫₀ʳ P (r - s) (B (G s x)) ds`. If `P` acts jointly continuously and is
bounded on `[0, τ - σ]`, `G` and `Γ` act jointly continuously at positive lag with the bound
`C r^{-1/2}` on `(0, τ - σ]`, and `U`, `F` and the orbit of `U σ` are continuous, then a solution
of `U t = S (t - σ) (U σ) + ∫_σ^t G (t - r) (F r) dr` on `[σ, τ]` satisfies
`U τ = Z₁ (τ - σ) (U σ) + ∫_σ^τ Γ (τ - r) (F r - B (U r)) dr`. -/
theorem eq_freeMild_of_perturbedMild {ι : E₁ →L[ℝ] E₀} (hι : Function.Injective ι)
    (B : E₁ →L[ℝ] E₀) {S Z₁ : ℝ → E₁ →L[ℝ] E₁} {Z₀ P : ℝ → E₀ →L[ℝ] E₀}
    {G Γ : ℝ → E₀ →L[ℝ] E₁} {U : ℝ → E₁} {F : ℝ → E₀} {σ τ M C : ℝ} (hστ : σ ≤ τ)
    (hZ : ∀ t, 0 ≤ t → ∀ u, ι (Z₁ t u) = Z₀ t (ι u))
    (hΓ : ∀ r, 0 < r → ∀ x, ι (Γ r x) = P r x)
    (hS : ∀ t, 0 ≤ t → ∀ u,
      ι (S t u) = Z₀ t (ι u) - ∫ s in (0 : ℝ)..t, P (t - s) (B (S s u)))
    (hG : ∀ r, 0 < r → ∀ x,
      ι (G r x) = P r x - ∫ s in (0 : ℝ)..r, P (r - s) (B (G s x)))
    (hPc : Continuous fun p : ℝ × E₀ ↦ P p.1 p.2) (hP : ∀ r ∈ Icc 0 (τ - σ), ‖P r‖ ≤ M)
    (hGc : ContinuousOn (fun p : ℝ × E₀ ↦ G p.1 p.2) (Ioi 0 ×ˢ univ))
    (hGb : ∀ r, 0 < r → r ≤ τ - σ → ‖G r‖ ≤ C * r ^ (-(1 / 2 : ℝ)))
    (hΓc : ContinuousOn (fun p : ℝ × E₀ ↦ Γ p.1 p.2) (Ioi 0 ×ˢ univ))
    (hΓb : ∀ r, 0 < r → r ≤ τ - σ → ‖Γ r‖ ≤ C * r ^ (-(1 / 2 : ℝ)))
    (hSc : ContinuousOn (fun t ↦ S t (U σ)) (Icc 0 (τ - σ)))
    (hUc : ContinuousOn U (Icc σ τ)) (hFc : ContinuousOn F (Icc σ τ))
    (hU : ∀ t ∈ Icc σ τ, U t = S (t - σ) (U σ) + ∫ r in σ..t, G (t - r) (F r)) :
    U τ = Z₁ (τ - σ) (U σ) + ∫ r in σ..τ, Γ (τ - r) (F r - B (U r)) := by
  have hT : 0 ≤ τ - σ := sub_nonneg.mpr hστ
  set A : ℝ → E₁ →L[ℝ] E₀ := fun q ↦ (P (τ - q)).comp B with hA_def
  have hAc : Continuous fun p : ℝ × E₁ ↦ A p.1 p.2 :=
    hPc.comp ((continuous_const.sub continuous_fst).prodMk (B.continuous.comp continuous_snd))
  have hAb : ∀ q ∈ Icc σ τ, ‖A q‖ ≤ M * ‖B‖ := fun q hq ↦
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
      (hP _ ⟨by linarith [hq.2], by linarith [hq.1]⟩) (norm_nonneg _))
  -- continuity of the integrands on `[σ, τ]`
  have hPF : ContinuousOn (fun r ↦ P (τ - r) (F r)) (Icc σ τ) :=
    hPc.comp_continuousOn ((continuousOn_const.sub continuousOn_id).prodMk hFc)
  have hAU : ContinuousOn (fun q ↦ A q (U q)) (Icc σ τ) :=
    hAc.comp_continuousOn (continuousOn_id.prodMk hUc)
  have hSσ : ContinuousOn (fun q ↦ S (q - σ) (U σ)) (Icc σ τ) :=
    hSc.comp (continuousOn_id.sub continuousOn_const) fun q hq ↦
      ⟨sub_nonneg.mpr hq.1, by linarith [hq.2]⟩
  have hAS : ContinuousOn (fun q ↦ A q (S (q - σ) (U σ))) (Icc σ τ) :=
    hAc.comp_continuousOn (continuousOn_id.prodMk hSσ)
  have hGint : IntervalIntegrable (fun r ↦ G (τ - r) (F r)) volume σ τ :=
    intervalIntegrable_forwardIntegrand_of_continuousOn hστ hGc hGb hFc
  have hΓint : IntervalIntegrable (fun r ↦ Γ (τ - r) (F r - B (U r))) volume σ τ :=
    intervalIntegrable_forwardIntegrand_of_continuousOn hστ hΓc hΓb
      (hFc.sub (B.continuous.comp_continuousOn hUc))
  set X := ∫ r in σ..τ, P (τ - r) (F r) with hX
  set Y := ∫ q in σ..τ, A q (S (q - σ) (U σ)) with hY
  set W := ∫ q in σ..τ, A q (U q) with hW
  -- the Duhamel integral of the homogeneous part, from `σ`
  have hhom : ∫ s in (0 : ℝ)..(τ - σ), P (τ - σ - s) (B (S s (U σ))) = Y :=
    intervalIntegral_duhamel_shift P B (fun s ↦ S s (U σ)) σ τ
  -- the forcing part, after forgetting the extra order
  have hforce : ∫ r in σ..τ, ι (G (τ - r) (F r)) = X - (W - Y) := by
    have hexp : ∀ᵐ r, r ∈ Ι σ τ → ι (G (τ - r) (F r)) =
        P (τ - r) (F r) - ∫ q in r..τ, A q (G (q - r) (F r)) := by
      filter_upwards [Measure.ae_ne volume τ] with r hrτ hr
      rw [uIoc_of_le hστ] at hr
      have hpos : 0 < τ - r := sub_pos.mpr (lt_of_le_of_ne hr.2 hrτ)
      rw [hG _ hpos, intervalIntegral_duhamel_shift P B (fun s ↦ G s (F r)) r τ]
      rfl
    have hswap := intervalIntegral_forward_comp_swap hστ hAc.continuousOn hAb hGc hGb hFc
    have hEq : ∫ q in σ..τ, A q (∫ r in σ..q, G (q - r) (F r)) = W - Y := by
      rw [hW, hY, ← intervalIntegral.integral_sub (hAU.intervalIntegrable_of_Icc hστ)
        (hAS.intervalIntegrable_of_Icc hστ)]
      refine intervalIntegral.integral_congr fun q hq ↦ ?_
      rw [uIcc_of_le hστ] at hq
      rw [← map_sub, hU q hq, add_sub_cancel_left]
    have hinner : ∫ r in σ..τ, ∫ q in r..τ, A q (G (q - r) (F r)) =
        X - ∫ r in σ..τ, ι (G (τ - r) (F r)) := by
      rw [hX, ← intervalIntegral.integral_sub (hPF.intervalIntegrable_of_Icc hστ)
        (IntervalIntegrable.continuousLinearMap_comp hGint ι)]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hexp] with r hr hrmem
      rw [hr hrmem, sub_sub_cancel]
    rw [hswap, hEq] at hinner
    rw [hinner]
    abel
  have hL : ι (U τ) = Z₀ (τ - σ) (ι (U σ)) + X - W := by
    rw [hU τ ⟨hστ, le_rfl⟩, map_add, hS _ hT, hhom, ← ι.intervalIntegral_comp_comm hGint, hforce]
    abel
  have hR : ι (Z₁ (τ - σ) (U σ) + ∫ r in σ..τ, Γ (τ - r) (F r - B (U r))) =
      Z₀ (τ - σ) (ι (U σ)) + X - W := by
    rw [map_add, hZ _ hT, ← ι.intervalIntegral_comp_comm hΓint]
    have h1 : ∫ r in σ..τ, ι (Γ (τ - r) (F r - B (U r))) =
        ∫ r in σ..τ, (P (τ - r) (F r) - A r (U r)) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [Measure.ae_ne volume τ] with r hrτ hr
      rw [uIoc_of_le hστ] at hr
      rw [hΓ _ (sub_pos.mpr (lt_of_le_of_ne hr.2 hrτ)), map_sub]
      rfl
    rw [h1, intervalIntegral.integral_sub (hPF.intervalIntegrable_of_Icc hστ)
      (hAU.intervalIntegrable_of_Icc hστ)]
    abel
  exact hι (hL.trans hR.symm)

end Perturbation

end PDE.Analysis.Evolution
