/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.ForwardPerturbation

/-!
# Gain of regularity for forward mild solutions

Consider spaces `E₀`, `E₁`, `E₂` with continuous maps `ι₀ : E₁ → E₀` and `ι : E₂ → E₁` that
forget regularity, for example the inclusions `Hᵏ⁺² → Hᵏ⁺¹ → Hᵏ`. Let `K₀ r : E₀ → E₁` and
`K₁ r : E₁ → E₂` be kernels that gain one order with the bound `M r^(-1/2)` and agree after
forgetting, `ι ∘ K₁ r = K₀ r ∘ ι₀`, and let `Γ r : E₁ → E₂` be the gaining form of a free
evolution, `ι ∘ Γ r = S r` at positive times. Let `A₀ s : E₁ → E₀` and `A₁ s : E₂ → E₁` be
bounded families that agree after forgetting, `ι₀ ∘ A₁ s = A₀ s ∘ ι`.

A path `U` in `E₁`, continuous on `[0, T]`, that solves the forward mild equation
`U t = S t (U 0) + ∫₀ᵗ K₀ (t - s) (ι₀ (f s) + A₀ s (U s)) ds` with a forcing `f` continuous in
`E₁` lies in `E₂` at positive times. Its lift `V` is continuous on `(0, T]`, has the bound
`C t^(-1/2)` there, and solves the mild equation one order higher,
`V t = Γ t (U 0) + ∫₀ᵗ K₁ (t - s) (f s + A₁ s (V s)) ds`.

The proof is Kato's argument. The higher equation has a solution with a singular bound by the
weighted contraction of the perturbation operator. Forgetting the gained order turns this
solution into a solution of the original equation, and uniqueness on `(0, T]` identifies it
with `U`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology

namespace PDE.Analysis.Evolution

/-! ## Shifting and restarting forward integrals -/

section Restart

variable {E F X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The forward integral from `σ` to `t` is the forward integral from zero of the forcing
shifted by `σ`, evaluated at `t - σ`. -/
theorem intervalIntegral_eq_forwardDuhamel_sub (K : ℝ → F →L[ℝ] E) (g : ℝ → F) (σ t : ℝ) :
    ∫ s in σ..t, K (t - s) (g s) = forwardDuhamel K (fun s ↦ g (s + σ)) (t - σ) := by
  rw [forwardDuhamel]
  have h := intervalIntegral.integral_comp_add_right (a := 0) (b := t - σ)
    (fun x ↦ K (t - x) (g x)) σ
  simp only [zero_add, sub_add_cancel] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [show t - (s + σ) = t - σ - s by ring]

/-- A forward mild equation from time zero restarts at every later time `σ`. If the free
evolution `S` and the kernel satisfy `S a ∘ K b = K (a + b)` and `S a ∘ Γ b = Γ (a + b)` at
positive `b`, then `V t = Γ t x₀ + ∫₀ᵗ K (t - s) (G s) ds` on `(0, T]` gives
`V t = S (t - σ) (V σ) + ∫ σ..t, K (t - s) (G s) ds` for `0 < σ ≤ t ≤ T`. -/
theorem eq_add_intervalIntegral_of_forwardMild [CompleteSpace E]
    {K : ℝ → F →L[ℝ] E} {S : ℝ → E →L[ℝ] E} {Γ : ℝ → X →L[ℝ] E} {M D ω T : ℝ}
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hSK : ∀ a, 0 ≤ a → ∀ b, 0 < b → ∀ x, S a (K b x) = K (a + b) x)
    (hSΓ : ∀ a, 0 ≤ a → ∀ b, 0 < b → ∀ x, S a (Γ b x) = Γ (a + b) x)
    {G : ℝ → F} (hGc : ContinuousOn G (Ioc 0 T))
    (hGb : ∀ s ∈ Ioc 0 T, ‖G s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    {V : ℝ → E} {x₀ : X} (hV : ∀ t ∈ Ioc 0 T, V t = Γ t x₀ + forwardDuhamel K G t)
    {σ t : ℝ} (hσ : 0 < σ) (hσt : σ ≤ t) (htT : t ≤ T) :
    V t = S (t - σ) (V σ) + ∫ s in σ..t, K (t - s) (G s) := by
  have ht : 0 < t := hσ.trans_le hσt
  have hint := intervalIntegrable_forwardIntegrand_of_le hKc hK hGc hGb ht.le htT
  have hintσ := intervalIntegrable_forwardIntegrand_of_le hKc hK hGc hGb hσ.le (hσt.trans htT)
  have hσmem : σ ∈ uIcc 0 t := mem_uIcc_of_le hσ.le hσt
  have hSV : S (t - σ) (V σ) = Γ t x₀ + ∫ s in (0 : ℝ)..σ, K (t - s) (G s) := by
    rw [hV σ ⟨hσ, hσt.trans htT⟩, map_add, hSΓ _ (sub_nonneg.mpr hσt) σ hσ, sub_add_cancel,
      forwardDuhamel, ← (S (t - σ)).intervalIntegral_comp_comm hintσ]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume σ] with s hsσ hs
    rw [uIoc_of_le hσ.le] at hs
    rw [hSK _ (sub_nonneg.mpr hσt) _ (sub_pos.mpr (lt_of_le_of_ne hs.2 hsσ)),
      sub_add_sub_cancel]
  rw [hV t ⟨ht, htT⟩, hSV, forwardDuhamel, add_assoc,
    intervalIntegral.integral_add_adjacent_intervals
      (hint.mono_set (uIcc_subset_uIcc left_mem_uIcc hσmem))
      (hint.mono_set (uIcc_subset_uIcc hσmem right_mem_uIcc))]

end Restart

/-! ## Gain of regularity -/

variable {E₀ E₁ E₂ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]

/-- Kato's gain of regularity for forward mild solutions. A solution `U` of
`U t = S t (U 0) + ∫₀ᵗ K₀ (t - s) (ι₀ (f s) + A₀ s (U s)) ds` on `(0, T]`, continuous on
`[0, T]`, is the image under `ι` of a path `V` that is continuous on `(0, T]`, has the bound
`C t^(-1/2)` there and solves `V t = Γ t (U 0) + ∫₀ᵗ K₁ (t - s) (f s + A₁ s (V s)) ds`. -/
theorem exists_forwardMild_lift (ι : E₂ →L[ℝ] E₁) (ι₀ : E₁ →L[ℝ] E₀)
    {K₀ : ℝ → E₀ →L[ℝ] E₁} {K₁ : ℝ → E₁ →L[ℝ] E₂}
    {S : ℝ → E₁ →L[ℝ] E₁} {Γ : ℝ → E₁ →L[ℝ] E₂}
    {A₀ : ℝ → E₁ →L[ℝ] E₀} {A₁ : ℝ → E₂ →L[ℝ] E₁} {M a T : ℝ}
    (hK₀c : ContinuousOn (fun p : ℝ × E₀ ↦ K₀ p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK₀ : ∀ r, 0 < r → ‖K₀ r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hK₁c : ContinuousOn (fun p : ℝ × E₁ ↦ K₁ p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK₁ : ∀ r, 0 < r → ‖K₁ r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hK : ∀ r x, ι (K₁ r x) = K₀ r (ι₀ x))
    (hΓc : ContinuousOn (fun p : ℝ × E₁ ↦ Γ p.1 p.2) (Ioi 0 ×ˢ univ))
    (hΓ : ∀ r, 0 < r → ‖Γ r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hΓS : ∀ r, 0 < r → ∀ x, ι (Γ r x) = S r x)
    (hA₀c : ContinuousOn (fun p : ℝ × E₁ ↦ A₀ p.1 p.2) (Icc 0 T ×ˢ univ))
    (hA₀ : ∀ s ∈ Icc 0 T, ‖A₀ s‖ ≤ a)
    (hA₁c : ContinuousOn (fun p : ℝ × E₂ ↦ A₁ p.1 p.2) (Icc 0 T ×ˢ univ))
    (hA₁ : ∀ s ∈ Icc 0 T, ‖A₁ s‖ ≤ a)
    (hA : ∀ s ∈ Icc 0 T, ∀ x, ι₀ (A₁ s x) = A₀ s (ι x))
    {f U : ℝ → E₁} (hfc : ContinuousOn f (Icc 0 T)) (hUc : ContinuousOn U (Icc 0 T))
    (hU : ∀ t ∈ Ioc 0 T, U t = S t (U 0) +
      forwardDuhamel K₀ (fun s ↦ ι₀ (f s) + A₀ s (U s)) t) :
    ∃ V : ℝ → E₂, ContinuousOn V (Ioc 0 T) ∧
      (∃ C, ∀ t ∈ Ioc 0 T, ‖V t‖ ≤ C * t ^ (-(1 / 2 : ℝ))) ∧
      ∀ t ∈ Ioc 0 T, ι (V t) = U t ∧
        V t = Γ t (U 0) + forwardDuhamel K₁ (fun s ↦ f s + A₁ s (V s)) t := by
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨0, continuousOn_const, ⟨0, fun t ht ↦ ?_⟩, fun t ht ↦ ?_⟩ <;>
      exact absurd (ht.1.trans_le ht.2) hT.not_gt
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hK₁ 1 one_pos)
  have ha : 0 ≤ a := (norm_nonneg _).trans (hA₁ 0 ⟨le_rfl, hT.le⟩)
  -- Clamp the coefficients and the forcing to `[0, T]`.
  let c : ℝ → ℝ := fun s ↦ min (max s 0) T
  have hcc : Continuous c := (continuous_id.max continuous_const).min continuous_const
  have hcmem : ∀ s, c s ∈ Icc 0 T := fun s ↦ ⟨le_min (le_max_right _ _) hT.le, min_le_right _ _⟩
  have hcid : ∀ s ∈ Icc 0 T, c s = s := fun s hs ↦ by
    simp only [c, max_eq_left hs.1, min_eq_left hs.2]
  have hA'c : ContinuousOn (fun p : ℝ × E₂ ↦ A₁ (c p.1) p.2) (Ioi 0 ×ˢ univ) :=
    (hA₁c.comp_continuous ((hcc.comp continuous_fst).prodMk continuous_snd)
      fun p ↦ ⟨hcmem p.1, mem_univ _⟩).continuousOn
  have hA' : ∀ s, 0 < s → ‖A₁ (c s)‖ ≤ a := fun s _ ↦ hA₁ (c s) (hcmem s)
  have hf'c : Continuous (fun s ↦ f (c s)) := hfc.comp_continuous hcc hcmem
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨BU, hBU⟩ := isCompact_Icc.exists_bound_of_continuousOn hUc
  have hf'b : ∀ s, 0 < s → ‖f (c s)‖ ≤ max B₀ 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (1 * s) :=
    fun s hs ↦ ((hB₀ _ (hcmem s)).trans (le_max_left _ _)).trans
      (le_mul_rpow_neg_one_half_mul_exp (le_max_right _ _) hs)
  -- The forcing of the higher equation.
  have hgc : ContinuousOn (fun t ↦ Γ t (U 0) + forwardDuhamel K₁ (fun s ↦ f (c s)) t)
      (Ioi 0) :=
    (hΓc.comp (continuousOn_id.prodMk continuousOn_const) fun t ht ↦ ⟨ht, mem_univ _⟩).add
      (continuousOn_forwardDuhamel hK₁c hK₁ hf'c.continuousOn hf'b)
  have hgb : ∀ t, 0 < t → ‖Γ t (U 0) + forwardDuhamel K₁ (fun s ↦ f (c s)) t‖ ≤
      (M * ‖U 0‖ + forwardSmoothingConstant * M * max B₀ 0 / Real.sqrt 1) *
        t ^ (-(1 / 2 : ℝ)) * Real.exp (1 * t) := by
    intro t ht
    have h1 : ‖Γ t (U 0)‖ ≤ M * ‖U 0‖ * t ^ (-(1 / 2 : ℝ)) * Real.exp (1 * t) :=
      ((Γ t).le_of_opNorm_le_of_le (hΓ t ht) le_rfl).trans <| by
        rw [mul_right_comm]
        exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by linarith))
    have h2 := norm_forwardDuhamel_le_singular hK₁ ht (fun s hs ↦ hf'b s hs.1) one_pos
      (le_max_right B₀ 0)
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  obtain ⟨v, hvc, ⟨C, ω, hvb⟩, hv⟩ := exists_eq_add_forwardDuhamel hK₁c hK₁ hA'c hA' hgc hgb
  -- Common singular bounds with the rate `ρ = max 1 ω`.
  have hvb' : ∀ s, 0 < s → ‖v s‖ ≤ max C 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (max 1 ω * s) :=
    fun s hs ↦ (hvb s hs).trans (mul_rpow_neg_one_half_mul_exp_le hs (le_max_right _ _))
  have hfb : ∀ s ∈ Ioc 0 T, ‖f s‖ ≤ max B₀ 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (max 1 ω * s) := by
    intro s hs
    have h := (hf'b s hs.1).trans (mul_rpow_neg_one_half_mul_exp_le hs.1 (le_max_left 1 ω))
    rwa [hcid s (Ioc_subset_Icc_self hs), max_eq_left (le_max_right B₀ 0)] at h
  have hUb : ∀ s ∈ Ioc 0 T, ‖U s‖ ≤ max BU 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (max 1 ω * s) := by
    intro s hs
    have h := ((hBU s (Ioc_subset_Icc_self hs)).trans (le_max_left _ 0)).trans
      (le_mul_rpow_neg_one_half_mul_exp (le_max_right BU 0) hs.1)
    exact h.trans ((mul_rpow_neg_one_half_mul_exp_le hs.1 (le_max_left 1 ω)).trans_eq
      (by rw [max_eq_left (le_max_right BU 0)]))
  -- Integrability of the forward integrands.
  have hforce : ContinuousOn (fun s ↦ f s + A₁ s (v s)) (Ioc 0 T) :=
    (hfc.mono Ioc_subset_Icc_self).add (hA₁c.comp
      (continuousOn_id.prodMk (hvc.mono Ioc_subset_Ioi_self))
      fun s hs ↦ ⟨Ioc_subset_Icc_self hs, mem_univ _⟩)
  have hforceb : ∀ s ∈ Ioc 0 T, ‖f s + A₁ s (v s)‖ ≤
      (max B₀ 0 + a * max C 0) * s ^ (-(1 / 2 : ℝ)) * Real.exp (max 1 ω * s) := fun s hs ↦
    (norm_add_le _ _).trans <| (add_le_add (hfb s hs) ((A₁ s).le_of_opNorm_le_of_le
      (hA₁ s (Ioc_subset_Icc_self hs)) (hvb' s hs.1))).trans_eq (by ring)
  -- The lift solves the higher equation on `(0, T]`.
  have hV : ∀ t ∈ Ioc 0 T, v t = Γ t (U 0) + forwardDuhamel K₁ (fun s ↦ f s + A₁ s (v s)) t := by
    intro t ht
    have hint₁ : IntervalIntegrable (fun s ↦ K₁ (t - s) (f (c s))) volume 0 t :=
      intervalIntegrable_forwardIntegrand hK₁c hK₁ hf'c.continuousOn hf'b ht.1.le
    have hint₂ : IntervalIntegrable (fun s ↦ K₁ (t - s) (A₁ (c s) (v s))) volume 0 t :=
      intervalIntegrable_forwardIntegrand (D := a * max C 0) (ω := max 1 ω) hK₁c hK₁
        (hA'c.comp (continuousOn_id.prodMk hvc) fun s hs ↦ ⟨hs, mem_univ _⟩)
        (fun s hs ↦ ((A₁ (c s)).le_of_opNorm_le_of_le (hA' s hs) (hvb' s hs)).trans_eq
          (by ring)) ht.1.le
    rw [hv t ht.1, add_assoc, ← forwardDuhamel_add hint₁ hint₂]
    congr 1
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht.1.le] at hs
    simp only [Pi.add_apply, hcid s ⟨hs.1, hs.2.trans ht.2⟩, map_add]
  -- Forgetting the gained order gives a solution of the original equation.
  have hlow : ∀ t ∈ Ioc 0 T, ι (v t) = S t (U 0) +
      forwardDuhamel K₀ (fun s ↦ ι₀ (f s) + A₀ s (ι (v s))) t := by
    intro t ht
    have hint := intervalIntegrable_forwardIntegrand_of_le hK₁c hK₁ hforce hforceb ht.1.le ht.2
    rw [hV t ht, map_add, hΓS t ht.1, forwardDuhamel,
      ← ι.intervalIntegral_comp_comm hint, forwardDuhamel]
    congr 1
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht.1.le] at hs
    simp only [hK, map_add, hA s ⟨hs.1, hs.2.trans ht.2⟩]
  -- Uniqueness on `(0, T]` identifies the lift with `U`.
  have heq : ∀ t ∈ Ioc 0 T, U t = ι (v t) := fun t ht ↦
    eq_of_eq_add_forwardDuhamel_on (K := K₀) (A := A₀) (a := a)
      (D := ‖ι₀‖ * max B₀ 0) (ω := max 1 ω) (C₁ := max BU 0) (C₂ := ‖ι‖ * max C 0)
      (g := fun t ↦ S t (U 0)) (h := fun s ↦ ι₀ (f s)) (v₂ := fun s ↦ ι (v s))
      hK₀c hK₀ (hA₀c.mono (prod_mono Ioc_subset_Icc_self subset_rfl))
      (fun s hs ↦ hA₀ s (Ioc_subset_Icc_self hs))
      (ι₀.continuous.comp_continuousOn (hfc.mono Ioc_subset_Icc_self))
      (fun s hs ↦ (ι₀.le_of_opNorm_le_of_le le_rfl (hfb s hs)).trans_eq (by ring))
      (hUc.mono Ioc_subset_Icc_self)
      (ι.continuous.comp_continuousOn (hvc.mono Ioc_subset_Ioi_self)) hUb
      (fun s hs ↦ (ι.le_of_opNorm_le_of_le le_rfl (hvb' s hs.1)).trans_eq (by ring)) hU hlow ht
  refine ⟨v, hvc.mono Ioc_subset_Ioi_self,
    ⟨max C 0 * Real.exp (max 1 ω * T), fun t ht ↦ ?_⟩,
    fun t ht ↦ ⟨(heq t ht).symm, hV t ht⟩⟩
  calc
    _ ≤ _ := hvb' t ht.1
    _ ≤ max C 0 * t ^ (-(1 / 2 : ℝ)) * Real.exp (max 1 ω * T) := by
      gcongr
      exacts [mul_nonneg (le_max_right _ _) (Real.rpow_nonneg ht.1.le _), ht.2]
    _ = _ := by ring

end PDE.Analysis.Evolution
