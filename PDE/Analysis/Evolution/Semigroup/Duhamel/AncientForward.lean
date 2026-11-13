/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientBackward

/-!
# Forward form of mixed ancient identities

Let `T t` be operators indexed by `t ≥ 0`, and let `Ks`, `Ku` be stable and unstable kernels that
the operators continue: `T t ∘ Ks r = Ks (t + r)` at positive `r` and `T t ∘ Ku r = Ku (r - t)`.
At positive lag the two kernels add up to a forward kernel, `Ks r + Ku (-r) = G r`. A path `v`
that solves the mixed ancient identity

`v t = h t + ∫_{r > 0} Ks r (f (t - r)) dr - ∫_t^a Ku (s - t) (f s) ds`

for `t ≤ a`, with a homogeneous part `h` continued by the operators, `T t (h s) = h (s + t)`,
solves the forward equation

`v τ = T (τ - σ) (v σ) + ∫_σ^τ G (τ - r) (f r) dr`

for `σ ≤ τ ≤ a`. Applying `T (τ - σ)` moves the past integral at `σ` to the part of the past
integral at `τ` with lag above `τ - σ`, and moves the future integral at `σ` to the future
integral from `σ` with the kernel evaluated at `s - τ`. The missing pieces are the stable
integral over lags in `(0, τ - σ]` and the unstable integral over `[σ, τ]`, which add up to the
forward integral of `G`. The operators need no semigroup law.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace PDE.Analysis.Evolution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Translating the variable of an integral over a right half-line. -/
theorem setIntegral_Ioi_comp_add_right (g : ℝ → E) (a d : ℝ) :
    ∫ x in Ioi a, g (x + d) = ∫ x in Ioi (a + d), g x := by
  rw [← image_add_const_Ioi]
  exact ((measurePreserving_add_right volume d).setIntegral_image_emb
    (measurableEmbedding_addRight d) g (Ioi a)).symm

variable [CompleteSpace E]

/-- **Forward form of a mixed ancient identity.** If the operators `T t` continue the stable
kernel, `T t ∘ Ks r = Ks (t + r)` at positive `r`, the unstable kernel, `T t ∘ Ku r = Ku (r - t)`,
and the homogeneous part, `T t (h s) = h (s + t)`, and if `Ks r + Ku (-r) = G r` at positive `r`,
then a path solving `v t = h t + ∫_{r > 0} Ks r (f (t - r)) dr - ∫_t^a Ku (s - t) (f s) ds` for
`t ≤ a` solves `v τ = T (τ - σ) (v σ) + ∫_σ^τ G (τ - r) (f r) dr` for `σ ≤ τ ≤ a`. -/
theorem eq_add_intervalIntegral_of_mixed {T : ℝ≥0 → E →L[ℝ] E} {Ks Ku G : ℝ → F →L[ℝ] E}
    {h v : ℝ → E} {f : ℝ → F} {a σ τ : ℝ}
    (hTKs : ∀ (t : ℝ≥0) r, 0 < r → ∀ x, T t (Ks r x) = Ks (t + r) x)
    (hTKu : ∀ (t : ℝ≥0) r x, T t (Ku r x) = Ku (r - t) x)
    (hG : ∀ r, 0 < r → ∀ x, Ks r x + Ku (-r) x = G r x)
    (hTh : ∀ (t : ℝ≥0) s, T t (h s) = h (s + t))
    (hKs : ∀ t ≤ a, IntegrableOn (fun r ↦ Ks r (f (t - r))) (Ioi 0))
    (hKu : Continuous Ku) (hf : ContinuousOn f (Icc σ a))
    (hv : ∀ t ≤ a, v t = h t + (ancientDuhamel Ks f t - backwardDuhamel Ku f a t))
    (hστ : σ ≤ τ) (hτa : τ ≤ a) :
    v τ = T (τ - σ).toNNReal (v σ) + ∫ r in σ..τ, G (τ - r) (f r) := by
  have ht : 0 ≤ τ - σ := sub_nonneg.mpr hστ
  have htN : (((τ - σ).toNNReal : ℝ≥0) : ℝ) = τ - σ := Real.coe_toNNReal _ ht
  set g : ℝ → E := fun r ↦ Ks r (f (τ - r)) with hg
  have hgτ : IntegrableOn g (Ioi 0) := hKs τ hτa
  -- the homogeneous part
  have h1 : T (τ - σ).toNNReal (h σ) = h τ := by
    rw [hTh, htN, add_sub_cancel]
  -- the past integral
  have h2 : T (τ - σ).toNNReal (ancientDuhamel Ks f σ) =
      ancientDuhamel Ks f τ - ∫ r in (0 : ℝ)..(τ - σ), g r := by
    have hshift : T (τ - σ).toNNReal (ancientDuhamel Ks f σ) = ∫ r in Ioi (τ - σ), g r := by
      have hs := setIntegral_Ioi_comp_add_right g 0 (τ - σ)
      rw [zero_add] at hs
      rw [ancientDuhamel, ← (T (τ - σ).toNNReal).integral_comp_comm (hKs σ (hστ.trans hτa)),
        ← hs]
      refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
      simp only [hg]
      rw [hTKs _ _ hr, htN, add_comm, show τ - (r + (τ - σ)) = σ - r by ring]
    have hsplit : ancientDuhamel Ks f τ =
        (∫ r in Ioc 0 (τ - σ), g r) + ∫ r in Ioi (τ - σ), g r := by
      rw [ancientDuhamel, ← Ioc_union_Ioi_eq_Ioi ht]
      exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hgτ.mono_set Ioc_subset_Ioi_self) (hgτ.mono_set (Ioi_subset_Ioi ht))
    rw [hshift, hsplit, intervalIntegral.integral_of_le ht, add_sub_cancel_left]
  -- the future integral
  have hKuf : ∀ c, ContinuousOn (fun s ↦ Ku (s - c) (f s)) (Icc σ a) := fun c ↦
    ((hKu.comp (continuous_id.sub continuous_const)).continuousOn).clm_apply hf
  have h3 : T (τ - σ).toNNReal (backwardDuhamel Ku f a σ) =
      (∫ s in σ..τ, Ku (s - τ) (f s)) + backwardDuhamel Ku f a τ := by
    have hint : ∀ c, ∀ x ∈ Icc σ a, ∀ y ∈ Icc σ a,
        IntervalIntegrable (fun s ↦ Ku (s - c) (f s)) volume x y := fun c x hx y hy ↦
      ((hKuf c).mono (uIcc_subset_Icc hx hy)).intervalIntegrable
    have hσmem : σ ∈ Icc σ a := ⟨le_rfl, hστ.trans hτa⟩
    have hτmem : τ ∈ Icc σ a := ⟨hστ, hτa⟩
    have haMem : a ∈ Icc σ a := ⟨hστ.trans hτa, le_rfl⟩
    rw [backwardDuhamel, backwardDuhamel,
      ← (T (τ - σ).toNNReal).intervalIntegral_comp_comm (hint σ σ hσmem a haMem)]
    rw [intervalIntegral.integral_add_adjacent_intervals (hint τ σ hσmem τ hτmem)
      (hint τ τ hτmem a haMem)]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    rw [hTKu, htN, show s - σ - (τ - σ) = s - τ by ring]
  -- the two missing pieces add up to the forward integral
  have hgint : IntervalIntegrable (fun s ↦ Ks (τ - s) (f s)) volume σ τ := by
    have h0 : IntervalIntegrable g volume 0 (τ - σ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
        (hgτ.mono_set Ioc_subset_Ioi_self)
    have h := h0.comp_sub_left τ
    simp only [sub_zero, sub_sub_cancel, hg] at h
    exact h.symm
  have h4 : (∫ r in (0 : ℝ)..(τ - σ), g r) + ∫ s in σ..τ, Ku (s - τ) (f s) =
      ∫ r in σ..τ, G (τ - r) (f r) := by
    have hsub : ∫ r in (0 : ℝ)..(τ - σ), g r = ∫ s in σ..τ, Ks (τ - s) (f s) := by
      have h := intervalIntegral.integral_comp_sub_left (fun s ↦ Ks (τ - s) (f s)) τ
        (a := 0) (b := τ - σ)
      simp only [sub_sub_cancel, sub_zero] at h
      rw [← h]
    rw [hsub, ← intervalIntegral.integral_add hgint
      (ContinuousOn.intervalIntegrable_of_Icc hστ ((hKuf τ).mono (Icc_subset_Icc le_rfl hτa)))]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume τ] with s hsτ hs
    rw [uIoc_of_le hστ] at hs
    have hpos : 0 < τ - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsτ)
    rw [show s - τ = -(τ - s) by ring, hG _ hpos]
  rw [hv σ (hστ.trans hτa), map_add, map_sub, h1, h2, h3, hv τ hτa, ← h4]
  abel

end PDE.Analysis.Evolution
