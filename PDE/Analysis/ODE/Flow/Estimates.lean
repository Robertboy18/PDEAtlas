/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.SecondVariation

/-!
# Flow estimates on an invariant set

Let `S` be a convex set that every map `flowOn v a b s t` sends into itself, for example the
closed upper half-plane for a field tangent to its boundary. Along flow lines starting in `S` the
first and second variations only see the field on `S`, so bounds `‖v‖ ≤ V`, `‖Dv‖ ≤ K₁`,
`‖D²v‖ ≤ K₂` and `[D²v]_α ≤ K₃` on `S` control the flow on `S`, whatever the field does outside.
With `τ = |s - t|` and `L = exp (K₁ τ)`:

* `‖J‖ ≤ L` and `‖J - id‖ ≤ L - 1` for the first variation `J`; the flow maps are
  `L`-Lipschitz on `S` and move points by at most `V τ`;
* the second variation is bounded by `K₂ τ exp (3 K₁ τ)`, so `J` is Lipschitz on `S`, and it is
  `α`-Hölder on `S` with the constant `secondVariationHolderConst K₁ K₂ K₃ τ`;
* the flow and the first variation are Lipschitz in the final and in the initial time.

## Main results

* `IsC1FieldOn.norm_variationOn_le_of_invariant`, `IsC1FieldOn.norm_flowOn_sub_le_of_invariant`,
  `IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant`,
  `IsC1FieldOn.norm_variationOn_sub_id_le_of_invariant`.
* `IsC2FieldOn.norm_secondVariationOn_le_of_invariant`,
  `IsC2FieldOn.norm_variationOn_sub_le_of_invariant`,
  `IsC2FieldOn.norm_secondVariationOn_sub_le_of_invariant`,
  `IsC2FieldOn.norm_secondVariationOn_sub_le_rpow_of_invariant`.
* `IsLipschitzFieldOn.norm_flowOn_final_sub_le_of_invariant`,
  `IsC1FieldOn.norm_flowOn_initial_sub_le_of_invariant`,
  `IsC1FieldOn.norm_variationOn_final_sub_le_of_invariant`,
  `IsC2FieldOn.norm_variationOn_initial_sub_le_of_invariant`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace PDE.Analysis.ODE

/-! ### Elementary bounds -/

/-- `gronwallBound 0 K K x = exp (K x) - 1`. -/
theorem gronwallBound_zero_self (K x : ℝ) : gronwallBound 0 K K x = Real.exp (K * x) - 1 := by
  by_cases hK : K = 0
  · subst hK
    simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hK, div_self hK]
    ring

/-- `exp y - 1 ≤ y exp y`. -/
theorem exp_sub_one_le_mul_exp (y : ℝ) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have hpos := Real.exp_pos y
  have hmul : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith

/-- `gronwallBound δ K ε x ≤ (δ + ε x) exp (K x)` for nonnegative `K` and `ε`. -/
theorem gronwallBound_le_add_mul_exp {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rcases hK.eq_or_lt with rfl | hKpos
  · simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hKpos.ne']
    have h1 := exp_sub_one_le_mul_exp (K * x)
    have h2 : ε / K * (Real.exp (K * x) - 1) ≤ ε * x * Real.exp (K * x) := by
      calc ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) := by
            gcongr
        _ = ε * x * Real.exp (K * x) := by field_simp
    nlinarith [Real.exp_pos (K * x)]

section Gronwall

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Grönwall's inequality between two times.** If `e` has derivatives within `[a, b]` and
`‖e'‖ ≤ K ‖e‖ + A` between `t` and `s`, then `‖e s‖ ≤ gronwallBound ‖e t‖ K A |s - t|`. Only
the bound between the two times is used. -/
theorem norm_le_gronwallBound_of_uIcc {e e' : ℝ → F} {a b t s δ K A : ℝ}
    (ht : t ∈ Icc a b) (hs : s ∈ Icc a b)
    (he : ∀ r ∈ Icc a b, HasDerivWithinAt e (e' r) (Icc a b) r) (he₀ : ‖e t‖ ≤ δ)
    (hbound : ∀ r ∈ uIcc t s, ‖e' r‖ ≤ K * ‖e r‖ + A) :
    ‖e s‖ ≤ gronwallBound δ K A |s - t| := by
  have hsub : uIcc t s ⊆ Icc a b := uIcc_subset_Icc ht hs
  have ht' : t ∈ Icc (min t s) (max t s) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hs' : s ∈ Icc (min t s) (max t s) := ⟨min_le_right _ _, le_max_right _ _⟩
  exact norm_le_gronwallBound_of_hasDerivWithinAt ht'
    (fun r hr ↦ (he r (hsub hr)).mono hsub) he₀ (fun r hr ↦ hbound r hr) hs'

end Gronwall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E}
  {a b : ℝ} {K₀ Q₀ : ℝ≥0} {S : Set E} {K₁ K₂ K₃ V α : ℝ}

/-! ### The flow and its first variation -/

namespace IsLipschitzFieldOn

omit [FiniteDimensional ℝ E] in
/-- **Lipschitz dependence on the final time** on an invariant set. No Lipschitz bound on `v`
is needed: `flowOn` is either a chosen solution through `(t, x)`, whose speed is at most `V` on
`S`, or the constant `x`. -/
theorem norm_flowOn_final_sub_le_of_invariant
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hV : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖v r y‖ ≤ V) {s s' t : ℝ} (hs : s ∈ Icc a b)
    (hs' : s' ∈ Icc a b) (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) :
    ‖flowOn v a b s t x - flowOn v a b s' t x‖ ≤ V * |s - s'| := by
  by_cases hsol : ∃ γ : ℝ → E, γ t = x ∧ ∀ r ∈ Icc a b, HasDerivAt γ (v r (γ r)) r
  · have hflow : (fun r ↦ flowOn v a b r t x) = hsol.choose := by
      funext r
      simp only [flowOn, hsol, ↓reduceDIte]
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r ↦ flowOn v a b r t x) (f' := fun r ↦ v r (flowOn v a b r t x))
      (fun r hr ↦ by
        rw [hflow, show flowOn v a b r t x = hsol.choose r from congrFun hflow r]
        exact (hsol.choose_spec.2 r hr).hasDerivWithinAt)
      (fun r hr ↦ hV r hr _ (hS r hr t ht hx)) hs' hs
    rwa [Real.norm_eq_abs] at h
  · have hconst (r : ℝ) : flowOn v a b r t x = x := by
      simp only [flowOn, hsol, ↓reduceDIte]
    rw [hconst, hconst, sub_self, norm_zero]
    exact mul_nonneg ((norm_nonneg _).trans (hV s hs x hx)) (abs_nonneg _)

omit [FiniteDimensional ℝ E] in
/-- **Displacement bound on an invariant set.** If `‖v‖ ≤ V` on `S` and the flow keeps `S`,
flow lines from `S` move at speed at most `V`. -/
theorem norm_flowOn_sub_self_le_of_invariant
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hV : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖v r y‖ ≤ V) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) : ‖flowOn v a b s t x - x‖ ≤ V * |s - t| := by
  have hself : flowOn v a b t t x = x := by
    by_cases hsol : ∃ γ : ℝ → E, γ t = x ∧ ∀ r ∈ Icc a b, HasDerivAt γ (v r (γ r)) r
    · simp only [flowOn, hsol, ↓reduceDIte]
      exact hsol.choose_spec.1
    · simp only [flowOn, hsol, ↓reduceDIte]
  simpa only [hself] using norm_flowOn_final_sub_le_of_invariant hS hV hs ht ht hx

end IsLipschitzFieldOn

namespace IsC1FieldOn

/-- **Bound of the first variation on an invariant set:** `‖J‖ ≤ exp (K₁ |s - t|)` when
`‖Dv‖ ≤ K₁` on `S`. -/
theorem norm_variationOn_le_of_invariant (hv : IsC1FieldOn v Dv a b K₀)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) :
    ‖variationOn v Dv a b s t x‖ ≤ Real.exp (K₁ * |s - t|) := by
  have h := norm_le_gronwallBound_of_hasDerivWithinAt
    (e := fun r ↦ variationOn v Dv a b r t x) (δ := 1) (K := K₁) (A := 0) ht
    (fun r hr ↦ hv.hasDerivWithinAt_variationOn hr ht x)
    (by rw [hv.variationOn_self ht]; exact ContinuousLinearMap.norm_id_le)
    (fun r hr ↦ by
      rw [add_zero]
      exact ((Dv r _).opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_right (hDv r hr _ (hS r hr t ht hx)) (norm_nonneg _))) hs
  rwa [gronwallBound_ε0, one_mul] at h

/-- **Lipschitz dependence on the initial point** on a convex invariant set. -/
theorem norm_flowOn_sub_le_of_invariant (hv : IsC1FieldOn v Dv a b K₀) (hSc : Convex ℝ S)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖flowOn v a b s t x - flowOn v a b s t y‖ ≤ Real.exp (K₁ * |s - t|) * ‖x - y‖ :=
  hSc.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := flowOn v a b s t)
    (f' := fun z ↦ variationOn v Dv a b s t z)
    (fun z _ ↦ (hv.hasFDerivAt_flowOn hs ht z).hasFDerivWithinAt)
    (fun _ hz ↦ hv.norm_variationOn_le_of_invariant hS hDv hs ht hz) hy hx

/-- **The first variation is close to the identity:** `‖J - id‖ ≤ exp (K₁ |s - t|) - 1`. -/
theorem norm_variationOn_sub_id_le_of_invariant (hv : IsC1FieldOn v Dv a b K₀)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) :
    ‖variationOn v Dv a b s t x - ContinuousLinearMap.id ℝ E‖ ≤
      Real.exp (K₁ * |s - t|) - 1 := by
  have h := norm_le_gronwallBound_of_hasDerivWithinAt
    (e := fun r ↦ variationOn v Dv a b r t x - ContinuousLinearMap.id ℝ E) (δ := 0) (K := K₁)
    (A := K₁) ht
    (fun r hr ↦ by
      simpa using (hv.hasDerivWithinAt_variationOn hr ht x).sub_const
        (ContinuousLinearMap.id ℝ E))
    (by rw [hv.variationOn_self ht, sub_self, norm_zero])
    (fun r hr ↦ by
      have hD := hDv r hr _ (hS r hr t ht hx)
      have hsplit : (Dv r (flowOn v a b r t x)).comp (variationOn v Dv a b r t x) =
          (Dv r (flowOn v a b r t x)).comp
            (variationOn v Dv a b r t x - ContinuousLinearMap.id ℝ E) +
            Dv r (flowOn v a b r t x) := by
        rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id, sub_add_cancel]
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ hD)
      exact ((Dv r _).opNorm_comp_le _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _)))
    hs
  rwa [gronwallBound_zero_self] at h

/-- **Lipschitz dependence of the first variation on the final time.** -/
theorem norm_variationOn_final_sub_le_of_invariant (hv : IsC1FieldOn v Dv a b K₀)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) {s s' t : ℝ} (hs : s ∈ Icc a b)
    (hs' : s' ∈ Icc a b) (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) :
    ‖variationOn v Dv a b s t x - variationOn v Dv a b s' t x‖ ≤
      K₁ * Real.exp (K₁ * (b - a)) * |s - s'| := by
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv t ht x hx)
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r ↦ variationOn v Dv a b r t x) (fun r hr ↦ hv.hasDerivWithinAt_variationOn hr ht x)
    (fun r hr ↦ by
      have hJ : ‖variationOn v Dv a b r t x‖ ≤ Real.exp (K₁ * (b - a)) := by
        refine (hv.norm_variationOn_le_of_invariant hS hDv hr ht hx).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hK₁))
        rw [abs_le]; constructor <;> linarith [hr.1, hr.2, ht.1, ht.2]
      exact ((Dv r _).opNorm_comp_le _).trans
        (mul_le_mul (hDv r hr _ (hS r hr t ht hx)) hJ (norm_nonneg _) hK₁)) hs' hs
  rwa [Real.norm_eq_abs] at h

/-- **Lipschitz dependence of the flow on the initial time** on a convex invariant set, through
the cocycle law. -/
theorem norm_flowOn_initial_sub_le_of_invariant (hv : IsC1FieldOn v Dv a b K₀)
    (hSc : Convex ℝ S) (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) (hV : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖v r y‖ ≤ V)
    {s t t' : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (ht' : t' ∈ Icc a b) {x : E}
    (hx : x ∈ S) :
    ‖flowOn v a b s t x - flowOn v a b s t' x‖ ≤ Real.exp (K₁ * |s - t|) * (V * |t - t'|) := by
  have hL := hv.isLipschitzFieldOn
  rw [← hL.flowOn_flowOn hs ht ht' x]
  refine (hv.norm_flowOn_sub_le_of_invariant hSc hS hDv hs ht hx
    (hS t ht t' ht' hx)).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  rw [norm_sub_rev]
  exact IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hS hV ht ht' hx

end IsC1FieldOn

/-! ### The second variation -/

/-- The bound `K₂ τ exp (3 K₁ τ)` of the second variation over a time span `τ`. -/
def secondVariationBound (K₁ K₂ τ : ℝ) : ℝ :=
  K₂ * τ * Real.exp (3 * K₁ * τ)

/-- The `α`-Hölder constant of the second variation over a time span `τ`:
`τ L (3 K₂ L σ + K₃ L³) + 2 σ` with `L = exp (K₁ τ)` and `σ = secondVariationBound K₁ K₂ τ`. -/
def secondVariationHolderConst (K₁ K₂ K₃ τ : ℝ) : ℝ :=
  τ * Real.exp (K₁ * τ) * (3 * K₂ * Real.exp (K₁ * τ) * secondVariationBound K₁ K₂ τ +
    K₃ * Real.exp (3 * K₁ * τ)) + 2 * secondVariationBound K₁ K₂ τ

/-- The second-variation bound is monotone in the time span. -/
theorem secondVariationBound_mono {K₁ K₂ τ τ' : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hτ : 0 ≤ τ) (hττ' : τ ≤ τ') :
    secondVariationBound K₁ K₂ τ ≤ secondVariationBound K₁ K₂ τ' := by
  unfold secondVariationBound
  have h₁ : Real.exp (3 * K₁ * τ) ≤ Real.exp (3 * K₁ * τ') :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hττ' (by positivity))
  have h₂ : K₂ * τ ≤ K₂ * τ' := mul_le_mul_of_nonneg_left hττ' hK₂
  exact mul_le_mul h₂ h₁ (Real.exp_pos _).le (by nlinarith)

namespace IsC2FieldOn

/-- **Bound of the second variation on an invariant set:**
`‖H‖ ≤ K₂ |s - t| exp (3 K₁ |s - t|)` when `‖Dv‖ ≤ K₁` and `‖D²v‖ ≤ K₂` on `S`. -/
theorem norm_secondVariationOn_le_of_invariant (hv : IsC2FieldOn v Dv D2v a b K₀ Q₀)
    (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) (hD2v : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖D2v r y‖ ≤ K₂)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x : E} (hx : x ∈ S) :
    ‖secondVariationOn v Dv D2v a b s t x‖ ≤ secondVariationBound K₁ K₂ |s - t| := by
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv t ht x hx)
  have hK₂ : 0 ≤ K₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hD2v t ht x hx)
  have hsub : uIcc t s ⊆ Icc a b := uIcc_subset_Icc ht hs
  set L := Real.exp (K₁ * |s - t|) with hLdef
  have hL : 0 ≤ L := (Real.exp_pos _).le
  have hJ (r : ℝ) (hr : r ∈ uIcc t s) : ‖variationOn v Dv a b r t x‖ ≤ L :=
    (hv.norm_variationOn_le_of_invariant hS hDv (hsub hr) ht hx).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hr) hK₁))
  have h := norm_le_gronwallBound_of_uIcc (F := E →L[ℝ] E →L[ℝ] E)
    (e := fun r ↦ secondVariationOn v Dv D2v a b r t x) (δ := 0) (K := K₁) (A := K₂ * L * L) ht hs
    (fun r hr ↦ hv.hasDerivWithinAt_secondVariationOn hr ht x)
    (by rw [hv.secondVariationOn_self ht, ContinuousLinearMap.opNorm_zero])
    (fun r hr ↦ by
      have hr' := hsub hr
      have hΦ := hS r hr' t ht hx
      have h₁ : ‖(ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x))).comp
          (secondVariationOn v Dv D2v a b r t x)‖ ≤
            K₁ * ‖secondVariationOn v Dv D2v a b r t x‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_compL_apply_le _).trans (hDv r hr' _ hΦ))
          (ContinuousLinearMap.opNorm_nonneg _))
      have h₂ : ‖secondVariationForcing (D2v r (flowOn v a b r t x))
          (variationOn v Dv a b r t x)‖ ≤ K₂ * L * L := by
        refine (norm_secondVariationForcing_le _ _).trans ?_
        have hT := hD2v r hr' _ hΦ
        have hJr := hJ r hr
        have hJ0 := norm_nonneg (variationOn v Dv a b r t x)
        exact mul_le_mul (mul_le_mul hT hJr hJ0 hK₂) hJr hJ0 (mul_nonneg hK₂ hL)
      exact (norm_add_le _ _).trans (add_le_add h₁ h₂))
  refine h.trans ((gronwallBound_le_add_mul_exp hK₁ (by positivity)).trans_eq ?_)
  unfold secondVariationBound
  rw [show 3 * K₁ * |s - t| = K₁ * |s - t| + K₁ * |s - t| + K₁ * |s - t| by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- **The first variation is Lipschitz on a convex invariant set** in the initial point. -/
theorem norm_variationOn_sub_le_of_invariant (hv : IsC2FieldOn v Dv D2v a b K₀ Q₀)
    (hSc : Convex ℝ S) (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) (hD2v : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖D2v r y‖ ≤ K₂)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖variationOn v Dv a b s t x - variationOn v Dv a b s t y‖ ≤
      secondVariationBound K₁ K₂ |s - t| * ‖x - y‖ :=
  hSc.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := variationOn v Dv a b s t)
    (f' := fun z ↦ secondVariationOn v Dv D2v a b s t z)
    (fun z _ ↦ (hv.hasFDerivAt_variationOn hs ht z).hasFDerivWithinAt)
    (fun _ hz ↦ hv.norm_secondVariationOn_le_of_invariant hS hDv hD2v hs ht hz) hy hx

/-- **Lipschitz dependence of the first variation on the initial time** on a convex invariant
set, through the cocycle law `J(s, t', x) = J(s, t, Φ(t, t', x)) ∘ J(t, t', x)`. -/
theorem norm_variationOn_initial_sub_le_of_invariant (hv : IsC2FieldOn v Dv D2v a b K₀ Q₀)
    (hSc : Convex ℝ S) (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hV : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖v r y‖ ≤ V)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) (hD2v : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖D2v r y‖ ≤ K₂)
    {s t t' : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (ht' : t' ∈ Icc a b) {x : E}
    (hx : x ∈ S) :
    ‖variationOn v Dv a b s t x - variationOn v Dv a b s t' x‖ ≤
      secondVariationBound K₁ K₂ |s - t| * (V * |t - t'|) +
        Real.exp (K₁ * |s - t|) * (Real.exp (K₁ * |t - t'|) - 1) := by
  have hL := hv.isLipschitzFieldOn
  set y := flowOn v a b t t' x
  have hy : y ∈ S := hS t ht t' ht' hx
  have hσ : 0 ≤ secondVariationBound K₁ K₂ |s - t| :=
    (ContinuousLinearMap.opNorm_nonneg _).trans
      (hv.norm_secondVariationOn_le_of_invariant hS hDv hD2v hs ht hx)
  rw [hv.variationOn_eq_comp hs ht ht' x]
  have hsplit : variationOn v Dv a b s t x - (variationOn v Dv a b s t y).comp
      (variationOn v Dv a b t t' x) = (variationOn v Dv a b s t x - variationOn v Dv a b s t y) +
      (variationOn v Dv a b s t y).comp
        (ContinuousLinearMap.id ℝ E - variationOn v Dv a b t t' x) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (hv.norm_variationOn_sub_le_of_invariant hSc hS hDv hD2v hs ht hx hy).trans
      (mul_le_mul_of_nonneg_left ?_ hσ)
    rw [norm_sub_rev]
    exact IsLipschitzFieldOn.norm_flowOn_sub_self_le_of_invariant hS hV ht ht' hx
  · refine ((variationOn v Dv a b s t y).opNorm_comp_le _).trans (mul_le_mul
      (hv.norm_variationOn_le_of_invariant hS hDv hs ht hy) ?_ (norm_nonneg _)
      (Real.exp_pos _).le)
    rw [norm_sub_rev]
    exact hv.norm_variationOn_sub_id_le_of_invariant hS hDv ht ht' hx

/-- **The second variation is Lipschitz plus Hölder on a convex invariant set.** If moreover
`‖D²v r y - D²v r z‖ ≤ K₃ ‖y - z‖ ^ α` on `S` with `0 ≤ α ≤ 1` and `0 ≤ K₃`, then, with
`τ = |s - t|`, `L = exp (K₁ τ)` and `σ = secondVariationBound K₁ K₂ τ`,
`‖H x - H y‖ ≤ τ L (3 K₂ L σ ‖x - y‖ + K₃ exp (3 K₁ τ) ‖x - y‖ ^ α)`. -/
theorem norm_secondVariationOn_sub_le_of_invariant (hv : IsC2FieldOn v Dv D2v a b K₀ Q₀)
    (hSc : Convex ℝ S) (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) (hD2v : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖D2v r y‖ ≤ K₂)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK₃ : 0 ≤ K₃)
    (hD2vH : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ‖D2v r y - D2v r z‖ ≤ K₃ * ‖y - z‖ ^ α)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖secondVariationOn v Dv D2v a b s t x - secondVariationOn v Dv D2v a b s t y‖ ≤
      |s - t| * Real.exp (K₁ * |s - t|) *
        (3 * K₂ * Real.exp (K₁ * |s - t|) * secondVariationBound K₁ K₂ |s - t| * ‖x - y‖ +
          K₃ * Real.exp (3 * K₁ * |s - t|) * ‖x - y‖ ^ α) := by
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv t ht x hx)
  have hK₂ : 0 ≤ K₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hD2v t ht x hx)
  have hsub : uIcc t s ⊆ Icc a b := uIcc_subset_Icc ht hs
  set τ := |s - t| with hτdef
  set L := Real.exp (K₁ * τ) with hLdef
  set σ := secondVariationBound K₁ K₂ τ with hσdef
  set d := ‖x - y‖ with hddef
  have hL1 : 1 ≤ L := Real.one_le_exp (mul_nonneg hK₁ (abs_nonneg _))
  have hL : 0 ≤ L := zero_le_one.trans hL1
  have hτ : 0 ≤ τ := abs_nonneg _
  have hσ : 0 ≤ σ := by rw [hσdef, secondVariationBound]; positivity
  have hd : 0 ≤ d := norm_nonneg _
  have hdα : 0 ≤ d ^ α := Real.rpow_nonneg hd _
  have hLr (r : ℝ) (hr : r ∈ uIcc t s) : Real.exp (K₁ * |r - t|) ≤ L :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hr) hK₁)
  have hσr (r : ℝ) (hr : r ∈ uIcc t s) : secondVariationBound K₁ K₂ |r - t| ≤ σ :=
    secondVariationBound_mono hK₁ hK₂ (abs_nonneg _) (abs_sub_left_of_mem_uIcc hr)
  have hJ (r : ℝ) (hr : r ∈ uIcc t s) {z : E} (hz : z ∈ S) :
      ‖variationOn v Dv a b r t z‖ ≤ L :=
    (hv.norm_variationOn_le_of_invariant hS hDv (hsub hr) ht hz).trans (hLr r hr)
  have hH (r : ℝ) (hr : r ∈ uIcc t s) {z : E} (hz : z ∈ S) :
      ‖secondVariationOn v Dv D2v a b r t z‖ ≤ σ :=
    (hv.norm_secondVariationOn_le_of_invariant hS hDv hD2v (hsub hr) ht hz).trans (hσr r hr)
  have hJd (r : ℝ) (hr : r ∈ uIcc t s) :
      ‖variationOn v Dv a b r t x - variationOn v Dv a b r t y‖ ≤ σ * d :=
    (hv.norm_variationOn_sub_le_of_invariant hSc hS hDv hD2v (hsub hr) ht hx hy).trans
      (mul_le_mul_of_nonneg_right (hσr r hr) hd)
  have hΦd (r : ℝ) (hr : r ∈ uIcc t s) :
      ‖flowOn v a b r t x - flowOn v a b r t y‖ ≤ L * d :=
    (hv.norm_flowOn_sub_le_of_invariant hSc hS hDv (hsub hr) ht hx hy).trans
      (mul_le_mul_of_nonneg_right (hLr r hr) hd)
  have hDvLip (r : ℝ) (hr : r ∈ Icc a b) {z w : E} (hz : z ∈ S) (hw : w ∈ S) :
      ‖Dv r z - Dv r w‖ ≤ K₂ * ‖z - w‖ :=
    hSc.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := Dv r) (f' := D2v r)
      (fun q _ ↦ (hv.hasFDerivAt_deriv r hr q).hasFDerivWithinAt)
      (fun q hq ↦ hD2v r hr q hq) hw hz
  have h := norm_le_gronwallBound_of_uIcc (F := E →L[ℝ] E →L[ℝ] E)
    (e := fun r ↦ secondVariationOn v Dv D2v a b r t x - secondVariationOn v Dv D2v a b r t y)
    (e' := fun r ↦ (ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x))).comp
        (secondVariationOn v Dv D2v a b r t x) +
        secondVariationForcing (D2v r (flowOn v a b r t x)) (variationOn v Dv a b r t x) -
      ((ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t y))).comp
        (secondVariationOn v Dv D2v a b r t y) +
        secondVariationForcing (D2v r (flowOn v a b r t y)) (variationOn v Dv a b r t y)))
    (δ := 0) (K := K₁) (A := 3 * K₂ * L * σ * d + K₃ * (L * L * L) * d ^ α) ht hs
    (fun r hr ↦ HasDerivWithinAt.sub (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] E)
      (hv.hasDerivWithinAt_secondVariationOn hr ht x)
      (hv.hasDerivWithinAt_secondVariationOn hr ht y))
    (by rw [hv.secondVariationOn_self ht, hv.secondVariationOn_self ht, sub_self,
      ContinuousLinearMap.opNorm_zero])
    (fun r hr ↦ by
      have hr' := hsub hr
      have hΦx := hS r hr' t ht hx
      have hΦy := hS r hr' t ht hy
      set A₁ := Dv r (flowOn v a b r t x)
      set A₂ := Dv r (flowOn v a b r t y)
      set H₁ := secondVariationOn v Dv D2v a b r t x
      set H₂ := secondVariationOn v Dv D2v a b r t y
      set T₁ := D2v r (flowOn v a b r t x)
      set T₂ := D2v r (flowOn v a b r t y)
      set J₁ := variationOn v Dv a b r t x
      set J₂ := variationOn v Dv a b r t y
      have hsplit : (ContinuousLinearMap.compL ℝ E E E A₁).comp H₁ +
          secondVariationForcing T₁ J₁ -
          ((ContinuousLinearMap.compL ℝ E E E A₂).comp H₂ + secondVariationForcing T₂ J₂) =
          (ContinuousLinearMap.compL ℝ E E E A₁).comp (H₁ - H₂) +
            (ContinuousLinearMap.compL ℝ E E E (A₁ - A₂)).comp H₂ +
            (secondVariationForcing T₁ J₁ - secondVariationForcing T₂ J₂) := by
        rw [map_sub, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
        abel
      rw [hsplit]
      have h₁ : ‖(ContinuousLinearMap.compL ℝ E E E A₁).comp (H₁ - H₂)‖ ≤ K₁ * ‖H₁ - H₂‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_compL_apply_le _).trans (hDv r hr' _ hΦx))
          (ContinuousLinearMap.opNorm_nonneg _))
      have h₂ : ‖(ContinuousLinearMap.compL ℝ E E E (A₁ - A₂)).comp H₂‖ ≤ K₂ * (L * d) * σ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul ((norm_compL_apply_le _).trans
          ((hDvLip r hr' hΦx hΦy).trans (mul_le_mul_of_nonneg_left (hΦd r hr) hK₂)))
          (hH r hr hy) (ContinuousLinearMap.opNorm_nonneg _) (by positivity))
      have hT : ‖T₁ - T₂‖ ≤ K₃ * (L * d ^ α) := by
        refine (hD2vH r hr' _ hΦx _ hΦy).trans (mul_le_mul_of_nonneg_left ?_ hK₃)
        calc ‖flowOn v a b r t x - flowOn v a b r t y‖ ^ α ≤ (L * d) ^ α :=
              Real.rpow_le_rpow (norm_nonneg _) (hΦd r hr) hα₀
          _ = L ^ α * d ^ α := Real.mul_rpow hL hd
          _ ≤ L * d ^ α := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hL1 hα₁) hdα
      have hT₂ : ‖T₂‖ ≤ K₂ := hD2v r hr' _ hΦy
      have hJ₁ := hJ r hr hx
      have hJ₂ := hJ r hr hy
      have h₃ : ‖secondVariationForcing T₁ J₁ - secondVariationForcing T₂ J₂‖ ≤
          K₃ * (L * d ^ α) * L * L + K₂ * (L + L) * (σ * d) := by
        refine (norm_secondVariationForcing_sub_le _ _ _ _).trans (add_le_add ?_ ?_)
        · exact mul_le_mul (mul_le_mul hT hJ₁ (norm_nonneg _) (by positivity)) hJ₁
            (norm_nonneg _) (by positivity)
        · exact mul_le_mul (mul_le_mul hT₂ (add_le_add hJ₁ hJ₂) (by positivity) hK₂)
            (hJd r hr) (norm_nonneg _) (by positivity)
      exact norm_add₃_le.trans ((add_le_add (add_le_add h₁ h₂) h₃).trans_eq (by ring)))
  have hA : 0 ≤ 3 * K₂ * L * σ * d + K₃ * (L * L * L) * d ^ α := by positivity
  refine h.trans ((gronwallBound_le_add_mul_exp hK₁ hA).trans_eq ?_)
  rw [show 3 * K₁ * τ = K₁ * τ + K₁ * τ + K₁ * τ by ring, Real.exp_add, Real.exp_add]
  ring

/-- **The second variation is `α`-Hölder on a convex invariant set**, with the constant
`secondVariationHolderConst K₁ K₂ K₃ |s - t|`, for `0 ≤ α ≤ 1`. -/
theorem norm_secondVariationOn_sub_le_rpow_of_invariant (hv : IsC2FieldOn v Dv D2v a b K₀ Q₀)
    (hSc : Convex ℝ S) (hS : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, MapsTo (flowOn v a b s t) S S)
    (hDv : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖Dv r y‖ ≤ K₁) (hD2v : ∀ r ∈ Icc a b, ∀ y ∈ S, ‖D2v r y‖ ≤ K₂)
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK₃ : 0 ≤ K₃)
    (hD2vH : ∀ r ∈ Icc a b, ∀ y ∈ S, ∀ z ∈ S, ‖D2v r y - D2v r z‖ ≤ K₃ * ‖y - z‖ ^ α)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖secondVariationOn v Dv D2v a b s t x - secondVariationOn v Dv D2v a b s t y‖ ≤
      secondVariationHolderConst K₁ K₂ K₃ |s - t| * ‖x - y‖ ^ α := by
  have hK₁ : 0 ≤ K₁ := (norm_nonneg _).trans (hDv t ht x hx)
  have hK₂ : 0 ≤ K₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hD2v t ht x hx)
  set τ := |s - t|
  set σ := secondVariationBound K₁ K₂ τ with hσdef
  have hτ : 0 ≤ τ := abs_nonneg _
  have hσ : 0 ≤ σ := by rw [hσdef, secondVariationBound]; positivity
  have hd : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hdα : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg hd _
  have hP : 0 ≤ τ * Real.exp (K₁ * τ) *
      (3 * K₂ * Real.exp (K₁ * τ) * σ + K₃ * Real.exp (3 * K₁ * τ)) := by positivity
  rcases le_or_gt ‖x - y‖ 1 with hd1 | hd1
  · have hle : ‖x - y‖ ≤ ‖x - y‖ ^ α := Real.self_le_rpow_of_le_one hd hd1 hα₁
    refine (hv.norm_secondVariationOn_sub_le_of_invariant hSc hS hDv hD2v hα₀ hα₁ hK₃ hD2vH hs ht
      hx hy).trans ?_
    have hstep : 3 * K₂ * Real.exp (K₁ * τ) * σ * ‖x - y‖ + K₃ * Real.exp (3 * K₁ * τ) *
        ‖x - y‖ ^ α ≤ (3 * K₂ * Real.exp (K₁ * τ) * σ + K₃ * Real.exp (3 * K₁ * τ)) *
          ‖x - y‖ ^ α := by
      have h3 : 0 ≤ 3 * K₂ * Real.exp (K₁ * τ) * σ := by positivity
      linarith [mul_le_mul_of_nonneg_left hle h3]
    calc τ * Real.exp (K₁ * τ) * (3 * K₂ * Real.exp (K₁ * τ) * σ * ‖x - y‖ +
          K₃ * Real.exp (3 * K₁ * τ) * ‖x - y‖ ^ α)
        ≤ τ * Real.exp (K₁ * τ) * ((3 * K₂ * Real.exp (K₁ * τ) * σ +
          K₃ * Real.exp (3 * K₁ * τ)) * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ secondVariationHolderConst K₁ K₂ K₃ τ * ‖x - y‖ ^ α := by
          unfold secondVariationHolderConst
          linarith [mul_nonneg hσ hdα]
  · have hone : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hd1.le hα₀
    calc ‖secondVariationOn v Dv D2v a b s t x - secondVariationOn v Dv D2v a b s t y‖
        ≤ ‖secondVariationOn v Dv D2v a b s t x‖ + ‖secondVariationOn v Dv D2v a b s t y‖ :=
          norm_sub_le (E := E →L[ℝ] E →L[ℝ] E) _ _
      _ ≤ σ + σ := add_le_add (hv.norm_secondVariationOn_le_of_invariant hS hDv hD2v hs ht hx)
          (hv.norm_secondVariationOn_le_of_invariant hS hDv hD2v hs ht hy)
      _ ≤ 2 * σ * ‖x - y‖ ^ α := by linarith [mul_le_mul_of_nonneg_left hone hσ]
      _ ≤ secondVariationHolderConst K₁ K₂ K₃ τ * ‖x - y‖ ^ α := by
          unfold secondVariationHolderConst
          linarith [mul_nonneg hP hdα]

end IsC2FieldOn

end PDE.Analysis.ODE
