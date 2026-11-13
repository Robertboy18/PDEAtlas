/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.Variation

/-!
# The second variation of a flow

Let `v` be a time-dependent field whose first and second spatial derivatives `Dv`, `D²v` are
jointly continuous and bounded by `K`, `K₂` on `[a, b] × E`. With `Φ = flowOn v a b r t x` and
`J = variationOn v Dv a b r t x`, the second variation `secondVariationOn v Dv D2v a b s t x`
solves
`∂ₛ H = Dv(s, Φ) ∘ H + (h ↦ D²v(s, Φ)(J h) ∘ J)` with `H = 0` at `s = t`.
It is the derivative of the first variation in the initial point, so each map
`flowOn v a b s t` is `C²`. The first variation is Lipschitz in the initial point, and the
second variation is jointly continuous in the final time and the initial point.

## Main results

* `IsC2FieldOn.hasFDerivAt_variationOn`: the second variation is the derivative of the first.
* `IsC2FieldOn.contDiff_flowOn`: each map `flowOn v a b s t` is `C²`.
* `IsC2FieldOn.norm_variationOn_sub_le`, `IsC2FieldOn.norm_secondVariationOn_le`: bounds.
* `IsC2FieldOn.continuousOn_secondVariationOn_final`: joint continuity in the final time and
  the initial point.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The field `v` has spatial derivatives `Dv` and `D2v` that are jointly continuous on
`[a, b] × E` and bounded by `K` and `K₂`. -/
structure IsC2FieldOn (v : ℝ → E → E) (Dv : ℝ → E → E →L[ℝ] E)
    (D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E) (a b : ℝ) (K K₂ : ℝ≥0) : Prop
    extends IsC1FieldOn v Dv a b K where
  /-- Joint continuity of the second derivative. -/
  continuousOn_deriv₂ : ContinuousOn (Function.uncurry D2v) (Icc a b ×ˢ univ)
  /-- `D2v t x` is the derivative of `Dv t` at `x`. -/
  hasFDerivAt_deriv : ∀ t ∈ Icc a b, ∀ x, HasFDerivAt (Dv t) (D2v t x) x
  /-- The bound `‖D2v‖ ≤ K₂`. -/
  norm_deriv₂_le : ∀ t ∈ Icc a b, ∀ x, ‖D2v t x‖ ≤ K₂

/-- The forcing `h ↦ T (J h) ∘ J` of the second variation, for `T = D²v(r, Φ)`. -/
def secondVariationForcing (T : E →L[ℝ] E →L[ℝ] E) (J : E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.compL ℝ E E E).flip J).comp (T.comp J)

/-- The forcing applied to `h` is `T (J h) ∘ J`. -/
@[simp]
theorem secondVariationForcing_apply (T : E →L[ℝ] E →L[ℝ] E) (J : E →L[ℝ] E) (h : E) :
    secondVariationForcing T J h = (T (J h)).comp J := rfl

/-- `‖h ↦ T (J h) ∘ J‖ ≤ ‖T‖ ‖J‖²`. -/
theorem norm_secondVariationForcing_le (T : E →L[ℝ] E →L[ℝ] E) (J : E →L[ℝ] E) :
    ‖secondVariationForcing T J‖ ≤ ‖T‖ * ‖J‖ * ‖J‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ by
    rw [secondVariationForcing_apply]
    calc ‖(T (J h)).comp J‖ ≤ ‖T (J h)‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖ * ‖J h‖ * ‖J‖ := by gcongr; exact T.le_opNorm _
      _ ≤ ‖T‖ * (‖J‖ * ‖h‖) * ‖J‖ := by gcongr; exact J.le_opNorm _
      _ = ‖T‖ * ‖J‖ * ‖J‖ * ‖h‖ := by ring

/-- The forcing of the second variation depends continuously on `T` and `J`. -/
theorem norm_secondVariationForcing_sub_le (T T' : E →L[ℝ] E →L[ℝ] E) (J J' : E →L[ℝ] E) :
    ‖secondVariationForcing T J - secondVariationForcing T' J'‖ ≤
      ‖T - T'‖ * ‖J‖ * ‖J‖ + ‖T'‖ * (‖J‖ + ‖J'‖) * ‖J - J'‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ by
    rw [sub_apply, secondVariationForcing_apply, secondVariationForcing_apply]
    have hsplit : (T (J h)).comp J - (T' (J' h)).comp J' =
        ((T - T') (J h)).comp J + (T' (J h - J' h)).comp J + (T' (J' h)).comp (J - J') := by
      simp only [map_sub, sub_apply, ContinuousLinearMap.comp_sub,
        ContinuousLinearMap.sub_comp]
      abel
    rw [hsplit]
    -- `‖(A x).comp B‖ ≤ ‖A‖ ‖x‖ ‖B‖` for each of the three terms
    have hcomp (A : E →L[ℝ] E →L[ℝ] E) (y : E) (B : E →L[ℝ] E) : ‖(A y).comp B‖ ≤ ‖A‖ * ‖y‖ * ‖B‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact A.le_opNorm y)
    calc _ ≤ ‖T - T'‖ * ‖J h‖ * ‖J‖ + ‖T'‖ * ‖J h - J' h‖ * ‖J‖ + ‖T'‖ * ‖J' h‖ * ‖J - J'‖ :=
          norm_add₃_le.trans (add_le_add (add_le_add (hcomp _ _ _) (hcomp _ _ _)) (hcomp _ _ _))
      _ ≤ ‖T - T'‖ * (‖J‖ * ‖h‖) * ‖J‖ + ‖T'‖ * (‖J - J'‖ * ‖h‖) * ‖J‖ +
          ‖T'‖ * (‖J'‖ * ‖h‖) * ‖J - J'‖ := by
        gcongr
        · exact J.le_opNorm h
        · rw [← sub_apply]
          exact (J - J').le_opNorm h
        · exact J'.le_opNorm h
      _ = _ := by ring

/-- The second variation of the flow of `v` along the flow line through `x` at time `t`. -/
def secondVariationOn (v : ℝ → E → E) (Dv : ℝ → E → E →L[ℝ] E)
    (D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E) (a b s t : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] E :=
  flowOn (fun r H ↦ (ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x))).comp H +
    secondVariationForcing (D2v r (flowOn v a b r t x)) (variationOn v Dv a b r t x)) a b s t 0

variable {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E}
  {a b : ℝ} {K K₂ : ℝ≥0}

namespace IsC2FieldOn

/-- The spatial derivative of a field with `‖D²v‖ ≤ K₂` is `K₂`-Lipschitz. -/
theorem lipschitzWith_deriv (hv : IsC2FieldOn v Dv D2v a b K K₂) {t : ℝ} (ht : t ∈ Icc a b) :
    LipschitzWith K₂ (Dv t) :=
  lipschitzWith_of_nnnorm_fderiv_le (fun x ↦ (hv.hasFDerivAt_deriv t ht x).differentiableAt)
    fun x ↦ by
      rw [(hv.hasFDerivAt_deriv t ht x).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hv.norm_deriv₂_le t ht x

variable [FiniteDimensional ℝ E]

/-- The forcing of the second variation is continuous in time. -/
theorem continuousOn_forcing (hv : IsC2FieldOn v Dv D2v a b K K₂) {t : ℝ} (ht : t ∈ Icc a b)
    (x : E) : ContinuousOn (fun r ↦ secondVariationForcing (D2v r (flowOn v a b r t x))
      (variationOn v Dv a b r t x)) (Icc a b) := by
  have hJ := hv.continuousOn_variationOn_time ht x
  have hT : ContinuousOn (fun r ↦ D2v r (flowOn v a b r t x)) (Icc a b) :=
    hv.continuousOn_deriv₂.comp (f := fun r ↦ (r, flowOn v a b r t x)) (continuousOn_id.prodMk
      (hv.isLipschitzFieldOn.continuousOn_flowOn_time ht x)) fun _ hr ↦ ⟨hr, mem_univ _⟩
  exact (((ContinuousLinearMap.compL ℝ E E E).flip).continuous.comp_continuousOn hJ).clm_comp
    (hT.clm_comp hJ)

/-- The second variational field is a Lipschitz field. -/
theorem isLipschitzFieldOn_secondVariation (hv : IsC2FieldOn v Dv D2v a b K K₂) {t : ℝ}
    (ht : t ∈ Icc a b) (x : E) :
    IsLipschitzFieldOn (fun r (H : E →L[ℝ] E →L[ℝ] E) ↦
      (ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x))).comp H +
        secondVariationForcing (D2v r (flowOn v a b r t x)) (variationOn v Dv a b r t x))
      a b K := by
  refine ⟨?_, fun r hr ↦ LipschitzWith.of_dist_le_mul fun H H' ↦ ?_⟩
  · have hA := (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn
      (hv.continuousOn_deriv_flowOn ht x)
    exact ((hA.comp continuousOn_fst fun _ hp ↦ hp.1).clm_comp continuousOn_snd).add
      ((hv.continuousOn_forcing ht x).comp continuousOn_fst fun _ hp ↦ hp.1)
  · rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← ContinuousLinearMap.comp_sub]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
      ((norm_compL_apply_le _).trans (hv.norm_le r hr _)) (norm_nonneg _))

/-- The second variation vanishes at the initial time. -/
theorem secondVariationOn_self (hv : IsC2FieldOn v Dv D2v a b K K₂) {t : ℝ} (ht : t ∈ Icc a b)
    (x : E) : secondVariationOn v Dv D2v a b t t x = 0 :=
  (hv.isLipschitzFieldOn_secondVariation ht x).flowOn_self ht _

/-- The second variation solves the second variational equation within `[a, b]`. -/
theorem hasDerivWithinAt_secondVariationOn (hv : IsC2FieldOn v Dv D2v a b K K₂) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    HasDerivWithinAt (fun r ↦ secondVariationOn v Dv D2v a b r t x)
      ((ContinuousLinearMap.compL ℝ E E E (Dv s (flowOn v a b s t x))).comp
          (secondVariationOn v Dv D2v a b s t x) +
        secondVariationForcing (D2v s (flowOn v a b s t x)) (variationOn v Dv a b s t x))
      (Icc a b) s :=
  (hv.isLipschitzFieldOn_secondVariation ht x).hasDerivWithinAt_flowOn hs ht _

/-- The second variation is continuous in its final time. -/
theorem continuousOn_secondVariationOn_time (hv : IsC2FieldOn v Dv D2v a b K K₂) {t : ℝ}
    (ht : t ∈ Icc a b) (x : E) :
    ContinuousOn (fun r ↦ secondVariationOn v Dv D2v a b r t x) (Icc a b) :=
  (hv.isLipschitzFieldOn_secondVariation ht x).continuousOn_flowOn_time ht _

/-- **The first variation is Lipschitz in the initial point**, with constant
`gronwallBound 0 K (K₂ L²) (b - a)`, `L = exp (K (b - a))`. -/
theorem norm_variationOn_sub_le (hv : IsC2FieldOn v Dv D2v a b K K₂) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x y : E) :
    ‖variationOn v Dv a b s t x - variationOn v Dv a b s t y‖ ≤
      gronwallBound 0 K (K₂ * Real.exp (K * (b - a)) * Real.exp (K * (b - a))) (b - a) *
        ‖x - y‖ := by
  have hL := hv.isLipschitzFieldOn
  set L := Real.exp (K * (b - a))
  have h := norm_sub_le_of_hasDerivWithinAt_affine (G := E →L[ℝ] E)
    (M₁ := fun r ↦ variationOn v Dv a b r t x) (M₂ := fun r ↦ variationOn v Dv a b r t y)
    (A₁ := fun r ↦ ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x)))
    (A₂ := fun r ↦ ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t y)))
    (B₁ := fun _ ↦ 0) (B₂ := fun _ ↦ 0) (K := K) (ε₁ := K₂ * L * ‖x - y‖) (ε₂ := 0) (m := L) ht
    (fun r hr ↦ by simpa using hv.hasDerivWithinAt_variationOn hr ht x)
    (fun r hr ↦ by simpa using hv.hasDerivWithinAt_variationOn hr ht y)
    (fun r hr ↦ (norm_compL_apply_le _).trans (hv.norm_le r hr _))
    (fun r hr ↦ by
      rw [← map_sub, mul_assoc]
      refine (norm_compL_apply_le _).trans (((hv.lipschitzWith_deriv hr).norm_sub_le _ _).trans ?_)
      gcongr
      simpa only [dist_eq_norm] using hL.dist_flowOn_le_of_mem hr ht x y)
    (fun r hr ↦ hv.norm_variationOn_le_of_mem hr ht x) (fun _ _ ↦ by simp) hs
  rw [hv.variationOn_self ht, hv.variationOn_self ht, sub_self, norm_zero, add_zero,
    show K₂ * L * ‖x - y‖ * L = ‖x - y‖ * (K₂ * L * L) by ring,
    show (0 : ℝ) = ‖x - y‖ * 0 by ring, gronwallBound_mul] at h
  have hab : a ≤ b := ht.1.trans ht.2
  have hmono : gronwallBound 0 K (K₂ * L * L) |s - t| ≤
      gronwallBound 0 K (K₂ * L * L) (b - a) := by
    apply gronwallBound_mono le_rfl (by positivity) K.coe_nonneg
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  calc ‖variationOn v Dv a b s t x - variationOn v Dv a b s t y‖
      ≤ ‖x - y‖ * gronwallBound 0 K (K₂ * L * L) |s - t| := h
    _ ≤ ‖x - y‖ * gronwallBound 0 K (K₂ * L * L) (b - a) := by gcongr
    _ = _ := by ring

/-- **Bound on the second variation**:
`‖secondVariationOn v Dv D2v a b s t x‖ ≤ gronwallBound 0 K (K₂ L²) (b - a)`,
`L = exp (K (b - a))`. -/
theorem norm_secondVariationOn_le (hv : IsC2FieldOn v Dv D2v a b K K₂) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    ‖secondVariationOn v Dv D2v a b s t x‖ ≤
      gronwallBound 0 K (K₂ * Real.exp (K * (b - a)) * Real.exp (K * (b - a))) (b - a) := by
  set L := Real.exp (K * (b - a))
  have h := norm_le_gronwallBound_of_hasDerivWithinAt (F := E →L[ℝ] E →L[ℝ] E)
    (e := fun r ↦ secondVariationOn v Dv D2v a b r t x) (δ := 0) (K := K) (A := K₂ * L * L) ht
    (fun r hr ↦ hv.hasDerivWithinAt_secondVariationOn hr ht x)
    (by rw [hv.secondVariationOn_self ht, ContinuousLinearMap.opNorm_zero])
    (fun r hr ↦ by
      have h₁ : ‖(ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x))).comp
          (secondVariationOn v Dv D2v a b r t x)‖ ≤ K * ‖secondVariationOn v Dv D2v a b r t x‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_compL_apply_le _).trans (hv.norm_le r hr _)) (norm_nonneg _))
      have hJ := hv.norm_variationOn_le_of_mem hr ht x
      have h₂ : ‖secondVariationForcing (D2v r (flowOn v a b r t x))
          (variationOn v Dv a b r t x)‖ ≤ K₂ * L * L := by
        refine (norm_secondVariationForcing_le _ _).trans ?_
        gcongr
        exact hv.norm_deriv₂_le r hr _
      exact (norm_add_le _ _).trans (add_le_add h₁ h₂)) hs
  have hab : a ≤ b := ht.1.trans ht.2
  refine h.trans (gronwallBound_mono le_rfl (by positivity) K.coe_nonneg ?_)
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- **The second variation is the derivative of the first variation.** -/
theorem hasFDerivAt_variationOn (hv : IsC2FieldOn v Dv D2v a b K K₂) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    HasFDerivAt (variationOn v Dv a b s t) (secondVariationOn v Dv D2v a b s t x) x := by
  have hL := hv.isLipschitzFieldOn
  set L := Real.exp (K * (b - a))
  let Df : ℝ → (E →L[ℝ] E) → E → ((E →L[ℝ] E) × E) →L[ℝ] (E →L[ℝ] E) := fun r M p ↦
    (ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t p))).comp
        (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) E) +
      ((ContinuousLinearMap.compL ℝ E E E).flip M).comp
        ((D2v r (flowOn v a b r t p)).comp
          ((variationOn v Dv a b r t p).comp (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) E)))
  have hinl (r : ℝ) (M : E →L[ℝ] E) (p : E) :
      (Df r M p).comp (ContinuousLinearMap.inl ℝ (E →L[ℝ] E) E) =
        ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t p)) := by
    ext H : 1
    simp [Df]
  have hinr (r : ℝ) (p : E) :
      (Df r (variationOn v Dv a b r t p) p).comp (ContinuousLinearMap.inr ℝ (E →L[ℝ] E) E) =
        secondVariationForcing (D2v r (flowOn v a b r t p)) (variationOn v Dv a b r t p) := by
    ext h : 1
    simp [Df]
  have hΦ : ContinuousOn (fun q : ℝ × E ↦ flowOn v a b q.1 t q.2) (Icc a b ×ˢ univ) :=
    hL.continuousOn_flowOn.comp (f := fun q : ℝ × E ↦ (q.1, t, q.2))
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      fun q hq ↦ ⟨hq.1, ht, mem_univ _⟩
  have hmaps : MapsTo (fun q : ℝ × E ↦ (q.1, flowOn v a b q.1 t q.2)) (Icc a b ×ˢ univ)
      (Icc a b ×ˢ univ) := fun q hq ↦ ⟨hq.1, mem_univ _⟩
  have hA : ContinuousOn (fun q : ℝ × E ↦ Dv q.1 (flowOn v a b q.1 t q.2)) (Icc a b ×ˢ univ) :=
    hv.continuousOn_deriv.comp (f := fun q : ℝ × E ↦ (q.1, flowOn v a b q.1 t q.2))
      (continuousOn_fst.prodMk hΦ) hmaps
  have hT : ContinuousOn (fun q : ℝ × E ↦ D2v q.1 (flowOn v a b q.1 t q.2)) (Icc a b ×ˢ univ) :=
    hv.continuousOn_deriv₂.comp (f := fun q : ℝ × E ↦ (q.1, flowOn v a b q.1 t q.2))
      (continuousOn_fst.prodMk hΦ) hmaps
  have hJ := hv.continuousOn_variationOn_final ht
  have hproj : MapsTo (fun q : ℝ × (E →L[ℝ] E) × E ↦ (q.1, q.2.2))
      (Icc a b ×ˢ univ) (Icc a b ×ˢ univ) := fun q hq ↦ ⟨hq.1, mem_univ _⟩
  have hcproj : ContinuousOn (fun q : ℝ × (E →L[ℝ] E) × E ↦ (q.1, q.2.2)) (Icc a b ×ˢ univ) :=
    (continuous_fst.prodMk continuous_snd.snd).continuousOn
  refine hasFDerivAt_of_parametric (f := fun r M p ↦ (Dv r (flowOn v a b r t p)).comp M)
    (Df := Df) (y := fun p r ↦ variationOn v Dv a b r t p)
    (Z := fun r ↦ secondVariationOn v Dv D2v a b r t x) (Dy₀ := 0) (ρ := 1)
    (C := gronwallBound 0 K (K₂ * L * L) (b - a)) (K := K)
    ht one_pos ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hv.secondVariationOn_self ht x) hs
  · have h₁ : ContinuousOn (fun q : ℝ × (E →L[ℝ] E) × E ↦
        (ContinuousLinearMap.compL ℝ E E E (Dv q.1 (flowOn v a b q.1 t q.2.2))).comp
          (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) E)) (Icc a b ×ˢ univ) :=
      ((ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn
        (hA.comp hcproj hproj)).clm_comp continuousOn_const
    have hM : ContinuousOn (fun q : ℝ × (E →L[ℝ] E) × E ↦
        (ContinuousLinearMap.compL ℝ E E E).flip q.2.1) (Icc a b ×ˢ univ) :=
      (ContinuousLinearMap.compL ℝ E E E).flip.continuous.comp_continuousOn
        (continuous_snd.fst : Continuous fun q : ℝ × (E →L[ℝ] E) × E ↦ q.2.1).continuousOn
    have h₂ : ContinuousOn (fun q : ℝ × (E →L[ℝ] E) × E ↦
        ((ContinuousLinearMap.compL ℝ E E E).flip q.2.1).comp
          ((D2v q.1 (flowOn v a b q.1 t q.2.2)).comp ((variationOn v Dv a b q.1 t q.2.2).comp
            (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) E)))) (Icc a b ×ˢ univ) :=
      hM.clm_comp ((hT.comp hcproj hproj).clm_comp
        ((hJ.comp hcproj hproj).clm_comp continuousOn_const))
    exact h₁.add h₂
  · intro r hr M p
    exact (HasFDerivAt.comp (M, p) (g := Dv r)
      (f := fun q : (E →L[ℝ] E) × E ↦ flowOn v a b r t q.2) (hv.hasFDerivAt_deriv r hr _)
      (HasFDerivAt.comp (M, p) (g := flowOn v a b r t) (f := Prod.snd)
        (hv.hasFDerivAt_flowOn hr ht p) hasFDerivAt_snd)).clm_comp hasFDerivAt_fst
  · intro r hr
    rw [hinl]
    exact (norm_compL_apply_le _).trans (hv.norm_le r hr _)
  · exact fun p _ r hr ↦ hv.hasDerivWithinAt_variationOn hr ht p
  · exact (hasFDerivAt_const _ x).congr_of_eventuallyEq (.of_forall (hv.variationOn_self ht))
  · exact fun p _ r hr ↦ hv.norm_variationOn_sub_le hr ht p x
  · intro r hr
    rw [hinl, hinr]
    exact hv.hasDerivWithinAt_secondVariationOn hr ht x

/-- The second variation depends continuously on the initial point, uniformly in the final
time. -/
theorem exists_forall_norm_secondVariationOn_sub_le (hv : IsC2FieldOn v Dv D2v a b K K₂)
    {t : ℝ} (ht : t ∈ Icc a b) (x₀ : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ s ∈ Icc a b,
      ‖secondVariationOn v Dv D2v a b s t x - secondVariationOn v Dv D2v a b s t x₀‖ ≤ ε := by
  have hL := hv.isLipschitzFieldOn
  have hab : a ≤ b := ht.1.trans ht.2
  set L : ℝ := Real.exp (K * (b - a))
  have hL0 : 0 < L := Real.exp_pos _
  have hgr₀ {e z : ℝ} (he : 0 ≤ e) (hz : 0 ≤ z) : 0 ≤ gronwallBound 0 K e z := by
    simpa [gronwallBound_x0] using gronwallBound_mono (δ := 0) le_rfl he K.coe_nonneg hz
  set C₂ : ℝ := gronwallBound 0 K (K₂ * L * L) (b - a)
  have hC₂ : 0 ≤ C₂ := hgr₀ (by positivity) (sub_nonneg.mpr hab)
  set G₁ : ℝ := gronwallBound 0 K 1 (b - a)
  have hG₁ : 0 ≤ G₁ := hgr₀ zero_le_one (sub_nonneg.mpr hab)
  set θ : ℝ := ε / ((1 + L * L) * (G₁ + 1))
  have hθ : 0 < θ := div_pos hε (by positivity)
  obtain ⟨δ₁, hδ₁, hclose⟩ := exists_forall_dist_lt_of_continuousOn (G := D2v)
    hv.continuousOn_deriv₂ (c := fun r ↦ flowOn v a b r t x₀)
    (hL.continuousOn_flowOn_time ht x₀) hθ
  set c : ℝ := 3 * K₂ * L * C₂ + 1
  have hc : 0 < c := by positivity
  refine ⟨min (δ₁ / L) (θ / c), lt_min (div_pos hδ₁ hL0) (div_pos hθ hc), fun x hx s hs ↦ ?_⟩
  set d : ℝ := ‖x - x₀‖
  rw [dist_eq_norm] at hx
  have hd₁ : d < δ₁ / L := hx.trans_le (min_le_left _ _)
  have hd₂ : c * d ≤ θ := ((lt_div_iff₀' hc).1 (hx.trans_le (min_le_right _ _))).le
  have hd₀ : 0 ≤ d := norm_nonneg _
  have hΦ (r : ℝ) (hr : r ∈ Icc a b) : ‖flowOn v a b r t x - flowOn v a b r t x₀‖ ≤ L * d := by
    simpa only [dist_eq_norm] using hL.dist_flowOn_le_of_mem hr ht x x₀
  have hJ (r : ℝ) (hr : r ∈ Icc a b) :
      ‖variationOn v Dv a b r t x - variationOn v Dv a b r t x₀‖ ≤ C₂ * d :=
    hv.norm_variationOn_sub_le hr ht x x₀
  have hA (r : ℝ) (hr : r ∈ Icc a b) :
      ‖Dv r (flowOn v a b r t x) - Dv r (flowOn v a b r t x₀)‖ ≤ K₂ * L * d := by
    rw [mul_assoc]
    exact ((hv.lipschitzWith_deriv hr).norm_sub_le _ _).trans (by gcongr; exact hΦ r hr)
  have hT (r : ℝ) (hr : r ∈ Icc a b) :
      ‖D2v r (flowOn v a b r t x) - D2v r (flowOn v a b r t x₀)‖ ≤ θ := by
    refine ((dist_eq_norm (D2v r (flowOn v a b r t x)) (D2v r (flowOn v a b r t x₀))).symm.trans_lt
      (hclose r hr _ ?_)).le
    rw [dist_eq_norm]
    exact (hΦ r hr).trans_lt ((lt_div_iff₀' hL0).1 hd₁)
  have hfx (r : ℝ) (hr : r ∈ Icc a b) := hv.hasDerivWithinAt_secondVariationOn hr ht x
  have hf₀ (r : ℝ) (hr : r ∈ Icc a b) := hv.hasDerivWithinAt_secondVariationOn hr ht x₀
  have hB (r : ℝ) (hr : r ∈ Icc a b) :
      ‖secondVariationForcing (D2v r (flowOn v a b r t x)) (variationOn v Dv a b r t x) -
        secondVariationForcing (D2v r (flowOn v a b r t x₀)) (variationOn v Dv a b r t x₀)‖ ≤
        θ * L * L + K₂ * (L + L) * (C₂ * d) := by
    refine (norm_secondVariationForcing_sub_le (D2v r (flowOn v a b r t x))
      (D2v r (flowOn v a b r t x₀)) (variationOn v Dv a b r t x)
      (variationOn v Dv a b r t x₀)).trans ?_
    have hJx := hv.norm_variationOn_le_of_mem hr ht x
    have hJ₀ := hv.norm_variationOn_le_of_mem hr ht x₀
    have hT₀ := hv.norm_deriv₂_le r hr (flowOn v a b r t x₀)
    have hTr := hT r hr
    have hJr := hJ r hr
    gcongr
  set η : ℝ := K₂ * L * d * C₂ + (θ * L * L + K₂ * (L + L) * (C₂ * d))
  have hη : η ≤ θ * (1 + L * L) := by
    have : K₂ * L * d * C₂ + K₂ * (L + L) * (C₂ * d) = (3 * K₂ * L * C₂) * d := by ring
    have h3 : (3 * K₂ * L * C₂) * d ≤ c * d := by
      gcongr; simp only [c]; linarith
    nlinarith
  have hη₀ : 0 ≤ η := by positivity
  have hgb (z : ℝ) : gronwallBound 0 K η z = η * gronwallBound 0 K 1 z := by
    simpa using gronwallBound_mul η 0 K 1 z
  have hmono : gronwallBound 0 K 1 |s - t| ≤ G₁ := by
    apply gronwallBound_mono le_rfl zero_le_one K.coe_nonneg
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hgb₀ : 0 ≤ gronwallBound 0 K 1 |s - t| := hgr₀ zero_le_one (abs_nonneg _)
  have happly (h : E) : ‖secondVariationOn v Dv D2v a b s t x h -
      secondVariationOn v Dv D2v a b s t x₀ h‖ ≤ η * G₁ * ‖h‖ := by
    have hgr := norm_sub_le_of_hasDerivWithinAt_affine (G := E →L[ℝ] E)
      (M₁ := fun r ↦ secondVariationOn v Dv D2v a b r t x h)
      (M₂ := fun r ↦ secondVariationOn v Dv D2v a b r t x₀ h)
      (A₁ := fun r ↦ ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x)))
      (A₂ := fun r ↦ ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x₀)))
      (B₁ := fun r ↦ secondVariationForcing (D2v r (flowOn v a b r t x))
        (variationOn v Dv a b r t x) h)
      (B₂ := fun r ↦ secondVariationForcing (D2v r (flowOn v a b r t x₀))
        (variationOn v Dv a b r t x₀) h)
      (K := K) (ε₁ := K₂ * L * d) (ε₂ := (θ * L * L + K₂ * (L + L) * (C₂ * d)) * ‖h‖)
      (m := C₂ * ‖h‖) ht
      (fun r hr ↦ by
        simpa using (hfx r hr).clm_apply (hasDerivWithinAt_const r (Icc a b) h))
      (fun r hr ↦ by
        simpa using (hf₀ r hr).clm_apply (hasDerivWithinAt_const r (Icc a b) h))
      (fun r hr ↦ (norm_compL_apply_le _).trans (hv.norm_le r hr _))
      (fun r hr ↦ by
        rw [← map_sub]
        exact (norm_compL_apply_le _).trans (hA r hr))
      (fun r hr ↦ ((secondVariationOn v Dv D2v a b r t x).le_opNorm h).trans
        (mul_le_mul_of_nonneg_right (hv.norm_secondVariationOn_le hr ht x) (norm_nonneg h)))
      (fun r hr ↦ by
        rw [← sub_apply]
        exact (ContinuousLinearMap.le_opNorm _ h).trans
          (mul_le_mul_of_nonneg_right (hB r hr) (norm_nonneg h))) hs
    rw [hv.secondVariationOn_self ht, hv.secondVariationOn_self ht,
      zero_apply, sub_self, norm_zero,
      show K₂ * L * d * (C₂ * ‖h‖) + (θ * L * L + K₂ * (L + L) * (C₂ * d)) * ‖h‖ =
        ‖h‖ * η by ring, show (0 : ℝ) = ‖h‖ * 0 by ring, gronwallBound_mul, hgb] at hgr
    calc _ ≤ ‖h‖ * (η * gronwallBound 0 K 1 |s - t|) := hgr
      _ ≤ ‖h‖ * (η * G₁) := by gcongr
      _ = η * G₁ * ‖h‖ := by ring
  have hop : ‖secondVariationOn v Dv D2v a b s t x - secondVariationOn v Dv D2v a b s t x₀‖ ≤
      η * G₁ :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ by
      rw [sub_apply]; exact happly h
  calc _ ≤ η * G₁ := hop
    _ ≤ θ * (1 + L * L) * G₁ := by gcongr
    _ ≤ ε := by
        have h1 : θ * ((1 + L * L) * (G₁ + 1)) = ε := div_mul_cancel₀ ε (by positivity)
        nlinarith [mul_nonneg hθ.le (by positivity : (0 : ℝ) ≤ 1 + L * L)]

/-- The second variation from a fixed initial time is jointly continuous in the final time and
the initial point. -/
theorem continuousOn_secondVariationOn_final (hv : IsC2FieldOn v Dv D2v a b K K₂) {t : ℝ}
    (ht : t ∈ Icc a b) :
    ContinuousOn (fun q : ℝ × E ↦ secondVariationOn v Dv D2v a b q.1 t q.2) (Icc a b ×ˢ univ) :=
  continuousOn_uncurry_of_uniform (g := fun s x ↦ secondVariationOn v Dv D2v a b s t x)
    (fun x ↦ hv.continuousOn_secondVariationOn_time ht x) fun x₀ ε hε ↦ by
      obtain ⟨δ, hδ, h⟩ := hv.exists_forall_norm_secondVariationOn_sub_le ht x₀ (half_pos hε)
      exact ⟨δ, hδ, fun x hx r hr ↦ lt_of_eq_of_lt
        (dist_eq_norm (secondVariationOn v Dv D2v a b r t x)
          (secondVariationOn v Dv D2v a b r t x₀))
        ((h x hx r hr).trans_lt (half_lt_self hε))⟩

/-- The second variation is continuous in the initial point. -/
theorem continuous_secondVariationOn (hv : IsC2FieldOn v Dv D2v a b K K₂) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    Continuous (secondVariationOn v Dv D2v a b s t) :=
  Metric.continuous_iff.mpr fun x₀ ε hε ↦ by
    obtain ⟨δ, hδ, h⟩ := hv.exists_forall_norm_secondVariationOn_sub_le ht x₀ (half_pos hε)
    exact ⟨δ, hδ, fun x hx ↦ lt_of_eq_of_lt
      (dist_eq_norm (secondVariationOn v Dv D2v a b s t x)
        (secondVariationOn v Dv D2v a b s t x₀))
      ((h x hx s hs).trans_lt (half_lt_self hε))⟩

/-- **Each map `flowOn v a b s t` is `C²`.** -/
theorem contDiff_flowOn (hv : IsC2FieldOn v Dv D2v a b K K₂) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) : ContDiff ℝ 2 (flowOn v a b s t) := by
  rw [show (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 by norm_num,
    contDiff_succ_iff_hasFDerivAt]
  refine ⟨variationOn v Dv a b s t, ?_, fun x ↦ hv.hasFDerivAt_flowOn hs ht x⟩
  rw [Nat.cast_one]
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨secondVariationOn v Dv D2v a b s t,
    hv.continuous_secondVariationOn hs ht, fun x ↦ hv.hasFDerivAt_variationOn hs ht x⟩

end IsC2FieldOn

end PDE.Analysis.ODE
