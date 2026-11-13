/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.Parametric
import PDE.Analysis.Calculus.PartialRegularity

/-!
# The first variation of a flow

Let `v` be a time-dependent field on a finite-dimensional real normed space whose spatial
derivative `Dv` is jointly continuous and bounded by `K` on `[a, b] × E`. The first variation
`variationOn v Dv a b s t x` solves `∂ₛ J = Dv(s, flowOn v a b s t x) ∘ J` with `J = id` at
`s = t`. It is the derivative of `flowOn v a b s t` at `x`, it is jointly continuous in
`(s, t, x)`, it satisfies the chain rule of the cocycle law, and the derivative of the flow in
its initial time `t` is `-(J (v t x))`. Consequently the flow is jointly `C¹` in the initial point
and either time on the open time interval.

## Main results

* `IsC1FieldOn.hasFDerivAt_flowOn`: the first variation is the derivative of the flow.
* `IsC1FieldOn.continuousOn_variationOn`: joint continuity in `(s, t, x)`.
* `IsC1FieldOn.variationOn_eq_comp`: the chain rule of the cocycle law.
* `IsC1FieldOn.hasDerivWithinAt_flowOn_initial`: the derivative in the initial time.
* `IsC1FieldOn.contDiffOn_flowOn_initial`, `IsC1FieldOn.contDiffOn_flowOn_final`: joint `C¹`
  regularity in the initial point and the initial or final time.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace PDE.Analysis.ODE

/-- A function continuous in its first variable and continuous in its second variable uniformly
in the first is jointly continuous. -/
theorem continuousOn_uncurry_of_uniform {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {g : ℝ → X → Y} {I : Set ℝ} (h₁ : ∀ x, ContinuousOn (fun r ↦ g r x) I)
    (h₂ : ∀ x₀, ∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ r ∈ I, dist (g r x) (g r x₀) < ε) :
    ContinuousOn (Function.uncurry g) (I ×ˢ univ) := by
  rw [Metric.continuousOn_iff]
  rintro ⟨r₀, x₀⟩ ⟨hr₀, -⟩ ε hε
  obtain ⟨δ, hδ, hx⟩ := h₂ x₀ (ε / 2) (half_pos hε)
  obtain ⟨δ', hδ', hr⟩ := Metric.continuousOn_iff.mp (h₁ x₀) r₀ hr₀ (ε / 2) (half_pos hε)
  refine ⟨min δ δ', lt_min hδ hδ', ?_⟩
  rintro ⟨r, x⟩ ⟨hr', -⟩ hd
  rw [Prod.dist_eq, max_lt_iff] at hd
  calc dist (g r x) (g r₀ x₀) ≤ dist (g r x) (g r x₀) + dist (g r x₀) (g r₀ x₀) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
        add_lt_add (hx x (hd.2.trans_le (min_le_left _ _)) r hr')
          (hr r hr' (hd.1.trans_le (min_le_right _ _)))
    _ = ε := add_halves ε

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm of `M ↦ A ∘ M` is at most the norm of `A`. -/
theorem norm_compL_apply_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : F →L[ℝ] G) :
    ‖ContinuousLinearMap.compL ℝ E F G A‖ ≤ ‖A‖ :=
  (ContinuousLinearMap.le_opNorm _ A).trans
    (mul_le_of_le_one_left (norm_nonneg A) (ContinuousLinearMap.norm_compL_le ℝ E F G))

/-- The field `v` has a spatial derivative `Dv` that is jointly continuous and bounded by `K` on
`[a, b] × E`. -/
structure IsC1FieldOn (v : ℝ → E → E) (Dv : ℝ → E → E →L[ℝ] E) (a b : ℝ) (K : ℝ≥0) : Prop where
  /-- Joint continuity of the field. -/
  continuousOn : ContinuousOn (Function.uncurry v) (Icc a b ×ˢ univ)
  /-- Joint continuity of the spatial derivative. -/
  continuousOn_deriv : ContinuousOn (Function.uncurry Dv) (Icc a b ×ˢ univ)
  /-- `Dv t x` is the spatial derivative of `v t` at `x`. -/
  hasFDerivAt : ∀ t ∈ Icc a b, ∀ x, HasFDerivAt (v t) (Dv t x) x
  /-- The bound `‖Dv‖ ≤ K`. -/
  norm_le : ∀ t ∈ Icc a b, ∀ x, ‖Dv t x‖ ≤ K

/-- The first variation of the flow of `v` along the flow line through `x` at time `t`: the
solution of `∂ₛ J = Dv(s, flowOn v a b s t x) ∘ J` with `J = id` at `s = t`. -/
def variationOn (v : ℝ → E → E) (Dv : ℝ → E → E →L[ℝ] E) (a b s t : ℝ) (x : E) : E →L[ℝ] E :=
  flowOn (fun r M ↦ (Dv r (flowOn v a b r t x)).comp M) a b s t (ContinuousLinearMap.id ℝ E)

variable {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b : ℝ} {K : ℝ≥0}

namespace IsC1FieldOn

/-- A field with spatial derivative bounded by `K` is `K`-Lipschitz in space. -/
theorem lipschitzWith (hv : IsC1FieldOn v Dv a b K) {t : ℝ} (ht : t ∈ Icc a b) :
    LipschitzWith K (v t) :=
  lipschitzWith_of_nnnorm_fderiv_le (fun x ↦ (hv.hasFDerivAt t ht x).differentiableAt)
    fun x ↦ by
      rw [(hv.hasFDerivAt t ht x).fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hv.norm_le t ht x

/-- A `C¹` field is a Lipschitz field. -/
theorem isLipschitzFieldOn (hv : IsC1FieldOn v Dv a b K) : IsLipschitzFieldOn v a b K :=
  ⟨hv.continuousOn, fun _ ht ↦ hv.lipschitzWith ht⟩

variable [FiniteDimensional ℝ E]

/-- The coefficient `Dv(r, flowOn v a b r t x)` is continuous on `[a, b]`. -/
theorem continuousOn_deriv_flowOn (hv : IsC1FieldOn v Dv a b K) {t : ℝ} (ht : t ∈ Icc a b)
    (x : E) : ContinuousOn (fun r ↦ Dv r (flowOn v a b r t x)) (Icc a b) :=
  hv.continuousOn_deriv.comp (continuousOn_id.prodMk
    (hv.isLipschitzFieldOn.continuousOn_flowOn_time ht x)) fun _ hr ↦ ⟨hr, mem_univ _⟩

/-- The variational field `M ↦ Dv(r, flowOn v a b r t x) ∘ M` is a Lipschitz field. -/
theorem isLipschitzFieldOn_variation (hv : IsC1FieldOn v Dv a b K) {t : ℝ} (ht : t ∈ Icc a b)
    (x : E) :
    IsLipschitzFieldOn (fun r (M : E →L[ℝ] E) ↦ (Dv r (flowOn v a b r t x)).comp M) a b K := by
  refine ⟨?_, fun r hr ↦ LipschitzWith.of_dist_le_mul fun M N ↦ ?_⟩
  · exact ((hv.continuousOn_deriv_flowOn ht x).comp continuousOn_fst fun _ hp ↦ hp.1).clm_comp
      continuousOn_snd
  · rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
    exact ((Dv r _).opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_right (hv.norm_le r hr _) (norm_nonneg _))

/-- The first variation is the identity at the initial time. -/
theorem variationOn_self (hv : IsC1FieldOn v Dv a b K) {t : ℝ} (ht : t ∈ Icc a b) (x : E) :
    variationOn v Dv a b t t x = ContinuousLinearMap.id ℝ E :=
  (hv.isLipschitzFieldOn_variation ht x).flowOn_self ht _

/-- The first variation solves the variational equation. -/
theorem hasDerivAt_variationOn (hv : IsC1FieldOn v Dv a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x : E) :
    HasDerivAt (fun r ↦ variationOn v Dv a b r t x)
      ((Dv s (flowOn v a b s t x)).comp (variationOn v Dv a b s t x)) s :=
  (hv.isLipschitzFieldOn_variation ht x).hasDerivAt_flowOn hs ht _

/-- The first variation solves the variational equation within `[a, b]`. -/
theorem hasDerivWithinAt_variationOn (hv : IsC1FieldOn v Dv a b K) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    HasDerivWithinAt (fun r ↦ variationOn v Dv a b r t x)
      ((Dv s (flowOn v a b s t x)).comp (variationOn v Dv a b s t x)) (Icc a b) s :=
  (hv.hasDerivAt_variationOn hs ht x).hasDerivWithinAt

/-- The first variation is continuous in its final time. -/
theorem continuousOn_variationOn_time (hv : IsC1FieldOn v Dv a b K) {t : ℝ} (ht : t ∈ Icc a b)
    (x : E) : ContinuousOn (fun r ↦ variationOn v Dv a b r t x) (Icc a b) :=
  (hv.isLipschitzFieldOn_variation ht x).continuousOn_flowOn_time ht _

omit [FiniteDimensional ℝ E] in
/-- `‖variationOn v Dv a b s t x‖ ≤ exp (K |s - t|)`. If the variational equation has no
solution, `variationOn` is the identity and the bound is trivial. -/
theorem norm_variationOn_le (hv : IsC1FieldOn v Dv a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x : E) :
    ‖variationOn v Dv a b s t x‖ ≤ Real.exp (K * |s - t|) := by
  rw [variationOn, flowOn]
  split_ifs with h
  · obtain ⟨hγt, hγ⟩ := h.choose_spec
    have hb := norm_le_gronwallBound_of_hasDerivWithinAt (e := h.choose) (δ := 1) (K := K)
      (A := 0) ht (fun r hr ↦ (hγ r hr).hasDerivWithinAt)
      (by rw [hγt]; exact ContinuousLinearMap.norm_id_le)
      (fun r hr ↦ by
        rw [add_zero]
        exact ((Dv r _).opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_right (hv.norm_le r hr _) (norm_nonneg _))) hs
    rwa [gronwallBound_ε0, one_mul] at hb
  · exact ContinuousLinearMap.norm_id_le.trans
      (Real.one_le_exp (mul_nonneg K.coe_nonneg (abs_nonneg _)))

omit [FiniteDimensional ℝ E] in
/-- `‖variationOn v Dv a b s t x‖ ≤ exp (K (b - a))`. -/
theorem norm_variationOn_le_of_mem (hv : IsC1FieldOn v Dv a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x : E) :
    ‖variationOn v Dv a b s t x‖ ≤ Real.exp (K * (b - a)) := by
  refine (hv.norm_variationOn_le hs ht x).trans (Real.exp_le_exp.mpr ?_)
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  rw [abs_le]
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- **The first variation is the derivative of the flow.** -/
theorem hasFDerivAt_flowOn (hv : IsC1FieldOn v Dv a b K) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x : E) :
    HasFDerivAt (flowOn v a b s t) (variationOn v Dv a b s t x) x := by
  have hL := hv.isLipschitzFieldOn
  refine hasFDerivAt_of_parametric (f := fun r z (_ : E) ↦ v r z)
    (Df := fun r z _ ↦ (Dv r z).comp (ContinuousLinearMap.fst ℝ E E))
    (y := fun p r ↦ flowOn v a b r t p) (Z := fun r ↦ variationOn v Dv a b r t x)
    (Dy₀ := ContinuousLinearMap.id ℝ E) (ρ := 1) (C := Real.exp (K * (b - a))) (K := K)
    ht one_pos ?_ ?_ ?_ ?_ ?_ ?_ ?_ (hv.variationOn_self ht x) hs
  · exact (hv.continuousOn_deriv.comp (continuous_fst.prodMk continuous_snd.fst).continuousOn
      fun q hq ↦ ⟨hq.1, mem_univ _⟩).clm_comp continuousOn_const
  · exact fun r hr z p ↦ (hv.hasFDerivAt r hr z).comp (z, p) hasFDerivAt_fst
  · intro r hr
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.fst_comp_inl,
      ContinuousLinearMap.comp_id]
    exact hv.norm_le r hr _
  · exact fun p _ r hr ↦ hL.hasDerivWithinAt_flowOn hr ht p
  · have hid : (fun p ↦ flowOn v a b t t p) = id := funext fun p ↦ hL.flowOn_self ht p
    rw [hid]
    exact hasFDerivAt_id x
  · intro p _ r hr
    simpa only [dist_eq_norm] using hL.dist_flowOn_le_of_mem hr ht p x
  · intro r hr
    have h := hv.hasDerivWithinAt_variationOn hr ht x
    convert h using 1
    ext y : 1
    simp

/-- **The chain rule of the cocycle law.** -/
theorem variationOn_eq_comp (hv : IsC1FieldOn v Dv a b K) {s r t : ℝ} (hs : s ∈ Icc a b)
    (hr : r ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    variationOn v Dv a b s t x =
      (variationOn v Dv a b s r (flowOn v a b r t x)).comp (variationOn v Dv a b r t x) := by
  have hcomp := (hv.hasFDerivAt_flowOn hs hr (flowOn v a b r t x)).comp x
    (hv.hasFDerivAt_flowOn hr ht x)
  have hfun : flowOn v a b s r ∘ flowOn v a b r t = flowOn v a b s t :=
    funext fun y ↦ hv.isLipschitzFieldOn.flowOn_flowOn hs hr ht y
  rw [hfun] at hcomp
  exact (hv.hasFDerivAt_flowOn hs ht x).unique hcomp

/-- The first variation along the inverse flow inverts the first variation. -/
theorem variationOn_flowOn_comp_variationOn (hv : IsC1FieldOn v Dv a b K) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    (variationOn v Dv a b t s (flowOn v a b s t x)).comp (variationOn v Dv a b s t x) =
      ContinuousLinearMap.id ℝ E := by
  rw [← hv.variationOn_eq_comp ht hs ht, hv.variationOn_self ht]

/-- The first variation depends continuously on the initial point, uniformly in the final
time. -/
theorem exists_forall_norm_variationOn_sub_le (hv : IsC1FieldOn v Dv a b K) {t : ℝ}
    (ht : t ∈ Icc a b) (x₀ : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ s ∈ Icc a b,
      ‖variationOn v Dv a b s t x - variationOn v Dv a b s t x₀‖ ≤ ε := by
  have hL := hv.isLipschitzFieldOn
  set L : ℝ := Real.exp (K * (b - a))
  have hL0 : 0 < L := Real.exp_pos _
  set G : ℝ := gronwallBound 0 K L (b - a)
  have hab : a ≤ b := ht.1.trans ht.2
  have hG : 0 ≤ G := by
    have := gronwallBound_mono (δ := 0) (K := K) (ε := L) le_rfl hL0.le K.coe_nonneg
      (sub_nonneg.mpr hab)
    simpa [G, gronwallBound_x0] using this
  set ε' : ℝ := ε / (G + 1)
  have hε' : 0 < ε' := div_pos hε (by linarith)
  obtain ⟨δ₁, hδ₁, hclose⟩ := exists_forall_dist_lt_of_continuousOn (G := Dv)
    hv.continuousOn_deriv (c := fun r ↦ flowOn v a b r t x₀)
    (hL.continuousOn_flowOn_time ht x₀) hε'
  refine ⟨δ₁ / L, div_pos hδ₁ hL0, fun x hx s hs ↦ ?_⟩
  have hdist (r : ℝ) (hr : r ∈ Icc a b) :
      dist (flowOn v a b r t x) (flowOn v a b r t x₀) < δ₁ := by
    calc dist (flowOn v a b r t x) (flowOn v a b r t x₀) ≤ L * dist x x₀ :=
          hL.dist_flowOn_le_of_mem hr ht x x₀
      _ < L * (δ₁ / L) := by gcongr
      _ = δ₁ := mul_div_cancel₀ δ₁ hL0.ne'
  have h := norm_sub_le_of_hasDerivWithinAt_affine (G := E →L[ℝ] E)
    (M₁ := fun r ↦ variationOn v Dv a b r t x) (M₂ := fun r ↦ variationOn v Dv a b r t x₀)
    (A₁ := fun r ↦ ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x)))
    (A₂ := fun r ↦ ContinuousLinearMap.compL ℝ E E E (Dv r (flowOn v a b r t x₀)))
    (B₁ := fun _ ↦ 0) (B₂ := fun _ ↦ 0) (K := K) (ε₁ := ε') (ε₂ := 0) (m := L) ht
    (fun r hr ↦ by simpa using hv.hasDerivWithinAt_variationOn hr ht x)
    (fun r hr ↦ by simpa using hv.hasDerivWithinAt_variationOn hr ht x₀)
    (fun r hr ↦ (norm_compL_apply_le _).trans (hv.norm_le r hr _))
    (fun r hr ↦ by
      rw [← map_sub]
      refine (norm_compL_apply_le _).trans ?_
      rw [← dist_eq_norm]
      exact (hclose r hr _ (hdist r hr)).le)
    (fun r hr ↦ hv.norm_variationOn_le_of_mem hr ht x) (fun _ _ ↦ by simp) hs
  rw [hv.variationOn_self ht, hv.variationOn_self ht, sub_self, norm_zero, add_zero,
    show (0 : ℝ) = ε' * 0 by ring, gronwallBound_mul] at h
  have hmono : gronwallBound 0 K L |s - t| ≤ G := by
    apply gronwallBound_mono le_rfl hL0.le K.coe_nonneg
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  calc ‖variationOn v Dv a b s t x - variationOn v Dv a b s t x₀‖
      ≤ ε' * gronwallBound 0 K L |s - t| := h
    _ ≤ ε' * G := by gcongr
    _ ≤ ε := by
        have : ε' * (G + 1) = ε := div_mul_cancel₀ ε (by linarith)
        nlinarith

/-- The first variation from a fixed initial time is jointly continuous in the final time and
the initial point. -/
theorem continuousOn_variationOn_final (hv : IsC1FieldOn v Dv a b K) {t : ℝ}
    (ht : t ∈ Icc a b) :
    ContinuousOn (fun q : ℝ × E ↦ variationOn v Dv a b q.1 t q.2) (Icc a b ×ˢ univ) :=
  continuousOn_uncurry_of_uniform (g := fun s x ↦ variationOn v Dv a b s t x)
    (fun x ↦ hv.continuousOn_variationOn_time ht x) fun x₀ ε hε ↦ by
      obtain ⟨δ, hδ, h⟩ := hv.exists_forall_norm_variationOn_sub_le ht x₀ (half_pos hε)
      refine ⟨δ, hδ, fun x hx r hr ↦ ?_⟩
      rw [dist_eq_norm]
      exact (h x hx r hr).trans_lt (half_lt_self hε)

/-- The first variation in terms of the first variation from the left endpoint and its
inverse. -/
private theorem variationOn_eq_mul_inverse (hv : IsC1FieldOn v Dv a b K) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    ∃ u : (E →L[ℝ] E)ˣ, (u : E →L[ℝ] E) = variationOn v Dv a b t a (flowOn v a b a t x) ∧
      variationOn v Dv a b s t x =
        variationOn v Dv a b s a (flowOn v a b a t x) *
          Ring.inverse (variationOn v Dv a b t a (flowOn v a b a t x)) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  set ξ := flowOn v a b a t x
  have h₁ : variationOn v Dv a b t a ξ * variationOn v Dv a b a t x = 1 := by
    rw [ContinuousLinearMap.mul_def, ← hv.variationOn_eq_comp ht ha ht, hv.variationOn_self ht,
      ContinuousLinearMap.one_def]
  have h₂ : variationOn v Dv a b a t x * variationOn v Dv a b t a ξ = 1 := by
    have hx : flowOn v a b t a ξ = x := hv.isLipschitzFieldOn.flowOn_flowOn_self ha ht x
    rw [ContinuousLinearMap.mul_def]
    nth_rw 1 [← hx]
    rw [← hv.variationOn_eq_comp ha ht ha, hv.variationOn_self ha, ContinuousLinearMap.one_def]
  refine ⟨⟨_, _, h₁, h₂⟩, rfl, ?_⟩
  have hinv : Ring.inverse (variationOn v Dv a b t a ξ) = variationOn v Dv a b a t x := by
    have h := Ring.inverse_unit (⟨_, _, h₁, h₂⟩ : (E →L[ℝ] E)ˣ)
    rw [Units.inv_mk] at h
    exact h
  rw [hinv, ContinuousLinearMap.mul_def, ← hv.variationOn_eq_comp hs ha ht]

/-- **Joint continuity** of the first variation in the final time, the initial time and the
initial point. -/
theorem continuousOn_variationOn (hv : IsC1FieldOn v Dv a b K) :
    ContinuousOn (fun p : ℝ × ℝ × E ↦ variationOn v Dv a b p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ Icc a b ×ˢ univ) := by
  rcases (Icc a b).eq_empty_or_nonempty with he | ⟨c, hc⟩
  · simp [he]
  have ha : a ∈ Icc a b := ⟨le_rfl, hc.1.trans hc.2⟩
  have hL := hv.isLipschitzFieldOn
  have hξ : ContinuousOn (fun p : ℝ × ℝ × E ↦ flowOn v a b a p.2.1 p.2.2)
      (Icc a b ×ˢ Icc a b ×ˢ univ) :=
    hL.continuousOn_flowOn.comp (f := fun p : ℝ × ℝ × E ↦ (a, p.2))
      (continuous_const.prodMk continuous_snd).continuousOn fun p hp ↦ ⟨ha, hp.2⟩
  have hG := hv.continuousOn_variationOn_final ha
  have hg₁ : ContinuousOn (fun p : ℝ × ℝ × E ↦
      variationOn v Dv a b p.1 a (flowOn v a b a p.2.1 p.2.2)) (Icc a b ×ˢ Icc a b ×ˢ univ) :=
    hG.comp (f := fun p : ℝ × ℝ × E ↦ (p.1, flowOn v a b a p.2.1 p.2.2))
      (continuousOn_fst.prodMk hξ) fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have hg₂ : ContinuousOn (fun p : ℝ × ℝ × E ↦
      variationOn v Dv a b p.2.1 a (flowOn v a b a p.2.1 p.2.2)) (Icc a b ×ˢ Icc a b ×ˢ univ) :=
    hG.comp (f := fun p : ℝ × ℝ × E ↦ (p.2.1, flowOn v a b a p.2.1 p.2.2))
      (continuousOn_snd.fst.prodMk hξ) fun p hp ↦ ⟨hp.2.1, mem_univ _⟩
  have hinv : ContinuousOn (fun q : ℝ × ℝ × E ↦
      Ring.inverse (variationOn v Dv a b q.2.1 a (flowOn v a b a q.2.1 q.2.2)))
      (Icc a b ×ˢ Icc a b ×ˢ univ) := by
    intro p hp
    obtain ⟨u, hu, -⟩ := variationOn_eq_mul_inverse hv hp.1 hp.2.1 p.2.2
    have h := NormedRing.inverse_continuousAt u
    rw [hu] at h
    exact h.comp_continuousWithinAt
      (f := fun q : ℝ × ℝ × E ↦ variationOn v Dv a b q.2.1 a (flowOn v a b a q.2.1 q.2.2))
      (hg₂ p hp)
  have hprod : ContinuousOn (fun q : ℝ × ℝ × E ↦
      variationOn v Dv a b q.1 a (flowOn v a b a q.2.1 q.2.2) *
        Ring.inverse (variationOn v Dv a b q.2.1 a (flowOn v a b a q.2.1 q.2.2)))
      (Icc a b ×ˢ Icc a b ×ˢ univ) := hg₁.mul hinv
  exact hprod.congr fun q hq ↦ (variationOn_eq_mul_inverse hv hq.1 hq.2.1 q.2.2).choose_spec.2

end IsC1FieldOn

namespace IsLipschitzFieldOn

variable [FiniteDimensional ℝ E]

/-- The flow line ending at time `t` at `x`, as a function of its initial time `r`, has
derivative `-v t x` at `r = t`. -/
theorem hasDerivWithinAt_flowOn_initial_self (hv : IsLipschitzFieldOn v a b K) {t : ℝ}
    (ht : t ∈ Icc a b) (x : E) :
    HasDerivWithinAt (fun r ↦ flowOn v a b t r x) (-v t x) (Icc a b) t := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hF : ContinuousOn (fun p : ℝ × ℝ ↦ v p.1 (flowOn v a b p.1 p.2 x)) (Icc a b ×ˢ Icc a b) :=
    hv.continuousOn.comp (f := fun p : ℝ × ℝ ↦ (p.1, flowOn v a b p.1 p.2 x))
      (continuousOn_fst.prodMk (hv.continuousOn_flowOn.comp (f := fun p : ℝ × ℝ ↦ (p.1, p.2, x))
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
      fun p hp ↦ ⟨hp.1, hp.2, mem_univ _⟩)) fun p hp ↦ ⟨hp.1, mem_univ _⟩
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousOn_iff.mp hF (t, t) ⟨ht, ht⟩ c hc
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds t hδ)] with
    r hr hrt
  have hsub : uIcc r t ⊆ Icc a b := uIcc_subset_Icc hr ht
  have hderiv (q : ℝ) (hq : q ∈ uIcc r t) : HasDerivWithinAt
      (fun q ↦ flowOn v a b q r x - (q - r) • v t x)
      (v q (flowOn v a b q r x) - v t x) (uIcc r t) q := by
    have h₁ := hv.hasDerivAt_flowOn (hsub hq) hr x
    have h₂ : HasDerivAt (fun q ↦ (q - r) • v t x) (v t x) q := by
      simpa using ((hasDerivAt_id q).sub_const r).smul_const (v t x)
    exact (h₁.sub h₂).hasDerivWithinAt
  have hbound (q : ℝ) (hq : q ∈ uIcc r t) : ‖v q (flowOn v a b q r x) - v t x‖ ≤ c := by
    have hqt : dist (q, r) (t, t) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      change dist q t < δ ∧ dist r t < δ
      have hrt' : dist r t < δ := hrt
      have hq' := abs_sub_le_of_uIcc_subset_uIcc (uIcc_subset_uIcc_right hq)
      refine ⟨?_, hrt'⟩
      rw [Real.dist_eq] at hrt' ⊢
      rw [abs_sub_comm] at hq'
      rw [abs_sub_comm r t] at hrt'
      linarith
    have := hclose (q, r) ⟨hsub hq, hr⟩ hqt
    rw [dist_eq_norm] at this
    simpa [hv.flowOn_self ht] using this.le
  have hmv := (convex_uIcc r t).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    left_mem_uIcc right_mem_uIcc
  rw [hv.flowOn_self hr, sub_self, zero_smul, sub_zero, show t - r = -(r - t) by ring,
    neg_smul, sub_neg_eq_add, norm_neg] at hmv
  rw [hv.flowOn_self ht, smul_neg, sub_neg_eq_add]
  convert hmv using 2
  abel

end IsLipschitzFieldOn

namespace IsC1FieldOn

variable [FiniteDimensional ℝ E]

/-- **The derivative of the flow in its initial time** is `-(J (v t x))`, where `J` is the first
variation. -/
theorem hasDerivWithinAt_flowOn_initial (hv : IsC1FieldOn v Dv a b K) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    HasDerivWithinAt (fun r ↦ flowOn v a b s r x) (-(variationOn v Dv a b s t x (v t x)))
      (Icc a b) t := by
  have hL := hv.isLipschitzFieldOn
  have hJ : HasFDerivAt (flowOn v a b s t) (variationOn v Dv a b s t x)
      (flowOn v a b t t x) := by
    rw [hL.flowOn_self ht]; exact hv.hasFDerivAt_flowOn hs ht x
  have h := hJ.comp_hasDerivWithinAt t (hL.hasDerivWithinAt_flowOn_initial_self ht x)
  rw [map_neg] at h
  refine h.congr (fun r hr ↦ ?_) ?_
  · exact (hL.flowOn_flowOn hs ht hr x).symm
  · exact (hL.flowOn_flowOn hs ht ht x).symm

/-- **Joint `C¹` regularity in the initial point and the initial time.** -/
theorem contDiffOn_flowOn_initial (hv : IsC1FieldOn v Dv a b K) {s : ℝ} (hs : s ∈ Icc a b) :
    ContDiffOn ℝ 1 (fun p : E × ℝ ↦ flowOn v a b s p.2 p.1) (univ ×ˢ Ioo a b) := by
  have hmaps : MapsTo (fun p : E × ℝ ↦ (s, p.2, p.1)) (univ ×ˢ Ioo a b)
      (Icc a b ×ˢ Icc a b ×ˢ univ) := fun p hp ↦ ⟨hs, Ioo_subset_Icc_self hp.2, mem_univ _⟩
  have hJ : ContinuousOn (fun p : E × ℝ ↦ variationOn v Dv a b s p.2 p.1) (univ ×ˢ Ioo a b) :=
    hv.continuousOn_variationOn.comp (f := fun p : E × ℝ ↦ (s, p.2, p.1))
      (continuous_const.prodMk (continuous_snd.prodMk continuous_fst)).continuousOn hmaps
  have hvc : ContinuousOn (fun p : E × ℝ ↦ v p.2 p.1) (univ ×ˢ Ioo a b) :=
    hv.continuousOn.comp (f := fun p : E × ℝ ↦ (p.2, p.1))
      (continuous_snd.prodMk continuous_fst).continuousOn
      fun p hp ↦ ⟨Ioo_subset_Icc_self hp.2, mem_univ _⟩
  refine PDE.Analysis.contDiffOn_one_of_partial_derivatives (isOpen_univ.prod isOpen_Ioo)
    (D₁ := fun p ↦ variationOn v Dv a b s p.2 p.1)
    (D₂ := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ
      (-(variationOn v Dv a b s p.2 p.1 (v p.2 p.1)))) hJ ?_ ?_ ?_
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn
      (hJ.clm_apply hvc).neg
  · exact fun p hp ↦ hv.hasFDerivAt_flowOn hs (Ioo_subset_Icc_self hp.2) p.1
  · intro p hp
    exact ((hv.hasDerivWithinAt_flowOn_initial hs (Ioo_subset_Icc_self hp.2) p.1).hasDerivAt
      (Icc_mem_nhds hp.2.1 hp.2.2)).hasFDerivAt

/-- **Joint `C¹` regularity in the initial point and the final time.** -/
theorem contDiffOn_flowOn_final (hv : IsC1FieldOn v Dv a b K) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffOn ℝ 1 (fun p : E × ℝ ↦ flowOn v a b p.2 t p.1) (univ ×ˢ Ioo a b) := by
  have hL := hv.isLipschitzFieldOn
  have hJ : ContinuousOn (fun p : E × ℝ ↦ variationOn v Dv a b p.2 t p.1) (univ ×ˢ Ioo a b) :=
    (hv.continuousOn_variationOn_final ht).comp (f := fun p : E × ℝ ↦ (p.2, p.1))
      (continuous_snd.prodMk continuous_fst).continuousOn
      fun p hp ↦ ⟨Ioo_subset_Icc_self hp.2, mem_univ _⟩
  have hΦ : ContinuousOn (fun p : E × ℝ ↦ flowOn v a b p.2 t p.1) (univ ×ˢ Ioo a b) :=
    hL.continuousOn_flowOn.comp (f := fun p : E × ℝ ↦ (p.2, t, p.1))
      (continuous_snd.prodMk (continuous_const.prodMk continuous_fst)).continuousOn
      fun p hp ↦ ⟨Ioo_subset_Icc_self hp.2, ht, mem_univ _⟩
  have hvc : ContinuousOn (fun p : E × ℝ ↦ v p.2 (flowOn v a b p.2 t p.1)) (univ ×ˢ Ioo a b) :=
    hv.continuousOn.comp (f := fun p : E × ℝ ↦ (p.2, flowOn v a b p.2 t p.1))
      (continuousOn_snd.prodMk hΦ) fun p hp ↦ ⟨Ioo_subset_Icc_self hp.2, mem_univ _⟩
  refine PDE.Analysis.contDiffOn_one_of_partial_derivatives (isOpen_univ.prod isOpen_Ioo)
    (D₁ := fun p ↦ variationOn v Dv a b p.2 t p.1)
    (D₂ := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ (v p.2 (flowOn v a b p.2 t p.1)))
    hJ ?_ ?_ ?_
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn hvc
  · exact fun p hp ↦ hv.hasFDerivAt_flowOn (Ioo_subset_Icc_self hp.2) ht p.1
  · exact fun p hp ↦ (hL.hasDerivAt_flowOn (Ioo_subset_Icc_self hp.2) ht p.1).hasFDerivAt

end IsC1FieldOn

end PDE.Analysis.ODE
