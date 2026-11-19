/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.Basic

/-!
# Differentiable dependence of solutions on a parameter

Let `y p` solve `y' = f(r, y, p)` on `[a, b]` for every parameter `p` near `p₀`, where `f(r, ·, ·)`
is differentiable with a derivative `Df` that is jointly continuous in `(r, y, p)`. If the
solutions depend Lipschitz continuously on `p` and their initial values are differentiable at
`p₀`, then `p ↦ y p s` is differentiable at `p₀` for every `s ∈ [a, b]`, uniformly in `s`, and
its derivative `Z s` solves the linearized equation `Z' = D_y f ∘ Z + D_p f` along `y p₀`. The
proof bounds the Taylor remainder of `f` uniformly along the compact trajectory and applies
Grönwall's inequality in both time directions. No second derivative of `f` is used.

## Main results

* `exists_forall_dist_lt_of_continuousOn`: a field continuous on `[a, b] × X` is uniformly
  continuous near a continuous trajectory.
* `norm_sub_le_of_hasDerivWithinAt_affine`: solutions of two affine equations `M₁' = A₁ M₁ + B₁`
  and `M₂' = A₂ M₂ + B₂` differ by at most a Grönwall bound in `‖A₁ - A₂‖` and `‖B₁ - B₂‖`.
* `exists_forall_norm_remainder_le`: the first-order Taylor remainder of a jointly `C¹` field is
  small uniformly along a trajectory.
* `exists_forall_norm_sub_sub_le_of_parametric`: the differentiable dependence on the parameter,
  uniformly in the time.
* `hasFDerivAt_of_parametric`: `p ↦ y p s` has the derivative `Z s` at `p₀` for every `s ∈ [a, b]`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped NNReal Topology

namespace PDE.Analysis.ODE

/-- `gronwallBound` is homogeneous in the initial bound and the forcing jointly. -/
theorem gronwallBound_mul (c δ K ε x : ℝ) :
    gronwallBound (c * δ) K (c * ε) x = c * gronwallBound δ K ε x := by
  by_cases hK : K = 0
  · subst hK
    simp only [gronwallBound_K0]
    ring
  · simp only [gronwallBound_of_K_ne_0 hK]
    field_simp

/-- A field continuous on `[a, b] × X` is uniformly continuous near a continuous trajectory:
for `ε > 0` there is `δ > 0` with `dist (G r z) (G r (c r)) < ε` whenever `r ∈ [a, b]` and
`dist z (c r) < δ`. -/
theorem exists_forall_dist_lt_of_continuousOn {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [PseudoMetricSpace Y] {G : ℝ → X → Y} {a b : ℝ}
    (hG : ContinuousOn (Function.uncurry G) (Icc a b ×ˢ univ)) {c : ℝ → X}
    (hc : ContinuousOn c (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r ∈ Icc a b, ∀ z, dist z (c r) < δ → dist (G r z) (G r (c r)) < ε := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hS : IsCompact (Icc a b ×ˢ closedBall (0 : X) (R + 1)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have huc := hS.uniformContinuousOn_of_continuous
    (hG.mono (prod_mono subset_rfl (subset_univ _)))
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun r hr z hz ↦ ?_⟩
  have hcr : c r ∈ closedBall (0 : X) (R + 1) := by
    rw [mem_closedBall, dist_zero_right]; linarith [hR r hr]
  have hzr : z ∈ closedBall (0 : X) (R + 1) := by
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖z - c r‖ < 1 := by rw [← dist_eq_norm]; exact hz.trans_le (min_le_right _ _)
    have h2 := norm_le_norm_add_norm_sub' z (c r)
    linarith [hR r hr]
  have hd : dist (r, z) (r, c r) < δ₀ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact hz.trans_le (min_le_left _ _)
  exact hδ (r, z) ⟨hr, hzr⟩ (r, c r) ⟨hr, hcr⟩ hd

/-- **Comparison of two affine equations.** If `M₁' = A₁ M₁ + B₁` and `M₂' = A₂ M₂ + B₂` on
`[a, b]`, with `‖A₂‖ ≤ K`, `‖A₁ - A₂‖ ≤ ε₁`, `‖M₁‖ ≤ m` and `‖B₁ - B₂‖ ≤ ε₂`, then
`‖M₁ s - M₂ s‖ ≤ gronwallBound ‖M₁ t - M₂ t‖ K (ε₁ m + ε₂) |s - t|`. -/
theorem norm_sub_le_of_hasDerivWithinAt_affine {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {M₁ M₂ B₁ B₂ : ℝ → G} {A₁ A₂ : ℝ → G →L[ℝ] G} {a b t K ε₁ ε₂ m : ℝ}
    (ht : t ∈ Icc a b)
    (h₁ : ∀ r ∈ Icc a b, HasDerivWithinAt M₁ (A₁ r (M₁ r) + B₁ r) (Icc a b) r)
    (h₂ : ∀ r ∈ Icc a b, HasDerivWithinAt M₂ (A₂ r (M₂ r) + B₂ r) (Icc a b) r)
    (hK : ∀ r ∈ Icc a b, ‖A₂ r‖ ≤ K) (hA : ∀ r ∈ Icc a b, ‖A₁ r - A₂ r‖ ≤ ε₁)
    (hm : ∀ r ∈ Icc a b, ‖M₁ r‖ ≤ m) (hB : ∀ r ∈ Icc a b, ‖B₁ r - B₂ r‖ ≤ ε₂)
    {s : ℝ} (hs : s ∈ Icc a b) :
    ‖M₁ s - M₂ s‖ ≤ gronwallBound ‖M₁ t - M₂ t‖ K (ε₁ * m + ε₂) |s - t| := by
  refine norm_le_gronwallBound_of_hasDerivWithinAt (e := fun r ↦ M₁ r - M₂ r) ht
    (fun r hr ↦ (h₁ r hr).sub (h₂ r hr)) le_rfl (fun r hr ↦ ?_) hs
  have hsplit : A₁ r (M₁ r) + B₁ r - (A₂ r (M₂ r) + B₂ r) =
      A₂ r (M₁ r - M₂ r) + ((A₁ r - A₂ r) (M₁ r) + (B₁ r - B₂ r)) := by
    rw [map_sub, sub_apply]
    abel
  rw [hsplit]
  have hε₁ : 0 ≤ ε₁ := (norm_nonneg _).trans (hA r hr)
  calc ‖A₂ r (M₁ r - M₂ r) + ((A₁ r - A₂ r) (M₁ r) + (B₁ r - B₂ r))‖
      ≤ ‖A₂ r (M₁ r - M₂ r)‖ + (‖(A₁ r - A₂ r) (M₁ r)‖ + ‖B₁ r - B₂ r‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ‖A₂ r‖ * ‖M₁ r - M₂ r‖ + (‖A₁ r - A₂ r‖ * ‖M₁ r‖ + ‖B₁ r - B₂ r‖) := by
        gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * ‖M₁ r - M₂ r‖ + (ε₁ * m + ε₂) := by
        gcongr; exacts [hK r hr, hA r hr, hm r hr, hB r hr]

section Parametric

variable {F P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The uniform Taylor remainder of a jointly `C¹` field along a trajectory: for `θ > 0` there is
`δ > 0` such that the first-order remainder of `f(r, ·, ·)` at `(c r, p₀)` is at most `θ` times
the displacement whenever the displacement is smaller than `δ`. -/
theorem exists_forall_norm_remainder_le {f : ℝ → F → P → F} {Df : ℝ → F → P → (F × P) →L[ℝ] F}
    {a b : ℝ} {c : ℝ → F} {p₀ : P}
    (hDf : ContinuousOn (fun q : ℝ × F × P ↦ Df q.1 q.2.1 q.2.2) (Icc a b ×ˢ univ))
    (hf : ∀ r ∈ Icc a b, ∀ z p, HasFDerivAt (fun q : F × P ↦ f r q.1 q.2) (Df r z p) (z, p))
    (hc : ContinuousOn c (Icc a b)) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ > 0, ∀ r ∈ Icc a b, ∀ z p, ‖(z, p) - (c r, p₀)‖ < δ →
      ‖f r z p - f r (c r) p₀ - Df r (c r) p₀ (z - c r, p - p₀)‖ ≤
        θ * ‖(z, p) - (c r, p₀)‖ := by
  obtain ⟨δ, hδ, hclose⟩ := exists_forall_dist_lt_of_continuousOn
    (G := fun r (q : F × P) ↦ Df r q.1 q.2) hDf
    (c := fun r ↦ (c r, p₀)) (hc.prodMk continuousOn_const) hθ
  refine ⟨δ, hδ, fun r hr z p hzp ↦ ?_⟩
  let g : F × P → F := fun q ↦ f r q.1 q.2 - Df r (c r) p₀ q
  have hg : ∀ q ∈ segment ℝ (c r, p₀) (z, p),
      HasFDerivWithinAt g (Df r q.1 q.2 - Df r (c r) p₀) (segment ℝ (c r, p₀) (z, p)) q :=
    fun q _ ↦ ((hf r hr q.1 q.2).sub (Df r (c r) p₀).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ q ∈ segment ℝ (c r, p₀) (z, p), ‖Df r q.1 q.2 - Df r (c r) p₀‖ ≤ θ := by
    intro q hq
    have hq' : dist q (c r, p₀) < δ := (mem_closedBall.1
      (segment_subset_closedBall_left _ _ hq)).trans_lt (by rwa [dist_comm, dist_eq_norm])
    simpa only [dist_eq_norm] using (hclose r hr q hq').le
  have hmv := (convex_segment _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbound
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have heq : g (z, p) - g (c r, p₀) = f r z p - f r (c r) p₀ - Df r (c r) p₀ (z - c r, p - p₀) := by
    simp only [g]
    rw [← Prod.mk_sub_mk, map_sub]
    abel
  exact heq ▸ hmv

/-- **Differentiable dependence on a parameter, uniform form.** Let `y p` solve
`y' = f(r, y, p)` on `[a, b]` for `p ∈ ball p₀ ρ`, Lipschitz in `p` with constant `C`, with
initial values `y p t` differentiable at `p₀` with derivative `Dy₀`. Let `Z` solve
`Z' = D_y f ∘ Z + D_p f` along `(y p₀, p₀)` with `Z t = Dy₀`, where `‖D_y f‖ ≤ K` there. Then for
every `η > 0` there is `δ > 0` with `‖y p s - y p₀ s - Z s (p - p₀)‖ ≤ η ‖p - p₀‖` for all
`s ∈ [a, b]` and `‖p - p₀‖ < δ`. -/
theorem exists_forall_norm_sub_sub_le_of_parametric {f : ℝ → F → P → F}
    {Df : ℝ → F → P → (F × P) →L[ℝ] F} {y : P → ℝ → F} {Z : ℝ → P →L[ℝ] F} {Dy₀ : P →L[ℝ] F}
    {a b t ρ C : ℝ} {K : ℝ≥0} {p₀ : P} (ht : t ∈ Icc a b) (hρ : 0 < ρ)
    (hDf : ContinuousOn (fun q : ℝ × F × P ↦ Df q.1 q.2.1 q.2.2) (Icc a b ×ˢ univ))
    (hf : ∀ r ∈ Icc a b, ∀ z p, HasFDerivAt (fun q : F × P ↦ f r q.1 q.2) (Df r z p) (z, p))
    (hK : ∀ r ∈ Icc a b,
      ‖(Df r (y p₀ r) p₀).comp (ContinuousLinearMap.inl ℝ F P)‖ ≤ K)
    (hy : ∀ p ∈ ball p₀ ρ, ∀ r ∈ Icc a b, HasDerivWithinAt (y p) (f r (y p r) p) (Icc a b) r)
    (hy₀ : HasFDerivAt (fun p ↦ y p t) Dy₀ p₀)
    (hLip : ∀ p ∈ ball p₀ ρ, ∀ r ∈ Icc a b, ‖y p r - y p₀ r‖ ≤ C * ‖p - p₀‖)
    (hZ : ∀ r ∈ Icc a b, HasDerivWithinAt Z
      (((Df r (y p₀ r) p₀).comp (ContinuousLinearMap.inl ℝ F P)).comp (Z r) +
        (Df r (y p₀ r) p₀).comp (ContinuousLinearMap.inr ℝ F P)) (Icc a b) r)
    (hZt : Z t = Dy₀) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ p ∈ ball p₀ δ, ∀ s ∈ Icc a b, ‖y p s - y p₀ s - Z s (p - p₀)‖ ≤ η * ‖p - p₀‖ := by
  set c₁ : ℝ := |C| + 1
  have hc₁ : 0 < c₁ := by simp only [c₁]; positivity
  set G : ℝ := gronwallBound 1 K c₁ (b - a)
  have hab : a ≤ b := ht.1.trans ht.2
  have hG : 0 ≤ G := zero_le_one.trans <| by
    simpa [G, gronwallBound_x0] using gronwallBound_mono (δ := 1) (K := K) (ε := c₁)
      zero_le_one hc₁.le K.coe_nonneg (sub_nonneg.mpr hab)
  set θ : ℝ := η / (G + 1)
  have hθ : 0 < θ := div_pos hη (by linarith)
  have hθG : θ * G ≤ η := (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one)
    hθ.le).trans_eq (div_mul_cancel₀ η (by linarith))
  have hc : ContinuousOn (y p₀) (Icc a b) := fun r hr ↦
    (hy p₀ (mem_ball_self hρ) r hr).continuousWithinAt
  obtain ⟨δ₁, hδ₁, hrem⟩ := exists_forall_norm_remainder_le (p₀ := p₀) hDf hf hc hθ
  obtain ⟨δ₂, hδ₂, hinit⟩ := Metric.eventually_nhds_iff_ball.mp (hy₀.isLittleO.bound hθ)
  refine ⟨min ρ (min δ₂ (δ₁ / c₁)), lt_min hρ (lt_min hδ₂ (div_pos hδ₁ hc₁)),
    fun p hp s hs ↦ ?_⟩
  have hpρ : p ∈ ball p₀ ρ := ball_subset_ball (min_le_left _ _) hp
  have hpδ₂ : p ∈ ball p₀ δ₂ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hp
  have hpδ₁ : ‖p - p₀‖ < δ₁ / c₁ :=
    (mem_ball_iff_norm.1 hp).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set w := p - p₀
  have hdisp (r : ℝ) (hr : r ∈ Icc a b) : ‖(y p r, p) - (y p₀ r, p₀)‖ ≤ c₁ * ‖w‖ := by
    rw [Prod.mk_sub_mk, Prod.norm_def, max_le_iff]
    exact ⟨(hLip p hpρ r hr).trans (by gcongr; linarith [le_abs_self C]),
      le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg C])⟩
  set D₁ : ℝ → F →L[ℝ] F := fun r ↦ (Df r (y p₀ r) p₀).comp (ContinuousLinearMap.inl ℝ F P)
  set D₂ : ℝ → P →L[ℝ] F := fun r ↦ (Df r (y p₀ r) p₀).comp (ContinuousLinearMap.inr ℝ F P)
  have hderiv (r : ℝ) (hr : r ∈ Icc a b) : HasDerivWithinAt (fun r ↦ y p r - y p₀ r - Z r w)
      (f r (y p r) p - f r (y p₀ r) p₀ - (D₁ r (Z r w) + D₂ r w)) (Icc a b) r := by
    have hZw := (hZ r hr).clm_apply (hasDerivWithinAt_const r (Icc a b) w)
    simp only [map_zero, add_zero, FunLike.coe_add, Pi.add_apply,
      ContinuousLinearMap.comp_apply] at hZw
    exact ((hy p hpρ r hr).sub (hy p₀ (mem_ball_self hρ) r hr)).sub hZw
  have hbound (r : ℝ) (hr : r ∈ Icc a b) :
      ‖f r (y p r) p - f r (y p₀ r) p₀ - (D₁ r (Z r w) + D₂ r w)‖ ≤
        K * ‖y p r - y p₀ r - Z r w‖ + θ * c₁ * ‖w‖ := by
    have hsplit : f r (y p r) p - f r (y p₀ r) p₀ - (D₁ r (Z r w) + D₂ r w) =
        D₁ r (y p r - y p₀ r - Z r w) +
          (f r (y p r) p - f r (y p₀ r) p₀ - Df r (y p₀ r) p₀ (y p r - y p₀ r, w)) := by
      have hL := ContinuousLinearMap.comp_inl_add_comp_inr (Df r (y p₀ r) p₀) (y p r - y p₀ r, w)
      simp only [D₁, D₂, map_sub] at hL ⊢
      rw [← hL]
      abel
    rw [hsplit]
    have hsmall : ‖(y p r, p) - (y p₀ r, p₀)‖ < δ₁ :=
      (hdisp r hr).trans_lt (by rwa [lt_div_iff₀' hc₁] at hpδ₁)
    calc _ ≤ ‖D₁ r‖ * ‖y p r - y p₀ r - Z r w‖ + θ * ‖(y p r, p) - (y p₀ r, p₀)‖ :=
          (norm_add_le _ _).trans (add_le_add ((D₁ r).le_opNorm _) (hrem r hr (y p r) p hsmall))
      _ ≤ K * ‖y p r - y p₀ r - Z r w‖ + θ * (c₁ * ‖w‖) := by gcongr; exacts [hK r hr, hdisp r hr]
      _ = _ := by ring
  have hstart : ‖y p t - y p₀ t - Z t w‖ ≤ θ * ‖w‖ := by
    rw [hZt]; exact hinit p hpδ₂
  have hgr := norm_le_gronwallBound_of_hasDerivWithinAt (e := fun r ↦ y p r - y p₀ r - Z r w)
    ht hderiv hstart hbound hs
  rw [show θ * c₁ * ‖w‖ = (θ * ‖w‖) * c₁ by ring, ← mul_one (θ * ‖w‖),
    mul_assoc (θ * ‖w‖) 1 c₁, one_mul, gronwallBound_mul] at hgr
  have hmono : gronwallBound 1 K c₁ |s - t| ≤ G := gronwallBound_mono zero_le_one hc₁.le
    K.coe_nonneg (abs_le.2 ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩)
  calc _ ≤ θ * ‖w‖ * G := hgr.trans (by gcongr)
    _ = θ * G * ‖w‖ := by ring
    _ ≤ η * ‖w‖ := by gcongr

/-- **Differentiable dependence on a parameter.** Under the hypotheses of
`exists_forall_norm_sub_sub_le_of_parametric`, `p ↦ y p s` has derivative `Z s` at `p₀` for every
`s ∈ [a, b]`. -/
theorem hasFDerivAt_of_parametric {f : ℝ → F → P → F}
    {Df : ℝ → F → P → (F × P) →L[ℝ] F} {y : P → ℝ → F} {Z : ℝ → P →L[ℝ] F} {Dy₀ : P →L[ℝ] F}
    {a b t ρ C : ℝ} {K : ℝ≥0} {p₀ : P} (ht : t ∈ Icc a b) (hρ : 0 < ρ)
    (hDf : ContinuousOn (fun q : ℝ × F × P ↦ Df q.1 q.2.1 q.2.2) (Icc a b ×ˢ univ))
    (hf : ∀ r ∈ Icc a b, ∀ z p, HasFDerivAt (fun q : F × P ↦ f r q.1 q.2) (Df r z p) (z, p))
    (hK : ∀ r ∈ Icc a b,
      ‖(Df r (y p₀ r) p₀).comp (ContinuousLinearMap.inl ℝ F P)‖ ≤ K)
    (hy : ∀ p ∈ ball p₀ ρ, ∀ r ∈ Icc a b, HasDerivWithinAt (y p) (f r (y p r) p) (Icc a b) r)
    (hy₀ : HasFDerivAt (fun p ↦ y p t) Dy₀ p₀)
    (hLip : ∀ p ∈ ball p₀ ρ, ∀ r ∈ Icc a b, ‖y p r - y p₀ r‖ ≤ C * ‖p - p₀‖)
    (hZ : ∀ r ∈ Icc a b, HasDerivWithinAt Z
      (((Df r (y p₀ r) p₀).comp (ContinuousLinearMap.inl ℝ F P)).comp (Z r) +
        (Df r (y p₀ r) p₀).comp (ContinuousLinearMap.inr ℝ F P)) (Icc a b) r)
    (hZt : Z t = Dy₀) {s : ℝ} (hs : s ∈ Icc a b) :
    HasFDerivAt (fun p ↦ y p s) (Z s) p₀ := by
  refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.mpr fun η hη ↦ ?_)
  obtain ⟨δ, hδ, h⟩ := exists_forall_norm_sub_sub_le_of_parametric ht hρ hDf hf hK hy hy₀ hLip
    hZ hZt hη
  filter_upwards [ball_mem_nhds p₀ hδ] with p hp
  exact h p hp s hs

end Parametric

end PDE.Analysis.ODE
