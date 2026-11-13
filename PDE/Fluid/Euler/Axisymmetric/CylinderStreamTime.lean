/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderStreamSources
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import PDE.Analysis.Calculus.PartialRegularity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smoothness in time of the stream profile

For a vorticity profile `Φ(t, (s, z))` depending smoothly on time and `L`-periodic in `z`, the
stream profiles `Ψ_t = streamProfile L Φ_t` of the slices `Φ_t = Φ(t, ·)` are jointly smooth in
`(t, s, z)` (`contDiff_streamProfile_slices`; on `ℝ³`, `contDiff_streamProfile_param`; for
smoothness on an open set of times, `contDiffOn_streamProfile_slices`).

## Main definitions

* `paramMode`: `H_{Φ,j}(t, s)`, the `j`-th `s`-derivative of the `k`-th cut-off mode `sourceMode` of
  the slice `Φ_t`.
* `paramStreamMode`: the `k`-th stream mode of `Φ_t` as a function of `(t, (s, z))`.

The partial derivatives `tPartial`, `sPartial`, `zPartial`, the conditions `IsZPeriodic` and
`VanishesBeyond`, the cut-off modes `sourceMode`, the constants `modeConst` of the mode bounds and
the common collar `modeCollar` are imported, together with the coefficient decay and the linearity
of the mode operators.

## Main results

* `hasDerivAt_paramMode_space`, `hasDerivAt_paramMode_time`: `∂_s H_{Φ,j} = H_{Φ,j+1}` and
  `∂_t H_{Φ,j} = H_{∂_t Φ,j}` for smooth `Φ`.
* `exists_abs_paramMode_le`, `contDiff_paramMode`, `exists_norm_iteratedFDeriv_paramMode_le`: if `Φ`
  is also periodic in `z` and vanishes for large `|t|`, the parametric modes are smooth, and they
  and all their derivatives decay faster than any power of `k`, uniformly in `(t, s)`.
* `exists_norm_iteratedFDeriv_paramStreamMode_le`, `contDiff_streamProfile_of_vanishesBeyond`: every
  derivative of the `k`-th parametric stream mode is `O((1 + k)⁻²)`, so their series, the stream
  profile, is smooth in `(t, s, z)`.
* `contDiff_streamProfile_slices`, `contDiffOn_streamProfile_slices`,
  `contDiff_streamProfile_param`: smoothness in time of the stream profile.
* `streamProfile_const_mul`: the stream profile is homogeneous in the source.

## How it works

The stream profile is the series of the cut-off mode solutions `η_k(s) Ψ_k(s)` times `sin(μ_k z)`,
and `hasDerivAt_paramMode_space` holds by the definition of `paramMode`. For the time derivative we
write the defect `H_{Φ,j}(t + h, s) - H_{Φ,j}(t, s) - h H_{∂_t Φ,j}(t, s)` as the mode of the source
`Φ_{t+h} - Φ_t - h ∂_t Φ_t` (`iteratedDeriv_sourceMode_linear`). By the mean value theorem in time
and the uniform continuity of `∂_t ∂_s^l Φ` on compact sets, the `s`-derivatives of this source are
`o(h)` on `modeCollar L × [0, L]`, and a cut-off mode is bounded by the `s`-derivatives of its
source there (`abs_iteratedDeriv_sourceMode_le`). Under periodicity and vanishing for large times
the sine coefficients of the slices decay uniformly in time
(`exists_abs_iteratedDeriv_coefficientMode_le`), which gives `exists_abs_paramMode_le` and a
Lipschitz bound in time (`exists_abs_paramMode_sub_le`). Smoothness and the derivative bounds follow
by induction on the order: the two partial derivatives of `H_{Φ,j}` are the parametric modes of
`∂_t Φ` and of order `j + 1`, and `contDiffOn_succ_of_scalar_partial_derivatives` raises the order
by one. In the Leibniz rule each derivative of `sin(μ_k z)` costs a factor `μ_k`, which the decay
absorbs, and `contDiff_tsum` from Mathlib makes the series smooth. Multiplying `Φ` by a bump
function of `t` equal to `1` near a given time gives a source that vanishes for large times and has
the same slices near that time, which removes the vanishing hypothesis.
-/
@[expose] public section

namespace Euler.Cylinder

open Set Filter PDE.Analysis.Fourier.SineSeries
open scoped Topology Real

set_option linter.missingDocs true

noncomputable section

variable {Φ : ℝ × (ℝ × ℝ) → ℝ}

/-! ### The parametric modes -/

/-- The parametric mode `H(t, s)`: the `j`-th `s`-derivative of the `k`-th source mode of the
slice `p ↦ Φ(t, p)`. -/
def paramMode (L : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ) (k j : ℕ) (q : ℝ × ℝ) : ℝ :=
  iteratedDeriv j (sourceMode L (fun p ↦ Φ (q.1, p)) k) q.2

/-- **Decay of the parametric modes.** For a smooth `Φ`, `L`-periodic in `z` and vanishing for
`|t| > R`, the parametric modes decay faster than any power of `k`, uniformly in `(t, s)`. -/
theorem exists_abs_paramMode_le {L R : ℝ} (hL : 0 < L) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ) (j N : ℕ) :
    ∃ E, 0 ≤ E ∧ ∀ (k : ℕ) (q : ℝ × ℝ), |paramMode L Φ k j q| ≤ E / (1 + (k : ℝ)) ^ N := by
  have hcoef : ∀ l : ℕ, ∃ C, 0 ≤ C ∧ ∀ (k : ℕ) (t : ℝ), ∀ s ∈ modeCollar L,
      |iteratedDeriv l (coefficientMode L (fun p ↦ Φ (t, p)) k) s| ≤
        C / (1 + (k : ℝ)) ^ (2 * j + N) := fun l ↦
    exists_abs_iteratedDeriv_coefficientMode_le hL hΦ hper hR l (2 * j + N)
      (isCompact_modeCollar L)
  choose C hC0 hC using hcoef
  set c : ℝ := 2 * π / L
  have hc : 0 < c := by positivity
  set SC : ℝ := ∑ l ∈ Finset.range (j + 1), C l
  have hSC : 0 ≤ SC := Finset.sum_nonneg fun l _ ↦ hC0 l
  refine ⟨3 * modeConst j * (1 + c) ^ (2 * j) * SC / c ^ 2,
    by have := modeConst_nonneg j; positivity, fun k q ↦ ?_⟩
  set μ := modeFrequency L k
  have hμ : μ = c * (1 + k) := modeFrequency_eq L k
  have hμpos : 0 < μ := modeFrequency_pos hL k
  have hk1 : (1 : ℝ) ≤ 1 + k := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hkpos : (0 : ℝ) < 1 + k := by linarith
  have h := abs_iteratedDeriv_modeTerm_le_modeConst hμpos
    (contDiff_coefficientMode (contDiff_slice hΦ q.1) k) j
    (fun l ↦ C l / (1 + (k : ℝ)) ^ (2 * j + N))
    (fun i hi s hs ↦ hC i k q.1 s (collar_subset_modeCollar k hs)) q.2
  change |paramMode L Φ k j q| ≤ _ at h
  refine h.trans ?_
  rw [← Finset.sum_div]
  have hD := modeConst_nonneg j
  have h1μ : 1 + μ ^ 2 ≤ (1 + c) ^ 2 * (1 + k) ^ 2 := by
    rw [hμ]
    have h1 : 1 ≤ (1 + (k : ℝ)) ^ 2 := one_le_pow₀ hk1
    nlinarith
  have hμc : c ^ 2 ≤ μ ^ 2 := by
    rw [hμ, mul_pow]
    exact le_mul_of_one_le_right (sq_nonneg c) (one_le_pow₀ hk1)
  have hpow : (1 + μ ^ 2) ^ j ≤ (1 + c) ^ (2 * j) * (1 + (k : ℝ)) ^ (2 * j) := by
    calc (1 + μ ^ 2) ^ j ≤ ((1 + c) ^ 2 * (1 + k) ^ 2) ^ j :=
          pow_le_pow_left₀ (by positivity) h1μ j
      _ = (1 + c) ^ (2 * j) * (1 + (k : ℝ)) ^ (2 * j) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
  have hsplit : (1 + (k : ℝ)) ^ (2 * j + N) = (1 + k) ^ (2 * j) * (1 + k) ^ N := pow_add _ _ _
  calc 3 * modeConst j * (1 + μ ^ 2) ^ j * (SC / (1 + (k : ℝ)) ^ (2 * j + N)) / μ ^ 2
      ≤ 3 * modeConst j * ((1 + c) ^ (2 * j) * (1 + (k : ℝ)) ^ (2 * j)) *
          (SC / (1 + (k : ℝ)) ^ (2 * j + N)) / c ^ 2 := by
        apply div_le_div₀ (by positivity) _ (by positivity) hμc
        gcongr
    _ = 3 * modeConst j * (1 + c) ^ (2 * j) * SC / c ^ 2 / (1 + (k : ℝ)) ^ N := by
        rw [hsplit]
        field_simp

/-- The `s`-derivative is linear on differentiable functions. -/
theorem sDeriv_linear {a b : ℝ} {G₁ G₂ : ℝ × ℝ → ℝ} (hG₁ : Differentiable ℝ G₁)
    (hG₂ : Differentiable ℝ G₂) (p : ℝ × ℝ) :
    sDeriv (fun p ↦ a * G₁ p + b * G₂ p) p = a * sDeriv G₁ p + b * sDeriv G₂ p := by
  have h := (((hG₁ p).hasFDerivAt.const_mul a).add ((hG₂ p).hasFDerivAt.const_mul b)).fderiv
  simp only [sDeriv]
  change fderiv ℝ ((fun y ↦ a * G₁ y) + fun y ↦ b * G₂ y) p (1, 0) = _
  rw [h]
  simp

/-- Iterated `s`-derivatives are linear on smooth functions. -/
theorem iterate_sDeriv_linear {a b : ℝ} {G₁ G₂ : ℝ × ℝ → ℝ} (hG₁ : ContDiff ℝ (⊤ : ℕ∞) G₁)
    (hG₂ : ContDiff ℝ (⊤ : ℕ∞) G₂) (l : ℕ) :
    sDeriv^[l] (fun p ↦ a * G₁ p + b * G₂ p) =
      fun p ↦ a * (sDeriv^[l] G₁) p + b * (sDeriv^[l] G₂) p := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    funext p
    exact sDeriv_linear ((contDiff_iterate_sDeriv hG₁ l).differentiable (by simp))
      ((contDiff_iterate_sDeriv hG₂ l).differentiable (by simp)) p

/-- **The time derivative of the parametric modes** is the parametric mode of the time
derivative: `∂_t H_Φ = H_{∂_t Φ}`. -/
theorem hasDerivAt_paramMode_time {L : ℝ} (hL : 0 < L) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (k j : ℕ) (t s : ℝ) :
    HasDerivAt (fun t ↦ paramMode L Φ k j (t, s)) (paramMode L (tPartial Φ) k j (t, s)) t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set μ := modeFrequency L k
  set A : ℝ := 3 * modeConst j * (1 + μ ^ 2) ^ j * ((j + 1) * 2) / μ ^ 2
  have hA : 0 ≤ A := by have := modeConst_nonneg j; positivity
  set ε : ℝ := c / (A + 1)
  have hε : 0 < ε := by positivity
  -- uniform continuity of the time derivatives of the `s`-derivatives
  set g : ℝ × (ℝ × ℝ) → (Fin (j + 1) → ℝ) :=
    fun x l ↦ tPartial (sPartial^[(l : ℕ)] Φ) x
  have hg : Continuous g :=
    continuous_pi fun l ↦ (contDiff_tPartial (contDiff_iterate_sPartial hΦ l)).continuous
  set Kc : Set (ℝ × (ℝ × ℝ)) := Icc (t - 1) (t + 1) ×ˢ (modeCollar L ×ˢ Icc 0 L)
  have hKc : IsCompact Kc := isCompact_Icc.prod ((isCompact_modeCollar L).prod isCompact_Icc)
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hg.continuousOn) ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hδ one_pos)] with h hh
  rw [mem_ball_zero_iff, Real.norm_eq_abs, lt_min_iff] at hh
  obtain ⟨hhδ, hh1⟩ := hh
  -- the defect of the difference quotient as a source mode
  set G₁ : ℝ × ℝ → ℝ := fun p ↦ Φ (t + h, p)
  set G₂ : ℝ × ℝ → ℝ := fun p ↦ Φ (t, p)
  set G₃ : ℝ × ℝ → ℝ := fun p ↦ tPartial Φ (t, p)
  have hG₁ : ContDiff ℝ (⊤ : ℕ∞) G₁ := contDiff_slice hΦ (t + h)
  have hG₂ : ContDiff ℝ (⊤ : ℕ∞) G₂ := contDiff_slice hΦ t
  have hG₃ : ContDiff ℝ (⊤ : ℕ∞) G₃ := contDiff_slice (contDiff_tPartial hΦ) t
  set G₂₃ : ℝ × ℝ → ℝ := fun p ↦ 1 * G₂ p + h * G₃ p
  have hG₂₃ : ContDiff ℝ (⊤ : ℕ∞) G₂₃ := (contDiff_const.mul hG₂).add (contDiff_const.mul hG₃)
  set Δ : ℝ × ℝ → ℝ := fun p ↦ 1 * G₁ p + (-1) * G₂₃ p
  have hΔ : ContDiff ℝ (⊤ : ℕ∞) Δ := (contDiff_const.mul hG₁).add (contDiff_const.mul hG₂₃)
  have hlin : paramMode L Φ k j (t + h, s) - paramMode L Φ k j (t, s) -
      h • paramMode L (tPartial Φ) k j (t, s) = iteratedDeriv j (sourceMode L Δ k) s := by
    rw [iteratedDeriv_sourceMode_linear hL hG₁ hG₂₃, iteratedDeriv_sourceMode_linear hL hG₂ hG₃]
    simp only [paramMode, smul_eq_mul, G₁, G₂, G₃]
    ring
  rw [hlin, Real.norm_eq_abs, Real.norm_eq_abs]
  -- the `s`-derivatives of the defect are small
  have hsm : ∀ l ≤ j, ∀ s' ∈ modeCollar L, ∀ z ∈ Icc 0 L,
      |(sDeriv^[l] Δ) (s', z)| ≤ ε * |h| := by
    intro l hl s' hs' z hz
    have hS := contDiff_iterate_sPartial hΦ l
    have e1 : sDeriv^[l] Δ = fun p ↦ 1 * (sDeriv^[l] G₁) p + (-1) *
        (1 * (sDeriv^[l] G₂) p + h * (sDeriv^[l] G₃) p) := by
      rw [iterate_sDeriv_linear hG₁ hG₂₃, iterate_sDeriv_linear hG₂ hG₃]
    have e2 : sDeriv^[l] G₃ = fun p ↦ tPartial (sPartial^[l] Φ) (t, p) := by
      rw [show G₃ = fun p ↦ tPartial Φ (t, p) from rfl,
        iterate_sDeriv_slice (contDiff_tPartial hΦ) t l, iterate_sPartial_tPartial hΦ l]
    rw [e1, e2, iterate_sDeriv_slice hΦ (t + h) l, iterate_sDeriv_slice hΦ t l]
    simp only [one_mul, neg_one_mul]
    -- the mean value theorem in time
    set S := sPartial^[l] Φ
    set p : ℝ × ℝ := (s', z)
    have hderiv : ∀ r ∈ uIcc t (t + h), HasDerivWithinAt
        (fun r ↦ S (r, p) - r * tPartial S (t, p)) (tPartial S (r, p) - tPartial S (t, p))
        (uIcc t (t + h)) r := fun r _ ↦
      ((hasDerivAt_slice_time (hS.differentiable (by simp)) r p).sub
        ((hasDerivAt_id r).mul_const _) |>.congr_deriv (by simp)).hasDerivWithinAt
    have hbound : ∀ r ∈ uIcc t (t + h), ‖tPartial S (r, p) - tPartial S (t, p)‖ ≤ ε := by
      intro r hr
      have hrt : |r - t| ≤ |h| := by
        rcases mem_uIcc.1 hr with h' | h' <;>
          exact abs_le.2 ⟨by linarith [neg_abs_le h, abs_nonneg h],
            by linarith [le_abs_self h, abs_nonneg h]⟩
      have hrK : (r, p) ∈ Kc := ⟨⟨by linarith [(abs_le.1 (hrt.trans hh1.le)).1],
        by linarith [(abs_le.1 (hrt.trans hh1.le)).2]⟩, hs', hz⟩
      have htK : (t, p) ∈ Kc := ⟨⟨by linarith, by linarith⟩, hs', hz⟩
      have hd : dist (r, p) (t, p) < δ := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq]
        simpa using hrt.trans_lt hhδ
      rw [Real.norm_eq_abs, ← Real.dist_eq]
      exact (dist_le_pi_dist (g (r, p)) (g (t, p)) ⟨l, Nat.lt_succ_of_le hl⟩).trans
        (hδg _ hrK _ htK hd).le
    have hmvt := (convex_uIcc t (t + h)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
      hbound left_mem_uIcc right_mem_uIcc
    rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left] at hmvt
    calc |S (t + h, p) + -(S (t, p) + h * tPartial S (t, p))|
        = |S (t + h, p) - (t + h) * tPartial S (t, p) - (S (t, p) - t * tPartial S (t, p))| := by
          ring_nf
      _ ≤ ε * |h| := hmvt
  have hb := abs_iteratedDeriv_sourceMode_le hL hΔ k j hsm s
  calc |iteratedDeriv j (sourceMode L Δ k) s| ≤
        3 * modeConst j * (1 + μ ^ 2) ^ j * ((j + 1) * (2 * (ε * |h|))) / μ ^ 2 := hb
    _ = A * ε * |h| := by simp only [A]; ring
    _ ≤ c * |h| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg h)
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        linarith

/-- The `s`-derivative of the parametric modes raises the order: `∂_s H_{Φ,j} = H_{Φ,j+1}`. -/
theorem hasDerivAt_paramMode_space {L : ℝ} (hL : 0 < L) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (k j : ℕ) (t s : ℝ) :
    HasDerivAt (fun s ↦ paramMode L Φ k j (t, s)) (paramMode L Φ k (j + 1) (t, s)) s := by
  have hf := contDiff_sourceMode hL (contDiff_slice hΦ t) k
  have hd := (hf.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top _)) s
  simp only [paramMode]
  rw [iteratedDeriv_succ]
  exact hd.hasDerivAt

/-- The parametric modes of a smooth `Φ`, periodic in `z` and vanishing for large times, are
Lipschitz in time uniformly in `s`. -/
theorem exists_abs_paramMode_sub_le {L R : ℝ} (hL : 0 < L) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ) (j : ℕ) :
    ∃ E, 0 ≤ E ∧ ∀ (k : ℕ) (t t' s : ℝ),
      |paramMode L Φ k j (t', s) - paramMode L Φ k j (t, s)| ≤ E * |t' - t| := by
  obtain ⟨E, hE0, hE⟩ := exists_abs_paramMode_le hL (contDiff_tPartial hΦ) hper.tPartial
    hR.tPartial j 0
  refine ⟨E, hE0, fun k t t' s ↦ ?_⟩
  have h := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t ↦ paramMode L Φ k j (t, s)) (f' := fun t ↦ paramMode L (tPartial Φ) k j (t, s))
    (C := E) (fun t _ ↦ (hasDerivAt_paramMode_time hL hΦ k j t s).hasDerivWithinAt)
    (fun t _ ↦ by simpa using hE k (t, s)) (mem_univ t) (mem_univ t')
  simpa [Real.norm_eq_abs] using h

/-- The parametric modes of a smooth `Φ`, periodic in `z` and vanishing for large times, are
jointly continuous. -/
theorem continuous_paramMode {L R : ℝ} (hL : 0 < L) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ) (k j : ℕ) :
    Continuous (paramMode L Φ k j) := by
  obtain ⟨E, -, hE⟩ := exists_abs_paramMode_sub_le hL hΦ hper hR j
  rw [continuous_iff_continuousAt]
  intro q₀
  have hs : Continuous fun s ↦ paramMode L Φ k j (q₀.1, s) :=
    continuous_iff_continuousAt.2 fun s ↦
      (hasDerivAt_paramMode_space hL hΦ k j q₀.1 s).continuousAt
  have hlim : Tendsto (fun q : ℝ × ℝ ↦ E * |q.1 - q₀.1| +
      |paramMode L Φ k j (q₀.1, q.2) - paramMode L Φ k j q₀|) (𝓝 q₀) (𝓝 0) := by
    have h1 : Tendsto (fun q : ℝ × ℝ ↦ E * |q.1 - q₀.1|) (𝓝 q₀) (𝓝 (E * |q₀.1 - q₀.1|)) :=
      ((continuous_const.mul ((continuous_fst.sub continuous_const).abs)).tendsto q₀)
    have h2 : Tendsto (fun q : ℝ × ℝ ↦ |paramMode L Φ k j (q₀.1, q.2) - paramMode L Φ k j q₀|)
        (𝓝 q₀) (𝓝 (|paramMode L Φ k j (q₀.1, q₀.2) - paramMode L Φ k j q₀|)) :=
      (((hs.comp continuous_snd).sub continuous_const).abs).tendsto q₀
    simpa using h1.add h2
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun q ↦ ?_) hlim
  rw [Real.dist_eq]
  calc |paramMode L Φ k j q - paramMode L Φ k j q₀|
      ≤ |paramMode L Φ k j (q.1, q.2) - paramMode L Φ k j (q₀.1, q.2)| +
          |paramMode L Φ k j (q₀.1, q.2) - paramMode L Φ k j q₀| := abs_sub_le _ _ _
    _ ≤ E * |q.1 - q₀.1| + |paramMode L Φ k j (q₀.1, q.2) - paramMode L Φ k j q₀| :=
        add_le_add (hE k q₀.1 q.1 q.2) le_rfl

/-- **The parametric modes are smooth** for a smooth `Φ`, periodic in `z` and vanishing for
large times. -/
theorem contDiff_paramMode {L R : ℝ} (hL : 0 < L) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ) (k j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (paramMode L Φ k j) := by
  suffices h : ∀ n : ℕ, ∀ Φ : ℝ × (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) Φ → IsZPeriodic L Φ →
      VanishesBeyond R Φ → ∀ j, ContDiff ℝ n (paramMode L Φ k j) from
    contDiff_infty.2 fun n ↦ h n Φ hΦ hper hR j
  intro n
  induction n with
  | zero =>
    intro Φ hΦ hper hR j
    exact contDiff_zero.2 (continuous_paramMode hL hΦ hper hR k j)
  | succ n ih =>
    intro Φ hΦ hper hR j
    rw [← contDiffOn_univ]
    exact PDE.Analysis.contDiffOn_succ_of_scalar_partial_derivatives isOpen_univ
      (ih _ (contDiff_tPartial hΦ) hper.tPartial hR.tPartial j).contDiffOn
      (ih _ hΦ hper hR (j + 1)).contDiffOn
      (fun z _ ↦ hasDerivAt_paramMode_time hL hΦ k j z.1 z.2)
      (fun z _ ↦ hasDerivAt_paramMode_space hL hΦ k j z.1 z.2)

/-- The linear map `c ↦ c • fst` of the time part of a derivative. -/
private def timeCLM : ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) ℝ ℝ).flip (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ))

/-- The linear map `c ↦ c • snd` of the space part of a derivative. -/
private def spaceCLM : ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) ℝ ℝ).flip (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ))

/-- The derivative of a parametric mode is assembled from its two partial derivatives. -/
private theorem fderiv_paramMode {L R : ℝ} (hL : 0 < L) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ) (k j : ℕ) :
    fderiv ℝ (paramMode L Φ k j) = fun q ↦
      timeCLM (paramMode L (tPartial Φ) k j q) + spaceCLM (paramMode L Φ k (j + 1) q) := by
  funext q
  have hD₁ : ContinuousOn (fun z : ℝ × ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ
      (paramMode L (tPartial Φ) k j z)) univ :=
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
      (continuous_paramMode hL (contDiff_tPartial hΦ) hper.tPartial hR.tPartial k j)).continuousOn
  have hD₂ : ContinuousOn (fun z : ℝ × ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ
      (paramMode L Φ k (j + 1) z)) univ :=
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
      (continuous_paramMode hL hΦ hper hR k (j + 1))).continuousOn
  have h := PDE.Analysis.hasFDerivAt_of_partial_derivatives isOpen_univ hD₁ hD₂
    (fun z _ ↦ (hasDerivAt_paramMode_time hL hΦ k j z.1 z.2).hasFDerivAt)
    (fun z _ ↦ (hasDerivAt_paramMode_space hL hΦ k j z.1 z.2).hasFDerivAt) (mem_univ q)
  rw [h.fderiv]
  ext <;> simp [timeCLM, spaceCLM]

/-- **Derivative bounds of the parametric modes.** Every iterated derivative of the parametric
modes decays faster than any power of `k`, uniformly in `(t, s)`. -/
theorem exists_norm_iteratedFDeriv_paramMode_le {L R : ℝ} (hL : 0 < L)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ)
    (n N j : ℕ) :
    ∃ C, ∀ (k : ℕ) (q : ℝ × ℝ),
      ‖iteratedFDeriv ℝ n (paramMode L Φ k j) q‖ ≤ C / (1 + (k : ℝ)) ^ N := by
  induction n generalizing Φ j with
  | zero =>
    obtain ⟨E, -, hE⟩ := exists_abs_paramMode_le hL hΦ hper hR j N
    exact ⟨E, fun k q ↦ by rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact hE k q⟩
  | succ n ih =>
    obtain ⟨C₁, hC₁⟩ := ih (contDiff_tPartial hΦ) hper.tPartial hR.tPartial j
    obtain ⟨C₂, hC₂⟩ := ih hΦ hper hR (j + 1)
    refine ⟨‖timeCLM‖ * C₁ + ‖spaceCLM‖ * C₂, fun k q ↦ ?_⟩
    have ht := contDiff_paramMode hL (contDiff_tPartial hΦ) hper.tPartial hR.tPartial k j
    have hs := contDiff_paramMode hL hΦ hper hR k (j + 1)
    rw [← norm_iteratedFDeriv_fderiv, fderiv_paramMode hL hΦ hper hR k j]
    have hA : ContDiffAt ℝ n (fun q ↦ timeCLM (paramMode L (tPartial Φ) k j q)) q :=
      ((timeCLM.contDiff.comp ht).of_le (by exact_mod_cast le_top)).contDiffAt
    have hB : ContDiffAt ℝ n (fun q ↦ spaceCLM (paramMode L Φ k (j + 1) q)) q :=
      ((spaceCLM.contDiff.comp hs).of_le (by exact_mod_cast le_top)).contDiffAt
    rw [fun_iteratedFDeriv_add_apply hA hB]
    refine (norm_add_le _ _).trans ?_
    have h1 := timeCLM.norm_iteratedFDeriv_comp_left (f := paramMode L (tPartial Φ) k j)
      (x := q) (n := n) ht.contDiffAt (by exact_mod_cast le_top)
    have h2 := spaceCLM.norm_iteratedFDeriv_comp_left (f := paramMode L Φ k (j + 1))
      (x := q) (n := n) hs.contDiffAt (by exact_mod_cast le_top)
    calc ‖iteratedFDeriv ℝ n (fun q ↦ timeCLM (paramMode L (tPartial Φ) k j q)) q‖ +
          ‖iteratedFDeriv ℝ n (fun q ↦ spaceCLM (paramMode L Φ k (j + 1) q)) q‖
        ≤ ‖timeCLM‖ * (C₁ / (1 + (k : ℝ)) ^ N) + ‖spaceCLM‖ * (C₂ / (1 + (k : ℝ)) ^ N) :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left (hC₁ k q) (norm_nonneg _)))
            (h2.trans (mul_le_mul_of_nonneg_left (hC₂ k q) (norm_nonneg _)))
      _ = (‖timeCLM‖ * C₁ + ‖spaceCLM‖ * C₂) / (1 + (k : ℝ)) ^ N := by ring

/-! ### The stream modes as functions of time and space -/

/-- The `k`-th stream mode of the slice of `Φ` at time `x.1`, at the point `x.2 = (s, z)`. -/
def paramStreamMode (L : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ) (k : ℕ) (x : ℝ × ℝ^2) : ℝ :=
  paramMode L Φ k 0 (x.1, x.2 0) * Real.sin (modeFrequency L k * x.2 1)

/-- The parametric stream mode is the stream mode of the slice. -/
theorem paramStreamMode_eq (L : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ) (k : ℕ) (x : ℝ × ℝ^2) :
    paramStreamMode L Φ k x = streamMode L (fun p ↦ Φ (x.1, p)) k x.2 := by
  simp [paramStreamMode, paramMode, streamMode, sineTerm, sourceMode]

/-- For a continuous linear map `A`, `‖Dⁱ(f ∘ A)(x)‖ ≤ ‖Dⁱf(A x)‖ ‖A‖ⁱ`. -/
private theorem norm_iteratedFDeriv_comp_clm_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) {f : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (f ∘ A) x‖ ≤ ‖iteratedFDeriv ℝ i f (A x)‖ * ‖A‖ ^ i := by
  rw [A.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The time-and-`s` projection `(t, (s, z)) ↦ (t, s)`. -/
private def tsCLM : ℝ × ℝ^2 →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ^2)).prod
    ((EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ^2)))

/-- The `z` projection `(t, (s, z)) ↦ z`. -/
private def zCLM : ℝ × ℝ^2 →L[ℝ] ℝ :=
  (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ^2))

/-- The parametric stream modes are smooth. -/
theorem contDiff_paramStreamMode {L R : ℝ} (hL : 0 < L) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (paramStreamMode L Φ k) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (paramMode L Φ k 0 ∘ tsCLM) :=
    (contDiff_paramMode hL hΦ hper hR k 0).comp tsCLM.contDiff
  have h2 : ContDiff ℝ (⊤ : ℕ∞) ((fun z ↦ Real.sin (modeFrequency L k * z)) ∘ zCLM) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).comp zCLM.contDiff
  exact h1.mul h2

/-- **Derivative bounds of the parametric stream modes**: `‖Dⁿ m_k‖ ≤ Dₙ / (1 + k)²`. -/
theorem exists_norm_iteratedFDeriv_paramStreamMode_le {L R : ℝ} (hL : 0 < L)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ) (n : ℕ) :
    ∃ D, ∀ (k : ℕ) (x : ℝ × ℝ^2),
      ‖iteratedFDeriv ℝ n (paramStreamMode L Φ k) x‖ ≤ D / (1 + (k : ℝ)) ^ 2 := by
  have hb : ∀ i : ℕ, ∃ C, ∀ (k : ℕ) (q : ℝ × ℝ),
      ‖iteratedFDeriv ℝ i (paramMode L Φ k 0) q‖ ≤ C / (1 + (k : ℝ)) ^ (n + 2) := fun i ↦
    exists_norm_iteratedFDeriv_paramMode_le hL hΦ hper hR i (n + 2) 0
  choose C hC using hb
  set c : ℝ := 2 * π / L
  have hc : 0 < c := by positivity
  set P := ‖tsCLM‖
  set Q := ‖zCLM‖
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (|C i| * (1 + P) ^ n) *
    ((1 + c) ^ n * (1 + Q) ^ n), fun k x ↦ ?_⟩
  have hkpos : (0 : ℝ) < 1 + k := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hk1 : (1 : ℝ) ≤ 1 + k := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  set μ := modeFrequency L k
  have hμ : μ = c * (1 + k) := modeFrequency_eq L k
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (paramMode L Φ k 0) := contDiff_paramMode hL hΦ hper hR k 0
  have hsin : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ Real.sin (μ * z)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hm := norm_iteratedFDeriv_mul_le (h1.comp tsCLM.contDiff) (hsin.comp zCLM.contDiff) x
    (n := n) (by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ n (fun x ↦ (paramMode L Φ k 0 ∘ tsCLM) x *
    ((fun z ↦ Real.sin (μ * z)) ∘ zCLM) x) x‖ ≤ _
  refine hm.trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hA := norm_iteratedFDeriv_comp_clm_le tsCLM h1 i x
  have hB := norm_iteratedFDeriv_comp_clm_le zCLM hsin (n - i) x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hB
  have hsinb := abs_iteratedDeriv_sin_mul_le μ (n - i) (zCLM x)
  have hP : P ^ i ≤ (1 + P) ^ n :=
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith) i).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg tsCLM]) hin)
  have hQ : Q ^ (n - i) ≤ (1 + Q) ^ n :=
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg zCLM]) (Nat.sub_le n i))
  have hμn : |μ| ^ (n - i) ≤ (1 + c) ^ n * (1 + k) ^ n := by
    rw [hμ, abs_of_pos (by positivity), ← mul_pow]
    calc (c * (1 + (k : ℝ))) ^ (n - i) ≤ ((1 + c) * (1 + k)) ^ (n - i) :=
          pow_le_pow_left₀ (by positivity) (by nlinarith) _
      _ ≤ ((1 + c) * (1 + k)) ^ n :=
          pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (by linarith) hk1) (Nat.sub_le n i)
  have hCi : ‖iteratedFDeriv ℝ i (paramMode L Φ k 0) (tsCLM x)‖ ≤
      |C i| / (1 + (k : ℝ)) ^ (n + 2) :=
    (hC i k (tsCLM x)).trans (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))
  have hsplit : (1 + (k : ℝ)) ^ (n + 2) = (1 + k) ^ n * (1 + k) ^ 2 := pow_add _ _ _
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (paramMode L Φ k 0 ∘ tsCLM) x‖ *
        ‖iteratedFDeriv ℝ (n - i) ((fun z ↦ Real.sin (μ * z)) ∘ zCLM) x‖
      ≤ (n.choose i : ℝ) * (|C i| / (1 + (k : ℝ)) ^ (n + 2) * (1 + P) ^ n) *
          ((1 + c) ^ n * (1 + k) ^ n * (1 + Q) ^ n) := by
        gcongr
        · exact hA.trans (mul_le_mul hCi hP (by positivity) (by positivity))
        · refine hB.trans (mul_le_mul (hsinb.trans hμn) hQ (by positivity) (by positivity))
    _ = (n.choose i : ℝ) * (|C i| * (1 + P) ^ n) * ((1 + c) ^ n * (1 + Q) ^ n) /
          (1 + (k : ℝ)) ^ 2 := by
        rw [hsplit]
        field_simp

/-- **Smoothness in time of the stream profile, for sources vanishing at large times.** -/
theorem contDiff_streamProfile_of_vanishesBeyond {L R : ℝ} (hL : 0 < L)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ^2 ↦ streamProfile L (fun p ↦ Φ (x.1, p)) x.2) := by
  have hb : ∀ n : ℕ, ∃ D, ∀ (k : ℕ) (x : ℝ × ℝ^2),
      ‖iteratedFDeriv ℝ n (paramStreamMode L Φ k) x‖ ≤ D / (1 + (k : ℝ)) ^ 2 := fun n ↦
    exists_norm_iteratedFDeriv_paramStreamMode_le hL hΦ hper hR n
  choose D hD using hb
  have heq : (fun x : ℝ × ℝ^2 ↦ streamProfile L (fun p ↦ Φ (x.1, p)) x.2) =
      fun x ↦ ∑' k, paramStreamMode L Φ k x := by
    funext x
    simp only [streamProfile, paramStreamMode_eq]
  rw [heq]
  exact contDiff_tsum (fun k ↦ contDiff_paramStreamMode hL hΦ hper hR k)
    (fun n _ ↦ summable_div_one_add_sq (D n)) (fun n k x _ ↦ hD n k x)

/-! ### Localization in time -/

/-- The stream profile is homogeneous in the source. -/
theorem streamProfile_const_mul {L : ℝ} (hL : 0 < L) (a : ℝ) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (p : ℝ^2) :
    streamProfile L (fun q ↦ a * G q) p = a * streamProfile L G p := by
  have hmode : ∀ k, streamMode L (fun q ↦ a * G q) k p = a * streamMode L G k p := by
    intro k
    have hμ := modeFrequency_pos hL k
    have hc : coefficientMode L (fun q ↦ a * G q) k =
        fun s ↦ a * coefficientMode L G k s := by
      funext s
      have h := coefficientMode_linear (L := L) (a := a) (b := 0) hG.continuous hG.continuous k s
      simpa using h
    have hF := contDiff_coefficientMode (L := L) hG k
    have hm : modeTerm (modeFrequency L k) (fun s ↦ a * coefficientMode L G k s) =
        fun s ↦ a * modeTerm (modeFrequency L k) (coefficientMode L G k) s := by
      have h := modeTerm_linear (a := a) (b := 0) hμ hF hF
      simpa using h
    simp only [streamMode, sineTerm, hc, hm]
    ring
  simp only [streamProfile, hmode, tsum_mul_left]

/-- **Smoothness in time of the stream profile.** For a smooth `Φ(t, (s, z))`, `L`-periodic in
`z`, the stream profile `(t, p) ↦ Ψ_t(p)` of the slices `p ↦ Φ(t, p)` is smooth. -/
theorem contDiff_streamProfile_slices {L : ℝ} (hL : 0 < L) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hper : IsZPeriodic L Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ^2 ↦ streamProfile L (fun p ↦ Φ (x.1, p)) x.2) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  let η : ContDiffBump x₀.1 := ⟨1, 2, one_pos, one_lt_two⟩
  set Φ' : ℝ × (ℝ × ℝ) → ℝ := fun q ↦ η q.1 * Φ q
  have hΦ' : ContDiff ℝ (⊤ : ℕ∞) Φ' := (η.contDiff.comp contDiff_fst).mul hΦ
  have hper' : IsZPeriodic L Φ' := fun t s z ↦ by simp only [Φ', hper t s z]
  have hR' : VanishesBeyond (|x₀.1| + 2) Φ' := by
    intro q hq
    have : (2 : ℝ) ≤ dist q.1 x₀.1 := by
      rw [Real.dist_eq]
      have := abs_sub_abs_le_abs_sub q.1 x₀.1
      linarith
    simp only [Φ', η.zero_of_le_dist (show η.rOut ≤ dist q.1 x₀.1 from this), zero_mul]
  have hmain := (contDiff_streamProfile_of_vanishesBeyond hL hΦ' hper' hR').contDiffAt (x := x₀)
  refine hmain.congr_of_eventuallyEq ?_
  have hopen : IsOpen {x : ℝ × ℝ^2 | dist x.1 x₀.1 < 1} :=
    isOpen_lt (continuous_fst.dist continuous_const) continuous_const
  filter_upwards [hopen.mem_nhds (by simp)] with x hx
  have hη : η x.1 = 1 := η.one_of_mem_closedBall (Metric.mem_closedBall.2 (le_of_lt hx))
  simp only [Φ', hη, one_mul]

/-- **Local smoothness in time.** If `Φ` is smooth on `U × ℝ²` for an open set of times `U` and
its slices at times of `U` are `L`-periodic in `z`, the stream profile of the slices is smooth on
`U × ℝ²`. -/
theorem contDiffOn_streamProfile_slices {L : ℝ} (hL : 0 < L) {U : Set ℝ} (hU : IsOpen U)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ univ))
    (hper : ∀ t ∈ U, ∀ s z, Φ (t, (s, z + L)) = Φ (t, (s, z))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ × ℝ^2 ↦ streamProfile L (fun p ↦ Φ (x.1, p)) x.2)
      (U ×ˢ univ) := by
  intro x₀ hx₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x₀.1 hx₀.1
  let η : ContDiffBump x₀.1 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set Φ' : ℝ × (ℝ × ℝ) → ℝ := fun q ↦ η q.1 * Φ q
  have hUopen : IsOpen (U ×ˢ (univ : Set (ℝ × ℝ))) := hU.prod isOpen_univ
  have hΦ' : ContDiff ℝ (⊤ : ℕ∞) Φ' := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : dist q.1 x₀.1 < r
    · have hqU : q ∈ U ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hrU hq, mem_univ _⟩
      exact (η.contDiff.comp contDiff_fst).contDiffAt.mul (hΦ.contDiffAt (hUopen.mem_nhds hqU))
    · have hopen : IsOpen {q : ℝ × (ℝ × ℝ) | r / 2 < dist q.1 x₀.1} :=
        isOpen_lt continuous_const (continuous_fst.dist continuous_const)
      have hmem : q ∈ {q : ℝ × (ℝ × ℝ) | r / 2 < dist q.1 x₀.1} := by
        change r / 2 < dist q.1 x₀.1
        linarith [not_lt.1 hq]
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hmem] with q' hq'
      simp only [Φ', η.zero_of_le_dist (show η.rOut ≤ dist q'.1 x₀.1 from le_of_lt hq'),
        zero_mul]
  have hper' : IsZPeriodic L Φ' := by
    intro t s z
    by_cases ht : dist t x₀.1 < r
    · simp only [Φ', hper t (hrU ht) s z]
    · have h0 : η t = 0 := η.zero_of_le_dist (by
        change r / 2 ≤ dist t x₀.1
        linarith [not_lt.1 ht])
      simp only [Φ', h0, zero_mul]
  have hR' : VanishesBeyond (|x₀.1| + r) Φ' := by
    intro q hq
    have : r ≤ dist q.1 x₀.1 := by
      rw [Real.dist_eq]
      have := abs_sub_abs_le_abs_sub q.1 x₀.1
      linarith
    simp only [Φ', η.zero_of_le_dist (show η.rOut ≤ dist q.1 x₀.1 by
      change r / 2 ≤ _; linarith), zero_mul]
  have hmain := (contDiff_streamProfile_of_vanishesBeyond hL hΦ' hper' hR').contDiffAt (x := x₀)
  refine (hmain.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hopen : IsOpen {x : ℝ × ℝ^2 | dist x.1 x₀.1 < r / 4} :=
    isOpen_lt (continuous_fst.dist continuous_const) continuous_const
  filter_upwards [hopen.mem_nhds (by simpa using (by positivity : 0 < r / 4))] with x hx
  have hη : η x.1 = 1 := η.one_of_mem_closedBall (Metric.mem_closedBall.2 (le_of_lt hx))
  simp only [Φ', hη, one_mul]

/-- **Joint smoothness in time of the stream profile** (the profile form of
`contDiff_streamProfile_slices`). For `Ω : ℝ → ℝ × ℝ → ℝ` with `(t, s, z) ↦ Ω t (s, z)` smooth on
`ℝ³` and every slice `L`-periodic in `z`, the stream profiles `Ψ(t, s, z)` of the slices
`Ω t` are jointly smooth. -/
theorem contDiff_streamProfile_param {L : ℝ} (hL : 0 < L) {Ω : ℝ → ℝ × ℝ → ℝ}
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ^3 ↦ Ω (q 0) (q 1, q 2)))
    (hper : ∀ t s z, Ω t (s, z + L) = Ω t (s, z)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ^3 ↦ streamProfile L (Ω (q 0)) (WithLp.toLp 2 ![q 1, q 2])) := by
  set e : ℝ × (ℝ × ℝ) →L[ℝ] ℝ^3 :=
    ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).smulRight (EuclideanSpace.single (0 : Fin 3) 1)) +
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight
      (EuclideanSpace.single (1 : Fin 3) 1)) +
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).smulRight
      (EuclideanSpace.single (2 : Fin 3) 1))
  have he : ∀ q : ℝ × (ℝ × ℝ), e q = WithLp.toLp 2 ![q.1, q.2.1, q.2.2] := by
    intro q
    ext i
    fin_cases i <;> simp [e]
  set Φ : ℝ × (ℝ × ℝ) → ℝ := fun q ↦ Ω q.1 q.2
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    have hfun : Φ = (fun q : ℝ^3 ↦ Ω (q 0) (q 1, q 2)) ∘ e := by
      funext q
      simp [Φ, he]
    rw [hfun]
    exact hΩ.comp e.contDiff
  have hper' : IsZPeriodic L Φ := fun t s z ↦ hper t s z
  have hmain := contDiff_streamProfile_slices hL hΦ hper'
  set g : ℝ^3 →L[ℝ] ℝ × ℝ^2 :=
    (EuclideanSpace.proj (0 : Fin 3) : ℝ^3 →L[ℝ] ℝ).prod
      (((EuclideanSpace.proj (1 : Fin 3) : ℝ^3 →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single (0 : Fin 2) 1)) +
      ((EuclideanSpace.proj (2 : Fin 3) : ℝ^3 →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single (1 : Fin 2) 1)))
  have hg : ∀ q : ℝ^3, g q = (q 0, WithLp.toLp 2 ![q 1, q 2]) := by
    intro q
    refine Prod.ext rfl ?_
    ext i
    fin_cases i <;> simp [g]
  have hfun : (fun q : ℝ^3 ↦ streamProfile L (Ω (q 0)) (WithLp.toLp 2 ![q 1, q 2])) =
      (fun x : ℝ × ℝ^2 ↦ streamProfile L (fun p ↦ Φ (x.1, p)) x.2) ∘ g := by
    funext q
    simp only [Function.comp_apply, hg, Φ]
  rw [hfun]
  exact hmain.comp g.contDiff

end

end Euler.Cylinder
