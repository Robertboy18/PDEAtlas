/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderStreamSources

/-!
# Bounds of the stream profile by finitely many derivatives of the source

For a smooth source `G(s, z)`, `L`-periodic in `z`, the stream profile `Ψ = streamProfile L G`
is linear in `G` (`streamProfile_sub`), and for `n ≤ p` its derivatives of order `n` are bounded
on the whole plane by a constant depending only on `L`, `p` and `n` times a bound `m` of the
derivatives `∂_s^l ∂_z^{2p} G`, `l ≤ n`, on the collar `modeCollar L × [0, L]`
(`norm_iteratedFDeriv_streamProfile_le`).

The `k`-th mode of `∂_z^{2p} G` is `(-μ_k²)^p` times the `k`-th mode of `G`,
`μ_k = 2π (k + 1) / L` (`sourceMode_iterate_zDeriv`), so the bound of the cut-off modes by the
`s`-derivatives of their source (`abs_iteratedDeriv_sourceMode_le`) gains `μ_k^{-2p}`. A
derivative of order `n ≤ p` of the `k`-th stream mode `η_k Ψ_k(s) sin(μ_k z)` costs at most
`(1 + μ_k²)^p`, and `(1 + μ_k²)^p / μ_k^{2p+2} ≲ (1 + k)⁻²` is summable.

This is the continuity of the stream operator from sources with bounded `∂_s^{≤n} ∂_z^{2p}` to
`C^n` profiles, which extends the construction to sources of finite regularity.

## Main definitions

* `modeBoundConst L p n`, `profileBoundConst L p n`: the constants of the bounds.

## Main results

* `streamMode_sub`, `streamProfile_sub`: linearity.
* `coefficientMode_iterate_zDeriv`, `sourceMode_iterate_zDeriv`: the modes of `∂_z^{2p} G`.
* `norm_iteratedFDeriv_streamMode_le_of_zDeriv`: the bound of one stream mode.
* `norm_iteratedFDeriv_streamProfile_le`: the bound of the stream profile.
-/

@[expose] public section

namespace Euler.Cylinder

open Set Filter PDE.Analysis.Fourier.SineSeries
open scoped Topology Real

set_option linter.missingDocs true

noncomputable section

variable {L : ℝ}

/-- The mode term depends on the frequency only through its square. -/
theorem modeTerm_neg (μ : ℝ) (F : ℝ → ℝ) : modeTerm (-μ) F = modeTerm μ F := by
  funext s
  simp only [modeTerm, modeCutoff, modeSolution, particularMode, modeQuotient, modeAverage,
    homogeneousMode, neg_sq]

/-- The stream modes are linear in the source (for `L = 0` every mode vanishes). -/
theorem streamMode_sub {G₁ G₂ : ℝ × ℝ → ℝ} (hG₁ : ContDiff ℝ (⊤ : ℕ∞) G₁)
    (hG₂ : ContDiff ℝ (⊤ : ℕ∞) G₂) (k : ℕ) (p : ℝ^2) :
    streamMode L (fun q ↦ G₁ q - G₂ q) k p = streamMode L G₁ k p - streamMode L G₂ k p := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp [streamMode, sineTerm, modeFrequency]
  have hμ0 : modeFrequency L k ≠ 0 := by
    unfold modeFrequency
    exact div_ne_zero (by positivity) hL
  have hμ : 0 < |modeFrequency L k| := abs_pos.mpr hμ0
  have habs (F : ℝ → ℝ) : modeTerm (modeFrequency L k) F = modeTerm |modeFrequency L k| F := by
    rcases abs_choice (modeFrequency L k) with h | h <;> rw [h]
    rw [modeTerm_neg]
  have hfun : (fun q ↦ G₁ q - G₂ q) = fun q ↦ 1 * G₁ q + (-1) * G₂ q := by
    funext q
    ring
  have hc : coefficientMode L (fun q ↦ G₁ q - G₂ q) k =
      fun s ↦ 1 * coefficientMode L G₁ k s + (-1) * coefficientMode L G₂ k s := by
    funext s
    rw [hfun]
    exact coefficientMode_linear hG₁.continuous hG₂.continuous k s
  have hm := modeTerm_linear (a := 1) (b := -1) hμ (contDiff_coefficientMode (L := L) hG₁ k)
    (contDiff_coefficientMode (L := L) hG₂ k)
  simp only [streamMode, sineTerm, hc, habs, hm]
  ring

/-- **Linearity of the stream profile.** -/
theorem streamProfile_sub (hL : 0 < L) {G₁ G₂ : ℝ × ℝ → ℝ} (hG₁ : ContDiff ℝ (⊤ : ℕ∞) G₁)
    (hG₂ : ContDiff ℝ (⊤ : ℕ∞) G₂) (hper₁ : ∀ s z, G₁ (s, z + L) = G₁ (s, z))
    (hper₂ : ∀ s z, G₂ (s, z + L) = G₂ (s, z)) (p : ℝ^2) :
    streamProfile L (fun q ↦ G₁ q - G₂ q) p = streamProfile L G₁ p - streamProfile L G₂ p := by
  have hs (G : ℝ × ℝ → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hper : ∀ s z, G (s, z + L) = G (s, z)) :
      Summable fun k ↦ streamMode L G k p := by
    obtain ⟨D, hD⟩ := exists_streamMode_bounds hL hG hper
    refine (summable_div_one_add_sq (D 0)).of_norm_bounded fun k ↦ ?_
    have := hD 0 k p
    rwa [norm_iteratedFDeriv_zero] at this
  unfold streamProfile
  rw [← (hs G₁ hG₁ hper₁).tsum_sub (hs G₂ hG₂ hper₂)]
  exact tsum_congr fun k ↦ streamMode_sub hG₁ hG₂ k p

/-- The coefficient modes of `∂_z^{2p} G` are `(-μ_k²)^p` times those of `G`. -/
theorem coefficientMode_iterate_zDeriv (hL : 0 < L) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hper : ∀ s z, G (s, z + L) = G (s, z)) (p k : ℕ) (s : ℝ) :
    coefficientMode L (zDeriv^[2 * p] G) k s =
      (-modeFrequency L k ^ 2) ^ p * coefficientMode L G k s := by
  have h := sineCoeff_iterate_zDeriv hL hG hper (k + 1) p s
  simp only [coefficientMode, modeFrequency]
  rw [h]
  push_cast
  ring

/-- The source modes of `∂_z^{2p} G` are `(-μ_k²)^p` times those of `G`. -/
theorem sourceMode_iterate_zDeriv (hL : 0 < L) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hper : ∀ s z, G (s, z + L) = G (s, z)) (p k : ℕ) :
    sourceMode L (zDeriv^[2 * p] G) k =
      fun s ↦ (-modeFrequency L k ^ 2) ^ p * sourceMode L G k s := by
  have hμ := modeFrequency_pos hL k
  have hc : coefficientMode L (zDeriv^[2 * p] G) k =
      fun s ↦ (-modeFrequency L k ^ 2) ^ p * coefficientMode L G k s +
        0 * (fun _ : ℝ ↦ (0 : ℝ)) s := by
    funext s
    rw [coefficientMode_iterate_zDeriv hL hG hper p k s]
    ring
  have hm := modeTerm_linear (a := (-modeFrequency L k ^ 2) ^ p) (b := 0) hμ
    (contDiff_coefficientMode (L := L) hG k) (contDiff_const (c := (0 : ℝ)))
  funext s
  simp only [sourceMode, hc, hm]
  ring

/-- The `s`-derivatives of the source modes of `G` are bounded by `μ_k^{-2p-2}` times a bound `m`
of the derivatives `∂_s^l ∂_z^{2p} G`, `l ≤ j`, on the collar. -/
theorem abs_iteratedDeriv_sourceMode_le_of_zDeriv (hL : 0 < L) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hper : ∀ s z, G (s, z + L) = G (s, z)) (p k j : ℕ) {m : ℝ}
    (hm : ∀ l ≤ j, ∀ s ∈ modeCollar L, ∀ z ∈ Icc 0 L,
      |(sDeriv^[l] (zDeriv^[2 * p] G)) (s, z)| ≤ m) (s : ℝ) :
    |iteratedDeriv j (sourceMode L G k) s| ≤
      3 * modeConst j * (1 + modeFrequency L k ^ 2) ^ j * ((j + 1) * (2 * m)) /
        modeFrequency L k ^ (2 * p + 2) := by
  set μ := modeFrequency L k
  have hμ : 0 < μ := modeFrequency_pos hL k
  have hGp : ContDiff ℝ (⊤ : ℕ∞) (zDeriv^[2 * p] G) := contDiff_iterate_zDeriv hG _
  have h := abs_iteratedDeriv_sourceMode_le hL hGp k j hm s
  have hd : iteratedDeriv j (sourceMode L (zDeriv^[2 * p] G) k) s =
      (-μ ^ 2) ^ p * iteratedDeriv j (sourceMode L G k) s := by
    rw [sourceMode_iterate_zDeriv hL hG hper p k]
    exact iteratedDeriv_const_mul _ ((contDiff_sourceMode hL hG k).contDiffAt.of_le
      (by exact_mod_cast le_top))
  have habs : |(-μ ^ 2) ^ p| = μ ^ (2 * p) := by
    rw [abs_pow, abs_neg, abs_of_pos (by positivity), ← pow_mul]
  rw [hd, abs_mul, habs] at h
  rw [show μ ^ (2 * p + 2) = μ ^ 2 * μ ^ (2 * p) by ring, ← div_div, le_div_iff₀ (by positivity)]
  linarith

/-- `(1 + μ²)^i μ^{n-i} / μ^{2p+2} ≤ (1 + c⁻²)^p / (c² (1 + k)²)` for `i ≤ n ≤ p` and
`μ = c (1 + k)`. -/
private theorem pow_mul_pow_div_le {c μ : ℝ} {k i n p : ℕ} (hc : 0 < c) (hμ : μ = c * (1 + k))
    (hin : i ≤ n) (hn : n ≤ p) :
    (1 + μ ^ 2) ^ i * μ ^ (n - i) / μ ^ (2 * p + 2) ≤
      (1 + c⁻¹ ^ 2) ^ p / (c ^ 2 * (1 + k) ^ 2) := by
  have hk : (1 : ℝ) ≤ 1 + k := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hμc : c ≤ μ := by rw [hμ]; nlinarith
  have hμpos : 0 < μ := hc.trans_le hμc
  set Λ := 1 + μ ^ 2 with hΛ
  have hΛ1 : 1 ≤ Λ := by nlinarith
  have hμΛ : μ ≤ Λ := by nlinarith [sq_nonneg (μ - 1)]
  have h1 : (1 + μ ^ 2) ^ i * μ ^ (n - i) ≤ Λ ^ p := by
    calc (1 + μ ^ 2) ^ i * μ ^ (n - i) ≤ Λ ^ i * Λ ^ (n - i) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμpos.le hμΛ _) (by positivity)
      _ = Λ ^ n := by rw [← pow_add, Nat.add_sub_cancel' hin]
      _ ≤ Λ ^ p := pow_le_pow_right₀ hΛ1 hn
  have h2 : Λ ≤ (1 + c⁻¹ ^ 2) * μ ^ 2 := by
    have : 1 ≤ c⁻¹ ^ 2 * μ ^ 2 := by
      rw [← mul_pow, one_le_sq_iff_one_le_abs, abs_of_pos (by positivity)]
      rw [inv_mul_eq_div, one_le_div hc]
      exact hμc
    nlinarith
  have h3 : Λ ^ p / μ ^ (2 * p + 2) ≤ (1 + c⁻¹ ^ 2) ^ p / μ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := pow_le_pow_left₀ (by positivity) h2 p
    calc Λ ^ p * μ ^ 2 ≤ ((1 + c⁻¹ ^ 2) * μ ^ 2) ^ p * μ ^ 2 :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (1 + c⁻¹ ^ 2) ^ p * μ ^ (2 * p + 2) := by rw [mul_pow, ← pow_mul]; ring
  calc (1 + μ ^ 2) ^ i * μ ^ (n - i) / μ ^ (2 * p + 2) ≤ Λ ^ p / μ ^ (2 * p + 2) :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ (1 + c⁻¹ ^ 2) ^ p / μ ^ 2 := h3
    _ = (1 + c⁻¹ ^ 2) ^ p / (c ^ 2 * (1 + k) ^ 2) := by rw [hμ, mul_pow]

/-- The constant `D_{p,n} = ∑_{i ≤ n} (n choose i) 6 (i + 1) C_i (1 + c⁻²)^p / c²` of the mode
bounds, `c = 2π/L`, `C_i` the constants of the cut-off modes. -/
def modeBoundConst (L : ℝ) (p n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (6 * (i + 1) * modeConst i) *
    ((1 + (2 * π / L)⁻¹ ^ 2) ^ p / (2 * π / L) ^ 2)

/-- The constant `∑ₖ D_{p,n} / (1 + k)²` of the bound of the stream profile. -/
def profileBoundConst (L : ℝ) (p n : ℕ) : ℝ :=
  ∑' k : ℕ, modeBoundConst L p n / (1 + (k : ℝ)) ^ 2

/-- The constants of the mode bounds are nonnegative. -/
theorem modeBoundConst_nonneg (L : ℝ) (p n : ℕ) : 0 ≤ modeBoundConst L p n :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (by positivity) (modeConst_nonneg i))) (by positivity)

/-- The constants of the profile bounds are nonnegative. -/
theorem profileBoundConst_nonneg (L : ℝ) (p n : ℕ) : 0 ≤ profileBoundConst L p n :=
  tsum_nonneg fun _ ↦ div_nonneg (modeBoundConst_nonneg L p n) (by positivity)

/-- **The bound of one stream mode.** For `n ≤ p`,
`‖Dⁿ (streamMode L G k)‖ ≤ D_{p,n} m / (1 + k)²`, with `m` a bound of `∂_s^l ∂_z^{2p} G`,
`l ≤ n`, on the collar. -/
theorem norm_iteratedFDeriv_streamMode_le_of_zDeriv (hL : 0 < L) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hper : ∀ s z, G (s, z + L) = G (s, z)) {p n : ℕ}
    (hn : n ≤ p) {m : ℝ} (hm : ∀ l ≤ n, ∀ s ∈ modeCollar L, ∀ z ∈ Icc 0 L,
      |(sDeriv^[l] (zDeriv^[2 * p] G)) (s, z)| ≤ m) (k : ℕ) (p' : ℝ^2) :
    ‖iteratedFDeriv ℝ n (streamMode L G k) p'‖ ≤
      modeBoundConst L p n * m / (1 + (k : ℝ)) ^ 2 := by
  set c : ℝ := 2 * π / L
  have hc : 0 < c := by positivity
  set μ := modeFrequency L k
  have hμ : μ = c * (1 + k) := by simp only [μ, modeFrequency, c]; ring
  have hμpos : 0 < μ := modeFrequency_pos hL k
  have h0mem : (0 : ℝ) ∈ modeCollar L :=
    ⟨div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity), by positivity⟩
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm 0 (Nat.zero_le _) 0 h0mem 0 ⟨le_rfl, hL.le⟩)
  have h := norm_iteratedFDeriv_sineTerm_le (contDiff_sourceMode (L := L) hL hG k) μ n p'
  change ‖iteratedFDeriv ℝ n (sineTerm (sourceMode L G k) μ) p'‖ ≤ _
  refine h.trans ?_
  rw [modeBoundConst, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hb := abs_iteratedDeriv_sourceMode_le_of_zDeriv hL hG hper p k i
    (fun l hl ↦ hm l (hl.trans hin)) (p' 0)
  have hpow := pow_mul_pow_div_le (k := k) hc hμ hin hn
  have hC0 : 0 ≤ modeConst i := modeConst_nonneg i
  rw [abs_of_pos hμpos]
  calc (n.choose i : ℝ) * |iteratedDeriv i (sourceMode L G k) (p' 0)| * μ ^ (n - i)
      ≤ (n.choose i : ℝ) * (3 * modeConst i * (1 + μ ^ 2) ^ i * ((i + 1) * (2 * m)) /
          μ ^ (2 * p + 2)) * μ ^ (n - i) := by gcongr
    _ = (n.choose i : ℝ) * (6 * (i + 1) * modeConst i) * m *
          ((1 + μ ^ 2) ^ i * μ ^ (n - i) / μ ^ (2 * p + 2)) := by ring
    _ ≤ (n.choose i : ℝ) * (6 * (i + 1) * modeConst i) * m *
          ((1 + c⁻¹ ^ 2) ^ p / (c ^ 2 * (1 + k) ^ 2)) := by gcongr
    _ = (n.choose i : ℝ) * (6 * (i + 1) * modeConst i) * ((1 + c⁻¹ ^ 2) ^ p / c ^ 2) * m /
          (1 + (k : ℝ)) ^ 2 := by field_simp

/-- **The bound of the stream profile.** For a smooth source `G`, `L`-periodic in `z`, and
`n ≤ p`, `‖Dⁿ (streamProfile L G) x‖ ≤ profileBoundConst L p n * m` at every point, with `m` a
bound of `∂_s^l ∂_z^{2p} G`, `l ≤ n`, on `modeCollar L × [0, L]`. -/
theorem norm_iteratedFDeriv_streamProfile_le (hL : 0 < L) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hper : ∀ s z, G (s, z + L) = G (s, z)) {p n : ℕ}
    (hn : n ≤ p) {m : ℝ} (hm : ∀ l ≤ n, ∀ s ∈ modeCollar L, ∀ z ∈ Icc 0 L,
      |(sDeriv^[l] (zDeriv^[2 * p] G)) (s, z)| ≤ m) (x : ℝ^2) :
    ‖iteratedFDeriv ℝ n (streamProfile L G) x‖ ≤ profileBoundConst L p n * m := by
  rw [iteratedFDeriv_streamProfile hL hG hper n x]
  have hb := norm_iteratedFDeriv_streamMode_le_of_zDeriv hL hG hper hn hm
  have hsum : Summable fun k : ℕ ↦ modeBoundConst L p n * m / (1 + (k : ℝ)) ^ 2 :=
    summable_div_one_add_sq _
  have hnorm : Summable fun k ↦ ‖iteratedFDeriv ℝ n (streamMode L G k) x‖ :=
    hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun k ↦ hb k x
  calc ‖∑' k, iteratedFDeriv ℝ n (streamMode L G k) x‖
      ≤ ∑' k, ‖iteratedFDeriv ℝ n (streamMode L G k) x‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, modeBoundConst L p n * m / (1 + (k : ℝ)) ^ 2 :=
        hnorm.tsum_le_tsum (fun k ↦ hb k x) hsum
    _ = profileBoundConst L p n * m := by
        rw [profileBoundConst, ← tsum_mul_right]
        congr 1
        funext k
        ring

end

end Euler.Cylinder
