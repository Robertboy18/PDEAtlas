/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderStreamExistence
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Sources of the stream profile depending on time

For a vorticity profile `Φ(t, (s, z))`, `L`-periodic in `z`, we collect the facts about its slices
that the smoothness in time of the stream profile needs:

* the partial derivatives `tPartial`, `sPartial`, `zPartial` and their commutation;
* periodicity in `z` (`IsZPeriodic`) and vanishing for large times (`VanishesBeyond`), both
  inherited by the partial derivatives;
* the decay of the sine coefficients of the slices, uniformly in time
  (`exists_abs_iteratedDeriv_coefficientMode_le`, from `abs_sineCoeff_le_of_iterate_zDeriv_le`);
* the linearity of the mode operators in the source (`modeTerm_linear`,
  `iteratedDeriv_sourceMode_linear`) and the bound of a cut-off mode by the `s`-derivatives of its
  source on the common collar `modeCollar L` (`abs_iteratedDeriv_sourceMode_le`).

## Main definitions

* `tPartial`, `sPartial`, `zPartial`, `IsZPeriodic`, `VanishesBeyond`.
* `sourceMode`, `modeConst`, `modeCollar`.
-/

@[expose] public section

namespace Euler.Cylinder

open Set Filter PDE.Analysis.Fourier.SineSeries
open scoped Topology Real

set_option linter.missingDocs true

noncomputable section

/-! ### Partial derivatives in time and in the profile variables -/

/-- The time derivative `∂_t Φ` of `Φ(t, (s, z))`. -/
def tPartial (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ Φ q (1, (0, 0))

/-- The derivative `∂_s Φ` of `Φ(t, (s, z))`. -/
def sPartial (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ Φ q (0, (1, 0))

/-- The derivative `∂_z Φ` of `Φ(t, (s, z))`. -/
def zPartial (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  fderiv ℝ Φ q (0, (0, 1))

variable {Φ : ℝ × (ℝ × ℝ) → ℝ}

/-- The time derivative of a smooth function is smooth. -/
theorem contDiff_tPartial (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : ContDiff ℝ (⊤ : ℕ∞) (tPartial Φ) :=
  (hΦ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- The `s`-derivative of a smooth function is smooth. -/
theorem contDiff_sPartial (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : ContDiff ℝ (⊤ : ℕ∞) (sPartial Φ) :=
  (hΦ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- The `z`-derivative of a smooth function is smooth. -/
theorem contDiff_zPartial (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : ContDiff ℝ (⊤ : ℕ∞) (zPartial Φ) :=
  (hΦ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- Iterated `s`-derivatives of a smooth function are smooth. -/
theorem contDiff_iterate_sPartial (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (l : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sPartial^[l] Φ) := by
  induction l with
  | zero => simpa using hΦ
  | succ l ih => rw [Function.iterate_succ_apply']; exact contDiff_sPartial ih

/-- Iterated `z`-derivatives of a smooth function are smooth. -/
theorem contDiff_iterate_zPartial (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (zPartial^[j] Φ) := by
  induction j with
  | zero => simpa using hΦ
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiff_zPartial ih

/-- Iterated time derivatives of a smooth function are smooth. -/
theorem contDiff_iterate_tPartial (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (a : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (tPartial^[a] Φ) := by
  induction a with
  | zero => simpa using hΦ
  | succ a ih => rw [Function.iterate_succ_apply']; exact contDiff_tPartial ih

/-- The slices `p ↦ Φ(t, p)` of a smooth function are smooth. -/
theorem contDiff_slice (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ ↦ Φ (t, p)) :=
  hΦ.comp (contDiff_const.prodMk contDiff_id)

/-- The `s`-derivative of a slice is the slice of the `s`-derivative. -/
theorem sDeriv_slice (hΦ : Differentiable ℝ Φ) (t : ℝ) (p : ℝ × ℝ) :
    sDeriv (fun p ↦ Φ (t, p)) p = sPartial Φ (t, p) := by
  have hp : HasFDerivAt (fun p : ℝ × ℝ ↦ ((t, p) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) p :=
    (hasFDerivAt_const t p).prodMk (hasFDerivAt_id p)
  have h := ((hΦ (t, p)).hasFDerivAt.comp p hp).fderiv
  simp only [sDeriv, sPartial]
  change fderiv ℝ (Φ ∘ fun p : ℝ × ℝ ↦ ((t, p) : ℝ × (ℝ × ℝ))) p (1, 0) = _
  rw [h]
  rfl

/-- The `z`-derivative of a slice is the slice of the `z`-derivative. -/
theorem zDeriv_slice (hΦ : Differentiable ℝ Φ) (t : ℝ) (p : ℝ × ℝ) :
    zDeriv (fun p ↦ Φ (t, p)) p = zPartial Φ (t, p) := by
  have hp : HasFDerivAt (fun p : ℝ × ℝ ↦ ((t, p) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) p :=
    (hasFDerivAt_const t p).prodMk (hasFDerivAt_id p)
  have h := ((hΦ (t, p)).hasFDerivAt.comp p hp).fderiv
  simp only [zDeriv, zPartial]
  change fderiv ℝ (Φ ∘ fun p : ℝ × ℝ ↦ ((t, p) : ℝ × (ℝ × ℝ))) p (0, 1) = _
  rw [h]
  rfl

/-- The time derivative along a slice in time is the time partial derivative. -/
theorem hasDerivAt_slice_time (hΦ : Differentiable ℝ Φ) (t : ℝ) (p : ℝ × ℝ) :
    HasDerivAt (fun t ↦ Φ (t, p)) (tPartial Φ (t, p)) t := by
  have hp : HasDerivAt (fun t : ℝ ↦ ((t, p) : ℝ × (ℝ × ℝ))) (1, (0, 0)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t p)
  exact (hΦ (t, p)).hasFDerivAt.comp_hasDerivAt t hp

/-- Iterated `s`-derivatives of a slice are the slices of the iterated `s`-derivatives. -/
theorem iterate_sDeriv_slice (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (t : ℝ) (l : ℕ) :
    sDeriv^[l] (fun p ↦ Φ (t, p)) = fun p ↦ (sPartial^[l] Φ) (t, p) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext p
    exact sDeriv_slice ((contDiff_iterate_sPartial hΦ l).differentiable (by simp)) t p

/-- Iterated `z`-derivatives of a slice are the slices of the iterated `z`-derivatives. -/
theorem iterate_zDeriv_slice (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (t : ℝ) (j : ℕ) :
    zDeriv^[j] (fun p ↦ Φ (t, p)) = fun p ↦ (zPartial^[j] Φ) (t, p) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext p
    exact zDeriv_slice ((contDiff_iterate_zPartial hΦ j).differentiable (by simp)) t p

/-- For smooth `f`, the derivative of `q ↦ Df(q) v` in the direction `w` is `D²f(q) w v`. -/
private theorem fderiv_fderiv_apply {f : ℝ × (ℝ × ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (q v w : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (fun q ↦ fderiv ℝ f q v) q w = fderiv ℝ (fderiv ℝ f) q w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) q :=
    ((hf.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero) q
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- **Mixed partial derivatives commute**: `∂_s ∂_t Φ = ∂_t ∂_s Φ` for smooth `Φ`. -/
theorem sPartial_tPartial (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    sPartial (tPartial Φ) = tPartial (sPartial Φ) := by
  funext q
  change fderiv ℝ (fun q ↦ fderiv ℝ Φ q (1, (0, 0))) q (0, (1, 0)) =
    fderiv ℝ (fun q ↦ fderiv ℝ Φ q (0, (1, 0))) q (1, (0, 0))
  rw [fderiv_fderiv_apply hΦ, fderiv_fderiv_apply hΦ]
  exact (hΦ.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- Iterated `s`-derivatives commute with the time derivative. -/
theorem iterate_sPartial_tPartial (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (l : ℕ) :
    sPartial^[l] (tPartial Φ) = tPartial (sPartial^[l] Φ) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      sPartial_tPartial (contDiff_iterate_sPartial hΦ l)]

/-! ### Periodicity and vanishing for large times -/

/-- `Φ` is `L`-periodic in `z`. -/
def IsZPeriodic (L : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ) : Prop :=
  ∀ t s z, Φ (t, (s, z + L)) = Φ (t, (s, z))

/-- `Φ` vanishes for `|t| > R`. -/
def VanishesBeyond (R : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ) : Prop :=
  ∀ q : ℝ × (ℝ × ℝ), R < |q.1| → Φ q = 0

/-- The derivative of a profile `L`-periodic in `z` is `L`-periodic in `z`. -/
private theorem fderiv_add_zPeriod {L : ℝ} (hper : IsZPeriodic L Φ) (q : ℝ × (ℝ × ℝ)) :
    fderiv ℝ Φ (q + (0, (0, L))) = fderiv ℝ Φ q := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext q'
  have : q' + ((0 : ℝ), ((0 : ℝ), L)) = (q'.1, (q'.2.1, q'.2.2 + L)) := by
    ext <;> simp
  rw [this, hper]

/-- The derivative of a profile `L`-periodic in `z` takes the same value at `(t, s, z + L)` and at
`(t, s, z)`. -/
private theorem fderiv_zPeriod {L : ℝ} (hper : IsZPeriodic L Φ) (t s z : ℝ) :
    fderiv ℝ Φ (t, (s, z + L)) = fderiv ℝ Φ (t, (s, z)) := by
  have := fderiv_add_zPeriod hper (t, (s, z))
  rwa [show ((t, (s, z)) : ℝ × (ℝ × ℝ)) + (0, (0, L)) = (t, (s, z + L)) by ext <;> simp]
    at this

/-- The partial derivatives of a periodic function are periodic. -/
theorem IsZPeriodic.tPartial {L : ℝ} (hper : IsZPeriodic L Φ) : IsZPeriodic L (tPartial Φ) :=
  fun t s z ↦ by simp only [Euler.Cylinder.tPartial, fderiv_zPeriod hper]

/-- The partial derivatives of a periodic function are periodic. -/
theorem IsZPeriodic.sPartial {L : ℝ} (hper : IsZPeriodic L Φ) : IsZPeriodic L (sPartial Φ) :=
  fun t s z ↦ by simp only [Euler.Cylinder.sPartial, fderiv_zPeriod hper]

/-- The partial derivatives of a periodic function are periodic. -/
theorem IsZPeriodic.zPartial {L : ℝ} (hper : IsZPeriodic L Φ) : IsZPeriodic L (zPartial Φ) :=
  fun t s z ↦ by simp only [Euler.Cylinder.zPartial, fderiv_zPeriod hper]

/-- Iterated partial derivatives of a periodic function are periodic. -/
theorem IsZPeriodic.iterate {L : ℝ} (hper : IsZPeriodic L Φ) (a l j : ℕ) :
    IsZPeriodic L (Euler.Cylinder.zPartial^[j] (Euler.Cylinder.sPartial^[l]
      (Euler.Cylinder.tPartial^[a] Φ))) := by
  have ha : ∀ a, IsZPeriodic L (Euler.Cylinder.tPartial^[a] Φ) := by
    intro a
    induction a with
    | zero => exact hper
    | succ a ih => rw [Function.iterate_succ_apply']; exact ih.tPartial
  have hl : ∀ l, IsZPeriodic L (Euler.Cylinder.sPartial^[l]
      (Euler.Cylinder.tPartial^[a] Φ)) := by
    intro l
    induction l with
    | zero => exact ha a
    | succ l ih => rw [Function.iterate_succ_apply']; exact ih.sPartial
  induction j with
  | zero => exact hl l
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih.zPartial

/-- The derivative of a profile vanishing for `|t| > R` vanishes for `|t| > R`. -/
private theorem fderiv_eq_zero_of_vanishesBeyond {R : ℝ} (hR : VanishesBeyond R Φ)
    {q : ℝ × (ℝ × ℝ)} (hq : R < |q.1|) : fderiv ℝ Φ q = 0 := by
  have hopen : IsOpen {q : ℝ × (ℝ × ℝ) | R < |q.1|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : Φ =ᶠ[𝓝 q] fun _ ↦ 0 := by
    filter_upwards [hopen.mem_nhds hq] with q' hq'
    exact hR q' hq'
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

/-- The partial derivatives of a function vanishing for `|t| > R` vanish there. -/
theorem VanishesBeyond.tPartial {R : ℝ} (hR : VanishesBeyond R Φ) :
    VanishesBeyond R (tPartial Φ) := fun q hq ↦ by
  simp [Euler.Cylinder.tPartial, fderiv_eq_zero_of_vanishesBeyond hR hq]

/-- The partial derivatives of a function vanishing for `|t| > R` vanish there. -/
theorem VanishesBeyond.sPartial {R : ℝ} (hR : VanishesBeyond R Φ) :
    VanishesBeyond R (sPartial Φ) := fun q hq ↦ by
  simp [Euler.Cylinder.sPartial, fderiv_eq_zero_of_vanishesBeyond hR hq]

/-- The partial derivatives of a function vanishing for `|t| > R` vanish there. -/
theorem VanishesBeyond.zPartial {R : ℝ} (hR : VanishesBeyond R Φ) :
    VanishesBeyond R (zPartial Φ) := fun q hq ↦ by
  simp [Euler.Cylinder.zPartial, fderiv_eq_zero_of_vanishesBeyond hR hq]

/-- Iterated partial derivatives of a function vanishing for `|t| > R` vanish there. -/
theorem VanishesBeyond.iterate {R : ℝ} (hR : VanishesBeyond R Φ) (a l j : ℕ) :
    VanishesBeyond R (Euler.Cylinder.zPartial^[j] (Euler.Cylinder.sPartial^[l]
      (Euler.Cylinder.tPartial^[a] Φ))) := by
  have ha : ∀ a, VanishesBeyond R (Euler.Cylinder.tPartial^[a] Φ) := by
    intro a
    induction a with
    | zero => exact hR
    | succ a ih => rw [Function.iterate_succ_apply']; exact ih.tPartial
  have hl : ∀ l, VanishesBeyond R (Euler.Cylinder.sPartial^[l]
      (Euler.Cylinder.tPartial^[a] Φ)) := by
    intro l
    induction l with
    | zero => exact ha a
    | succ l ih => rw [Function.iterate_succ_apply']; exact ih.sPartial
  induction j with
  | zero => exact hl l
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih.zPartial

/-- A continuous function vanishing for `|t| > R` is bounded on `ℝ × (K × [0, L])` for a compact
`K`. -/
theorem exists_bound_of_vanishesBeyond {R : ℝ} {f : ℝ × (ℝ × ℝ) → ℝ} (hf : Continuous f)
    (hR : VanishesBeyond R f) {K : Set ℝ} (hK : IsCompact K) (L : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ t, ∀ s ∈ K, ∀ z ∈ Icc 0 L, |f (t, (s, z))| ≤ M := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -R) (b := R)).prod (hK.prod isCompact_Icc)
    |>.exists_bound_of_continuousOn (hf.continuousOn (s := Icc (-R) R ×ˢ (K ×ˢ Icc 0 L)))
  refine ⟨max M₀ 0, le_max_right _ _, fun t s hs z hz ↦ ?_⟩
  by_cases ht : |t| ≤ R
  · have := hM₀ (t, (s, z)) ⟨abs_le.1 ht, hs, hz⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [hR (t, (s, z)) (not_le.1 ht), abs_zero]
    exact le_max_right _ _

/-! ### Decay of the coefficients, uniformly in time -/

/-- **Decay of one coefficient.** If `|∂_z^{2N} G(s, z)| ≤ M` on one period, the `k`-th sine
coefficient of `z ↦ G(s, z)` is at most `2^N (L/2π)^{2N} 2M / (1 + k)^N`. -/
theorem abs_sineCoeff_le_of_iterate_zDeriv_le {L : ℝ} (hL : 0 < L) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hper : ∀ s z, G (s, z + L) = G (s, z)) (N : ℕ) (s : ℝ)
    {M : ℝ} (hM : ∀ z ∈ Icc 0 L, |(zDeriv^[2 * N] G) (s, z)| ≤ M) (k : ℕ) :
    |sineCoeff L (fun z ↦ G (s, z)) k| ≤
      2 ^ N * (L / (2 * π)) ^ (2 * N) * (2 * M) / (1 + (k : ℝ)) ^ N := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hL.le⟩)
  have hC : 0 ≤ 2 ^ N * (L / (2 * π)) ^ (2 * N) * (2 * M) := by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [sineCoeff_zero, abs_zero, Nat.cast_zero, add_zero, one_pow, div_one]
    exact hC
  set c := sineCoeff L (fun z ↦ G (s, z)) k
  set ν : ℝ := 2 * π * k / L
  have hFb : |sineCoeff L (fun z ↦ (zDeriv^[2 * N] G) (s, z)) k| ≤ 2 * M :=
    abs_sineCoeff_le hL hM k
  have heq : sineCoeff L (fun z ↦ (zDeriv^[2 * N] G) (s, z)) k = (-ν ^ 2) ^ N * c :=
    sineCoeff_iterate_zDeriv hL hG hper k N s
  rw [heq, abs_mul, abs_pow, abs_neg, abs_of_nonneg (sq_nonneg ν)] at hFb
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < 1 + k := by linarith
  rw [le_div_iff₀ (pow_pos hkpos N)]
  have h1 : (1 + (k : ℝ)) ^ N ≤ 2 ^ N * (k : ℝ) ^ (2 * N) := by
    calc (1 + (k : ℝ)) ^ N ≤ (2 * k) ^ N := pow_le_pow_left₀ hkpos.le (by linarith) N
      _ = 2 ^ N * (k : ℝ) ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (k : ℝ) ^ (2 * N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ hk1 (by omega)
  have hν : (ν ^ 2) ^ N = (2 * π / L) ^ (2 * N) * (k : ℝ) ^ (2 * N) := by
    rw [← pow_mul, ← mul_pow]
    congr 1
    simp only [ν]
    ring
  have hLpi : (L / (2 * π)) ^ (2 * N) * (2 * π / L) ^ (2 * N) = 1 := by
    rw [← mul_pow]
    rw [show L / (2 * π) * (2 * π / L) = 1 by field_simp]
    exact one_pow _
  calc |c| * (1 + (k : ℝ)) ^ N ≤ |c| * (2 ^ N * (k : ℝ) ^ (2 * N)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = 2 ^ N * (L / (2 * π)) ^ (2 * N) * ((ν ^ 2) ^ N * |c|) := by
        rw [hν]
        linear_combination (-(2 ^ N * (k : ℝ) ^ (2 * N) * |c|)) * hLpi
    _ ≤ 2 ^ N * (L / (2 * π)) ^ (2 * N) * (2 * M) :=
        mul_le_mul_of_nonneg_left hFb (by positivity)

/-- **Decay of the coefficient modes, uniformly in time.** For a smooth `Φ(t, (s, z))`,
`L`-periodic in `z` and vanishing for `|t| > R`, every `s`-derivative of the coefficient modes of
the slices decays faster than any power of `k`, uniformly in `t` and in `s` in a compact set. -/
theorem exists_abs_iteratedDeriv_coefficientMode_le {L R : ℝ} (hL : 0 < L)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hper : IsZPeriodic L Φ) (hR : VanishesBeyond R Φ)
    (l N : ℕ) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ (k : ℕ) (t : ℝ), ∀ s ∈ K,
      |iteratedDeriv l (coefficientMode L (fun p ↦ Φ (t, p)) k) s| ≤ C / (1 + (k : ℝ)) ^ N := by
  set f := zPartial^[2 * N] (sPartial^[l] (tPartial^[0] Φ))
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_iterate_zPartial (contDiff_iterate_sPartial (contDiff_iterate_tPartial hΦ 0) l) _
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_vanishesBeyond hf.continuous (hR.iterate 0 l (2 * N))
    hK L
  refine ⟨2 ^ N * (L / (2 * π)) ^ (2 * N) * (2 * M), by positivity, fun k t s hs ↦ ?_⟩
  set G : ℝ × ℝ → ℝ := fun p ↦ (sPartial^[l] Φ) (t, p)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := contDiff_slice (contDiff_iterate_sPartial hΦ l) t
  have hperG : ∀ s z, G (s, z + L) = G (s, z) := fun s z ↦ by
    have := hper.iterate 0 l 0 t s z
    simpa using this
  have hcoef : iteratedDeriv l (coefficientMode L (fun p ↦ Φ (t, p)) k) =
      fun s ↦ sineCoeff L (fun z ↦ G (s, z)) (k + 1) := by
    have h := iteratedDeriv_sineCoeff_param (L := L) (contDiff_slice hΦ t) (k + 1) l
    rw [iterate_sDeriv_slice hΦ t l] at h
    exact h
  rw [hcoef]
  have hzG : zDeriv^[2 * N] G = fun p ↦ f (t, p) := by
    have := iterate_zDeriv_slice (contDiff_iterate_sPartial hΦ l) t (2 * N)
    simpa [f, G] using this
  have hb := abs_sineCoeff_le_of_iterate_zDeriv_le hL hG hperG N s (M := M)
    (fun z hz ↦ by rw [hzG]; exact hM t s hs z hz) (k + 1)
  refine hb.trans ?_
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  linarith

/-! ### Linearity of the mode operators -/

/-- The sine coefficients are linear in the function. -/
theorem sineCoeff_linear {L a b : ℝ} {g₁ g₂ : ℝ → ℝ} (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) (k : ℕ) :
    sineCoeff L (fun z ↦ a * g₁ z + b * g₂ z) k = a * sineCoeff L g₁ k + b * sineCoeff L g₂ k := by
  have hs : Continuous fun z ↦ Real.sin (2 * π * k / L * z) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have h1 : IntervalIntegrable (fun z ↦ g₁ z * Real.sin (2 * π * k / L * z))
      MeasureTheory.volume 0 L := (hg₁.mul hs).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun z ↦ g₂ z * Real.sin (2 * π * k / L * z))
      MeasureTheory.volume 0 L := (hg₂.mul hs).intervalIntegrable _ _
  have heq : (fun z ↦ (a * g₁ z + b * g₂ z) * Real.sin (2 * π * k / L * z)) =
      fun z ↦ a * (g₁ z * Real.sin (2 * π * k / L * z)) +
        b * (g₂ z * Real.sin (2 * π * k / L * z)) := by
    funext z
    ring
  simp only [sineCoeff]
  rw [heq, intervalIntegral.integral_add (h1.const_mul a) (h2.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- The coefficient modes are linear in the source. -/
theorem coefficientMode_linear {L a b : ℝ} {G₁ G₂ : ℝ × ℝ → ℝ} (hG₁ : Continuous G₁)
    (hG₂ : Continuous G₂) (k : ℕ) (s : ℝ) :
    coefficientMode L (fun p ↦ a * G₁ p + b * G₂ p) k s =
      a * coefficientMode L G₁ k s + b * coefficientMode L G₂ k s :=
  sineCoeff_linear (hG₁.comp (continuous_const.prodMk continuous_id))
    (hG₂.comp (continuous_const.prodMk continuous_id)) (k + 1)

/-- The averaged source is linear in the source. -/
theorem modeAverage_linear {μ a b : ℝ} {F₁ F₂ : ℝ → ℝ} (hF₁ : Continuous F₁)
    (hF₂ : Continuous F₂) (σ : ℝ) :
    modeAverage μ (fun s ↦ a * F₁ s + b * F₂ s) σ =
      a * modeAverage μ F₁ σ + b * modeAverage μ F₂ σ := by
  have hf : Continuous fun τ : ℝ ↦ homogeneousMode μ (σ * τ) :=
    (contDiff_homogeneousMode μ).continuous.comp (continuous_const.mul continuous_id)
  have hc (F : ℝ → ℝ) (hF : Continuous F) :
      IntervalIntegrable (fun τ ↦ τ * (homogeneousMode μ (σ * τ) * F (σ * τ)))
        MeasureTheory.volume 0 1 :=
    (continuous_id.mul (hf.mul (hF.comp (continuous_const.mul continuous_id)))).intervalIntegrable
      _ _
  have heq : (fun τ ↦ τ * (homogeneousMode μ (σ * τ) * (a * F₁ (σ * τ) + b * F₂ (σ * τ)))) =
      fun τ ↦ a * (τ * (homogeneousMode μ (σ * τ) * F₁ (σ * τ))) +
        b * (τ * (homogeneousMode μ (σ * τ) * F₂ (σ * τ))) := by
    funext τ
    ring
  simp only [modeAverage]
  rw [heq, intervalIntegral.integral_add ((hc F₁ hF₁).const_mul a) ((hc F₂ hF₂).const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The quotient of reduction of order is linear in the source. -/
theorem modeQuotient_linear {μ a b : ℝ} {F₁ F₂ : ℝ → ℝ} (hF₁ : Continuous F₁)
    (hF₂ : Continuous F₂) (σ : ℝ) :
    modeQuotient μ (fun s ↦ a * F₁ s + b * F₂ s) σ =
      a * modeQuotient μ F₁ σ + b * modeQuotient μ F₂ σ := by
  simp only [modeQuotient, modeAverage_linear hF₁ hF₂]
  ring

/-- The particular mode is linear in the source on the mode domain. -/
theorem particularMode_linear {μ a b : ℝ} (hμ : 0 < μ) {F₁ F₂ : ℝ → ℝ}
    (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hF₂ : ContDiff ℝ (⊤ : ℕ∞) F₂) {s : ℝ}
    (hs : s ∈ Ioi (-4 / μ ^ 2)) :
    particularMode μ (fun s ↦ a * F₁ s + b * F₂ s) s =
      a * particularMode μ F₁ s + b * particularMode μ F₂ s := by
  have hsub := uIcc_subset_modeDomain hμ hs
  have h1 := ((contDiffOn_modeQuotient hμ hF₁).continuousOn.mono hsub).intervalIntegrable
    (μ := MeasureTheory.volume)
  have h2 := ((contDiffOn_modeQuotient hμ hF₂).continuousOn.mono hsub).intervalIntegrable
    (μ := MeasureTheory.volume)
  have heq : (fun σ ↦ modeQuotient μ (fun s ↦ a * F₁ s + b * F₂ s) σ) =
      fun σ ↦ a * modeQuotient μ F₁ σ + b * modeQuotient μ F₂ σ :=
    funext (modeQuotient_linear hF₁.continuous hF₂.continuous)
  simp only [particularMode]
  rw [heq, intervalIntegral.integral_add (h1.const_mul a) (h2.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- The mode solution is linear in the source on the mode domain. -/
theorem modeSolution_linear {μ a b : ℝ} (hμ : 0 < μ) {F₁ F₂ : ℝ → ℝ}
    (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hF₂ : ContDiff ℝ (⊤ : ℕ∞) F₂) {s : ℝ}
    (hs : s ∈ Ioi (-4 / μ ^ 2)) :
    modeSolution μ (fun s ↦ a * F₁ s + b * F₂ s) s =
      a * modeSolution μ F₁ s + b * modeSolution μ F₂ s := by
  have h1 : (1 : ℝ) ∈ Ioi (-4 / μ ^ 2) := by
    simp only [mem_Ioi]
    have : 0 < 4 / μ ^ 2 := by positivity
    rw [neg_div]
    linarith
  simp only [modeSolution, particularMode_linear hμ hF₁ hF₂ hs, particularMode_linear hμ hF₁ hF₂ h1]
  ring

/-- **The cut-off modes are linear in the source.** -/
theorem modeTerm_linear {μ a b : ℝ} (hμ : 0 < μ) {F₁ F₂ : ℝ → ℝ}
    (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hF₂ : ContDiff ℝ (⊤ : ℕ∞) F₂) :
    modeTerm μ (fun s ↦ a * F₁ s + b * F₂ s) =
      fun s ↦ a * modeTerm μ F₁ s + b * modeTerm μ F₂ s := by
  funext s
  by_cases hs : s ∈ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2)
  · simp only [modeTerm, modeSolution_linear hμ hF₁ hF₂ (modeInterval_subset hμ hs)]
    ring
  · simp [modeTerm, modeCutoff_of_notMem hμ hs]

/-- The cut-off mode of the `k`-th coefficient of a source `G(s, z)`. -/
def sourceMode (L : ℝ) (G : ℝ × ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  modeTerm (modeFrequency L k) (coefficientMode L G k)

/-- The source modes of smooth sources are smooth. -/
theorem contDiff_sourceMode {L : ℝ} (hL : 0 < L) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (sourceMode L G k) :=
  contDiff_modeTerm (modeFrequency_pos hL k) (contDiff_coefficientMode hG k)

/-- **The iterated derivatives of the source modes are linear in the source.** -/
theorem iteratedDeriv_sourceMode_linear {L a b : ℝ} (hL : 0 < L) {G₁ G₂ : ℝ × ℝ → ℝ}
    (hG₁ : ContDiff ℝ (⊤ : ℕ∞) G₁) (hG₂ : ContDiff ℝ (⊤ : ℕ∞) G₂) (k j : ℕ) (s : ℝ) :
    iteratedDeriv j (sourceMode L (fun p ↦ a * G₁ p + b * G₂ p) k) s =
      a * iteratedDeriv j (sourceMode L G₁ k) s + b * iteratedDeriv j (sourceMode L G₂ k) s := by
  have hμ := modeFrequency_pos hL k
  have hc : coefficientMode L (fun p ↦ a * G₁ p + b * G₂ p) k =
      fun s ↦ a * coefficientMode L G₁ k s + b * coefficientMode L G₂ k s :=
    funext (coefficientMode_linear hG₁.continuous hG₂.continuous k)
  have hm : sourceMode L (fun p ↦ a * G₁ p + b * G₂ p) k =
      fun s ↦ a * sourceMode L G₁ k s + b * sourceMode L G₂ k s := by
    simp only [sourceMode, hc]
    exact modeTerm_linear hμ (contDiff_coefficientMode hG₁ k) (contDiff_coefficientMode hG₂ k)
  have h1 : ContDiffAt ℝ j (sourceMode L G₁ k) s :=
    ((contDiff_sourceMode hL hG₁ k).of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ j (sourceMode L G₂ k) s :=
    ((contDiff_sourceMode hL hG₂ k).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [hm, iteratedDeriv_fun_add (contDiffAt_const.mul h1) (contDiffAt_const.mul h2),
    iteratedDeriv_const_mul a h1, iteratedDeriv_const_mul b h2]

/-! ### Bounds of the source modes -/

/-- The constants `Dⱼ` of the derivative bounds of the cut-off modes
(`exists_abs_iteratedDeriv_modeTerm_le`). -/
def modeConst : ℕ → ℝ :=
  exists_abs_iteratedDeriv_modeTerm_le.choose

/-- The constants of the mode bounds are nonnegative. -/
theorem modeConst_nonneg (j : ℕ) : 0 ≤ modeConst j :=
  exists_abs_iteratedDeriv_modeTerm_le.choose_spec.1 j

/-- The derivative bounds of the cut-off modes with the constants `modeConst`. -/
theorem abs_iteratedDeriv_modeTerm_le_modeConst {μ : ℝ} (hμ : 0 < μ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (j : ℕ) (M : ℕ → ℝ)
    (hM : ∀ i ≤ j, ∀ s ∈ Icc (-2 / μ ^ 2) (1 + 2 / μ ^ 2), |iteratedDeriv i F s| ≤ M i)
    (s : ℝ) :
    |iteratedDeriv j (modeTerm μ F) s| ≤
      3 * modeConst j * (1 + μ ^ 2) ^ j * (∑ l ∈ Finset.range (j + 1), M l) / μ ^ 2 :=
  exists_abs_iteratedDeriv_modeTerm_le.choose_spec.2 hμ hF j M hM s

/-- The collar `[-2/c², 1 + 2/c²]`, `c = 2π/L`, containing the collars of all the modes. -/
def modeCollar (L : ℝ) : Set ℝ :=
  Icc (-2 / (2 * π / L) ^ 2) (1 + 2 / (2 * π / L) ^ 2)

/-- The mode frequency is `c (1 + k)` with `c = 2π/L`. -/
theorem modeFrequency_eq (L : ℝ) (k : ℕ) : modeFrequency L k = 2 * π / L * (1 + k) := by
  simp only [modeFrequency]
  ring

/-- The collar of every mode lies in `modeCollar L`. -/
theorem collar_subset_modeCollar {L : ℝ} (k : ℕ) :
    Icc (-2 / modeFrequency L k ^ 2) (1 + 2 / modeFrequency L k ^ 2) ⊆ modeCollar L := by
  set c : ℝ := 2 * π / L
  have hμ : modeFrequency L k = c * (1 + k) := modeFrequency_eq L k
  have hle : 2 / modeFrequency L k ^ 2 ≤ 2 / c ^ 2 := by
    rcases eq_or_ne c 0 with hc | hc
    · simp [hμ, hc]
    have hc2 : 0 < c ^ 2 := lt_of_le_of_ne (sq_nonneg c) (pow_ne_zero 2 hc).symm
    refine div_le_div_of_nonneg_left (by norm_num) hc2 ?_
    rw [hμ, mul_pow]
    exact le_mul_of_one_le_right hc2.le
      (one_le_pow₀ (by have := (k.cast_nonneg : (0 : ℝ) ≤ k); linarith))
  intro s hs
  constructor
  · have : -2 / c ^ 2 ≤ -2 / modeFrequency L k ^ 2 := by
      rw [neg_div, neg_div]
      linarith
    exact this.trans hs.1
  · linarith [hs.2]

/-- The mode collar is compact. -/
theorem isCompact_modeCollar (L : ℝ) : IsCompact (modeCollar L) :=
  isCompact_Icc

/-- **Source modes are bounded by their sources.** If the `s`-derivatives of order `≤ j` of `G` are
at most `m` on `modeCollar L × [0, L]`, the `j`-th derivative of the `k`-th source mode is at most
`3 Dⱼ (1 + μ²)^j (j + 1) 2m / μ²`, `μ = μ_k`. -/
theorem abs_iteratedDeriv_sourceMode_le {L : ℝ} (hL : 0 < L) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (k j : ℕ) {m : ℝ}
    (hm : ∀ l ≤ j, ∀ s ∈ modeCollar L, ∀ z ∈ Icc 0 L, |(sDeriv^[l] G) (s, z)| ≤ m) (s : ℝ) :
    |iteratedDeriv j (sourceMode L G k) s| ≤
      3 * modeConst j * (1 + modeFrequency L k ^ 2) ^ j * ((j + 1) * (2 * m)) /
        modeFrequency L k ^ 2 := by
  have h := abs_iteratedDeriv_modeTerm_le_modeConst (modeFrequency_pos hL k)
    (contDiff_coefficientMode hG k) j (fun _ ↦ 2 * m) (fun i hi s' hs' ↦ by
      have hc := iteratedDeriv_sineCoeff_param (L := L) hG (k + 1) i
      have : iteratedDeriv i (coefficientMode L G k) s' =
          sineCoeff L (fun z ↦ (sDeriv^[i] G) (s', z)) (k + 1) := congrFun hc s'
      rw [this]
      exact abs_sineCoeff_le hL (fun z hz ↦ hm i hi s' (collar_subset_modeCollar k hs') z hz)
        _) s
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  push_cast at h
  exact h

end

end Euler.Cylinder
