/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.SmoothData
public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Sine coefficients of periodic functions of any period

For a period `L > 0` the `k`-th sine coefficient of `g` is
`(2/L) ∫₀^L g(z) sin(2πkz/L) dz` (`sineCoeff`). Two integrations by parts, whose boundary
terms cancel by periodicity, give `b_k(g'') = -(2πk/L)² b_k(g)`
(`sineCoeff_iteratedDeriv_two`), and an odd `L`-periodic `C²` function is the sum of its sine
series (`hasSum_sineCoeff_mul_sin`, by rescaling the period-two reconstruction of
`SmoothData`).

For a jointly smooth `Ω(s, z)`, `L`-periodic in `z`, the coefficients of `z ↦ Ω(s, z)` are
smooth in `s` (`contDiff_sineCoeff_param`); their `s`-derivatives are the coefficients of the
`s`-derivatives of `Ω`, so on compact sets of `s` every derivative decays faster than any power
of `k` (`exists_abs_iteratedDeriv_sineCoeff_le`).

## Main definitions

* `sineCoeff`: the sine coefficients with period `L`.
* `sDeriv`, `zDeriv`: the partial derivatives of a function on `ℝ × ℝ`.

## Main results

* `abs_sineCoeff_le`, `sineCoeff_iteratedDeriv_two`, `hasSum_sineCoeff_mul_sin`.
* `contDiff_sineCoeff_param`, `iteratedDeriv_sineCoeff_param`,
  `exists_abs_iteratedDeriv_sineCoeff_le`.
-/

@[expose] public section

namespace PDE.Analysis.Fourier.SineSeries

open MeasureTheory Set
open scoped Real Topology

set_option linter.missingDocs true

noncomputable section

/-- The `k`-th sine coefficient `(2/L) ∫₀^L g(z) sin(2πkz/L) dz` of `g` for the period `L`. -/
def sineCoeff (L : ℝ) (g : ℝ → ℝ) (k : ℕ) : ℝ :=
  2 / L * ∫ z in (0 : ℝ)..L, g z * Real.sin (2 * π * k / L * z)

/-- The sine coefficients are bounded by twice a bound of the function on one period. -/
theorem abs_sineCoeff_le {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} {M : ℝ}
    (hM : ∀ z ∈ Set.Icc 0 L, |g z| ≤ M) (k : ℕ) : |sineCoeff L g k| ≤ 2 * M := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := L)
    (f := fun z ↦ g z * Real.sin (2 * π * k / L * z)) (C := M) (fun z hz ↦ by
      rw [uIoc_of_le hL.le] at hz
      rw [Real.norm_eq_abs, abs_mul]
      calc |g z| * |Real.sin (2 * π * k / L * z)| ≤ M * 1 :=
            mul_le_mul (hM z ⟨hz.1.le, hz.2⟩) (Real.abs_sin_le_one _) (abs_nonneg _)
              ((abs_nonneg _).trans (hM z ⟨hz.1.le, hz.2⟩))
        _ = M := mul_one M)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hL] at h
  rw [sineCoeff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
  calc 2 / L * |∫ z in (0 : ℝ)..L, g z * Real.sin (2 * π * k / L * z)| ≤ 2 / L * (M * L) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * M := by field_simp

/-- **Two integrations by parts.** For an `L`-periodic `C²` function,
`b_k(g'') = -(2πk/L)² b_k(g)`. -/
theorem sineCoeff_iteratedDeriv_two {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hper : Function.Periodic g L) (k : ℕ) :
    sineCoeff L (iteratedDeriv 2 g) k = -(2 * π * k / L) ^ 2 * sineCoeff L g k := by
  set ν : ℝ := 2 * π * k / L
  have hνL : ν * L = (2 * k : ℕ) * π := by
    simp only [ν]
    push_cast
    field_simp
  have hsinL : Real.sin (ν * L) = 0 := by rw [hνL]; exact Real.sin_nat_mul_pi _
  have hcosL : Real.cos (ν * L) = 1 := by
    rw [show ν * L = (k : ℝ) * (2 * π) by simp only [ν]; field_simp]
    exact Real.cos_nat_mul_two_pi k
  have hgL : g L = g 0 := by simpa using hper 0
  have hd1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hd2 : Differentiable ℝ (deriv g) := hg1.differentiable (by norm_num)
  have hsin : ∀ x, HasDerivAt (fun x ↦ Real.sin (ν * x)) (Real.cos (ν * x) * ν) x := by
    intro x
    simpa using ((hasDerivAt_id x).const_mul ν).sin
  have hcos : ∀ x, HasDerivAt (fun x ↦ Real.cos (ν * x)) (-Real.sin (ν * x) * ν) x := by
    intro x
    simpa using ((hasDerivAt_id x).const_mul ν).cos
  have hc2 : Continuous (deriv (deriv g)) := hg1.continuous_deriv le_rfl
  -- First integration by parts.
  have h1 : (∫ x in (0 : ℝ)..L, Real.sin (ν * x) * deriv (deriv g) x) =
      -(ν * ∫ x in (0 : ℝ)..L, Real.cos (ν * x) * deriv g x) := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ ↦ hsin x)
      (fun x _ ↦ (hd2 x).hasDerivAt) (by apply Continuous.intervalIntegrable; fun_prop)
      (hc2.intervalIntegrable _ _)]
    rw [hsinL, mul_zero, Real.sin_zero]
    simp only [zero_mul, sub_zero, zero_sub]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    congr 1
    funext x
    ring
  -- Second integration by parts.
  have h2 : (∫ x in (0 : ℝ)..L, Real.cos (ν * x) * deriv g x) =
      ν * ∫ x in (0 : ℝ)..L, Real.sin (ν * x) * g x := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ ↦ hcos x)
      (fun x _ ↦ (hd1 x).hasDerivAt) (by apply Continuous.intervalIntegrable; fun_prop)
      ((hg.continuous_deriv (by norm_num)).intervalIntegrable _ _)]
    rw [hcosL, mul_zero, Real.cos_zero, hgL, ← intervalIntegral.integral_const_mul]
    simp only [one_mul, sub_self, zero_sub]
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  unfold sineCoeff
  have hiter : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter]
  have e1 : (∫ z in (0 : ℝ)..L, deriv (deriv g) z * Real.sin (ν * z)) =
      ∫ x in (0 : ℝ)..L, Real.sin (ν * x) * deriv (deriv g) x := by
    congr 1; funext x; ring
  have e2 : (∫ z in (0 : ℝ)..L, g z * Real.sin (ν * z)) =
      ∫ x in (0 : ℝ)..L, Real.sin (ν * x) * g x := by
    congr 1; funext x; ring
  rw [e1, e2, h1, h2]
  ring

/-- The sine coefficients of `g` with period `L` are the period-two coefficients of
`x ↦ g(L x / 2)`. -/
theorem sineCoeff_succ_eq_periodicCoefficient {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : Continuous g) (hper : Function.Periodic g L) (hodd : ∀ z, g (-z) = -g z) (n : ℕ) :
    sineCoeff L g (n + 1) =
      periodicCoefficient (fun x ↦ g (L / 2 * x)) (hg.comp (continuous_const.mul continuous_id))
        (fun x ↦ by simp only; rw [mul_add, show L / 2 * 2 = L by ring, hper]) n := by
  set g₂ : ℝ → ℝ := fun x ↦ g (L / 2 * x)
  have hg₂ : Continuous g₂ := hg.comp (continuous_const.mul continuous_id)
  have hper₂ : Function.Periodic g₂ 2 := fun x ↦ by
    simp only [g₂]; rw [mul_add, show L / 2 * 2 = L by ring, hper]
  have hodd₂ : ∀ x, g₂ (-x) = -g₂ x := fun x ↦ by simp only [g₂, mul_neg, hodd]
  rw [periodicCoefficient_eq_integral g₂ hg₂ hper₂ hodd₂ n]
  set h : ℝ → ℝ := fun x ↦ g₂ x * PDE.Representations.intervalDirichletSineMode n x
  have hh : Continuous h :=
    hg₂.mul (PDE.Representations.contDiff_intervalDirichletSineMode (k := 0) n).continuous
  have hhper : Function.Periodic h 2 := by
    intro x
    simp only [h, PDE.Representations.intervalDirichletSineMode, hper₂ x]
    congr 1
    rw [show (n.succ : ℝ) * π * (x + 2) = (n.succ : ℝ) * π * x + n.succ * (2 * π) by ring,
      Real.sin_add_nat_mul_two_pi]
  have heven : ∀ x, h (-x) = h x := by
    intro x
    simp [h, PDE.Representations.intervalDirichletSineMode, hodd₂, Real.sin_neg]
  -- Change of variables `z = L x / 2`.
  have hsub : (∫ z in (0 : ℝ)..L, g z * Real.sin (2 * π * ((n + 1 : ℕ) : ℝ) / L * z)) =
      L / 2 * ∫ x in (0 : ℝ)..2, h x := by
    have hc : L / 2 ≠ 0 := by positivity
    have := intervalIntegral.integral_comp_mul_left
      (fun z ↦ g z * Real.sin (2 * π * ((n + 1 : ℕ) : ℝ) / L * z)) hc (a := 0) (b := 2)
    simp only [mul_zero, show L / 2 * 2 = L by ring, smul_eq_mul] at this
    rw [eq_inv_mul_iff_mul_eq₀ hc] at this
    rw [← this]
    congr 1
    congr 1
    funext x
    simp only [h, g₂, PDE.Representations.intervalDirichletSineMode]
    congr 2
    push_cast
    field_simp
  have hshift : (∫ x in (0 : ℝ)..2, h x) = ∫ x in (-1 : ℝ)..1, h x := by
    have := hhper.intervalIntegral_add_eq 0 (-1)
    rw [show (-1 : ℝ) + 2 = 1 by norm_num, zero_add] at this
    exact this
  have hsplit : (∫ x in (-1 : ℝ)..1, h x) = 2 * ∫ x in (0 : ℝ)..1, h x := by
    have hneg : (∫ x in (-1 : ℝ)..0, h x) = ∫ x in (0 : ℝ)..1, h x := by
      have := intervalIntegral.integral_comp_neg (f := h) (a := (0 : ℝ)) (b := 1)
      simpa only [heven, neg_zero] using this.symm
    rw [← intervalIntegral.integral_add_adjacent_intervals (hh.intervalIntegrable (-1) 0)
      (hh.intervalIntegrable 0 1), hneg, two_mul]
  unfold sineCoeff
  rw [hsub, hshift, hsplit]
  field_simp

/-- **Sine series of odd periodic functions.** An odd `L`-periodic `C²` function is the sum of
its sine series `∑ₖ b_k sin(2πkz/L)`; the term `k = 0` vanishes. -/
theorem hasSum_sineCoeff_mul_sin {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hper : Function.Periodic g L) (hodd : ∀ z, g (-z) = -g z) (z : ℝ) :
    HasSum (fun k : ℕ ↦ sineCoeff L g k * Real.sin (2 * π * k / L * z)) (g z) := by
  set g₂ : ℝ → ℝ := fun x ↦ g (L / 2 * x)
  have hg₂ : ContDiff ℝ 2 g₂ := hg.comp (contDiff_const.mul contDiff_id)
  have hper₂ : Function.Periodic g₂ 2 := fun x ↦ by
    simp only [g₂]; rw [mul_add, show L / 2 * 2 = L by ring, hper]
  have hodd₂ : ∀ x, g₂ (-x) = -g₂ x := fun x ↦ by simp only [g₂, mul_neg, hodd]
  have h := hasSum_periodicCoefficient_sineMode g₂ hg₂ hper₂ hodd₂ (2 / L * z)
  have hval : g₂ (2 / L * z) = g z := by
    simp only [g₂]; congr 1; field_simp
  rw [hval] at h
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_div,
    zero_mul, Real.sin_zero, sub_zero]
  convert h using 1
  funext n
  rw [sineCoeff_succ_eq_periodicCoefficient hL hg.continuous hper hodd n]
  congr 1
  simp only [PDE.Representations.intervalDirichletSineMode]
  congr 1
  push_cast
  field_simp

/-! ### Coefficients depending on a parameter -/

/-- The partial derivative `∂_s G` of a function `G(s, z)` on `ℝ × ℝ`. -/
def sDeriv (G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ G p (1, 0)

/-- The partial derivative `∂_z G` of a function `G(s, z)` on `ℝ × ℝ`. -/
def zDeriv (G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ G p (0, 1)

/-- The partial derivative in `s` of a smooth function is smooth. -/
theorem contDiff_sDeriv {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (sDeriv G) :=
  (hG.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- The partial derivative in `z` of a smooth function is smooth. -/
theorem contDiff_zDeriv {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (zDeriv G) :=
  (hG.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- Iterated partial derivatives in `s` of a smooth function are smooth. -/
theorem contDiff_iterate_sDeriv {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sDeriv^[m] G) := by
  induction m with
  | zero => simpa using hG
  | succ m ih => rw [Function.iterate_succ_apply']; exact contDiff_sDeriv ih

/-- Iterated partial derivatives in `z` of a smooth function are smooth. -/
theorem contDiff_iterate_zDeriv {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (zDeriv^[j] G) := by
  induction j with
  | zero => simpa using hG
  | succ j ih => rw [Function.iterate_succ_apply']; exact contDiff_zDeriv ih

/-- The derivative of a function periodic in a fixed direction is periodic. -/
theorem fderiv_add_of_periodic {G : ℝ × ℝ → ℝ} {a : ℝ × ℝ} (hper : ∀ p, G (p + a) = G p)
    (p : ℝ × ℝ) : fderiv ℝ G (p + a) = fderiv ℝ G p := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext q
  exact hper q

/-- The partial derivative in `s` of a function periodic in `z` is periodic in `z`. -/
theorem sDeriv_periodic {G : ℝ × ℝ → ℝ} {L : ℝ} (hper : ∀ s z, G (s, z + L) = G (s, z))
    (s z : ℝ) : sDeriv G (s, z + L) = sDeriv G (s, z) := by
  have h : ∀ p : ℝ × ℝ, G (p + (0, L)) = G p := fun p ↦ by
    have hp : p + (0, L) = (p.1, p.2 + L) := by ext <;> simp
    rw [hp, hper p.1 p.2]
  have := fderiv_add_of_periodic h (s, z)
  simp only [sDeriv]
  rw [show ((s, z + L) : ℝ × ℝ) = (s, z) + (0, L) by simp, this]

/-- The partial derivative in `z` of a function periodic in `z` is periodic in `z`. -/
theorem zDeriv_periodic {G : ℝ × ℝ → ℝ} {L : ℝ} (hper : ∀ s z, G (s, z + L) = G (s, z))
    (s z : ℝ) : zDeriv G (s, z + L) = zDeriv G (s, z) := by
  have h : ∀ p : ℝ × ℝ, G (p + (0, L)) = G p := fun p ↦ by
    have hp : p + (0, L) = (p.1, p.2 + L) := by ext <;> simp
    rw [hp, hper p.1 p.2]
  have := fderiv_add_of_periodic h (s, z)
  simp only [zDeriv]
  rw [show ((s, z + L) : ℝ × ℝ) = (s, z) + (0, L) by simp, this]

/-- Iterated partial derivatives of a function periodic in `z` are periodic in `z`. -/
theorem iterate_periodic {G : ℝ × ℝ → ℝ} {L : ℝ} (hper : ∀ s z, G (s, z + L) = G (s, z))
    (m j : ℕ) (s z : ℝ) :
    (zDeriv^[j] (sDeriv^[m] G)) (s, z + L) = (zDeriv^[j] (sDeriv^[m] G)) (s, z) := by
  have hs : ∀ m : ℕ, ∀ s z, (sDeriv^[m] G) (s, z + L) = (sDeriv^[m] G) (s, z) := by
    intro m
    induction m with
    | zero => simpa using hper
    | succ m ih =>
      intro s z
      rw [Function.iterate_succ_apply']
      exact sDeriv_periodic ih s z
  induction j generalizing s z with
  | zero => exact hs m s z
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact zDeriv_periodic (fun s z ↦ ih s z) s z

/-- The derivative in `z` of a slice is the partial derivative in `z`. -/
theorem deriv_slice {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (s z : ℝ) :
    deriv (fun z ↦ G (s, z)) z = zDeriv G (s, z) := by
  have hp : HasDerivAt (fun z : ℝ ↦ ((s, z) : ℝ × ℝ)) (0, 1) z :=
    (hasDerivAt_const z s).prodMk (hasDerivAt_id z)
  exact ((hG (s, z)).hasFDerivAt.comp_hasDerivAt z hp).deriv

/-- The iterated derivatives in `z` of the slices of a smooth function are the slices of its
iterated partial derivatives in `z`. -/
theorem iteratedDeriv_slice {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (j : ℕ) (s : ℝ) :
    iteratedDeriv j (fun z ↦ G (s, z)) = fun z ↦ (zDeriv^[j] G) (s, z) := by
  induction j with
  | zero => funext z; simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [deriv_slice ((contDiff_iterate_zDeriv hG j).differentiable (by simp)),
      Function.iterate_succ_apply']

/-- The coefficients of the slices of a smooth function are smooth in the parameter. -/
theorem contDiff_sineCoeff_param {L : ℝ} {Ω : ℝ × ℝ → ℝ} (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun s ↦ sineCoeff L (fun z ↦ Ω (s, z)) k) := by
  have hH : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ ↦ Ω p * Real.sin (2 * π * k / L * p.2)) :=
    hΩ.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd))
  exact contDiff_const.mul (PDE.Analysis.contDiff_intervalIntegral hH 0 L)

/-- The derivative in the parameter of the coefficients of the slices of a smooth function is
the coefficient of the slices of its partial derivative. -/
theorem deriv_sineCoeff_param {L : ℝ} {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (k : ℕ)
    (s : ℝ) :
    deriv (fun s ↦ sineCoeff L (fun z ↦ G (s, z)) k) s =
      sineCoeff L (fun z ↦ sDeriv G (s, z)) k := by
  set ν : ℝ := 2 * π * k / L
  set S : ℝ × ℝ → ℝ := fun p ↦ Real.sin (ν * p.2)
  set H : ℝ × ℝ → ℝ := fun p ↦ G p * S p
  have hS : ContDiff ℝ (⊤ : ℕ∞) S := Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hG.mul hS
  have hH1 : ContDiff ℝ 1 H := hH.of_le (by simp)
  have hfd : ∀ p : ℝ × ℝ, fderiv ℝ H p (1, 0) = sDeriv G p * S p := by
    intro p
    have hGd := ((hG.differentiable (by simp)) p).hasFDerivAt
    have hSd := ((hS.differentiable (by simp)) p).hasFDerivAt
    have hS10 : fderiv ℝ S p (1, 0) = 0 := by
      have hc : HasFDerivAt (fun q : ℝ × ℝ ↦ ν * q.2)
          (ν • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
        (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.const_smul ν
      have : HasFDerivAt S (Real.cos (ν * p.2) • ν • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
        hc.sin
      rw [this.fderiv]
      simp
    have hHd : HasFDerivAt H (G p • fderiv ℝ S p + S p • fderiv ℝ G p) p := hGd.mul hSd
    rw [hHd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul,
      hS10, mul_zero, zero_add, sDeriv]
    ring
  have hderiv := PDE.Analysis.hasFDerivAt_intervalIntegral_of_contDiff hH1 0 L s
  have hint : IntervalIntegrable (fun t ↦ (fderiv ℝ H (s, t)).comp
      (ContinuousLinearMap.inl ℝ ℝ ℝ)) volume 0 L := by
    apply Continuous.intervalIntegrable
    exact ((hH1.continuous_fderiv one_ne_zero).comp
      (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  have hfun : (fun s ↦ sineCoeff L (fun z ↦ G (s, z)) k) =
      fun s ↦ 2 / L * ∫ t in (0 : ℝ)..L, H (s, t) := by
    funext s
    rfl
  rw [hfun, deriv_const_mul _ hderiv.differentiableAt, hderiv.hasDerivAt.deriv]
  rw [ContinuousLinearMap.intervalIntegral_apply hint]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hfd]
  rfl

/-- The iterated derivatives in the parameter of the coefficients of the slices of a smooth
function are the coefficients of the slices of its iterated partial derivatives. -/
theorem iteratedDeriv_sineCoeff_param {L : ℝ} {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (k m : ℕ) :
    iteratedDeriv m (fun s ↦ sineCoeff L (fun z ↦ G (s, z)) k) =
      fun s ↦ sineCoeff L (fun z ↦ (sDeriv^[m] G) (s, z)) k := by
  induction m with
  | zero => funext s; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [deriv_sineCoeff_param (contDiff_iterate_sDeriv hG m), Function.iterate_succ_apply']

/-- Repeated integration by parts: the coefficients of the slices of `∂_z^{2N} G` are
`(-(2πk/L)²)^N` times those of `G`. -/
theorem sineCoeff_iterate_zDeriv {L : ℝ} (hL : 0 < L) {G : ℝ × ℝ → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hper : ∀ s z, G (s, z + L) = G (s, z)) (k N : ℕ) (s : ℝ) :
    sineCoeff L (fun z ↦ (zDeriv^[2 * N] G) (s, z)) k =
      (-(2 * π * k / L) ^ 2) ^ N * sineCoeff L (fun z ↦ G (s, z)) k := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hF := contDiff_iterate_zDeriv hG (2 * N)
    have hperF : Function.Periodic (fun z ↦ (zDeriv^[2 * N] G) (s, z)) L := fun z ↦ by
      simpa using iterate_periodic hper 0 (2 * N) s z
    have hF2 : ContDiff ℝ 2 (fun z ↦ (zDeriv^[2 * N] G) (s, z)) :=
      (hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    have h2 := sineCoeff_iteratedDeriv_two hL hF2 hperF k
    have hslice := iteratedDeriv_slice hF 2 s
    rw [hslice] at h2
    rw [show 2 * (N + 1) = 2 + 2 * N by ring, Function.iterate_add_apply, h2, ih, pow_succ]
    ring

/-- The coefficient `k = 0` vanishes. -/
@[simp]
theorem sineCoeff_zero (L : ℝ) (g : ℝ → ℝ) : sineCoeff L g 0 = 0 := by
  simp [sineCoeff]

/-- **Rapid decay of parametric coefficients.** For a smooth `Ω(s, z)`, `L`-periodic in `z`,
every `s`-derivative of the coefficients of the slices `z ↦ Ω(s, z)` decays faster than any
power of `k`, uniformly for `s` in a compact set. -/
theorem exists_abs_iteratedDeriv_sineCoeff_le {L : ℝ} (hL : 0 < L) {Ω : ℝ × ℝ → ℝ}
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω) (hper : ∀ s z, Ω (s, z + L) = Ω (s, z)) (m N : ℕ)
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ C, ∀ k : ℕ, ∀ s ∈ K, |iteratedDeriv m (fun s ↦ sineCoeff L (fun z ↦ Ω (s, z)) k) s| ≤
      C / (1 + (k : ℝ)) ^ N := by
  set Gm := sDeriv^[m] Ω
  have hGm : ContDiff ℝ (⊤ : ℕ∞) Gm := contDiff_iterate_sDeriv hΩ m
  have hperm : ∀ s z, Gm (s, z + L) = Gm (s, z) := fun s z ↦ by
    simpa using iterate_periodic hper m 0 s z
  set F := zDeriv^[2 * N] Gm
  have hFc : Continuous F := (contDiff_iterate_zDeriv hGm (2 * N)).continuous
  obtain ⟨M₀, hM₀⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (hFc.continuousOn (s := K ×ˢ Icc 0 L))
  set M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨2 ^ N * (L / (2 * π)) ^ (2 * N) * (2 * M), fun k s hs ↦ ?_⟩
  have hC : 0 ≤ 2 ^ N * (L / (2 * π)) ^ (2 * N) * (2 * M) := by positivity
  rw [iteratedDeriv_sineCoeff_param hΩ k m]
  change |sineCoeff L (fun z ↦ Gm (s, z)) k| ≤ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [sineCoeff_zero, abs_zero, Nat.cast_zero, add_zero, one_pow, div_one]
    exact hC
  set c := sineCoeff L (fun z ↦ Gm (s, z)) k
  set ν : ℝ := 2 * π * k / L
  have hFb : |sineCoeff L (fun z ↦ F (s, z)) k| ≤ 2 * M := by
    refine abs_sineCoeff_le hL (fun z hz ↦ ?_) k
    have := hM₀ (s, z) ⟨hs, hz⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have heq : sineCoeff L (fun z ↦ F (s, z)) k = (-ν ^ 2) ^ N * c :=
    sineCoeff_iterate_zDeriv hL hGm hperm k N s
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

end

end PDE.Analysis.Fourier.SineSeries
