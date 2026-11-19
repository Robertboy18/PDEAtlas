/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarHessian
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.FDeriv.Calculus
import PDE.Analysis.Complex.PlanarRealPart

/-!
# Derivatives of `log r` and of the planar Hessian kernels

Chen and Hou II, Appendix B.1, Lemma B.3: for `i + j ≥ 1` and `z ≠ 0`,

`|∂₀^i ∂₁^j log |z|| ≤ (i + j - 1)! |z|^(-i-j)`,

and for the Hessian kernels `K₂ = hessianKernel 0 0`, `K₁ = hessianKernel 0 1`,

`|∂₀^i ∂₁^j Kₖ| ≤ (i + j + 1)!/2 |z|^(-i-j-2)`,

which gives the constants `1/2, 3, 60, 2520` of the paper for `i + j = 0, 2, 4, 6`.

Every function involved is the real part of `c w^(-m)` with `w = z₀ + i z₁`. A coordinate
derivative maps it to the real part of `-m c eₖ w^(-m-1)` with `e₀ = 1`, `e₁ = i`, so `|c|` is
multiplied by `m` at each step.

## Main results

* `partialDeriv_re_mul_zpow`: `∂ₖ Re(c w^m) = Re(c m eₖ w^(m-1))`.
* `abs_iterate_partialDeriv_log_norm_le`: for `i + j ≥ 1` and `z ≠ 0`,
  `|∂₀^i ∂₁^j log |z|| ≤ (i + j - 1)! / |z|^(i+j)`.
* `abs_iterate_partialDeriv_hessianKernel_le`: `|∂₀^i ∂₁^j Kₖ(z)| ≤ (i + j + 1)!/2 / |z|^(i+j+2)`
  for `K₂` and `K₁` and `z ≠ 0`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix B.1,
  Lemma B.3.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open Filter Topology Set
open PDE.Analysis (orthonormalBasisOneI_repr_symm_single_zero
  orthonormalBasisOneI_repr_symm_single_one norm_orthonormalBasisOneI_repr_symm_single)

namespace PotentialTheory.Planar

local notation "𝔠" => (Complex.orthonormalBasisOneI.repr.symm : ℝ^2 → ℂ)

/-- A nonzero point `z` of the plane is a nonzero complex number `w = z₀ + i z₁`. -/
private theorem cx_ne_zero {z : ℝ^2} (hz : z ≠ 0) : 𝔠 z ≠ 0 := by
  rw [← norm_pos_iff, LinearIsometryEquiv.norm_map]; exact norm_pos_iff.mpr hz

/-- **A coordinate derivative of `Re(c w^m)`**: `∂ₖ Re(c w^m) = Re(c m eₖ w^(m-1))`, with
`w = z₀ + i z₁` and `e₀ = 1`, `e₁ = i`. -/
theorem partialDeriv_re_mul_zpow (k : Fin 2) (c : ℂ) (m : ℤ) {z : ℝ^2} (hz : z ≠ 0) :
    (∂[k] (fun y ↦ (c * 𝔠 y ^ m).re)) z =
      (c * m * 𝔠 (EuclideanSpace.single k 1) * 𝔠 z ^ (m - 1)).re := by
  set L : ℝ^2 →L[ℝ] ℂ :=
    Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ∀ y, L y = 𝔠 y := fun y ↦ rfl
  have hF : HasDerivAt (fun w : ℂ ↦ c * w ^ m) (c * (m * 𝔠 z ^ (m - 1))) (𝔠 z) :=
    (hasDerivAt_zpow m (𝔠 z) (Or.inl (cx_ne_zero hz))).const_mul c
  have hG := (hF.hasFDerivAt.restrictScalars ℝ).comp z L.hasFDerivAt
  have hR := Complex.reCLM.hasFDerivAt.comp z hG
  change fderiv ℝ (fun y ↦ (c * 𝔠 y ^ m).re) z (EuclideanSpace.single k 1) = _
  rw [show (fun y ↦ (c * 𝔠 y ^ m).re) = Complex.reCLM ∘ ((fun w : ℂ ↦ c * w ^ m) ∘ 𝔠) from
    funext fun y ↦ by simp, hR.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.reCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, hL]
  congr 1
  ring

/-- One coordinate derivative of a function agreeing with `Re(c w^(-m))` off the origin. -/
private theorem eqOn_partialDeriv_re {g : ℝ^2 → ℝ} {c : ℂ} {m : ℕ}
    (hg : EqOn g (fun y ↦ (c * 𝔠 y ^ (-(m : ℤ))).re) {y | y ≠ 0}) (k : Fin 2) :
    EqOn (fun x ↦ (∂[k] g) x)
      (fun y ↦ ((c * (-(m : ℂ)) * 𝔠 (EuclideanSpace.single k 1)) * 𝔠 y ^ (-((m + 1 : ℕ) : ℤ))).re)
      {y | y ≠ 0} := by
  intro z hz
  have hopen : IsOpen {y : ℝ^2 | y ≠ 0} := isOpen_ne
  have hev : g =ᶠ[𝓝 z] fun y ↦ (c * 𝔠 y ^ (-(m : ℤ))).re :=
    eventuallyEq_of_mem (hopen.mem_nhds hz) hg
  simp only
  rw [PDE.partialDeriv_congr_nhds k hev, partialDeriv_re_mul_zpow k c _ hz]
  congr 1
  push_cast
  ring_nf

/-- Iterating `∂₀` and `∂₁` on `Re(c w^(-m))` off the origin. -/
private theorem exists_eqOn_iterate {g : ℝ^2 → ℝ} {c : ℂ} {m : ℕ}
    (hg : EqOn g (fun y ↦ (c * 𝔠 y ^ (-(m : ℤ))).re) {y | y ≠ 0}) (a b : ℕ) :
    ∃ c' : ℂ, ‖c'‖ = ‖c‖ * m.ascFactorial (b + a) ∧
      EqOn ((fun g x ↦ (∂[(0 : Fin 2)] g) x)^[a] ((fun g x ↦ (∂[(1 : Fin 2)] g) x)^[b] g))
        (fun y ↦ (c' * 𝔠 y ^ (-((m + b + a : ℕ) : ℤ))).re) {y | y ≠ 0} := by
  -- the block of `∂₁`
  have hone : ∀ b : ℕ, ∃ c' : ℂ, ‖c'‖ = ‖c‖ * m.ascFactorial b ∧
      EqOn ((fun g x ↦ (∂[(1 : Fin 2)] g) x)^[b] g)
        (fun y ↦ (c' * 𝔠 y ^ (-((m + b : ℕ) : ℤ))).re) {y | y ≠ 0} := by
    intro b
    induction b with
    | zero => exact ⟨c, by simp, by simpa using hg⟩
    | succ b ih =>
      obtain ⟨c', hc', hEq⟩ := ih
      refine ⟨c' * (-((m + b : ℕ) : ℂ)) * 𝔠 (EuclideanSpace.single 1 1), ?_, ?_⟩
      · rw [norm_mul, norm_mul, norm_orthonormalBasisOneI_repr_symm_single, norm_neg,
          Complex.norm_natCast, hc',
          Nat.ascFactorial_succ]
        push_cast; ring
      · rw [Function.iterate_succ_apply']
        have := eqOn_partialDeriv_re hEq 1
        simpa [Nat.add_assoc] using this
  obtain ⟨c₁, hc₁, hEq₁⟩ := hone b
  -- the block of `∂₀`
  have hzero : ∀ a : ℕ, ∃ c' : ℂ, ‖c'‖ = ‖c₁‖ * (m + b).ascFactorial a ∧
      EqOn ((fun g x ↦ (∂[(0 : Fin 2)] g) x)^[a] ((fun g x ↦ (∂[(1 : Fin 2)] g) x)^[b] g))
        (fun y ↦ (c' * 𝔠 y ^ (-((m + b + a : ℕ) : ℤ))).re) {y | y ≠ 0} := by
    intro a
    induction a with
    | zero => exact ⟨c₁, by simp, by simpa using hEq₁⟩
    | succ a ih =>
      obtain ⟨c', hc', hEq⟩ := ih
      refine ⟨c' * (-((m + b + a : ℕ) : ℂ)) * 𝔠 (EuclideanSpace.single 0 1), ?_, ?_⟩
      · rw [norm_mul, norm_mul, norm_orthonormalBasisOneI_repr_symm_single, norm_neg,
          Complex.norm_natCast, hc',
          Nat.ascFactorial_succ]
        push_cast; ring
      · rw [Function.iterate_succ_apply']
        have := eqOn_partialDeriv_re hEq 0
        simpa [Nat.add_assoc] using this
  obtain ⟨c₂, hc₂, hEq₂⟩ := hzero a
  refine ⟨c₂, ?_, hEq₂⟩
  rw [hc₂, hc₁, mul_assoc, ← Nat.cast_mul, Nat.ascFactorial_mul_ascFactorial]

/-- `|Re(c w^(-n))| ≤ |c| |z|^(-n)`. -/
private theorem abs_re_mul_zpow_le (c : ℂ) (n : ℕ) (z : ℝ^2) :
    |(c * 𝔠 z ^ (-(n : ℤ))).re| ≤ ‖c‖ / ‖z‖ ^ n := by
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, norm_zpow, LinearIsometryEquiv.norm_map, zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- `∂ₖ log |z| = Re(eₖ / w)`. -/
private theorem eqOn_partialDeriv_log_norm (k : Fin 2) :
    EqOn (fun x ↦ (∂[k] (fun y : ℝ^2 ↦ Real.log ‖y‖)) x)
      (fun y ↦ (𝔠 (EuclideanSpace.single k 1) * 𝔠 y ^ (-((1 : ℕ) : ℤ))).re) {y | y ≠ 0} := by
  intro z hz
  have hz2 : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have h1 : HasFDerivAt (fun y : ℝ^2 ↦ ‖y‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 := HasFDerivAt.const_mul (h1.log hz2) (1 / 2 : ℝ)
  have hfun : (fun y : ℝ^2 ↦ Real.log ‖y‖) = fun y ↦ 1 / 2 * Real.log (‖y‖ ^ 2) := by
    funext y; rw [Real.log_pow]; push_cast; ring
  simp only
  change fderiv ℝ (fun y : ℝ^2 ↦ Real.log ‖y‖) z (EuclideanSpace.single k 1) = _
  rw [hfun, h2.fderiv]
  have hre := orthonormalBasisOneI_repr_symm_re z
  have him := orthonormalBasisOneI_repr_symm_im z
  have hns : Complex.normSq (𝔠 z) = ‖z‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, LinearIsometryEquiv.norm_map]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul,
    zpow_neg, zpow_one, Nat.cast_one]
  fin_cases k
  · simp only [Fin.zero_eta, orthonormalBasisOneI_repr_symm_single_zero, one_mul, Complex.inv_re,
      hns, hre]
    field_simp
  · simp only [Fin.mk_one, orthonormalBasisOneI_repr_symm_single_one, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.inv_re, Complex.inv_im, hns, him, zero_mul, one_mul, zero_sub]
    field_simp

/-- **Part II Lemma B.3**: for `i + j ≥ 1` and `z ≠ 0`,
`|∂₀^i ∂₁^j log |z|| ≤ (i + j - 1)! / |z|^(i+j)`. -/
theorem abs_iterate_partialDeriv_log_norm_le (i j : ℕ) (hij : 1 ≤ i + j) {z : ℝ^2}
    (hz : z ≠ 0) :
    |((fun g x ↦ (∂[(0 : Fin 2)] g) x)^[i] ((fun g x ↦ (∂[(1 : Fin 2)] g) x)^[j]
        fun y : ℝ^2 ↦ Real.log ‖y‖)) z| ≤ ((i + j - 1).factorial : ℝ) / ‖z‖ ^ (i + j) := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · -- no `∂₁`: start from `∂₀ log |z|`
    subst hj
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨c', hc', hEq⟩ := exists_eqOn_iterate (eqOn_partialDeriv_log_norm 0) i 0
    rw [Function.iterate_zero, id, Function.iterate_succ_apply]
    have h := hEq hz
    simp only [Function.iterate_zero, id] at h
    rw [h]
    refine (abs_re_mul_zpow_le c' _ z).trans (le_of_eq ?_)
    rw [hc', norm_orthonormalBasisOneI_repr_symm_single, one_mul, Nat.one_ascFactorial, show i + 1
        + 0 - 1 = 0 + i by omega,
      show i + 1 + 0 = 1 + 0 + i by omega]
  · -- start from `∂₁ log |z|`
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨c', hc', hEq⟩ := exists_eqOn_iterate (eqOn_partialDeriv_log_norm 1) i j
    rw [Function.iterate_succ_apply, hEq hz]
    refine (abs_re_mul_zpow_le c' _ z).trans (le_of_eq ?_)
    rw [hc', norm_orthonormalBasisOneI_repr_symm_single, one_mul, Nat.one_ascFactorial, show i + (j
        + 1) - 1 = j + i by omega,
      show i + (j + 1) = 1 + j + i by omega]

/-- **Part II Lemma B.3, Hessian kernels**: `|∂₀^i ∂₁^j Kₖ(z)| ≤ (i + j + 1)!/2 / |z|^(i+j+2)`
for `K₂ = hessianKernel 0 0` and `K₁ = hessianKernel 0 1`, `z ≠ 0`. -/
theorem abs_iterate_partialDeriv_hessianKernel_le (k : Fin 2) (i j : ℕ) {z : ℝ^2}
    (hz : z ≠ 0) :
    |((fun g x ↦ (∂[(0 : Fin 2)] g) x)^[i] ((fun g x ↦ (∂[(1 : Fin 2)] g) x)^[j]
        (hessianKernel 0 k))) z| ≤ ((i + j + 1).factorial : ℝ) / 2 / ‖z‖ ^ (i + j + 2) := by
  have hK : EqOn (hessianKernel 0 k)
      (fun y ↦ ((𝔠 (EuclideanSpace.single k 1) / 2) * 𝔠 y ^ (-((2 : ℕ) : ℤ))).re)
      {y | y ≠ 0} := by
    intro y _
    fin_cases k
    · simp only [Fin.zero_eta, orthonormalBasisOneI_repr_symm_single_zero,
        hessianKernel_zero_zero_eq_re]
      congr 1
      rw [zpow_neg, zpow_natCast]
      field_simp
    · simp only [Fin.mk_one, orthonormalBasisOneI_repr_symm_single_one,
        hessianKernel_zero_one_eq_neg_im]
      rw [zpow_neg, zpow_natCast, show Complex.I / 2 * ((𝔠 y) ^ 2)⁻¹ =
        Complex.I * (1 / (2 * 𝔠 y ^ 2)) by field_simp, Complex.mul_re, Complex.I_re,
        Complex.I_im]
      ring
  obtain ⟨c', hc', hEq⟩ := exists_eqOn_iterate hK i j
  rw [hEq hz]
  refine (abs_re_mul_zpow_le c' _ z).trans (le_of_eq ?_)
  have hasc : ((2 : ℕ).ascFactorial (j + i) : ℝ) = ((i + j + 1).factorial : ℝ) := by
    have h := Nat.factorial_mul_ascFactorial' 2 (j + i) (by norm_num)
    norm_num at h
    rw [h, show 1 + (j + i) = i + j + 1 by omega]
  rw [hc', norm_div, norm_orthonormalBasisOneI_repr_symm_single, Complex.norm_ofNat, hasc, show 2 +
      j + i = i + j + 2 by omega]
  ring

end PotentialTheory.Planar
