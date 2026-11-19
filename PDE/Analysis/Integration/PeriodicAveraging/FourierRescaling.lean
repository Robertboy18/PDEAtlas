/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.LocalLp
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Weak averaging of periodic Fourier modes

The Euclidean lift of a torus character is its usual exponential plane wave.
Every nonzero mode oscillates at a frequency escaping to infinity as the period
tends to zero. Mathlib's Riemann–Lebesgue theorem then gives convergence of its
integral against an arbitrary integrable weight.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter UnitAddTorus
open scoped ENNReal Topology InnerProductSpace FourierTransform

namespace PDE.Analysis.PeriodicAveraging

/-- A torus Fourier character lifts to the corresponding Euclidean plane wave. -/
theorem mFourier_toTorus {n : ℕ} (k : Fin n → ℤ) (x : ℝ^n) :
    mFourier k (toTorus n x) =
      (𝐞 ⟪x, WithLp.toLp 2 (fun i ↦ (k i : ℝ))⟫_ℝ : ℂ) := by
  simp only [mFourier, toTorus, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum, Real.fourierChar_apply]
  congr 1
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Rescaling a nonzero Euclidean frequency makes its weighted plane-wave integral vanish. -/
theorem tendsto_integral_fourierChar_rescale {n : ℕ} (v : ℝ^n) (hv : v ≠ 0)
    (ψ : ℝ^n → ℂ) {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x : ℝ^n, 𝐞 ⟪(ε j)⁻¹ • x, v⟫_ℝ • ψ x) l (𝓝 0) := by
  have hright : Tendsto ε l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hε⟩
  have hfreq : Tendsto (fun j ↦ -((ε j)⁻¹ • v)) l (cocompact (ℝ^n)) := by
    rw [← Metric.cobounded_eq_cocompact]
    apply tendsto_norm_atTop_iff_cobounded.mp
    have hnorm := hright.inv_tendsto_nhdsGT_zero.atTop_mul_const (norm_pos_iff.mpr hv)
    simpa only [Pi.inv_apply, norm_neg, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (hε _)] using hnorm
  have h := (tendsto_integral_exp_inner_smul_cocompact ψ).comp hfreq
  change Tendsto (fun j ↦ ∫ x : ℝ^n, 𝐞 (-⟪x, -((ε j)⁻¹ • v)⟫_ℝ) • ψ x)
    l (𝓝 0) at h
  simpa only [inner_neg_right, inner_smul_right,
    inner_smul_left, RCLike.conj_to_real, neg_neg] using h

/-- Every nonconstant periodic Fourier mode averages weakly to zero after rescaling. -/
theorem tendsto_integral_mFourier_rescale_mul {n : ℕ} (k : Fin n → ℤ) (hk : k ≠ 0)
    (ψ : ℝ^n → ℂ) {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun j ↦ ∫ x : ℝ^n,
      mFourier k (toTorus n ((ε j)⁻¹ • x)) * ψ x) l (𝓝 0) := by
  have hv : WithLp.toLp 2 (fun i ↦ (k i : ℝ)) ≠ (0 : ℝ^n) := by
    intro hz
    apply hk
    funext i
    have hi := congrArg (fun v : ℝ^n ↦ v i) hz
    simp only [PiLp.zero_apply] at hi
    exact_mod_cast hi
  simpa only [mFourier_toTorus, Circle.smul_def, smul_eq_mul] using
    tendsto_integral_fourierChar_rescale _ hv ψ ε hε ht

end PDE.Analysis.PeriodicAveraging
