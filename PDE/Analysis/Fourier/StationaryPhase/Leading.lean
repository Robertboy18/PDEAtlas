/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.Expansion
import CAS.ExactTactic

/-!
# Leading stationary phase as frequency tends to infinity

For a smooth compact amplitude and a smooth real phase whose critical points
on its support are nondegenerate, the oscillatory integral is the finite sum of
the Hessian contributions plus `o(t^(-n/2))`. The coefficient `hessianFresnel`
contains `(2π)^(n/2)`, the inverse square root of the absolute Hessian determinant,
and the phase `exp(iπ signature/4)`. This is formula (54) of Evans, §4.5.3(b), with
`t = 1 / ε` and an error `o(t^(-n/2))` in place of his relative error `O(ε)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), the stationary phase method, (52)-(54),
  p. 226. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- The stationary scale tends to zero through positive values. -/
theorem tendsto_stationary_scale :
    Tendsto (fun t : ℝ ↦ t ^ (-(1 / 2 : ℝ))) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_rpow_neg_atTop (by norm_num), ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact Real.rpow_pos_of_pos ht _

/-- The square of the stationary scale is the inverse frequency. -/
theorem stationary_scale_sq {t : ℝ} (ht : 0 < t) :
    (t ^ (-(1 / 2 : ℝ))) ^ 2 = t⁻¹ := by
  rw [← Real.rpow_mul_natCast ht.le]
  norm_num [Real.rpow_neg_one]

/-- The dimensional scale is the inverse half-dimensional frequency power. -/
theorem stationary_scale_pow {t : ℝ} (ht : 0 < t) :
    (t ^ (-(1 / 2 : ℝ))) ^ n = t ^ (-(n : ℝ) / 2) := by
  rw [← Real.rpow_mul_natCast ht.le]
  congr 1
  cas

/-- The leading stationary-phase asymptotic as `t → ∞` for a smooth compactly supported
amplitude. The finite set is exactly the critical set on the support of the amplitude, and
the coefficients are given by the Hessians there. -/
theorem exists_stationary_phase_expansion
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {a : ℝ^n → ℂ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a)
    (hdet : ∀ p ∈ tsupport a, fderiv ℝ φ p = 0 →
      (PDE.Analysis.hessianMatrix φ p).det ≠ 0) :
    ∃ C : Finset (ℝ^n),
      (∀ p, p ∈ C ↔ p ∈ tsupport a ∧ fderiv ℝ φ p = 0) ∧
      (fun t : ℝ ↦
        (∫ x, Complex.exp ((t * φ x : ℝ) * I) * a x) -
          (t ^ (-(n : ℝ) / 2) : ℝ) *
            ∑ p : C, Complex.exp ((t * φ p : ℝ) * I) * hessianFresnel φ p * a p)
        =o[atTop] (fun t : ℝ ↦ ((t ^ (-(n : ℝ) / 2) : ℝ) : ℂ)) := by
  obtain ⟨C, hC, hscale⟩ := exists_stationary_phase_expansion_scale hφ ha hc hdet
  refine ⟨C, hC, ?_⟩
  apply (isLittleO_iff_tendsto' ?_).mpr
  · have h := hscale.comp tendsto_stationary_scale
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hphase (x : ℝ^n) : φ x / (t ^ (-(1 / 2 : ℝ))) ^ 2 = t * φ x := by
      rw [stationary_scale_sq ht, div_inv_eq_mul, mul_comm]
    simp only [Function.comp_def, oscillatoryIntegral, hphase]
    simp only [← Complex.ofReal_pow, stationary_scale_pow (n := n) ht]
    exact (div_eq_inv_mul _ _).symm
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    intro hz
    exact ((Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos ht _).ne') hz).elim

end PDE.Analysis.StationaryPhase
