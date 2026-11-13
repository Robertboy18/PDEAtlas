/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.Localized
public import PDE.Analysis.Asymptotics.NonstationaryPhase.Euclidean

/-!
# The noncritical remainder

Repeated integration by parts in the nonstationary-phase theorem
`NonstationaryPhase.exists_norm_integral_osc_smul_le_pow` makes
the part of the amplitude away from the critical points negligible at the
stationary-phase scale, in every dimension.

This is the bound `O(ε^m)` in Evans's stationary phase method, §4.5.3(b), for an amplitude
with no critical points of the phase in its support; `tendsto_noncritical_remainder` states
the consequence that the integral is `o(ε^n)`, where our `ε²` is his `ε`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), the stationary phase method, p. 226.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Complex
open scoped Topology

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- If the phase has no critical points in the support of a smooth compactly supported
amplitude, the oscillatory integral is `o(ε^n)` as `ε → 0`. -/
theorem tendsto_noncritical_remainder
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {a : ℝ^n → ℂ} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a)
    (hne : ∀ x ∈ tsupport a, fderiv ℝ φ x ≠ 0) :
    Tendsto (fun ε : ℝ ↦ ((ε : ℂ) ^ n)⁻¹ * oscillatoryIntegral φ a ε)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ :=
    PDE.Analysis.NonstationaryPhase.exists_norm_integral_osc_smul_le_pow hφ ha hc hne (n + 1)
  have hzero : Tendsto (fun ε : ℝ ↦ C * ε ^ (n + 2)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ ↦ C * ε ^ (n + 2)) :=
      continuous_const.mul (continuous_id.pow (n + 2))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' ?_ hzero
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  have hI : oscillatoryIntegral φ a ε =
      ∫ x, PDE.Analysis.osc (ε ^ 2)⁻¹ (φ x) • a x := by
    simp only [oscillatoryIntegral, PDE.Analysis.osc, smul_eq_mul,
      div_eq_mul_inv, mul_comm (φ _) ((ε ^ 2)⁻¹), Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_pow]
  have hb := hC ((ε ^ 2)⁻¹) (inv_ne_zero (pow_ne_zero 2 hεpos.ne'))
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hεpos, hI]
  calc
    (ε ^ n)⁻¹ * ‖∫ x, PDE.Analysis.osc (ε ^ 2)⁻¹ (φ x) • a x‖ ≤
        (ε ^ n)⁻¹ * (C / |(ε ^ 2)⁻¹| ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (pow_nonneg hεpos.le n))
    _ = C * ε ^ (n + 2) := by
      rw [abs_of_pos (inv_pos.mpr (sq_pos_of_pos hεpos)),
        inv_pow, div_inv_eq_mul, ← pow_mul,
        show 2 * (n + 1) = n + (n + 2) by omega, pow_add]
      calc
        _ = ((ε ^ n)⁻¹ * ε ^ n) * (C * ε ^ (n + 2)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero n hεpos.ne'), one_mul]

end PDE.Analysis.StationaryPhase
