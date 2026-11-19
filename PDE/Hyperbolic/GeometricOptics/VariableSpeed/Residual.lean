/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.GeometricOptics.VariableSpeed.Operator
import CAS.ExactTactic

/-!
# Exact variable-speed geometric-optics expansion

For the packet `exp(i p / ε) a`, the residual of `∂ₜ² - c(x)² Δ`
has coefficients `L a`, `T(a,p)` and `-a E(p)` at orders 1, ε⁻¹ and ε⁻².
The eikonal and transport expressions below retain the variable wave speed.
Their cancellation leaves `exp(i p / ε) L a`, which need not tend to zero.

This is a local calculation for C² amplitude and phase in any spatial dimension.
It extends the constant-speed calculation of `GeometricOptics.Residual`.
-/

@[expose] public noncomputable section

open PDE PDE.Common PDE.Analysis

namespace WaveEquation.GeometricOptics.VariableSpeed

variable {n : ℕ}

/-- The variable-speed squared-eikonal expression `pₜ² - c² |∇p|²`. -/
def eikonalDefect (c : ℝ^n → ℝ) (p : ℝ^(n + 1) → ℝ) (z : ℝ^(n + 1)) : ℝ :=
  (∂[0] p) z ^ 2 - c (spatialPart z) ^ 2 * ∑ i : Fin n, (∂[i.succ] p) z ^ 2

/-- The transport expression `a Lp + 2(pₜ aₜ - c² ∇p · ∇a)`. -/
def transportTerm (c : ℝ^n → ℝ) (a p : ℝ^(n + 1) → ℝ) (z : ℝ^(n + 1)) : ℝ :=
  a z * VariableCoefficient.waveOperator (principalMatrix c) p z +
    2 * ((∂[0] p) z * (∂[0] a) z -
      c (spatialPart z) ^ 2 * ∑ i : Fin n, (∂[i.succ] p) z * (∂[i.succ] a) z)

/-- Expansion of the coordinate derivatives, before simplifying the imaginary square. -/
theorem residual_wavePacket_frequency (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) (ε : ℝ) :
    residual c (wavePacket ε a p) z =
      osc ε⁻¹ (p z) *
        ((VariableCoefficient.waveOperator (principalMatrix c) a z : ℂ) +
          ((ε⁻¹ : ℝ) * Complex.I) * (transportTerm c a p z : ℂ) +
          ((ε⁻¹ : ℝ) * Complex.I) ^ 2 * (a z : ℂ) * (eikonalDefect c p z : ℂ)) := by
  unfold residual
  simp_rw [secondPartialDeriv_wavePacket ha hp]
  rw [← Finset.mul_sum]
  unfold transportTerm eikonalDefect
  simp only [waveOperator_principalMatrix]
  push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.mul_sum]
  cas

/-- Scaling the differentiated residual exposes its real and imaginary coefficients. -/
theorem scaled_residual_wavePacket (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) {ε : ℝ} (hε : ε ≠ 0) :
    (ε : ℂ) ^ 2 * residual c (wavePacket ε a p) z = osc ε⁻¹ (p z) *
      (((ε ^ 2 * VariableCoefficient.waveOperator (principalMatrix c) a z - a z *
      eikonalDefect c p z : ℝ) : ℂ) + Complex.I * ((ε * transportTerm c a p z : ℝ) : ℂ)) := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  rw [residual_wavePacket_frequency c ha hp]
  push_cast
  simp only [mul_pow, Complex.I_sq]
  cas using hεc

/-- An exact packet solution satisfies both the real amplitude balance and transport equation. -/
theorem residual_wavePacket_eq_zero_iff (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) {ε : ℝ} (hε : ε ≠ 0) :
    residual c (wavePacket ε a p) z = 0 ↔ a z * eikonalDefect c p z = ε ^ 2 *
      VariableCoefficient.waveOperator (principalMatrix c) a z ∧ transportTerm c a p z = 0 := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have hosc : osc ε⁻¹ (p z) ≠ 0 := Complex.exp_ne_zero _
  constructor
  · intro hsol
    have hid := scaled_residual_wavePacket c ha hp hε
    rw [hsol, mul_zero] at hid
    have hbracket := (mul_eq_zero.mp hid.symm).resolve_left hosc
    have hreal := congrArg Complex.re hbracket
    have himag := congrArg Complex.im hbracket
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
      Complex.zero_re] at hreal
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, Complex.zero_im] at himag
    exact ⟨(sub_eq_zero.mp hreal).symm, (mul_eq_zero.mp himag).resolve_left hε⟩
  · rintro ⟨hreal, himag⟩
    have hid := scaled_residual_wavePacket c ha hp hε
    rw [← hreal, sub_self, himag, mul_zero] at hid
    have hzero : (ε : ℂ) ^ 2 * residual c (wavePacket ε a p) z = 0 := by
      simpa using hid
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hεc)

/-- Eikonal and transport cancellation leave the amplitude wave residual. -/
theorem residual_wavePacket_of_eikonal_transport (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) (he : eikonalDefect c p z = 0)
    (ht : transportTerm c a p z = 0) (ε : ℝ) :
    residual c (wavePacket ε a p) z =
      osc ε⁻¹ (p z) * (VariableCoefficient.waveOperator (principalMatrix c) a z : ℂ) := by
  simp only [residual_wavePacket_frequency c ha hp, he, ht, Complex.ofReal_zero, mul_zero, add_zero]

/-- The residual norm after the two leading cancellations is independent of frequency. -/
theorem norm_residual_wavePacket_of_eikonal_transport (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ}
    {z : ℝ^(n + 1)} (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z)
    (he : eikonalDefect c p z = 0) (ht : transportTerm c a p z = 0) (ε : ℝ) :
    ‖residual c (wavePacket ε a p) z‖ =
      |VariableCoefficient.waveOperator (principalMatrix c) a z| := by
  rw [residual_wavePacket_of_eikonal_transport c ha hp he ht, norm_mul,
    norm_osc_eq_one, one_mul, Complex.norm_real, Real.norm_eq_abs]

end WaveEquation.GeometricOptics.VariableSpeed
