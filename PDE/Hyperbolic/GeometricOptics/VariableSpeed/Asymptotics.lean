/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.GeometricOptics.VariableSpeed.Residual
import CAS.ExactTactic

/-!
# Leading coefficients of the variable-speed residual

For fixed C² amplitude and phase, the norm of ε² times the differentiated
residual tends to `|a E|`. When the eikonal defect vanishes, the norm of ε times
the residual tends to `|T|`. Thus small residuals force the eikonal and
transport equations, with nonvanishing amplitude required only for the former.

Conversely, the two equations give a bound of order ε² for the scaled residual
on any set where `|L a|` is bounded. This estimates the residual of the ansatz.
-/

@[expose] public noncomputable section

open PDE PDE.Analysis Filter
open scoped Topology

namespace WaveEquation.GeometricOptics.VariableSpeed

variable {n : ℕ}

/-- The unit-modulus oscillation drops out of the norm of the scaled residual. -/
theorem norm_scaled_residual_wavePacket (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) {ε : ℝ} (hε : ε ≠ 0) :
    ‖(ε : ℂ) ^ 2 * residual c (wavePacket ε a p) z‖ = ‖((ε ^ 2 *
      VariableCoefficient.waveOperator (principalMatrix c) a z - a z * eikonalDefect c p z : ℝ) :
      ℂ) + Complex.I * ((ε * transportTerm c a p z : ℝ) : ℂ)‖ := by
  rw [scaled_residual_wavePacket c ha hp hε, norm_mul, norm_osc_eq_one, one_mul]

/-- The leading norm coefficient is derived from coordinate derivatives. -/
theorem tendsto_norm_scaled_residual (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) :
    Tendsto (fun ε : ℝ ↦ ‖(ε : ℂ) ^ 2 * residual c (wavePacket ε a p) z‖)
      (𝓝[>] 0) (𝓝 |a z * eikonalDefect c p z|) := by
  have hcont : Continuous (fun ε : ℝ ↦
      ‖((ε ^ 2 * VariableCoefficient.waveOperator (principalMatrix c) a z -
          a z * eikonalDefect c p z : ℝ) : ℂ) +
        Complex.I * ((ε * transportTerm c a p z : ℝ) : ℂ)‖) := by fun_prop
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have heq : (fun ε : ℝ ↦ ‖(ε : ℂ) ^ 2 * residual c (wavePacket ε a p) z‖)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ ↦
        ‖((ε ^ 2 * VariableCoefficient.waveOperator (principalMatrix c) a z -
            a z * eikonalDefect c p z : ℝ) : ℂ) +
          Complex.I * ((ε * transportTerm c a p z : ℝ) : ℂ)‖) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact norm_scaled_residual_wavePacket c ha hp (ne_of_gt hε)
  simpa using hlim.congr' heq.symm

/-- Vanishing scaled residual forces the eikonal equation wherever the amplitude is nonzero. -/
theorem eikonalDefect_eq_zero_of_small_scaled_residual (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ}
    {z : ℝ^(n + 1)} (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) (ha₀ : a z ≠ 0)
    (hsmall :
      Tendsto (fun ε : ℝ ↦ ‖(ε : ℂ) ^ 2 * residual c (wavePacket ε a p) z‖) (𝓝[>] 0) (𝓝 0)) :
    eikonalDefect c p z = 0 := by
  have hzero := tendsto_nhds_unique (tendsto_norm_scaled_residual c ha hp) hsmall
  exact (mul_eq_zero.mp (abs_eq_zero.mp hzero)).resolve_left ha₀

/-- Once the eikonal term vanishes, the next scaled residual exposes transport. -/
theorem mul_residual_wavePacket_of_eikonal (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) (he : eikonalDefect c p z = 0) {ε : ℝ}
    (hε : ε ≠ 0) :
    (ε : ℂ) * residual c (wavePacket ε a p) z = osc ε⁻¹ (p z) *
      (((ε * VariableCoefficient.waveOperator (principalMatrix c) a z : ℝ) : ℂ) + Complex.I *
      (transportTerm c a p z : ℂ)) := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  rw [residual_wavePacket_frequency c ha hp, he]
  push_cast
  simp only [mul_zero, add_zero]
  cas using hεc

/-- After eikonal cancellation, the next leading norm coefficient is the transport term. -/
theorem tendsto_norm_mul_residual_of_eikonal (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) (he : eikonalDefect c p z = 0) :
    Tendsto (fun ε : ℝ ↦ ‖(ε : ℂ) * residual c (wavePacket ε a p) z‖)
      (𝓝[>] 0) (𝓝 |transportTerm c a p z|) := by
  have hcont : Continuous (fun ε : ℝ ↦
      ‖((ε * VariableCoefficient.waveOperator (principalMatrix c) a z : ℝ) : ℂ) +
        Complex.I * (transportTerm c a p z : ℂ)‖) := by fun_prop
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have heq : (fun ε : ℝ ↦ ‖(ε : ℂ) * residual c (wavePacket ε a p) z‖) =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ ↦
        ‖((ε * VariableCoefficient.waveOperator (principalMatrix c) a z : ℝ) : ℂ) +
          Complex.I * (transportTerm c a p z : ℂ)‖) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [mul_residual_wavePacket_of_eikonal c ha hp he (ne_of_gt hε),
      norm_mul, norm_osc_eq_one, one_mul]
  simpa using hlim.congr' heq.symm

/-- Vanishing of the next scaled residual forces the transport equation. -/
theorem transportTerm_eq_zero_of_small_mul_residual (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ}
    {z : ℝ^(n + 1)} (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z)
    (he : eikonalDefect c p z = 0)
    (hsmall : Tendsto (fun ε : ℝ ↦ ‖(ε : ℂ) * residual c (wavePacket ε a p) z‖) (𝓝[>] 0) (𝓝 0)) :
    transportTerm c a p z = 0 :=
  abs_eq_zero.mp (tendsto_nhds_unique (tendsto_norm_mul_residual_of_eikonal c ha hp he) hsmall)

/-- Small unscaled residual of a fixed ansatz forces both leading equations.
This is a necessary condition and does not construct an exact solution. -/
theorem eikonal_transport_of_small_residual (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (ha : ContDiffAt ℝ 2 a z) (hp : ContDiffAt ℝ 2 p z) (ha₀ : a z ≠ 0)
    (hsmall : Tendsto (fun ε : ℝ ↦ ‖residual c (wavePacket ε a p) z‖) (𝓝[>] 0) (𝓝 0)) :
    eikonalDefect c p z = 0 ∧ transportTerm c a p z = 0 := by
  have hε : Tendsto (fun ε : ℝ ↦ ‖(ε : ℂ)‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.norm.tendsto 0).mono_left nhdsWithin_le_nhds
  have hscaled : Tendsto (fun ε : ℝ ↦ ‖(ε : ℂ) ^ 2 * residual c (wavePacket ε a p) z‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa [norm_mul, norm_pow] using (hε.pow 2).mul hsmall
  have he := eikonalDefect_eq_zero_of_small_scaled_residual c ha hp ha₀ hscaled
  refine ⟨he, transportTerm_eq_zero_of_small_mul_residual c ha hp he ?_⟩
  simpa only [norm_mul, zero_mul] using hε.mul hsmall

/-- The two leading cancellations give a uniform bound for the scaled residual. -/
theorem norm_scaled_residual_le_on (c : ℝ^n → ℝ) {a p : ℝ^(n + 1) → ℝ} {K : Set (ℝ^(n + 1))} {M : ℝ}
    (ha : ∀ z ∈ K, ContDiffAt ℝ 2 a z) (hp : ∀ z ∈ K, ContDiffAt ℝ 2 p z)
    (he : ∀ z ∈ K, eikonalDefect c p z = 0) (ht : ∀ z ∈ K, transportTerm c a p z = 0)
    (hM : ∀ z ∈ K, |VariableCoefficient.waveOperator (principalMatrix c) a z| ≤ M) (ε : ℝ)
    {z : ℝ^(n + 1)} (hz : z ∈ K) :
    ‖(ε : ℂ) ^ 2 * residual c (wavePacket ε a p) z‖ ≤ ε ^ 2 * M := by
  rw [norm_mul, norm_pow,
    norm_residual_wavePacket_of_eikonal_transport c (ha z hz) (hp z hz) (he z hz) (ht z hz),
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_left (hM z hz) (sq_nonneg ε)

/-- Compactness supplies the uniform residual constant from continuous speed and C² germs.
No remainder bound or convergence statement is an assumption. -/
theorem exists_norm_scaled_residual_le_on_isCompact {c : ℝ^n → ℝ} {a p : ℝ^(n + 1) → ℝ}
    {K : Set (ℝ^(n + 1))} (hK : IsCompact K)
    (hc : ∀ z ∈ K, ContinuousAt c (PDE.Common.spatialPart z)) (ha : ∀ z ∈ K, ContDiffAt ℝ 2 a z)
    (hp : ∀ z ∈ K, ContDiffAt ℝ 2 p z) (he : ∀ z ∈ K, eikonalDefect c p z = 0)
    (ht : ∀ z ∈ K, transportTerm c a p z = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, ∀ z ∈ K,
      ‖(ε : ℂ) ^ 2 * residual c (wavePacket ε a p) z‖ ≤ ε ^ 2 * M := by
  have hL : ContinuousOn (VariableCoefficient.waveOperator (principalMatrix c) a) K :=
    fun z hz ↦ (continuousAt_waveOperator_principalMatrix (hc z hz) (ha z hz)).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hL
  refine ⟨max M 0, le_max_right _ _, fun ε z hz ↦ norm_scaled_residual_le_on c ha hp he ht ?_ ε hz⟩
  intro y hy
  have hyM : |VariableCoefficient.waveOperator (principalMatrix c) a y| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM y hy
  exact hyM.trans (le_max_left _ _)

end WaveEquation.GeometricOptics.VariableSpeed
