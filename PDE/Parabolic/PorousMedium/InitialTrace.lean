/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.PorousMedium.Mass
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The initial Dirac trace of the Barenblatt family

For every bounded continuous test `φ`, the pairing `∫ u(t, x) φ(x) dx` of the Barenblatt density
tends to `M φ(0)` as `t → 0⁺`, where `M` is the conserved mass
(`tendsto_barenblatt_boundedContinuous`); continuous compactly supported tests are included
(`tendsto_barenblatt_compactSupport`). For `C > 0` the initial trace is therefore `M δ₀`
(`tendsto_barenblatt_dirac`), and the solution with prescribed mass `M > 0` has initial trace `M δ₀`
(`tendsto_barenblatt_prescribed_dirac`).

After the change of variables `x = t^β y` the pairing is `∫ F(y) φ(t^β y) dy`. Since `β > 0`,
`t^β y` tends to zero (`tendsto_similarity_scale_zero`), and the integrable bound `F(y) ‖φ‖∞` gives
dominated convergence (`tendsto_barenblatt_pairing_of_bounded`).

The Barenblatt solution is (35)-(36) of Evans's §4.2.2, where it is derived for `t > 0` only.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2.2, Example (A scaling invariant solution), (27)-(36),
  pp. 185-186.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PorousMedium

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

variable {n : ℕ}

/-- The expanding similarity radius tends to zero at the initial time. -/
theorem tendsto_similarity_scale_zero {m : ℝ} (hm : 1 < m) :
    Tendsto (fun t : ℝ ↦ t ^ similarityBeta n m) (𝓝[>] 0) (𝓝 0) := by
  have hβ := similarityBeta_pos n hm
  simpa only [Real.zero_rpow hβ.ne'] using
    ((Real.continuous_rpow_const hβ.le).tendsto 0).mono_left nhdsWithin_le_nhds

/-- The density pairing tends to its conserved mass times the value of a bounded
continuous test at the origin. The only domination is by the integrable profile. -/
theorem tendsto_barenblatt_pairing_of_bounded {m C B : ℝ}
    (hm : 1 < m) {φ : ℝ^n → ℝ}
    (hφ : Continuous φ) (hB : ∀ x, ‖φ x‖ ≤ B) :
    Tendsto (fun t : ℝ ↦ ∫ x, barenblatt n m C t x * φ x)
      (𝓝[>] 0) (𝓝 (profileMass n m C * φ 0)) := by
  have hlim : Tendsto
      (fun t : ℝ ↦ ∫ y : ℝ^n, profile n m C y * φ (t ^ similarityBeta n m • y))
      (𝓝[>] 0) (𝓝 (∫ y : ℝ^n, profile n m C y * φ 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun y ↦ profile n m C y * B)
    · exact Eventually.of_forall fun t ↦
        ((continuous_profile hm C).mul (hφ.comp (by fun_prop))).aestronglyMeasurable
    · exact Eventually.of_forall fun t ↦ Eventually.of_forall fun y ↦ by
        rw [norm_mul, Real.norm_of_nonneg (profile_nonneg m C y)]
        exact mul_le_mul_of_nonneg_left (hB _) (profile_nonneg m C y)
    · exact (integrable_profile hm).mul_const B
    · apply Eventually.of_forall
      intro y
      have hy : Tendsto (fun t : ℝ ↦ t ^ similarityBeta n m • y) (𝓝[>] 0) (𝓝 0) := by
        simpa only [zero_smul] using (tendsto_similarity_scale_zero (n := n) hm).smul_const y
      exact tendsto_const_nhds.mul (hφ.continuousAt.tendsto.comp hy)
  rw [integral_mul_const] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (integral_barenblatt_mul m C ht φ).symm

/-- Bounded continuous tests detect the initial trace: the limit is the conserved mass
times `φ 0`. -/
theorem tendsto_barenblatt_boundedContinuous {m C : ℝ}
    (hm : 1 < m) (φ : ℝ^n →ᵇ ℝ) :
    Tendsto (fun t : ℝ ↦ ∫ x, barenblatt n m C t x * φ x)
      (𝓝[>] 0) (𝓝 (profileMass n m C * φ 0)) :=
  tendsto_barenblatt_pairing_of_bounded hm φ.continuous φ.norm_coe_le_norm

/-- Continuous compactly supported tests detect the same initial trace. -/
theorem tendsto_barenblatt_compactSupport {m C : ℝ}
    (hm : 1 < m) {φ : ℝ^n → ℝ}
    (hφ : Continuous φ) (hsupp : HasCompactSupport φ) :
    Tendsto (fun t : ℝ ↦ ∫ x, barenblatt n m C t x * φ x)
      (𝓝[>] 0) (𝓝 (profileMass n m C * φ 0)) := by
  obtain ⟨B, hB⟩ := hφ.bounded_above_of_compact_support hsupp
  exact tendsto_barenblatt_pairing_of_bounded hm hφ hB

/-- The initial trace is the Dirac measure at the origin weighted by the profile mass. -/
theorem tendsto_barenblatt_dirac {m C : ℝ}
    (hm : 1 < m) (hC : 0 < C) (φ : ℝ^n →ᵇ ℝ) :
    Tendsto (fun t : ℝ ↦ ∫ x, barenblatt n m C t x * φ x) (𝓝[>] 0)
      (𝓝 (∫ x, φ x ∂(ENNReal.ofReal (profileMass n m C) • Measure.dirac 0))) := by
  simpa only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (profileMass_pos hm hC).le, smul_eq_mul] using
    tendsto_barenblatt_boundedContinuous hm φ

/-- Choosing the explicit parameter for mass `M` gives the test limit `M φ(0)`. -/
theorem tendsto_barenblatt_prescribed_mass {m M : ℝ}
    (hm : 1 < m) (hM : 0 < M) (φ : ℝ^n →ᵇ ℝ) :
    Tendsto
      (fun t : ℝ ↦ ∫ x, barenblatt n m (profileParameterForMass n m M) t x * φ x)
      (𝓝[>] 0) (𝓝 (M * φ 0)) := by
  simpa only [profileMass_profileParameterForMass hm hM] using
    tendsto_barenblatt_boundedContinuous (C := profileParameterForMass n m M) hm φ

/-- The explicit solution with prescribed positive mass `M` has initial trace `M δ₀`. -/
theorem tendsto_barenblatt_prescribed_dirac {m M : ℝ}
    (hm : 1 < m) (hM : 0 < M) (φ : ℝ^n →ᵇ ℝ) :
    Tendsto
      (fun t : ℝ ↦ ∫ x, barenblatt n m (profileParameterForMass n m M) t x * φ x)
      (𝓝[>] 0) (𝓝 (∫ x, φ x ∂(ENNReal.ofReal M • Measure.dirac 0))) := by
  simpa only [profileMass_profileParameterForMass hm hM] using
    tendsto_barenblatt_dirac hm (profileParameterForMass_pos (n := n) hm hM) φ

end PorousMedium
