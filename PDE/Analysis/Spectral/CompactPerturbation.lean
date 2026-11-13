/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.CompactOperator
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Interval.Set.Infinite

/-!
# Spectrum of compact perturbations of power-bounded operators

Let `T = T₀ + K` act on a normed space over a nontrivially normed field, with `K` compact and
`‖T₀ⁿ‖ ≤ C qⁿ`.

* The powers are compact perturbations of the powers: `Tᵐ = T₀ᵐ + Kₘ` with `Kₘ` compact, and
  for `q < q'` the norm `‖T₀ᵐ‖ ≤ C qᵐ` is eventually below `ε q'ᵐ`. The accumulation criterion
  for eigenvalues therefore applies: distinct eigenvalues of norm at least `q'` cannot converge,
  and over a proper field only finitely many eigenvalues have norm at least `q'`.
* On a Banach space every `z` with `‖z‖ > q` lies in the resolvent set of `T₀`: for large `N`,
  `‖(T₀ / z)^N‖ < 1`, and `1 - (T₀ / z)^N` factors through `1 - T₀ / z`.
* Every point of the spectrum of `T` of norm greater than `q` is an eigenvalue. Indeed
  `z - T = (z - T₀) (1 - (z - T₀)⁻¹ K)`, and the Fredholm alternative applies to the compact
  operator `(z - T₀)⁻¹ K`.
* Hence every interval `(a, b)` with `q < a < b` contains the radius of a circle that carries no
  spectrum of `T`.
-/

@[expose] public noncomputable section

open Metric Set Filter Topology Function

namespace PDE.Analysis.Spectral

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The powers of a compact perturbation are compact perturbations of the powers. -/
theorem exists_pow_add_eq_pow_add {T₀ K : X →L[𝕜] X} (hK : IsCompactOperator K) (n : ℕ) :
    ∃ Kn : X →L[𝕜] X, IsCompactOperator Kn ∧ (T₀ + K) ^ n = T₀ ^ n + Kn := by
  induction n with
  | zero => exact ⟨0, isCompactOperator_zero, by simp⟩
  | succ n ih =>
    obtain ⟨Kn, hKn, h⟩ := ih
    refine ⟨T₀ * Kn + K * T₀ ^ n + K * Kn,
      ((hKn.clm_comp T₀).add (hK.comp_clm (T₀ ^ n))).add (hK.comp_clm Kn), ?_⟩
    rw [pow_succ', h, pow_succ', add_mul, mul_add, mul_add]
    abel

/-- For `T = T₀ + K` with `K` compact, `‖T₀ⁿ‖ ≤ C qⁿ` and `0 ≤ q < q'`, every `ε > 0` admits a
power `T ^ m = A + K'` with `K'` compact and `‖A‖ ≤ ε q' ^ m`. -/
theorem exists_pow_eq_add_of_pow_bound {T T₀ K : X →L[𝕜] X} (hT : T = T₀ + K)
    (hK : IsCompactOperator K) {C q q' : ℝ} (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n) (hq : 0 ≤ q)
    (hqq' : q < q') {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (A K' : X →L[𝕜] X), T ^ m = A + K' ∧ IsCompactOperator K' ∧ ‖A‖ ≤ ε * q' ^ m := by
  have hq' : 0 < q' := hq.trans_lt hqq'
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hq hq'.le)
    ((div_lt_one hq').mpr hqq')).const_mul C
  rw [mul_zero] at hlim
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨Km, hKm, hTm⟩ := exists_pow_add_eq_pow_add (T₀ := T₀) hK m
  refine ⟨m, T₀ ^ m, Km, hT ▸ hTm, hKm, ?_⟩
  calc ‖T₀ ^ m‖ ≤ C * q ^ m := hT₀ m
    _ = C * (q / q') ^ m * q' ^ m := by
        rw [div_pow]
        field_simp
    _ ≤ ε * q' ^ m := mul_le_mul_of_nonneg_right hm.le (by positivity)

/-- Distinct eigenvalues of `T = T₀ + K` with norms at least `q' > q` cannot converge. -/
theorem not_tendsto_eigenvalues_of_pow_bound [CompleteSpace 𝕜] {T T₀ K : X →L[𝕜] X}
    (hT : T = T₀ + K) (hK : IsCompactOperator K) {C q q' : ℝ}
    (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n) (hq : 0 ≤ q) (hqq' : q < q') (μ : ℕ → 𝕜)
    (hμinj : Injective μ) (hμeig : ∀ n, Module.End.HasEigenvalue (T : Module.End 𝕜 X) (μ n))
    (hμq : ∀ n, q' ≤ ‖μ n‖) {η : 𝕜} (hμ : Tendsto μ atTop (𝓝 η)) : False := by
  have hq' : 0 < q' := hq.trans_lt hqq'
  have hη : η ≠ 0 := norm_pos_iff.mp (hq'.trans_le (ge_of_tendsto' hμ.norm hμq))
  refine hη (PDE.Analysis.distinct_eigenvalues_tendsto_zero_of_pow_approx T μ hμinj
    (fun n ↦ norm_pos_iff.mp (hq'.trans_le (hμq n))) hμeig (fun ε hε ↦ ?_) hμ)
  obtain ⟨m, A, K', hTm, hK', hA⟩ := exists_pow_eq_add_of_pow_bound hT hK hT₀ hq hqq' hε
  exact ⟨m, A, K', hTm, hK', fun n ↦
    hA.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq'.le (hμq n) m) hε.le)⟩

/-- Only finitely many eigenvalues of `T = T₀ + K` have norm at least `q' > q`. -/
theorem finite_eigenvalues_norm_ge_of_pow_bound [ProperSpace 𝕜] {T T₀ K : X →L[𝕜] X}
    (hT : T = T₀ + K) (hK : IsCompactOperator K) {C q q' : ℝ}
    (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n) (hq : 0 ≤ q) (hqq' : q < q') :
    {μ : 𝕜 | Module.End.HasEigenvalue (T : Module.End 𝕜 X) μ ∧ q' ≤ ‖μ‖}.Finite := by
  have hq' : 0 < q' := hq.trans_lt hqq'
  refine PDE.Analysis.finite_eigenvalues_of_pow_approx T hq' (fun _ hμ ↦ hμ) fun ε hε ↦ ?_
  obtain ⟨m, A, K', hTm, hK', hA⟩ := exists_pow_eq_add_of_pow_bound hT hK hT₀ hq hqq' hε
  exact ⟨m, A, K', hTm, hK', fun μ hμ ↦
    hA.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq'.le hμ.2 m) hε.le)⟩

variable [CompleteSpace X]

/-- A power-bounded operator, `‖T₀ⁿ‖ ≤ C qⁿ`, has no spectrum outside the closed disc of
radius `q`. -/
theorem mem_resolventSet_of_pow_bound {T₀ : X →L[𝕜] X} {C q : ℝ}
    (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n) (hq : 0 ≤ q) {z : 𝕜} (hz : q < ‖z‖) :
    z ∈ resolventSet 𝕜 T₀ := by
  have hz0 : 0 < ‖z‖ := hq.trans_lt hz
  have hzne : z ≠ 0 := norm_pos_iff.mp hz0
  set S := z⁻¹ • T₀
  have hS : ∀ n : ℕ, ‖S ^ n‖ ≤ C * (q / ‖z‖) ^ n := fun n ↦ by
    rw [smul_pow, norm_smul, norm_pow, norm_inv, div_pow]
    calc ‖z‖⁻¹ ^ n * ‖T₀ ^ n‖ ≤ ‖z‖⁻¹ ^ n * (C * q ^ n) := by gcongr; exact hT₀ n
      _ = C * (q ^ n / ‖z‖ ^ n) := by rw [inv_pow]; ring
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hq hz0.le)
    ((div_lt_one hz0).mpr hz)).const_mul C
  rw [mul_zero] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
  have hu : IsUnit (1 - S ^ N) := IsUnit.one_sub_of_norm_lt_one ((hS N).trans_lt hN)
  have hcomm : Commute (∑ i ∈ Finset.range N, S ^ i) (1 - S) :=
    (Commute.one_right _).sub_right (Commute.sum_left _ _ _ fun i _ ↦ (Commute.refl S).pow_left i)
  have h1S : IsUnit (1 - S) := (hcomm.isUnit_mul_iff.mp (geom_sum_mul_neg S N ▸ hu)).2
  have hfac : algebraMap 𝕜 (X →L[𝕜] X) z - T₀ = algebraMap 𝕜 (X →L[𝕜] X) z * (1 - S) := by
    rw [mul_sub, mul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul,
      mul_inv_cancel₀ hzne, one_smul]
  rw [spectrum.mem_resolventSet_iff, hfac]
  exact ((IsUnit.mk0 z hzne).map (algebraMap 𝕜 (X →L[𝕜] X))).mul h1S

/-- Every point of the spectrum of `T = T₀ + K` of norm greater than `q` is an eigenvalue. -/
theorem hasEigenvalue_of_mem_spectrum_of_pow_bound {T T₀ K : X →L[𝕜] X} (hT : T = T₀ + K)
    (hK : IsCompactOperator K) {C q : ℝ} (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n) (hq : 0 ≤ q)
    {z : 𝕜} (hz : q < ‖z‖) (hzσ : z ∈ spectrum 𝕜 T) :
    Module.End.HasEigenvalue (T : Module.End 𝕜 X) z := by
  have h0 := mem_resolventSet_of_pow_bound hT₀ hq hz
  set R₀ := resolvent T₀ z
  have hR₀ : (algebraMap 𝕜 (X →L[𝕜] X) z - T₀) * R₀ = 1 := Ring.mul_inverse_cancel _ h0
  have hRK : IsCompactOperator (R₀ * K) := hK.clm_comp R₀
  rcases hRK.hasEigenvalue_or_mem_resolventSet one_ne_zero with h | h
  · obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have hv' : R₀ (K v) = v := by simpa using hv.apply_eq_smul
    have hKv : K v = z • v - T₀ v := by
      have h1 := DFunLike.congr_fun hR₀ (K v)
      rw [mul_apply_eq_comp, hv', one_apply_eq_self,
        sub_apply, Algebra.algebraMap_eq_smul_one,
        smul_apply, one_apply_eq_self] at h1
      exact h1.symm
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff]
    change T v = z • v
    rw [hT, add_apply, hKv]
    abel
  · exfalso
    apply hzσ
    rw [spectrum.mem_resolventSet_iff] at h ⊢
    have hfac : algebraMap 𝕜 (X →L[𝕜] X) z - T =
        (algebraMap 𝕜 (X →L[𝕜] X) z - T₀) * (algebraMap 𝕜 (X →L[𝕜] X) 1 - R₀ * K) := by
      rw [map_one, mul_sub, mul_one, ← mul_assoc, hR₀, one_mul, hT]
      abel
    rw [hfac]
    exact (spectrum.mem_resolventSet_iff.mp h0).mul h

variable [ProperSpace 𝕜]

/-- Only finitely many points of the spectrum of `T = T₀ + K` have norm at least `q' > q`. -/
theorem finite_spectrum_norm_ge_of_pow_bound {T T₀ K : X →L[𝕜] X} (hT : T = T₀ + K)
    (hK : IsCompactOperator K) {C q q' : ℝ} (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n) (hq : 0 ≤ q)
    (hqq' : q < q') : {z : 𝕜 | z ∈ spectrum 𝕜 T ∧ q' ≤ ‖z‖}.Finite :=
  (finite_eigenvalues_norm_ge_of_pow_bound hT hK hT₀ hq hqq').subset fun _ ⟨hz, hzq⟩ ↦
    ⟨hasEigenvalue_of_mem_spectrum_of_pow_bound hT hK hT₀ hq (hqq'.trans_le hzq) hz, hzq⟩

/-- **A spectrum-free circle in every interval.** For `T = T₀ + K` with `K` compact and
`‖T₀ⁿ‖ ≤ C qⁿ`, every interval `(a, b)` with `q < a < b` contains a radius `r` whose circle
carries no spectrum of `T`. -/
theorem exists_radius_notMem_spectrum_of_pow_bound {T T₀ K : X →L[𝕜] X} (hT : T = T₀ + K)
    (hK : IsCompactOperator K) {C q : ℝ} (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n) (hq : 0 ≤ q)
    {a b : ℝ} (hqa : q < a) (hab : a < b) :
    ∃ r, a < r ∧ r < b ∧ ∀ z : 𝕜, ‖z‖ = r → z ∉ spectrum 𝕜 T := by
  have hN := (finite_spectrum_norm_ge_of_pow_bound hT hK hT₀ hq hqa).image (fun z : 𝕜 ↦ ‖z‖)
  obtain ⟨r, ⟨har, hrb⟩, hrN⟩ := ((Set.Ioo_infinite hab).sdiff hN).nonempty
  exact ⟨r, har, hrb, fun z hz hzσ ↦ hrN ⟨z, ⟨hzσ, hz ▸ har.le⟩, hz⟩⟩

end PDE.Analysis.Spectral
