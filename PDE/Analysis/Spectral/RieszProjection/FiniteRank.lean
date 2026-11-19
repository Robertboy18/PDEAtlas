/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.RieszProjection.Operator
public import PDE.Analysis.Spectral.CompactPerturbation
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Finite rank of the outer Riesz projection for compact perturbations

Let `T = T₀ + K` act on a complex Banach space, with `K` compact and `‖T₀ⁿ‖ ≤ C qⁿ`. If the
circle of radius `r > q` carries no spectrum of `T`, the spectral part of `T` outside the circle
is finite-dimensional.

Let `P` be the Riesz projection, `Q = 1 - P`, and `W` the inverse of `T` on the range of `Q`.
Then `Q = Wⁿ Tⁿ = Wⁿ T₀ⁿ + Wⁿ Kₙ` with `Kₙ` compact, and `‖Wⁿ T₀ⁿ‖ ≤ C' (q / ρ)ⁿ` for some
`ρ > r`, which is below `1` for large `n`. Multiplying `Q = A + Wⁿ Kₙ` by `Q` gives
`(1 - A) Q = Wⁿ Kₙ Q`, so `Q` is compact, and so is the identity of its range.
-/

@[expose] public noncomputable section

open Metric Set Filter Topology

namespace PDE.Analysis.Spectral

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- If a compact operator `Q` fixes every vector of a closed subspace `V`, then `V` is
finite-dimensional. -/
theorem finiteDimensional_of_isCompactOperator_of_eqOn {Q : X →L[ℂ] X}
    (hQ : IsCompactOperator Q) {V : Submodule ℂ X} (hV : IsClosed (V : Set X))
    (hfix : ∀ x ∈ V, Q x = x) : FiniteDimensional ℂ V := by
  apply FiniteDimensional.of_isCompactOperator_id
  obtain ⟨Kc, hKc, hpre⟩ := hQ
  refine ⟨Subtype.val ⁻¹' Kc, hV.isClosedEmbedding_subtypeVal.isCompact_preimage hKc, ?_⟩
  have hpre' : (Q : X → X) ⁻¹' Kc ∈ 𝓝 ((0 : V) : X) := by simpa using hpre
  refine Filter.mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds hpre')
    fun y hy ↦ ?_
  simp only [mem_preimage, id_eq] at hy ⊢
  rwa [hfix y y.2] at hy

variable [CompleteSpace X]

/-- **Finite rank outside the essential radius.** Let `T = T₀ + K` with `K` compact and
`‖T₀ⁿ‖ ≤ C qⁿ`. If the circle of radius `r > q` carries no spectrum of `T`, the kernel of the
Riesz projection, which carries the spectral part of `T` outside the circle, is
finite-dimensional. -/
theorem finiteDimensional_ker_rieszInner {T T₀ K : X →L[ℂ] X} (hT : T = T₀ + K)
    (hK : IsCompactOperator K) {C q r : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    FiniteDimensional ℂ (LinearMap.ker (rieszInner T r).toLinearMap) := by
  have hr : 0 < r := hq.trans_lt hqr
  have hres := sphere_subset_resolventSet hfree
  set P := rieszInner T r with hPdef
  set W := rieszOuterInverse T r with hWdef
  have hP : IsIdempotentElem P := rieszInner_idem hfree
  have hWT : W * T = 1 - P := rieszOuterInverse_mul hr hres
  have hcomm : Commute W T := (commute_rieszOuterInverse (Commute.refl T) r).symm
  have hWQ : W * (1 - P) = W := by
    rw [mul_sub, mul_one, rieszOuterInverse_mul_rieszInner hr hfree, sub_zero]
  obtain ⟨ρ, C', hρ, hC', hW⟩ := exists_norm_rieszOuterInverse_pow_mul_le hr hfree
  have hρ0 : 0 < ρ := hr.trans hρ
  have hC : 0 ≤ C := by
    have h := hT₀ 0
    rw [pow_zero, pow_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have hqρ : q / ρ < 1 := (div_lt_one hρ0).mpr (hqr.trans hρ)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (C' * C + 1) by positivity) hqρ
  obtain ⟨KN, hKN, hTN⟩ := exists_pow_add_eq_pow_add (T₀ := T₀) hK (m + 1)
  have hWN : W ^ (m + 1) * (1 - P) = W ^ (m + 1) := by rw [pow_succ, mul_assoc, hWQ]
  have hA : ‖W ^ (m + 1) * T₀ ^ (m + 1)‖ < 1 := by
    have hpow : (q / ρ) ^ (m + 1) ≤ (q / ρ) ^ m :=
      pow_le_pow_of_le_one (by positivity) hqρ.le (by omega)
    calc ‖W ^ (m + 1) * T₀ ^ (m + 1)‖ ≤ ‖W ^ (m + 1)‖ * ‖T₀ ^ (m + 1)‖ := norm_mul_le _ _
      _ ≤ (C' * (ρ ^ (m + 1))⁻¹) * (C * q ^ (m + 1)) := by
          gcongr
          · rw [← hWN]
            exact hW (m + 1)
          · exact hT₀ (m + 1)
      _ = C' * C * (q / ρ) ^ (m + 1) := by
          rw [div_pow]
          field_simp
      _ ≤ C' * C * (1 / (C' * C + 1)) := by
          gcongr
          exact hpow.trans hm.le
      _ < 1 := by
          rw [mul_one_div, div_lt_one (by positivity)]
          linarith
  have hQ : 1 - P = W ^ (m + 1) * T₀ ^ (m + 1) + W ^ (m + 1) * KN := by
    rw [← mul_add, ← hTN, ← hT, ← hcomm.mul_pow, hWT, hP.one_sub.pow_succ_eq m]
  have hu : IsUnit (1 - W ^ (m + 1) * T₀ ^ (m + 1)) := IsUnit.one_sub_of_norm_lt_one hA
  have h2 : (1 - W ^ (m + 1) * T₀ ^ (m + 1)) * (1 - P) = W ^ (m + 1) * KN * (1 - P) := by
    have h := congrArg (· * (1 - P)) hQ
    simp only [hP.one_sub.eq, add_mul] at h
    rw [sub_mul, one_mul]
    nth_rewrite 1 [h]
    abel
  have h3 : 1 - P = ↑hu.unit⁻¹ * (W ^ (m + 1) * KN * (1 - P)) := by
    rw [← h2, ← mul_assoc, hu.val_inv_mul, one_mul]
  have hQc : IsCompactOperator (1 - P : X →L[ℂ] X) := by
    rw [h3]
    exact ((hKN.clm_comp (W ^ (m + 1))).comp_clm (1 - P)).clm_comp _
  refine finiteDimensional_of_isCompactOperator_of_eqOn hQc P.isClosed_ker fun x hx ↦ ?_
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  rw [sub_apply, one_apply_eq_self, hx, sub_zero]

/-- Under the hypotheses of `finiteDimensional_ker_rieszInner`, the spectral projection
`1 - rieszInner T r` onto the part of `T` outside the circle has finite rank. -/
theorem finiteDimensional_range_one_sub_rieszInner {T T₀ K : X →L[ℂ] X} (hT : T = T₀ + K)
    (hK : IsCompactOperator K) {C q r : ℝ} (hq : 0 ≤ q) (hqr : q < r)
    (hT₀ : ∀ n : ℕ, ‖T₀ ^ n‖ ≤ C * q ^ n)
    (hfree : ∀ z : ℂ, ‖z‖ = r → z ∉ spectrum ℂ T) :
    FiniteDimensional ℂ (LinearMap.range (1 - rieszInner T r).toLinearMap) := by
  have h := finiteDimensional_ker_rieszInner hT hK hq hqr hT₀ hfree
  have hP := ContinuousLinearMap.IsIdempotentElem.toLinearMap (rieszInner_idem hfree)
  rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hP] at h
  exact h

end PDE.Analysis.Spectral
