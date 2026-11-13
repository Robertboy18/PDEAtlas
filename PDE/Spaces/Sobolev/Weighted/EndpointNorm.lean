/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.Density
public import PDE.Spaces.Sobolev.Fractional.Integer.NormComparison

/-!
# Controlling intermediate derivatives from weighted endpoint rows

An energy often measures the function and its highest derivatives, without listing every
intermediate derivative. On the whole space, Fourier interpolation supplies the missing
unweighted rows. Positive lower bounds on the endpoint weights then let us use the weighted
energy in that estimate.

The objects here are completed weighted Sobolev jets. Their lower measure bounds identify
them with Sobolev functions, so the Fourier estimate applies to their weak derivatives. No
upper bound on an endpoint weight is needed.

The constants are explicit and not sharp.
-/

@[expose] public section

noncomputable section

open MeasureTheory SobolevSpace.GraphSpace
open scoped ENNReal

namespace SobolevSpace.Weighted.CompletedHkSpaceOn

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Forgetting a row weight costs at most the square root of its lower measure constant. -/
theorem norm_toHk_coordinate_le
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : DerivIndex n k → ℝ≥0∞) (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a, domainMeasure n Ω ≤
      D a • (domainMeasure n Ω).withDensity (w a))
    (U : CompletedHkSpaceOn n k Ω w) (a : DerivIndex n k) :
    ‖(toHkCLMOfMeasureLeSmul w D hD hlower U : WkpAmbientOn n k 2 Ω) a‖ ≤
      (D a).toReal ^ (1 / 2 : ℝ) * ‖coordinate w a U‖ := by
  change ‖Lp.LpToLpOfMeasureLeSMul (hD a) (hlower a) (coordinate w a U)‖ ≤ _
  refine ((Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2)
    (hD a) (hlower a)).le_opNorm _).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa using Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := 2) (hD a) (hlower a)

/-- Weighted base and pure top rows control the entire unweighted Sobolev norm.
The intermediate row weights may be singular or unbounded: only lower comparisons enter
this estimate. -/
theorem norm_toHk_le_base_add_sum_top
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : DerivIndex n k → ℝ≥0∞) (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a, domainMeasure n Set.univ ≤
      D a • (domainMeasure n Set.univ).withDensity (w a))
    (U : CompletedHkSpaceOn n k Set.univ w) (hk : 1 ≤ k) :
    ‖toHkCLMOfMeasureLeSmul w D hD hlower U‖ ≤
      Fractional.toWkpSpaceNormBound n k * Fractional.besselWeightBound n k *
        ((D (baseIndex n k)).toReal ^ (1 / 2 : ℝ) * ‖baseRow w U‖ +
          ∑ i, (D (topPureDerivIndex n k i)).toReal ^ (1 / 2 : ℝ) *
            ‖coordinate w (topPureDerivIndex n k i) U‖) := by
  refine (Fractional.norm_le_base_add_sum_top
    (toHkCLMOfMeasureLeSmul w D hD hlower U) hk).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg
    Fractional.toWkpSpaceNormBound_nonneg (Fractional.besselWeightBound_nonneg n k))
  exact add_le_add (norm_toHk_coordinate_le w D hD hlower U (baseIndex n k))
    (Finset.sum_le_sum fun i _ ↦
      norm_toHk_coordinate_le w D hD hlower U (topPureDerivIndex n k i))

/-- An upper measure comparison for one row bounds its weighted norm by the norm of the
same unweighted weak derivative. Lower comparisons identify the completed jet first. -/
theorem norm_coordinate_le_toHk
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : DerivIndex n k → ℝ≥0∞) (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a, domainMeasure n Ω ≤
      D a • (domainMeasure n Ω).withDensity (w a))
    (U : CompletedHkSpaceOn n k Ω w) (a : DerivIndex n k)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hupper : (domainMeasure n Ω).withDensity (w a) ≤ C • domainMeasure n Ω) :
    ‖coordinate w a U‖ ≤ C.toReal ^ (1 / 2 : ℝ) *
      ‖(toHkCLMOfMeasureLeSmul w D hD hlower U : WkpAmbientOn n k 2 Ω) a‖ := by
  let V := (toHkCLMOfMeasureLeSmul w D hD hlower U : WkpAmbientOn n k 2 Ω) a
  have hrow : Lp.LpToLpOfMeasureLeSMul hC hupper V = coordinate w a U := by
    apply Lp.ext
    refine (Lp.coeFn_LpToLpOfMeasureLeSMul hC hupper V).trans ?_
    exact (withDensity_absolutelyContinuous (domainMeasure n Ω) (w a)).ae_eq
      (Lp.coeFn_LpToLpOfMeasureLeSMul (hD a) (hlower a) (coordinate w a U))
  rw [← hrow]
  refine ((Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2) hC hupper).le_opNorm V).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa using Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := 2) hC hupper

/-- A weighted jet's norm is bounded by the sum of its row norms. This is the finite
`ℓ² ≤ ℓ¹` inequality; no measure comparison is needed. -/
theorem norm_le_sum_coordinate
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞) (U : CompletedHkSpaceOn n k Ω w) :
    ‖U‖ ≤ ∑ a, ‖coordinate w a U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).mp
  rw [norm_sq_eq_sum]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ norm_nonneg _

/-- On `ℝ^n` with `1 ≤ k`, suppose Lebesgue measure is at most `D` times every row measure, `s`
contains the base row and the pure top rows, and every row outside `s` has measure at most `C`
times Lebesgue measure, with `D, C < ∞`. Then
`‖U‖ ≤ (1 + |sᶜ| C^{1/2} B D^{1/2} (n + 1)) ∑_{a ∈ s} ‖coordinate w a U‖`, where
`B = toWkpSpaceNormBound n k * besselWeightBound n k`.

The weights of the rows in `s` may grow or be singular; Fourier interpolation bounds the
intermediate rows. The constant is explicit but not sharp. -/
theorem norm_le_selected_rows
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : ℝ≥0∞) (hD : D ≠ ∞)
    (hlower : ∀ a, domainMeasure n Set.univ ≤
      D • (domainMeasure n Set.univ).withDensity (w a))
    (s : Finset (DerivIndex n k)) (hbase : baseIndex n k ∈ s)
    (htop : ∀ i, topPureDerivIndex n k i ∈ s)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hupper : ∀ a ∉ s,
      (domainMeasure n Set.univ).withDensity (w a) ≤ C • domainMeasure n Set.univ)
    (U : CompletedHkSpaceOn n k Set.univ w) (hk : 1 ≤ k) :
    ‖U‖ ≤
      (1 + (sᶜ.card : ℝ) * C.toReal ^ (1 / 2 : ℝ) *
        (Fractional.toWkpSpaceNormBound n k * Fractional.besselWeightBound n k *
          D.toReal ^ (1 / 2 : ℝ) * ((n : ℝ) + 1))) *
        ∑ a ∈ s, ‖coordinate w a U‖ := by
  classical
  let S := ∑ a ∈ s, ‖coordinate w a U‖
  let V := toHkCLMOfMeasureLeSmul w (fun _ ↦ D) (fun _ ↦ hD) hlower U
  let B := Fractional.toWkpSpaceNormBound n k * Fractional.besselWeightBound n k
  have hB : 0 ≤ B := mul_nonneg Fractional.toWkpSpaceNormBound_nonneg
    (Fractional.besselWeightBound_nonneg n k)
  have hrow (a : DerivIndex n k) (ha : a ∈ s) : ‖coordinate w a U‖ ≤ S :=
    Finset.single_le_sum (f := fun b ↦ ‖coordinate w b U‖)
      (fun _ _ ↦ norm_nonneg _) ha
  have hV : ‖V‖ ≤ B * D.toReal ^ (1 / 2 : ℝ) * ((n : ℝ) + 1) * S := by
    calc
      ‖V‖ ≤ B * (D.toReal ^ (1 / 2 : ℝ) * ‖baseRow w U‖ +
          ∑ i : Fin n, D.toReal ^ (1 / 2 : ℝ) *
            ‖coordinate w (topPureDerivIndex n k i) U‖) :=
        norm_toHk_le_base_add_sum_top w (fun _ ↦ D) (fun _ ↦ hD) hlower U hk
      _ ≤ B * (D.toReal ^ (1 / 2 : ℝ) * S +
          ∑ _i : Fin n, D.toReal ^ (1 / 2 : ℝ) * S) := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hrow _ hbase) (Real.rpow_nonneg (by positivity) _))
          (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
            (hrow _ (htop i)) (Real.rpow_nonneg (by positivity) _))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring
  have hother (a : DerivIndex n k) (ha : a ∈ sᶜ) :
      ‖coordinate w a U‖ ≤ C.toReal ^ (1 / 2 : ℝ) *
        (B * D.toReal ^ (1 / 2 : ℝ) * ((n : ℝ) + 1) * S) := by
    calc
      ‖coordinate w a U‖ ≤ C.toReal ^ (1 / 2 : ℝ) *
          ‖(V : WkpAmbientOn n k 2 Set.univ) a‖ :=
        norm_coordinate_le_toHk w (fun _ ↦ D) (fun _ ↦ hD) hlower U a C hC
          (hupper a (Finset.mem_compl.1 ha))
      _ ≤ C.toReal ^ (1 / 2 : ℝ) * ‖V‖ :=
        mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ a)
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hV (Real.rpow_nonneg (by positivity) _)
  calc
    ‖U‖ ≤ ∑ a, ‖coordinate w a U‖ := norm_le_sum_coordinate w U
    _ = S + ∑ a ∈ sᶜ, ‖coordinate w a U‖ :=
      (Finset.sum_add_sum_compl s (fun a ↦ ‖coordinate w a U‖)).symm
    _ ≤ S + ∑ _a ∈ sᶜ, C.toReal ^ (1 / 2 : ℝ) *
        (B * D.toReal ^ (1 / 2 : ℝ) * ((n : ℝ) + 1) * S) :=
      add_le_add le_rfl (Finset.sum_le_sum hother)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, B, S]
      ring

/-- Under the hypotheses of `norm_le_selected_rows`, there is `B > 0` with
`‖U‖ ^ 2 ≤ B * ∑ a ∈ s, ‖coordinate w a U‖ ^ 2` for every `U`. We square `norm_le_selected_rows`
and apply Mathlib's Cauchy–Schwarz inequality `Finset.sum_mul_sq_le_sq_mul_sq` to the sum. -/
theorem exists_pos_norm_sq_le_selected_energy
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : ℝ≥0∞) (hD : D ≠ ∞)
    (hlower : ∀ a, domainMeasure n Set.univ ≤
      D • (domainMeasure n Set.univ).withDensity (w a))
    (s : Finset (DerivIndex n k)) (hbase : baseIndex n k ∈ s)
    (htop : ∀ i, topPureDerivIndex n k i ∈ s)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hupper : ∀ a ∉ s,
      (domainMeasure n Set.univ).withDensity (w a) ≤ C • domainMeasure n Set.univ)
    (hk : 1 ≤ k) :
    ∃ B > 0, ∀ U : CompletedHkSpaceOn n k Set.univ w,
      ‖U‖ ^ 2 ≤ B * ∑ a ∈ s, ‖coordinate w a U‖ ^ 2 := by
  classical
  let A := 1 + (sᶜ.card : ℝ) * C.toReal ^ (1 / 2 : ℝ) *
    (Fractional.toWkpSpaceNormBound n k * Fractional.besselWeightBound n k *
      D.toReal ^ (1 / 2 : ℝ) * ((n : ℝ) + 1))
  have hA : 0 < A := by
    have := Fractional.toWkpSpaceNormBound_nonneg (n := n) (k := k)
    have := Fractional.besselWeightBound_nonneg n k
    dsimp [A]
    positivity
  have hs : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨baseIndex n k, hbase⟩
  refine ⟨A ^ 2 * s.card, mul_pos (sq_pos_of_pos hA) hs, fun U ↦ ?_⟩
  have hnorm := norm_le_selected_rows w D hD hlower s hbase htop C hC hupper U hk
  have hsum :
      (∑ a ∈ s, ‖coordinate w a U‖) ^ 2 ≤
        (s.card : ℝ) * ∑ a ∈ s, ‖coordinate w a U‖ ^ 2 := by
    simpa only [one_pow, mul_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_comm] using
      Finset.sum_mul_sq_le_sq_mul_sq s (fun a ↦ ‖coordinate w a U‖) (fun _ ↦ (1 : ℝ))
  calc
    ‖U‖ ^ 2 ≤ (A * ∑ a ∈ s, ‖coordinate w a U‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = A ^ 2 * (∑ a ∈ s, ‖coordinate w a U‖) ^ 2 := mul_pow _ _ _
    _ ≤ A ^ 2 * ((s.card : ℝ) * ∑ a ∈ s, ‖coordinate w a U‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg A)
    _ = _ := (mul_assoc _ _ _).symm

end SobolevSpace.Weighted.CompletedHkSpaceOn
