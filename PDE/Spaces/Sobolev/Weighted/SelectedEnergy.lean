/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.EndpointNorm

/-!
# A Hilbert space for a selected derivative energy

An energy that counts the base function and top derivatives need not be the norm of the
full Sobolev jet. This distinction matters for Galerkin equations: the inner product used
to project the equation must be the one differentiated in the energy estimate.

We project the completed weighted jet onto its selected rows. When those rows
control the full norm, the projection has closed range and a continuous inverse on its
range. That range is therefore a complete Hilbert space whose squared norm is exactly the
selected energy. It represents the same Sobolev functions and weak derivatives as the
original completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory SobolevSpace.GraphSpace
open scoped ENNReal NNReal

namespace SobolevSpace.Weighted.CompletedHkSpaceOn

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Keep only the derivative rows listed in `s`, with their original weighted `L²` norms. -/
def selectedRows
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞) (s : Finset (DerivIndex n k)) :
    CompletedHkSpaceOn n k Ω w →L[ℝ]
      L2Rows (domainMeasure n Ω) (fun a : s ↦ w a) :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun a : s ↦ Lp ℝ 2 ((domainMeasure n Ω).withDensity (w a)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a : s ↦ coordinate w a)

/-- Selecting rows evaluates to the corresponding coordinate of the full jet. -/
@[simp] theorem selectedRows_apply
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞) (s : Finset (DerivIndex n k))
    (U : CompletedHkSpaceOn n k Ω w) (a : s) :
    selectedRows w s U a = coordinate w a U :=
  rfl

/-- The projected squared norm is exactly the selected quadratic energy. -/
theorem norm_selectedRows_sq
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞) (s : Finset (DerivIndex n k))
    (U : CompletedHkSpaceOn n k Ω w) :
    ‖selectedRows w s U‖ ^ 2 = ∑ a ∈ s, ‖coordinate w a U‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_coe_sort s (fun a ↦ ‖coordinate w a U‖ ^ 2)

/-- For open `Ω`, if Lebesgue measure on `Ω` is at most `D a < ∞` times every row measure and `s`
contains the base row, then `selectedRows w s` is injective: the base row determines the jet
(`baseRow_injective_of_measure_le_smul`). -/
theorem selectedRows_injective
    (w : DerivIndex n k → ℝ^n → ℝ≥0∞) (s : Finset (DerivIndex n k))
    (D : DerivIndex n k → ℝ≥0∞) (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a, domainMeasure n Ω ≤
      D a • (domainMeasure n Ω).withDensity (w a))
    (hΩ : IsOpen Ω) (hbase : baseIndex n k ∈ s) :
    Function.Injective (selectedRows (Ω := Ω) w s) := by
  intro U V hUV
  apply baseRow_injective_of_measure_le_smul w D hD hlower hΩ
  exact congrArg (fun Z : L2Rows (domainMeasure n Ω) (fun a : s ↦ w a) ↦
    Z ⟨baseIndex n k, hbase⟩) hUV

/-- Under the hypotheses of `norm_le_selected_rows`, `selectedRows w s` is antilipschitz with some
constant `B`, by `exists_pos_norm_sq_le_selected_energy` and `norm_selectedRows_sq`. -/
theorem exists_antilipschitz_selectedRows
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
    ∃ B : ℝ≥0, AntilipschitzWith B (selectedRows (Ω := Set.univ) w s) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_pos_norm_sq_le_selected_energy w D hD hlower s hbase htop C hC hupper hk
  refine ⟨⟨Real.sqrt B, Real.sqrt_nonneg B⟩,
    (selectedRows w s).antilipschitz_of_bound fun U ↦ ?_⟩
  have h := hbound U
  rw [← norm_selectedRows_sq] at h
  change ‖U‖ ≤ Real.sqrt B * ‖selectedRows w s U‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hB.le] using h

/-- Under the hypotheses of `norm_le_selected_rows`, the range of `selectedRows w s` is closed. -/
theorem isClosed_range_selectedRows
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
    IsClosed (Set.range (selectedRows (Ω := Set.univ) w s)) := by
  obtain ⟨B, hB⟩ :=
    exists_antilipschitz_selectedRows w D hD hlower s hbase htop C hC hupper hk
  exact hB.isClosed_range (selectedRows w s).uniformContinuous

/-- Under the hypotheses of `norm_le_selected_rows`, the range of `selectedRows w s` is complete;
its squared norm is the selected energy (`norm_selectedRows_sq`). -/
theorem completeSpace_range_selectedRows
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
    CompleteSpace (selectedRows (Ω := Set.univ) w s).range :=
  (isClosed_range_selectedRows w D hD hlower s hbase htop C hC hupper hk).completeSpace_coe

/-- Under the hypotheses of `norm_le_selected_rows`, the continuous linear equivalence between
`CompletedHkSpaceOn n k univ w` and the range of `selectedRows w s`, whose squared norm is the
selected energy. Its inverse is continuous, so the omitted rows depend continuously on the selected
ones. -/
def selectedEnergyEquiv
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
    CompletedHkSpaceOn n k Set.univ w ≃L[ℝ] (selectedRows (Ω := Set.univ) w s).range :=
  (selectedRows w s).equivRange
    (selectedRows_injective w s (fun _ ↦ D) (fun _ ↦ hD) hlower isOpen_univ hbase)
    (isClosed_range_selectedRows w D hD hlower s hbase htop C hC hupper hk)

end SobolevSpace.Weighted.CompletedHkSpaceOn
