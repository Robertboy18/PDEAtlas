/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Endpoint.L1.CellAverages

/-!
# Global L¹ grid approximation

Let `f ∈ L¹(ℝ^n)` vanish outside the lattice cells of mesh `δ` that cover the
ball `B(0, R)`, and suppose `f` has a linear translation modulus
`‖τ_h f - f‖_{L¹} ≤ |h| C` (as the base coordinate of every `W^{1,1}(ℝ^n)`
element does, with `C` its `W^{1,1}` norm, by
`Endpoint.L1.TranslationEstimate`).  Then the finite-rank grid average
satisfies

  `‖G_δ f - f‖_{L¹} ≤ 2ⁿ √n · δ · C`.

The proof chains the cell oscillation bound of `Endpoint.L1.CellAverages`, the
shear identity bounding total oscillation by `∫_{[-δ,δ]ⁿ} ‖τ_h f - f‖ dh`, the
diameter bound `|h| ≤ √n δ` on the difference box, and its volume `(2δ)ⁿ`; the
factor `δⁿ` from the cell volumes cancels against the box volume.  Applied to
the unit ball of a supported extension of `W^{1,1}(Ω)`, this gives uniform
approximation by compact operators, which is the Kolmogorov–Riesz–Fréchet
route to the endpoint case of the Rellich–Kondrachov theorem.

## Main results

* `euclideanGridAverageL1 δ R`: grid averaging on `L¹(ℝ^n)` over the cells
  covering `B(0, R)`; it is compact (`euclideanGridAverageL1.isCompactOperator`).
* `norm_le_sqrt_nat_mul_delta_of_mem_differenceBox`: `|h| ≤ √n δ` on `[-δ, δ]ⁿ`.
* `integral_translationL1_le_of_norm_le`: the box integral of the translation
  defect under a linear modulus.
* `euclideanGridAverageL1.norm_sub_le`: the uniform approximation estimate.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace RellichKondrachov

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ}

section EndpointL1

/-- Finite-grid averaging on global `L¹`, using exactly the finite index set
from the Hilbert-space Rellich argument. -/
noncomputable def euclideanGridAverageL1 (δ R : ℝ) :
    DerivLp n 1 Set.univ →L[ℝ] DerivLp n 1 Set.univ :=
  finiteCellAverageL1
    (Rellich.euclideanGridIndicesForBall (n := n) δ R)
    (Rellich.euclideanGridCell (n := n) δ)
    (fun k ↦ Rellich.measurableSet_euclideanGridCell (n := n) δ k)
    (fun k ↦ by
      simp [domainMeasure, Rellich.volume_euclideanGridCell])

/-- Grid averaging on `L¹(ℝ^n)` is compact: it is a finite sum of rank-one
operators. -/
theorem euclideanGridAverageL1.isCompactOperator (δ R : ℝ) :
    IsCompactOperator (euclideanGridAverageL1 (n := n) δ R) := by
  exact finiteCellAverageL1.isCompactOperator
    (Rellich.euclideanGridIndicesForBall (n := n) δ R)
    (Rellich.euclideanGridCell (n := n) δ)
    (fun k ↦ Rellich.measurableSet_euclideanGridCell (n := n) δ k)
    (fun k ↦ by
      simp [domainMeasure, Rellich.volume_euclideanGridCell])

/-- Diameter bound for the common difference box. -/
theorem norm_le_sqrt_nat_mul_delta_of_mem_differenceBox
    {δ : ℝ} (hδ : 0 ≤ δ) {h : ℝ^n}
    (hh : h ∈ Rellich.euclideanDifferenceBox (n := n) δ) :
    ‖h‖ ≤ √n * δ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hδ)).1
  calc
    ‖h‖ ^ 2 ≤ (n : ℝ) * δ ^ 2 :=
      Rellich.norm_sq_le_of_mem_euclideanDifferenceBox (n := n) hh
    _ = (√n * δ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Integrated translation control on a difference box for an arbitrary
global `L¹` function satisfying a linear translation modulus. -/
theorem integral_translationL1_le_of_norm_le
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (f : DerivLp n 1 Set.univ)
    (htrans : ∀ h : ℝ^n,
      ‖Rellich.translateLp 1 h f - f‖ ≤ ‖h‖ * C) :
    (∫ h in Rellich.euclideanDifferenceBox (n := n) δ,
        ‖Rellich.translateLp 1 h f - f‖) ≤
      (2 * δ) ^ n * (√n * δ * C) := by
  let F : ℝ^n → ℝ := fun h ↦
    ‖Rellich.translateLp 1 h f - f‖
  let M : ℝ := √n * δ * C
  have hFcont : Continuous F :=
    ((Rellich.continuous_translateLp
      (n := n) 1 (by norm_num) f).sub continuous_const).norm
  have hFint : IntegrableOn F
      (Rellich.euclideanDifferenceBox (n := n) δ)
      MeasureTheory.volume :=
    hFcont.continuousOn.integrableOn_compact
      (Rellich.isCompact_euclideanDifferenceBox (n := n) δ)
  have hmeasure :
      (MeasureTheory.volume : Measure (ℝ^n))
          (Rellich.euclideanDifferenceBox (n := n) δ) ≠ ∞ := by
    rw [Rellich.volume_euclideanDifferenceBox]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hMint : IntegrableOn (fun _ : ℝ^n ↦ M)
      (Rellich.euclideanDifferenceBox (n := n) δ)
      MeasureTheory.volume :=
    MeasureTheory.integrableOn_const hmeasure
  have hpoint : ∀ h ∈ Rellich.euclideanDifferenceBox (n := n) δ,
      F h ≤ M := by
    intro h hh
    calc
      F h ≤ ‖h‖ * C := htrans h
      _ ≤ (√n * δ) * C :=
        mul_le_mul_of_nonneg_right
          (norm_le_sqrt_nat_mul_delta_of_mem_differenceBox
            (n := n) hδ.le hh) hC
      _ = M := rfl
  calc
    (∫ h in Rellich.euclideanDifferenceBox (n := n) δ,
        ‖Rellich.translateLp 1 h f - f‖) =
        ∫ h in Rellich.euclideanDifferenceBox (n := n) δ, F h := rfl
    _ ≤ ∫ _ in Rellich.euclideanDifferenceBox (n := n) δ, M :=
      MeasureTheory.setIntegral_mono_on hFint hMint
        (Rellich.measurableSet_euclideanDifferenceBox (n := n) δ) hpoint
    _ = (2 * δ) ^ n * M := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]
      change ((MeasureTheory.volume : Measure (ℝ^n))
        (Rellich.euclideanDifferenceBox (n := n) δ)).toReal * M = _
      rw [Rellich.volume_euclideanDifferenceBox, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * δ)]
    _ = (2 * δ) ^ n * (√n * δ * C) := rfl

/-- Uniform finite-rank approximation estimate for compactly supported
global `L¹` functions with a linear translation modulus. -/
theorem euclideanGridAverageL1.norm_sub_le
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (R : ℝ)
    (f : DerivLp n 1 Set.univ)
    (hsupport : ∀ᵐ x ∂MeasureTheory.volume,
      x ∉ ⋃ k ∈ Rellich.euclideanGridIndicesForBall (n := n) δ R,
          Rellich.euclideanGridCell (n := n) δ k → f x = 0)
    (htrans : ∀ h : ℝ^n,
      ‖Rellich.translateLp 1 h f - f‖ ≤ ‖h‖ * C) :
    ‖euclideanGridAverageL1 (n := n) δ R f - f‖ ≤
      (2 : ℝ) ^ n * √n * δ * C := by
  let I := Rellich.euclideanGridIndicesForBall (n := n) δ R
  let cell : (Fin n → ℤ) → Set (ℝ^n) :=
    Rellich.euclideanGridCell (n := n) δ
  have herr := finiteCellAverageL1.norm_sub_le_pairwise
    (n := n) I cell
    (fun k ↦ Rellich.measurableSet_euclideanGridCell (n := n) δ k)
    (fun k hk ↦ by
      simpa [domainMeasure, cell] using
        Rellich.volume_euclideanGridCell_ne_zero (n := n) hδ k)
    (fun k ↦ by
      simp [domainMeasure, cell, Rellich.volume_euclideanGridCell])
    (by simpa [cell] using
      Rellich.pairwiseDisjoint_euclideanGridCell (n := n) hδ I)
    f (by simpa [domainMeasure, I, cell] using hsupport)
  have hpair :=
    sum_gridCell_pairwise_abs_le_integral_translateL1
      (n := n) hδ I f
  have hbox :=
    integral_translationL1_le_of_norm_le
      (n := n) hδ hC f htrans
  have hδpow : δ ^ n ≠ 0 := pow_ne_zero _ hδ.ne'
  calc
    ‖euclideanGridAverageL1 (n := n) δ R f - f‖ ≤
        ∑ k ∈ I, ((domainMeasure n Set.univ).real (cell k))⁻¹ *
          ∫ x in cell k, ∫ y in cell k, |f x - f y|
            ∂domainMeasure n Set.univ
            ∂domainMeasure n Set.univ := by
      simpa [euclideanGridAverageL1, I, cell] using herr
    _ = (δ ^ n)⁻¹ *
        ∑ k ∈ I,
          ∫ x in cell k, ∫ y in cell k, |f x - f y|
            ∂domainMeasure n Set.univ
            ∂domainMeasure n Set.univ := by
      simp_rw [show ∀ k : Fin n → ℤ,
          (domainMeasure n Set.univ).real (cell k) = δ ^ n by
        intro k
        simpa [domainMeasure, cell] using
          Rellich.volumeReal_euclideanGridCell (n := n) hδ k]
      rw [Finset.mul_sum]
    _ ≤ (δ ^ n)⁻¹ *
        ∫ h in Rellich.euclideanDifferenceBox (n := n) δ,
          ‖Rellich.translateLp 1 h f - f‖ := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [cell, domainMeasure] using hpair)
        (inv_nonneg.mpr (by positivity))
    _ ≤ (δ ^ n)⁻¹ *
        ((2 * δ) ^ n * (√n * δ * C)) := by
      exact mul_le_mul_of_nonneg_left hbox
        (inv_nonneg.mpr (by positivity))
    _ = (2 : ℝ) ^ n * √n * δ * C := by
      rw [mul_pow]
      field_simp

end EndpointL1

end RellichKondrachov
end GraphSpace
end SobolevSpace
