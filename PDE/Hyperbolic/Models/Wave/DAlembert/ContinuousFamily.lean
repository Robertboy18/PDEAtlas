/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.ContinuousFamily.IteratedDerivative
public import PDE.Hyperbolic.Models.Wave.DAlembert.Derivatives
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuously indexed one-dimensional waves

Integrating the initial velocity gains one spatial derivative in d'Alembert's
formula. A continuously indexed family of `C¹` velocities therefore gives
jointly continuous spacetime jets through order two, provided the velocities
and their first derivatives are jointly continuous. The index itself needs
only a topology. In Duhamel's formula the index is the time of the source slice.
-/

@[expose] public noncomputable section

namespace WaveEquation

variable {T : Type*} [TopologicalSpace T]

/-- Continuous initial velocities give a continuous family of zero-displacement waves. -/
theorem continuous_dAlembert_zero_displacement_family
    {h : T → ℝ → ℝ} (hh : Continuous (fun p : T × ℝ ↦ h p.1 p.2)) :
    Continuous (fun p : T × ℝ^2 ↦ dAlembertFormula (fun _ ↦ 0) (h p.1) (p.2 1) (p.2 0)) := by
  have hi (L : ℝ^2 →L[ℝ] ℝ) : Continuous (fun p : T × ℝ^2 ↦ ∫ y in (0 : ℝ)..L p.2, h p.1 y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun p : T × ℝ^2 ↦ h p.1)
      (hh.comp (continuous_fst.fst.prodMk continuous_snd)) (L.continuous.comp continuous_snd)
  have heq : (fun p : T × ℝ^2 ↦ dAlembertFormula (fun _ ↦ 0) (h p.1) (p.2 1)
      (p.2 0)) = fun p ↦ (1 / 2 : ℝ) * ((∫ y in (0 : ℝ)..characteristicCoordinate 1 p.2, h p.1 y) -
          ∫ y in (0 : ℝ)..characteristicCoordinate (-1) p.2, h p.1 y) := by
    funext p
    have hs : Continuous (h p.1) := hh.comp (continuous_const.prodMk continuous_id)
    change (1 / 2 : ℝ) * (0 + 0) +
        (1 / 2 : ℝ) * (∫ y in (p.2 1 - p.2 0)..(p.2 1 + p.2 0), h p.1 y) =
      (1 / 2 : ℝ) * ((∫ y in (0 : ℝ)..(p.2 1 + 1 * p.2 0), h p.1 y) -
        ∫ y in (0 : ℝ)..(p.2 1 + (-1) * p.2 0), h p.1 y)
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg, add_zero, mul_zero, zero_add]
    rw [intervalIntegral.integral_interval_sub_left (hs.intervalIntegrable 0 (p.2 1 + p.2 0))
      (hs.intervalIntegrable 0 (p.2 1 - p.2 0))]
  rw [heq]
  exact continuous_const.mul ((hi _).sub (hi _))

/-- One continuous velocity derivative supplies all continuous wave jets through order two.
No differentiability in the indexing parameter is required. -/
theorem continuous_iteratedFDeriv_dAlembert_zero_displacement_family {h : T → ℝ → ℝ}
    (hh : ∀ s, ContDiff ℝ 1 (h s)) (hcont : Continuous (fun p : T × ℝ ↦ h p.1 p.2))
    (hderiv : Continuous (fun p : T × ℝ ↦ deriv (h p.1) p.2)) {j : ℕ} (hj : j ≤ 2) :
    Continuous (fun p : T × ℝ^2 ↦ iteratedFDeriv ℝ j
      (fun q : ℝ^2 ↦ dAlembertFormula (fun _ ↦ 0) (h p.1) (q 1) (q 0)) p.2) := by
  let F (s : T) (p : ℝ^2) := dAlembertFormula (fun _ ↦ 0) (h s) (p 1) (p 0)
  let D (s : T) (p : ℝ^2) : ℝ^2 →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (h s (characteristicCoordinate 1 p) • characteristicCoordinate 1 -
      h s (characteristicCoordinate (-1) p) • characteristicCoordinate (-1))
  let D₂ (s : T) (p : ℝ^2) : ℝ^2 →L[ℝ] (ℝ^2 →L[ℝ] ℝ) := (1 / 2 : ℝ) •
      (deriv (h s) (characteristicCoordinate 1 p) •
          (characteristicCoordinate 1).smulRight (characteristicCoordinate 1) -
        deriv (h s) (characteristicCoordinate (-1) p) •
          (characteristicCoordinate (-1)).smulRight (characteristicCoordinate (-1)))
  have hD (s : T) : fderiv ℝ (F s) = D s := by
    funext p
    simpa [F, D, characteristicCoordinate, sub_eq_add_neg] using
      (hasFDerivAt_dAlembertFormula (fun _ ↦ 0) (h s)
        (differentiable_const 0) (hh s).continuous p).fderiv
  have hD₂ (s : T) : fderiv ℝ (D s) = D₂ s := by
    funext p
    have hd (v : ℝ) := (((hh s).differentiable (by simp))
      (characteristicCoordinate v p)).hasDerivAt.comp_hasFDerivAt p
        (characteristicCoordinate v).hasFDerivAt
    convert ((((hd 1).smul_const (characteristicCoordinate 1)).fun_sub
      ((hd (-1)).smul_const (characteristicCoordinate (-1)))).fun_const_smul
        (1 / 2 : ℝ)).fderiv using 1 <;> ext x y <;> simp [D, D₂, mul_assoc]
  have hcD : Continuous (fun p : T × ℝ^2 ↦ D p.1 p.2) := by
    have hc (L : ℝ^2 →L[ℝ] ℝ) : Continuous (fun p : T × ℝ^2 ↦ h p.1 (L p.2) • L) :=
      (hcont.comp (continuous_fst.prodMk (L.continuous.comp continuous_snd))).fun_smul
        continuous_const
    exact ((hc (characteristicCoordinate 1)).fun_sub
      (hc (characteristicCoordinate (-1)))).fun_const_smul (1 / 2 : ℝ)
  have hcD₂ : Continuous (fun p : T × ℝ^2 ↦ D₂ p.1 p.2) := by
    let : ContinuousSub (ℝ^2 →L[ℝ] (ℝ^2 →L[ℝ] ℝ)) :=
      IsTopologicalAddGroup.to_continuousSub (G := ℝ^2 →L[ℝ] (ℝ^2 →L[ℝ] ℝ))
    have hc (L : ℝ^2 →L[ℝ] ℝ) :
        Continuous (fun p : T × ℝ^2 ↦ deriv (h p.1) (L p.2) • L.smulRight L) :=
      (hderiv.comp (continuous_fst.prodMk (L.continuous.comp continuous_snd))).fun_smul
        continuous_const
    exact ((hc (characteristicCoordinate 1)).fun_sub
      (hc (characteristicCoordinate (-1)))).fun_const_smul (1 / 2 : ℝ)
  change Continuous (fun p : T × ℝ^2 ↦ iteratedFDeriv ℝ j (F p.1) p.2)
  interval_cases j
  · exact Continuous.iteratedFDeriv_zero_family (𝕜 := ℝ) (f := F)
      (continuous_dAlembert_zero_displacement_family hcont)
  · apply PDE.continuous_iteratedFDeriv_succ_family (𝕜 := ℝ) (f := F) (j := 0)
    simp_rw [hD]
    exact Continuous.iteratedFDeriv_zero_family (𝕜 := ℝ) (f := D) hcD
  · apply PDE.continuous_iteratedFDeriv_succ_family (𝕜 := ℝ) (f := F) (j := 1)
    simp_rw [hD]
    apply PDE.continuous_iteratedFDeriv_succ_family (𝕜 := ℝ) (f := D) (j := 0)
    simp_rw [hD₂]
    exact Continuous.iteratedFDeriv_zero_family (𝕜 := ℝ) (f := D₂) hcD₂

end WaveEquation
