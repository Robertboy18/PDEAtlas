/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.StationaryPhase.SquareRoot
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Smooth congruence of nearby symmetric operators

A smooth self-adjoint operator field near an invertible self-adjoint operator
admits a smooth congruence to that operator. The construction takes the local
square root of the relative operator; positivity is unnecessary.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis.StationaryPhase

variable {A P : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [ContinuousStar A]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A smooth self-adjoint family is locally congruent to its invertible value. -/
theorem exists_contDiffAt_congruence {B : P → A} {p : P} (u : Aˣ)
    (hu : star (u : A) = u) (hB : ContDiff ℝ (⊤ : ℕ∞) B)
    (hBp : B p = u) (hBs : ∀ᶠ x in 𝓝 p, star (B x) = B x) :
    ∃ R : P → A, R p = 1 ∧ ContDiffAt ℝ (⊤ : ℕ∞) R p ∧
      (∀ᶠ x in 𝓝 p, ContDiffAt ℝ (⊤ : ℕ∞) R x) ∧
      ∀ᶠ x in 𝓝 p, star (R x) * (u : A) * R x = B x := by
  let J (a : A) : A := (↑u⁻¹ : A) * star a * u
  have hJ : ContinuousAt J 1 := by fun_prop
  have hJone : J 1 = 1 := by simp [J]
  have hJsq (a : A) : J (a * a) = J a * J a := by
    simp only [J, star_mul]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  obtain ⟨r, hrone, hr, hrsq, hrJ⟩ :=
    exists_contDiffAt_square_root_commuting hJ hJone hJsq
  let M (x : P) : A := (↑u⁻¹ : A) * B x
  have hM : ContDiff ℝ (⊤ : ℕ∞) M := contDiff_const.mul hB
  have hMp : M p = 1 := by simp [M, hBp]
  have ht : Tendsto M (𝓝 p) (𝓝 1) := by
    simpa only [hMp] using hM.continuous.continuousAt (x := p) |>.tendsto
  have hu' : star u = u := Units.ext hu
  have hui : star (↑u⁻¹ : A) = ↑u⁻¹ := by
    rw [← Units.coe_star_inv, hu']
  refine ⟨fun x ↦ r (M x), ?_, ?_, ?_, ?_⟩
  · change r (M p) = 1
    rw [hMp, hrone]
  · have hrM : ContDiffAt ℝ (⊤ : ℕ∞) r (M p) := by
      simpa only [hMp] using hr.of_le (by simp)
    exact hrM.comp p hM.contDiffAt
  · filter_upwards [ht.eventually (hr.eventually (by simp))] with x hx
    exact (hx.of_le (by simp)).comp x hM.contDiffAt
  filter_upwards [hBs, ht.eventually hrsq, ht.eventually hrJ] with x hx hsq hj
  have hfix : J (M x) = M x := by
    simp [J, M, hx, hui, mul_assoc]
  rw [hfix] at hj
  have hcomm : (u : A) * r (M x) = star (r (M x)) * u := by
    have heq := congrArg (fun a : A ↦ (u : A) * a) hj
    simpa only [J, ← mul_assoc, Units.mul_inv, one_mul] using heq
  calc
    star (r (M x)) * (u : A) * r (M x) =
        (u : A) * (r (M x) * r (M x)) := by rw [← hcomm, mul_assoc]
    _ = (u : A) * M x := congrArg (fun a : A ↦ (u : A) * a) hsq
    _ = B x := by simp [M]

end PDE.Analysis.StationaryPhase
