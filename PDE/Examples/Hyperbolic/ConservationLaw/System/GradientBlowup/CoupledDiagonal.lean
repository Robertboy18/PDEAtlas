/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Data
public import PDE.Hyperbolic.Quasilinear.Diagonal.Gradient.Global
import CAS.ExactTactic

/-!
# A diagonal system with a nonconstant transverse weight

The first speed is `exp p + exp(-q)` and the second is `-exp(-q)`.
Thus the transverse derivative in the first family is nonzero and its signed
gap is `exp p + 2 exp(-q)`. The spatial integrating factor has derivative
`-1/3` at the zero state. For the diagonal system `∂ₜvⱼ + λⱼ(v) ∂ₓvⱼ = 0` and the
compact data `(compression, -compression)`, the theorem
`not_exists_global_of_compressive_slope` rules out a global `C²` solution
(`not_exists_global_solution`).
-/

@[expose] public noncomputable section

open Set PDE.Analysis PDE.Hyperbolic.Quasilinear.Diagonal
open scoped ContDiff

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.CoupledDiagonal

/-- A coupled pair of diagonal transport speeds. -/
def speeds (i : Fin 2) (z : Fin 2 → ℝ) : ℝ :=
  if i = 0 then Real.exp (z 0) + Real.exp (-z 1) else -Real.exp (-z 1)

/-- Both speeds are `C¹`. -/
theorem contDiff_speeds (i : Fin 2) : ContDiff ℝ 1 (speeds i) := by
  fin_cases i
  · change ContDiff ℝ 1 (fun z : Fin 2 → ℝ ↦ Real.exp (z 0) + Real.exp (-z 1))
    fun_prop
  · change ContDiff ℝ 1 (fun z : Fin 2 → ℝ ↦ -Real.exp (-z 1))
    fun_prop

/-- The derivatives of the two speeds. -/
theorem fderiv_speeds (i : Fin 2) (z v : Fin 2 → ℝ) :
    fderiv ℝ (speeds i) z v =
      if i = 0 then Real.exp (z 0) * v 0 - Real.exp (-z 1) * v 1
      else Real.exp (-z 1) * v 1 := by
  have h₀ : HasDerivAt Real.exp (Real.exp (z 0)) (z 0) := by cas
  have h₁ : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (-Real.exp (-z 1)) (z 1) := by
    cas
  have hP := h₀.comp_hasFDerivAt (𝕜 := ℝ) (f := fun w : Fin 2 → ℝ ↦ w 0) z
    (hasFDerivAt_apply 0 z)
  have hQ := h₁.comp_hasFDerivAt (𝕜 := ℝ) (f := fun w : Fin 2 → ℝ ↦ w 1) z
    (hasFDerivAt_apply 1 z)
  dsimp only [Function.comp_def] at hP hQ
  fin_cases i
  · change fderiv ℝ (fun w : Fin 2 → ℝ ↦ Real.exp (w 0) + Real.exp (-w 1)) z v =
      Real.exp (z 0) * v 0 - Real.exp (-z 1) * v 1
    have hs := hP.add hQ
    change HasFDerivAt (fun w : Fin 2 → ℝ ↦ Real.exp (w 0) + Real.exp (-w 1)) _ z at hs
    rw [hs.fderiv]
    simp [sub_eq_add_neg]
  · change fderiv ℝ (fun w : Fin 2 → ℝ ↦ -Real.exp (-w 1)) z v =
      Real.exp (-z 1) * v 1
    have hs := hQ.neg
    change HasFDerivAt (fun w : Fin 2 → ℝ ↦ -Real.exp (-w 1)) _ z at hs
    rw [hs.fderiv]
    simp

/-- The two speeds never coincide. -/
theorem speeds_ne_rev (i : Fin 2) (z : Fin 2 → ℝ) :
    speeds i z ≠ speeds i.rev z := by
  have hp := Real.exp_pos (z 0)
  have hq := Real.exp_pos (-z 1)
  fin_cases i
  · change Real.exp (z 0) + Real.exp (-z 1) ≠ -Real.exp (-z 1)
    linarith
  · change -Real.exp (-z 1) ≠ Real.exp (z 0) + Real.exp (-z 1)
    linarith

/-- Each speed is strictly increasing in its own coordinate. -/
theorem positive_speed_derivative (i : Fin 2) (z : Fin 2 → ℝ) :
    0 < fderiv ℝ (speeds i) z (Pi.single i 1) := by
  rw [fderiv_speeds]
  fin_cases i
  · simpa using Real.exp_pos (z 0)
  · simpa using Real.exp_pos (-z 1)

/-- The spatial integrating factor has derivative `-1/3` at the zero state. -/
theorem spatialWeight_derivative_zero :
    HasDerivAt (spatialWeight speeds 0 0) (-(1 / 3 : ℝ)) 0 := by
  have hd := hasDerivAt_spatialWeight contDiff_speeds speeds_ne_rev 0 (0 : Fin 2 → ℝ) 0
  have hw : spatialWeight speeds 0 0 0 = 1 := spatialWeight_initial (B := speeds) 0 0
  rw [hw] at hd
  convert hd using 1
  norm_num [transverseRatio, fderiv_speeds, speeds]

/-- Compact data compress the first family and expand the second. -/
def initialData (x : ℝ) : Fin 2 → ℝ := ![compression x, -compression x]

/-- The compact initial datum is smooth. -/
theorem contDiff_initialData : ContDiff ℝ ∞ initialData := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact contDiff_compression
  · exact contDiff_compression.neg

/-- The datum has compact support. -/
theorem hasCompactSupport_initialData : HasCompactSupport initialData :=
  hasCompactSupport_compression.comp_left (g := fun r : ℝ ↦ ![r, -r])
    (by ext i; fin_cases i <;> norm_num)

/-- No solution with continuous second jet on `t > 0` has the datum `initialData`. -/
theorem not_exists_global_solution :
    ¬ ∃ v : ℝ × ℝ → Fin 2 → ℝ,
      Nonempty (ContinuousSecondJetOn v (Ioi (0 : ℝ) ×ˢ univ)) ∧
      (∀ x, v (0, x) = initialData x) ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → ∀ j,
        fderiv ℝ v p (1, speeds j (v p)) j = 0) := by
  apply not_exists_global_of_compressive_slope contDiff_speeds speeds_ne_rev
    positive_speed_derivative (i := 0) (x₀ := 0)
  · obtain ⟨R, hR⟩ := (hasCompactSupport_initialData.isCompact_range
      contDiff_initialData.continuous).exists_bound_of_continuousOn continuous_id.continuousOn
    refine ⟨R, fun x i ↦ ?_⟩
    exact abs_le.mp ((norm_le_pi_norm (initialData x) i).trans (hR _ ⟨x, rfl⟩))
  · change deriv compression 0 < 0
    rw [deriv_compression_zero]
    norm_num

end PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.CoupledDiagonal
