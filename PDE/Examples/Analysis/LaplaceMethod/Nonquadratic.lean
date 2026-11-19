/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Asymptotics.LaplaceMethod.Euclidean
public import Mathlib.Analysis.InnerProductSpace.Calculus
import CAS.ExactTactic

/-!
# Laplace limits for a quartic phase

The phase `‖x‖² + ‖x‖⁴` has its strict minimum at the origin, with Hessian `2I`. Its first
and second Fréchet derivatives are computed explicitly and passed to the Laplace theorems
`tendsto_laplace_integral_compact_atTop` and
`tendsto_normalized_laplace_integral_of_hasCompactSupport`. The examples cover arbitrary
dimension, a square domain with corners, where the constant is `π`, and a compactly
supported amplitude vanishing at the minimum.
-/

open Filter MeasureTheory Set Metric
open scoped Topology

@[expose] public noncomputable section

namespace PDE.Examples.LaplaceMethod

open PDE.Analysis PDE.Analysis.Asymptotics

variable {n : ℕ}

/-- A nonquadratic phase whose minimum is at the origin in every dimension. -/
def quarticPhase (x : ℝ^n) : ℝ := ‖x‖ ^ 2 + (‖x‖ ^ 2) ^ 2

/-- The quartic phase is C². -/
theorem contDiff_quarticPhase : ContDiff ℝ 2 (quarticPhase (n := n)) :=
  (contDiff_norm_sq ℝ).add ((contDiff_norm_sq ℝ).pow 2)

/-- The actual first Fréchet derivative of the quartic phase. -/
theorem fderiv_quarticPhase (x : ℝ^n) :
    fderiv ℝ quarticPhase x =
      (2 : ℝ) • innerSL ℝ x + (2 * ‖x‖ ^ 2) • ((2 : ℝ) • innerSL ℝ x) := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change fderiv ℝ (fun y : ℝ^n ↦ ‖y‖ ^ 2 + (‖y‖ ^ 2) ^ 2) x = _
  simpa [Pi.add_def, two_smul, two_mul] using (h.add (h.pow 2)).fderiv

/-- At the origin, the actual Hessian is twice the inner product. -/
theorem hessian_quarticPhase :
    fderiv ℝ (fderiv ℝ (quarticPhase (n := n))) 0 = (2 : ℝ) • innerSL ℝ := by
  rw [show fderiv ℝ (quarticPhase (n := n)) = (fun x ↦
    (2 : ℝ) • innerSL ℝ x + (2 * ‖x‖ ^ 2) • ((2 : ℝ) • innerSL ℝ x)) from
      funext fderiv_quarticPhase]
  have hlinear := (innerSL ℝ (E := ℝ^n)).hasFDerivAt.const_smul (2 : ℝ) (x := 0)
  have hnorm := (hasStrictFDerivAt_norm_sq (0 : ℝ^n)).hasFDerivAt.const_mul 2
  simpa [Pi.add_def, Pi.smul_def] using (hlinear.add (hnorm.smul hlinear)).fderiv

/-- The standard-basis matrix of the actual Hessian is `2I`. -/
theorem hessianMatrix_quarticPhase :
    hessianMatrix (quarticPhase (n := n)) 0 = (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [hessianMatrix, LinearMap.BilinForm.toMatrix_apply,
    ContinuousLinearMap.toBilinForm_apply, hessian_quarticPhase,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change (2 : ℝ) * inner ℝ (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j (1 : ℝ)) = 2 * (1 : Matrix (Fin n) (Fin n) ℝ) i j
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply, Matrix.one_apply]

/-- The quartic phase is positive away from the origin. -/
theorem quarticPhase_pos {x : ℝ^n} (hx : x ≠ 0) : 0 < quarticPhase x :=
  add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)) (sq_nonneg _)

/-- The actual Hessian is positive on every nonzero vector. -/
theorem hessian_quarticPhase_pos {v : ℝ^n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ quarticPhase) 0 v v := by
  rw [hessian_quarticPhase]
  change 0 < 2 * inner ℝ v v
  rw [real_inner_self_eq_norm_sq]
  exact mul_pos (by norm_num) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))

/-- The compact Laplace theorem applies to a nonquadratic phase in arbitrary dimension. -/
theorem laplace_quartic_compact {K : Set (ℝ^n)}
    (hK : IsCompact K) (hzero : (0 : ℝ^n) ∈ interior K)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a : ℝ^n → E} (ha : ContinuousOn a K) :
    Tendsto (fun t : ℝ ↦ t ^ ((n : ℝ) / 2) •
      ∫ x in K, Real.exp (-t * (‖x‖ ^ 2 + (‖x‖ ^ 2) ^ 2)) • a x)
      atTop (𝓝 (((2 * Real.pi) ^ ((n : ℝ) / 2) / Real.sqrt (2 ^ n)) • a 0)) := by
  have h := tendsto_laplace_integral_compact_atTop hK hzero
    contDiff_quarticPhase.continuous.continuousOn contDiff_quarticPhase.contDiffAt
    (fun y _ hy ↦ by simpa [quarticPhase] using quarticPhase_pos hy)
    (fun v hv ↦ hessian_quarticPhase_pos hv) ha
  simpa [hessianMatrix_quarticPhase, Matrix.det_smul, quarticPhase] using h

/-- A compact amplitude vanishing at the minimum has zero leading normalized limit. -/
theorem laplace_quartic_zero_amplitude
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a : ℝ^n → E} (ha : Continuous a) (hcompact : HasCompactSupport a)
    (hzero : a 0 = 0) :
    Tendsto (fun t : ℝ ↦ t ^ ((n : ℝ) / 2) •
      ∫ x, Real.exp (-t * (‖x‖ ^ 2 + (‖x‖ ^ 2) ^ 2)) • a x)
      atTop (𝓝 0) := by
  have h := tendsto_normalized_laplace_integral_of_hasCompactSupport
    contDiff_quarticPhase.contDiffAt
    (by simp [fderiv_quarticPhase])
    (fun v hv ↦ hessian_quarticPhase_pos hv) ha hcompact
    contDiff_quarticPhase.continuous.continuousOn
    (fun y _ hy ↦ by simpa [quarticPhase] using quarticPhase_pos hy)
  simpa [quarticPhase, hzero] using h

/-- The closed square, viewed as a subset of Euclidean space. -/
def square : Set (ℝ^2) := {x | ∀ i, x i ∈ Icc (-1 : ℝ) 1}

/-- The square is compact in the Euclidean topology. -/
theorem isCompact_square : IsCompact square := by
  have h := (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi (fun _ : Fin 2 ↦ (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))))
  simpa [square, Set.preimage, Set.pi, PiLp.homeomorph] using h

/-- The origin lies in the interior even though the square has corners. -/
theorem zero_mem_interior_square : (0 : ℝ^2) ∈ interior square := by
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (ball_mem_nhds (0 : ℝ^2) (by norm_num : (0 : ℝ) < 1))
  intro x hx i
  have hnorm : ‖x‖ < 1 := by simpa using hx
  have hi := (PiLp.norm_apply_le x i).trans_lt hnorm
  exact ⟨(abs_lt.mp hi).1.le, (abs_lt.mp hi).2.le⟩

/-- On the square, the quartic phase gives the two-dimensional constant `π`. -/
theorem laplace_quartic_square {a : ℝ^2 → ℝ} (ha : ContinuousOn a square) :
    Tendsto (fun t : ℝ ↦ t *
      ∫ x in square, Real.exp (-t * (‖x‖ ^ 2 + (‖x‖ ^ 2) ^ 2)) * a x)
      atTop (𝓝 (Real.pi * a 0)) := by
  have h := laplace_quartic_compact isCompact_square zero_mem_interior_square ha
  have hcoeff : (2 * Real.pi) ^ ((2 : ℝ) / 2) / Real.sqrt ((2 : ℝ) ^ 2) =
      Real.pi := by
    norm_num
    cas
  simp only [Nat.cast_ofNat] at h
  rw [hcoeff] at h
  simpa only [smul_eq_mul, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one] using h

end PDE.Examples.LaplaceMethod
