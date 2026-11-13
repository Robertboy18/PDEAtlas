/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.HalfSpace
public import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Profiles
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# A vanishing strip for shifted Banach-valued mollification

The standard mollifier has support radius two. If a function vanishes almost everywhere
below height zero, convolution at scale `ε`, shifted upward by `3 * ε`, vanishes at every
point of height at most `ε`. This pointwise gap puts its topological support strictly
inside the upper half-space, including when the boundary dimension is zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.VectorValued.HalfSpace

open Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A convolution centered at least two scales below the boundary samples only
the region where the original function vanishes almost everywhere. -/
theorem mollifyVector_eq_zero_of_last_le {ε : ℝ} (hε : 0 < ε)
    {f : ℝ^(n + 1) → F}
    (hf : ∀ᵐ y ∂volume, y (Fin.last n) ≤ 0 → f y = 0)
    {x : ℝ^(n + 1)} (hx : x (Fin.last n) ≤ -(2 * ε)) :
    mollifyVector (standardMollifier (n + 1)) ε f x = 0 := by
  rw [mollifyVector, convolution_lsmul_swap]
  apply integral_eq_zero_of_ae
  filter_upwards [hf] with y hy
  by_cases hk : scaled (standardMollifier (n + 1)) ε (x - y) = 0
  · simp only [hk, zero_smul, Pi.zero_apply]
  · have hb := support_scaled_subset_closedBall (standardMollifier (n + 1)) hε
      (tsupport_standardMollifier_subset_closedBall (n + 1)) hk
    have hn := PiLp.norm_apply_le (x - y) (Fin.last n)
    have ha := neg_le_abs (x (Fin.last n) - y (Fin.last n))
    simp only [Metric.mem_closedBall, dist_zero_right] at hb
    change |x (Fin.last n) - y (Fin.last n)| ≤ ‖x - y‖ at hn
    have hlast : y (Fin.last n) ≤ 0 := by linarith
    simp only [hy hlast, smul_zero, Pi.zero_apply]

/-- Shifting the radius-two standard mollification upward by three scales leaves
a pointwise vanishing strip of width one scale. -/
theorem shifted_mollifyVector_eq_zero {ε : ℝ} (hε : 0 < ε)
    {f : ℝ^(n + 1) → F}
    (hf : ∀ᵐ y ∂volume, y (Fin.last n) ≤ 0 → f y = 0)
    {x : ℝ^(n + 1)} (hx : x (Fin.last n) ≤ ε) :
    mollifyVector (standardMollifier (n + 1)) ε f
      (x + (-(3 * ε)) • EuclideanSpace.single (Fin.last n) 1) = 0 := by
  apply mollifyVector_eq_zero_of_last_le hε hf
  simp only [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single,
    PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
  linarith

omit [NormedSpace ℝ F] in
/-- A function vanishing below a positive height has topological support in the
upper half-space; continuity of the function itself is not needed. -/
theorem tsupport_subset_upper_of_zero_strip {δ : ℝ} (hδ : 0 < δ)
    {f : ℝ^(n + 1) → F} (hf : ∀ x, x (Fin.last n) ≤ δ → f x = 0) :
    tsupport f ⊆ {x : ℝ^(n + 1) | 0 < x (Fin.last n)} := by
  have hs : tsupport f ⊆ {x : ℝ^(n + 1) | δ ≤ x (Fin.last n)} := by
    apply closure_minimal _ (isClosed_le continuous_const
      (EuclideanSpace.proj (Fin.last n)).continuous)
    intro x hx
    exact le_of_lt (lt_of_not_ge fun h ↦ hx (hf x h))
  exact fun x hx ↦ hδ.trans_le (hs hx)

end SobolevSpace.VectorValued.HalfSpace
