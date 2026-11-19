/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientSmoothing

/-!
# Exponentially weighted ancient paths

Bounded continuous functions on `(-∞, a]` represent paths with norm
`sup_{t ≤ a} exp (-β * t) * ‖f t‖`. Decoding multiplies by `exp (β * t)` and extends
the path constantly from the terminal time. A continuous path with a proved bound
`‖f t‖ ≤ exp (β * t) * C` for `t ≤ a` is encoded by multiplying by `exp (-β * t)`, and
decoding inverts the encoding on the half-line. The ancient Duhamel operator on these paths
is in `AncientStrong.lean`.

Completeness is inherited from Mathlib's bounded continuous functions, rather
than imposed as an additional hypothesis about a bespoke weighted path space.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction MeasureTheory Set
open scoped BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Decode a path in the backwards exponential weight `β`. Outside the ancient
half-line, the bounded representative is extended constantly from the endpoint. -/
def ancientLift (β : ℝ) {a : ℝ} (u : Iic a →ᵇ F) : C(ℝ, F) where
  toFun s := Real.exp (β * s) • u ⟨min s a, min_le_right _ _⟩
  continuous_toFun := by
    apply (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    exact u.continuous.comp
      ((continuous_id.min continuous_const).subtype_mk (fun s ↦ min_le_right s a))

/-- The decoded path has the exponential bound given by the norm of its
bounded representative. -/
theorem norm_ancientLift_le (β : ℝ) {a : ℝ} (u : Iic a →ᵇ F) (s : ℝ) :
    ‖ancientLift β u s‖ ≤ ‖u‖ * Real.exp (β * s) := by
  rw [ancientLift, ContinuousMap.coe_mk, norm_smul,
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _)
    (Real.exp_nonneg _)).trans_eq (mul_comm _ _)

/-- Encode a continuous path with a proved exponential bound `‖f t‖ ≤ exp (β * t) * C` on
`(-∞, a]` as a bounded continuous function in the backwards weight `β`. -/
def ofAncientBound (β : ℝ) {a : ℝ} (f : C(ℝ, F)) (C : ℝ)
    (hbound : ∀ t ≤ a, ‖f t‖ ≤ Real.exp (β * t) * C) : Iic a →ᵇ F :=
  ofNormedAddCommGroup (fun t ↦ Real.exp (-(β * t)) • f t)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val).neg).smul
      (f.continuous.comp continuous_subtype_val)) C fun t ↦ by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      Real.exp (-(β * t)) * ‖f t‖ ≤ Real.exp (-(β * t)) * (Real.exp (β * t) * C) :=
        mul_le_mul_of_nonneg_left (hbound t t.2) (Real.exp_nonneg _)
      _ = C := by
        rw [Real.exp_neg, ← mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero _), one_mul]

/-- Evaluation of the encoded path. -/
@[simp]
theorem ofAncientBound_apply (β : ℝ) {a : ℝ} (f : C(ℝ, F)) (C : ℝ)
    (hbound : ∀ t ≤ a, ‖f t‖ ≤ Real.exp (β * t) * C) (t : Iic a) :
    ofAncientBound β f C hbound t = Real.exp (-(β * t)) • f t :=
  rfl

/-- The norm of an encoded path is at most its proved growth constant. -/
theorem norm_ofAncientBound_le (β : ℝ) {a : ℝ} (f : C(ℝ, F)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ≤ a, ‖f t‖ ≤ Real.exp (β * t) * C) :
    ‖ofAncientBound β f C hbound‖ ≤ C :=
  norm_ofNormedAddCommGroup_le _ hC _

/-- Decoding an encoded path recovers it on the ancient half-line. -/
theorem ancientLift_ofAncientBound (β : ℝ) {a : ℝ} (f : C(ℝ, F)) (C : ℝ)
    (hbound : ∀ t ≤ a, ‖f t‖ ≤ Real.exp (β * t) * C) {s : ℝ} (hs : s ≤ a) :
    ancientLift β (ofAncientBound β f C hbound) s = f s := by
  rw [ancientLift, ContinuousMap.coe_mk, ofAncientBound_apply]
  simp only [min_eq_left hs]
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

end PDE.Analysis.Evolution
