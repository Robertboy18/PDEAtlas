/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.AutoDiff.Optimization

/-!
# PDE residual losses

Finite sampled losses built from the totalized expression `LinearPDE.residual`, and repeated
gradient-descent updates. The loss `∑ₓ (P u)(x)²` over a finite sample is defined for every
field `u`; it equals the classical squared residual when `u` is `C^k`.

## Main results

* `sampledLoss_nonneg`, `sampledLoss_eq_zero_iff`: the sampled loss is nonnegative and
  vanishes exactly when the residual vanishes at every sample point.
* `gradientDescent_eq_initial`: a critical initial parameter is fixed by every number of
  gradient-descent updates.
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace PDE.AutoDiff.ResidualLoss

/-- Square of the totalized pointwise residual expression of a linear PDE.

This objective is defined for every field. Reading the value as a classical order-`k` PDE
residual requires `C^k` regularity of the field. -/
def pointwiseEnergy {n k : ℕ}
    (pde : LinearPDE ℝ (ℝ^n) ℝ k)
    (u : ℝ^n → ℝ)
    (x : ℝ^n) : ℝ :=
  (pde.residual u x) ^ (2 : Nat)

/-- Sum of squared totalized residual expressions over a finite sample. -/
def sampledLoss {n k : ℕ}
    (pde : LinearPDE ℝ (ℝ^n) ℝ k)
    (u : ℝ^n → ℝ)
    (samples : List (ℝ^n)) : ℝ :=
  (samples.map (pointwiseEnergy pde u)).sum

/-- Every pointwise residual energy is nonnegative, including at nonsmooth fields
where the residual expression uses total derivatives. -/
theorem pointwiseEnergy_nonneg {n k : ℕ}
    (pde : LinearPDE ℝ (ℝ^n) ℝ k) (u : ℝ^n → ℝ) (x : ℝ^n) :
    0 ≤ pointwiseEnergy pde u x :=
  sq_nonneg _

/-- A finite sample of squared residuals has nonnegative loss. -/
theorem sampledLoss_nonneg {n k : ℕ}
    (pde : LinearPDE ℝ (ℝ^n) ℝ k) (u : ℝ^n → ℝ) (samples : List (ℝ^n)) :
    0 ≤ sampledLoss pde u samples := by
  apply List.sum_nonneg
  intro energy henergy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp henergy
  exact pointwiseEnergy_nonneg pde u x

/-- Zero sampled loss is equivalent to vanishing residual at every sampled point. -/
theorem sampledLoss_eq_zero_iff {n k : ℕ}
    (pde : LinearPDE ℝ (ℝ^n) ℝ k) (u : ℝ^n → ℝ) (samples : List (ℝ^n)) :
    sampledLoss pde u samples = 0 ↔ ∀ x ∈ samples, pde.residual u x = 0 := by
  induction samples with
  | nil => simp [sampledLoss]
  | cons x samples ih =>
      change pointwiseEnergy pde u x + sampledLoss pde u samples = 0 ↔ _
      rw [add_eq_zero_iff_of_nonneg (pointwiseEnergy_nonneg pde u x)
        (sampledLoss_nonneg pde u samples), ih]
      simp [pointwiseEnergy]

/-- Apply a fixed number of gradient-descent updates. -/
def gradientDescent {Θ : Type*}
    [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    [CompleteSpace Θ]
    (loss : Θ → ℝ) (initial : Θ) (stepSize : ℝ) (iterations : ℕ) : Θ :=
  Nat.rec initial
    (fun _ θ ↦ Optimization.gradientDescentStep loss θ stepSize)
    iterations

/-- A critical initial parameter remains fixed under every finite number of updates. -/
theorem gradientDescent_eq_initial {Θ : Type*}
    [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (loss : Θ → ℝ) (initial : Θ) (stepSize : ℝ) (iterations : ℕ)
    (h : ∇ loss initial = 0) :
    gradientDescent loss initial stepSize iterations = initial := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
      change Optimization.gradientDescentStep loss
        (gradientDescent loss initial stepSize iterations) stepSize = initial
      rw [ih, Optimization.gradientDescentStep_eq_self loss initial stepSize h]

end PDE.AutoDiff.ResidualLoss
