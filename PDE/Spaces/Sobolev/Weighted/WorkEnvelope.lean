/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Common envelopes for finite families of weighted work

Common spatial `L²` majorants `W i` and `V i` for `w t i * √(Φ i)` and `v t i * √(Φ i)`, valid for
all `t ∈ S` outside one null set, give the integrable envelope `∑ i, ‖V i * W i‖` for the total work
`∑ i, v t i * w t i * Φ i` (`integrable_work_envelope_of_memLp`). Mathlib's
`MeasureTheory.MemLp.integrable_mul` gives the integrability of each product. The measure is
arbitrary and the weights `Φ i` may vanish or be unbounded.

With `S` a time neighborhood, this gives the integrable bound used for differentiation under the
integral sign. The criterion is only sufficient: uniform-in-time `L²` bounds do not give common
majorants, and an integrable bound on the total work can exist without `L²` majorants for its
factors. The evolution equation and the measurability and integrability of the base energy are
separate inputs.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SobolevSpace.Weighted

/-- If `Φ i ≥ 0` a.e., `W i` and `V i` are in `L²(μ)`, and for a.e. `x` we have
`‖w t i x * √(Φ i x)‖ ≤ ‖W i x‖` and `‖v t i x * √(Φ i x)‖ ≤ ‖V i x‖` for all `t ∈ S` and `i`, then
`x ↦ ∑ i, ‖V i x * W i x‖` is integrable and for a.e. `x` it bounds
`‖∑ i, v t i x * w t i x * Φ i x‖` for every `t ∈ S`. Nothing is claimed about the measurability or
time-differentiability of `w` or `v`. -/
theorem integrable_work_envelope_of_memLp
    {α τ ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    (Φ : ι → α → ℝ) (w v : τ → ι → α → ℝ) (W V : ι → α → ℝ) {S : Set τ}
    (hΦ : ∀ i, 0 ≤ᵐ[μ] Φ i)
    (hW : ∀ i, MemLp (W i) 2 μ) (hV : ∀ i, MemLp (V i) 2 μ)
    (hw : ∀ᵐ x ∂μ, ∀ t ∈ S, ∀ i,
      ‖w t i x * Real.sqrt (Φ i x)‖ ≤ ‖W i x‖)
    (hv : ∀ᵐ x ∂μ, ∀ t ∈ S, ∀ i,
      ‖v t i x * Real.sqrt (Φ i x)‖ ≤ ‖V i x‖) :
    Integrable (fun x ↦ ∑ i, ‖V i x * W i x‖) μ ∧
      ∀ᵐ x ∂μ, ∀ t ∈ S,
        ‖∑ i, v t i x * w t i x * Φ i x‖ ≤ ∑ i, ‖V i x * W i x‖ := by
  constructor
  · exact integrable_finsetSum Finset.univ
      fun i _ ↦ ((hV i).integrable_mul (hW i)).norm
  · filter_upwards [ae_all_iff.2 hΦ, hw, hv] with x hΦx hwx hvx
    intro t ht
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    calc
      ‖v t i x * w t i x * Φ i x‖ =
          ‖(v t i x * Real.sqrt (Φ i x)) * (w t i x * Real.sqrt (Φ i x))‖ := by
        rw [mul_mul_mul_comm, Real.mul_self_sqrt (hΦx i)]
      _ = ‖v t i x * Real.sqrt (Φ i x)‖ * ‖w t i x * Real.sqrt (Φ i x)‖ :=
        norm_mul _ _
      _ ≤ ‖V i x‖ * ‖W i x‖ :=
        mul_le_mul (hvx t ht i) (hwx t ht i) (norm_nonneg _) (norm_nonneg _)
      _ = ‖V i x * W i x‖ := (norm_mul _ _).symm

end SobolevSpace.Weighted
