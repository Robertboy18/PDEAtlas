/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.WithinExtension

/-!
# Derivatives within a set at interior points

At a point `y` of the interior of a set `s` with unique derivatives, where `F` is `Cᵏ`, the iterated
partial derivative of `F` within `s` along a word `w` with `|w| < k` agrees near `y` with the
ordinary one, so it is differentiable at `y`, and its `i`-th partial derivative there is the
iterated derivative within `s` along `i :: w`.

## Main results

* `iteratedPartialDerivWithin_of_mem_nhds`: at an interior point the `i`-th partial derivative of
  the derivative within `s` along `w` is the derivative within `s` along `i :: w`.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE

variable {n : ℕ} {F : ℝ^n → ℝ} {s : Set (ℝ^n)}

/-- **Iterated derivatives within `s` at interior points.** -/
theorem iteratedPartialDerivWithin_of_mem_nhds (hs : UniqueDiffOn ℝ s) (w : List (Fin n))
    {k : ℕ} (hk : w.length + 1 ≤ k) {y : ℝ^n} (hy : s ∈ 𝓝 y) (hF : ContDiffAt ℝ k F y)
    (i : Fin n) :
    DifferentiableAt ℝ (iteratedPartialDerivWithin w F s) y ∧
      (∂[i] (iteratedPartialDerivWithin w F s)) y = iteratedPartialDerivWithin (i :: w) F s y := by
  have hV : IsOpen {x : ℝ^n | ContDiffAt ℝ k F x} := isOpen_setOf_contDiffAt k
  have heq := eqOn_iteratedPartialDerivWithin_of_contDiffAt (h := F) hs w (k := k) (by omega)
  have hev : iteratedPartialDerivWithin w F s =ᶠ[𝓝 y] iteratedPartialDeriv w F :=
    eventuallyEq_of_mem (inter_mem hy (hV.mem_nhds hF)) heq
  have hreg : ContDiffOn ℝ 1 (iteratedPartialDeriv w F) {x : ℝ^n | ContDiffAt ℝ k F x} :=
    contDiffOn_iteratedPartialDeriv hV w (m := 1)
      ((contDiffOn_setOf_contDiffAt k).of_le (by exact_mod_cast hk))
  have hd : DifferentiableAt ℝ (iteratedPartialDeriv w F) y :=
    ((hreg.differentiableOn one_ne_zero) y hF).differentiableAt (hV.mem_nhds hF)
  refine ⟨hd.congr_of_eventuallyEq hev, ?_⟩
  rw [iteratedPartialDerivWithin_cons, partialDerivWithin_of_mem_nhds i hy]

end PDE
