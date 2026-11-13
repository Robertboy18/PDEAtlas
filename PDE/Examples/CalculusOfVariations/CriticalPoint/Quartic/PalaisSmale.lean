/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.CalculusOfVariations.CriticalPoint.Quartic.Calculus
public import PDE.Analysis.Variational.CriticalPoint.PalaisSmale.Basic
import CAS.ExactTactic

/-!
# Palais–Smale compactness for the quartic energy

The component of the gradient along the unit direction is `2s - 4s³`. Its boundedness
forces the scalar coordinates to remain bounded. Each state is the sum of a multiple
of this direction and half its gradient. A compact scalar interval and the compact
range of the convergent gradients therefore contain all states in a compact image.
The argument works in every Hilbert dimension.
-/

@[expose] public noncomputable section

open Filter Function Metric Set
open scoped RealInnerProductSpace Topology Gradient

namespace PDE.Examples.CriticalPoint.Quartic

/-- The scalar bound `|s| ≤ 1 + |2s - 4s³|`. -/
theorem abs_le_one_add_abs_cubic_residual (s : ℝ) : |s| ≤ 1 + |2 * s - 4 * s ^ 3| := by
  by_cases hp : 1 ≤ s
  · have hs : 0 ≤ s := by cas
    have hs2 : 1 ≤ s ^ 2 := by cas
    have hprod := mul_nonneg hs (sub_nonneg.mpr hs2)
    have hn : 2 * s - 4 * s ^ 3 ≤ 0 := by cas
    rw [abs_of_nonneg hs, abs_of_nonpos hn]
    cas
  by_cases hn : s ≤ -1
  · have hs : s ≤ 0 := by cas
    have hs2 : 1 ≤ s ^ 2 := by cas
    have hprod := mul_nonpos_of_nonpos_of_nonneg hs (sub_nonneg.mpr hs2)
    have hp : 0 ≤ 2 * s - 4 * s ^ 3 := by cas
    rw [abs_of_nonpos hs, abs_of_nonneg hp]
    cas
  have hs : |s| ≤ 1 := abs_le.mpr ⟨by cas, by cas⟩
  exact hs.trans (le_add_of_nonneg_right (abs_nonneg _))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The gradient and the scalar coordinate together determine the state. -/
theorem eq_half_gradient_add (e u : H) :
    u = (1 / 2 : ℝ) • ∇ (energy e) u + (2 * ⟪e, u⟫ ^ 3) • e := by
  rw [gradient_energy, smul_sub, smul_smul, smul_smul]
  have htwo : (1 / 2 : ℝ) * 2 = 1 := by cas
  have hfour : (1 / 2 : ℝ) * (4 * ⟪e, u⟫ ^ 3) = 2 * ⟪e, u⟫ ^ 3 := by cas
  rw [htwo, hfour, one_smul, sub_add_cancel]

/-- For a unit vector `e`, the quartic energy satisfies the Palais–Smale condition. -/
theorem palaisSmale_energy {e : H} (he : ‖e‖ = 1) :
    PDE.Analysis.Variational.PalaisSmale (energy e) := by
  intro u _ hgrad
  obtain ⟨M, hM, hball⟩ :=
    hgrad.cauchySeq.isBounded_range.subset_closedBall_lt 0 (0 : H)
  have hcoord : ∀ n, |⟪e, u n⟫| ≤ 1 + M := by
    intro n
    have hg : ‖∇ (energy e) (u n)‖ ≤ M := by
      simpa using hball (mem_range_self n)
    have hid : 2 * ⟪e, u n⟫ - 4 * ⟪e, u n⟫ ^ 3 =
        ⟪e, ∇ (energy e) (u n)⟫ := by
      simp [gradient_energy, inner_sub_right, inner_smul_right, he]
    have hresidual : |2 * ⟪e, u n⟫ - 4 * ⟪e, u n⟫ ^ 3| ≤ M := by
      rw [hid]
      exact (abs_inner_le_norm he _).trans hg
    exact (abs_le_one_add_abs_cubic_residual _).trans
      (add_le_add (le_refl 1) hresidual)
  let K := Icc (-(1 + M)) (1 + M) ×ˢ insert (0 : H) (range (∇ (energy e) ∘ u))
  have hK : IsCompact K := isCompact_Icc.prod hgrad.isCompact_insert_range
  let F : ℝ × H → H := fun p ↦ (1 / 2 : ℝ) • p.2 + (2 * p.1 ^ 3) • e
  have hF : Continuous F :=
    (continuous_const.smul continuous_snd).add
      ((continuous_const.mul (continuous_fst.pow 3)).smul continuous_const)
  have hcompact : IsCompact (F '' K) := hK.image hF
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact.isClosed
  rintro _ ⟨n, rfl⟩
  refine ⟨(⟪e, u n⟫, ∇ (energy e) (u n)), ?_, ?_⟩
  · exact ⟨abs_le.mp (hcoord n), mem_insert_of_mem _ (mem_range_self n)⟩
  · exact (eq_half_gradient_add e (u n)).symm

end PDE.Examples.CriticalPoint.Quartic
