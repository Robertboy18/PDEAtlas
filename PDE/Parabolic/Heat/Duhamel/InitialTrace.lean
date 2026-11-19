/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.Representation

/-!
# Initial trace of the Duhamel source term

Positivity and unit mass of the heat kernel bound the source contribution by `M t`
when the source is bounded by `M`. This gives convergence to zero as `t ↓ 0`, uniformly
in space. Only nonnegative source times enter the estimate, which holds for the totalized
integral without any source-time integrability.
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise Topology Interval
open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- A bounded source contributes at most `M t` to the Duhamel solution.

The spatial convolution bound follows from positivity and unit mass of the heat kernel.
The totalized Bochner integral satisfies the bound even when source-time integrability
fails. -/
theorem abs_nonhomogeneousSolution_le_mul_time
    (f : ℝ^(n + 1) → ℝ) (M : ℝ)
    (hf_cont : ∀ s : ℝ, 0 ≤ s →
      Continuous fun y : ℝ^n ↦
        f (timeSpaceCons (n := n) s y))
    (hf_bound : ∀ (s : ℝ), 0 ≤ s → ∀ y : ℝ^n,
      |f (timeSpaceCons (n := n) s y)| ≤ M)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    |nonhomogeneousSolution (n := n) f x t| ≤ M * t := by
  rw [nonhomogeneousSolution_eq_integral_initialValueSolution (n := n) f x t ht]
  have hconst : IntegrableOn (fun _s : ℝ ↦ M) (Set.Icc 0 t) :=
    integrableOn_const measure_Icc_lt_top.ne
  have hpoint :
      ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)),
        ‖initialValueSolution (n := n)
            (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) s y))
            x (t - s)‖ ≤ M := by
    refine ae_restrict_of_forall_mem measurableSet_Icc ?_
    intro s hs
    simpa [Real.norm_eq_abs] using
      abs_initialValueSolution_le (n := n)
        (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) s y))
        (hf_cont s hs.1) (hf_bound s hs.1) x (t - s)
  calc
    |∫ s in Set.Icc 0 t,
        initialValueSolution (n := n)
          (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) s y))
          x (t - s)| =
        ‖∫ s in Set.Icc 0 t,
          initialValueSolution (n := n)
            (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) s y))
            x (t - s)‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ _s in Set.Icc 0 t, M :=
      norm_integral_le_of_norm_le hconst hpoint
    _ = M * t := by
      simp [ht.le, smul_eq_mul, mul_comm]

/-- Uniform right-time initial trace of the Duhamel term for bounded forcing.

The conclusion is uniform in space: for all sufficiently small `t > 0`, the source contribution
is smaller than `ε` at every spatial point. -/
theorem nonhomogeneousSolution_uniform_initial_trace
    (f : ℝ^(n + 1) → ℝ) (M : ℝ)
    (hf_cont : ∀ s : ℝ, 0 ≤ s →
      Continuous fun y : ℝ^n ↦
        f (timeSpaceCons (n := n) s y))
    (hf_bound : ∀ (s : ℝ), 0 ≤ s → ∀ y : ℝ^n,
      |f (timeSpaceCons (n := n) s y)| ≤ M) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (x : ℝ^n) (t : ℝ),
          0 < t → t < δ → |nonhomogeneousSolution (n := n) f x t| < ε := by
  have hM : 0 ≤ M := by
    exact (abs_nonneg (f (timeSpaceCons (n := n) 0 0))).trans (hf_bound 0 le_rfl 0)
  intro ε hε
  have hM1 : 0 < M + 1 := by linarith
  refine ⟨ε / (M + 1), div_pos hε hM1, ?_⟩
  intro x t ht htδ
  have hbound :=
    abs_nonhomogeneousSolution_le_mul_time (n := n) f M hf_cont hf_bound x t ht
  have htM1 : t * (M + 1) < ε := (lt_div_iff₀ hM1).mp htδ
  have hMt : M * t ≤ t * (M + 1) := by
    nlinarith
  exact hbound.trans_lt (hMt.trans_lt htM1)

end HeatEquation
