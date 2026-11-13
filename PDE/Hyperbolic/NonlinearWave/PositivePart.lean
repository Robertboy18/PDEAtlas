/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PositivePart.ZeroJet
public import PDE.Hyperbolic.Classical.ForwardLocalization

/-!
# Positive parts of classical semilinear waves

If a C² scalar field has zero full first derivative at every nearby zero, its
positive part is C² by `PDE.Analysis.contDiffAt_two_max_zero_of_zero_jet`.
For a reaction with `f 0 = 0`, the positive part satisfies the wave equation
with reaction `z ↦ f (max z 0)` wherever the original field satisfies its equation.

The proof uses the original or zero germ at locally one-sided points and the
vanishing Hessian at the remaining zeros. A quadratic minimum can retain its nonzero Hessian.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace WaveEquation

/-- A vanishing Hessian annihilates the coordinate wave operator. -/
theorem waveOperator_eq_zero_of_second_fderiv_eq_zero {n : ℕ} {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) p) (hH : fderiv ℝ (fderiv ℝ u) p = 0) :
    waveOperator u p = 0 := by
  simp only [waveOperator, PDE.secondPartialDeriv_eq_fderiv _ _ hu, hH,
    zero_apply, Finset.sum_const_zero, sub_zero]

/-- The positive part solves the sign-truncated reaction equation when nearby zeros
have zero full first jet. -/
theorem semilinearWave_max_zero_of_zero_jet {n : ℕ} {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)} {f : ℝ → ℝ}
    (hu : ContDiffAt ℝ 2 u p) (hz : ∀ᶠ q in 𝓝 p, u q = 0 → fderiv ℝ u q = 0) (hf : f 0 = 0)
    (heq : waveOperator u p + f (u p) = 0) :
    waveOperator (fun q ↦ max (u q) 0) p + f (max (max (u p) 0) 0) = 0 := by
  rcases PDE.Analysis.max_zero_germ_or_flat hu hz with h | h | ⟨hp, hH⟩
  · have hvalue : max (u p) 0 = u p := h.self_of_nhds
    rw [max_assoc, max_self, waveOperator_congr_nhds h, hvalue]
    exact heq
  · have hvalue : max (u p) 0 = 0 := h.self_of_nhds
    rw [max_assoc, max_self, waveOperator_congr_nhds h, waveOperator_const, hvalue, hf, add_zero]
  · have hd := PDE.Analysis.hasFDerivAt_fderiv_max_zero_of_second_zero hu hp hz hH
    rw [waveOperator_eq_zero_of_second_fderiv_eq_zero hd.differentiableAt hd.fderiv]
    simp only [hp, max_self, hf, add_zero]

end WaveEquation
