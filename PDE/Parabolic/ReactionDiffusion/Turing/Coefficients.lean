/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CAS.ExactTactic

/-!
# Two-species coefficients for diffusion-driven instability

For `u_t = d₁ u_xx + a u + b v`, `v_t = d₂ v_xx + c u + d v`, a Fourier mode of squared wave number
`μ` sees the matrix `A - μ diag(d₁,d₂)` (`Coefficients.modeMatrix`). The conditions `Conditions` use
only the six scalar coefficients. They make `A` stable and make the determinant of the mode matrix
negative at the squared wave number `Coefficients.selectedFrequencySq` (`selected_mode_det_neg`),
and they force a nonzero coupling `b` (`coupling_ne_zero`). SymLean's `cas` tactic verifies the
completed-square identity `selected_mode_det`.

In Evans's notation in §4.1.2, the reaction matrix is `Df(0)` with entries `α, β, γ, δ`, the
diffusion matrix is `A = diag(a₁, a₂)`, and the mode matrix is `A_j = Df(0) - λ_j A`, (25). The
conditions `trace_neg` and `det_pos` are his stability conditions (27). The determinant of the mode
matrix at `μ` is his polynomial `p(μ)`, (29); `weighted_trace_pos` and `discriminant_pos` make its
minimum, attained at `selectedFrequencySq`, negative, a strict form of his threshold condition (30).
Evans allows `a₁, a₂ ≥ 0`; `Conditions` requires positive diffusivities.

The chosen wave number is available on the line or on a suitably sized interval; a prescribed
bounded domain must also have a Laplacian eigenvalue in the unstable band.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.2 (Application: Turing instability), (25)-(30),
  pp. 173-174.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace ReactionDiffusion.Turing

/-- The four entries of the reaction matrix and the two diagonal diffusivities. -/
structure Coefficients where
  /-- The first component's reaction coefficient in its own equation. -/
  a : ℝ
  /-- Coupling from the second component into the first equation. -/
  b : ℝ
  /-- Coupling from the first component into the second equation. -/
  c : ℝ
  /-- The second component's reaction coefficient in its own equation. -/
  d : ℝ
  /-- The first component's diffusivity. Positivity is part of `Conditions`. -/
  diffusion₁ : ℝ
  /-- The second component's diffusivity. Positivity is part of `Conditions`. -/
  diffusion₂ : ℝ

/-- The reaction matrix of the spatially homogeneous linear system. -/
def Coefficients.reactionMatrix (C : Coefficients) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![C.a, C.b; C.c, C.d]

/-- The matrix acting on a Laplacian mode with eigenvalue `-μ`. -/
def Coefficients.modeMatrix (C : Coefficients) (μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![C.a - C.diffusion₁ * μ, C.b; C.c, C.d - C.diffusion₂ * μ]

/-- Raw strict Turing conditions: stable reaction, positive diffusion, and a
negative minimum of the mode determinant at a positive squared wave number. The first two
are Evans's stability conditions (27) in §4.1.2. -/
structure Conditions (C : Coefficients) : Prop where
  trace_neg : C.a + C.d < 0
  det_pos : 0 < C.a * C.d - C.b * C.c
  diffusion₁_pos : 0 < C.diffusion₁
  diffusion₂_pos : 0 < C.diffusion₂
  weighted_trace_pos : 0 < C.a * C.diffusion₂ + C.d * C.diffusion₁
  discriminant_pos :
    4 * C.diffusion₁ * C.diffusion₂ * (C.a * C.d - C.b * C.c) <
      (C.a * C.diffusion₂ + C.d * C.diffusion₁) ^ 2

/-- The squared wave number minimizing the determinant of the mode matrix.
This need not maximize the positive growth rate. -/
noncomputable def Coefficients.selectedFrequencySq (C : Coefficients) : ℝ :=
  (C.a * C.diffusion₂ + C.d * C.diffusion₁) / (2 * C.diffusion₁ * C.diffusion₂)

/-- The selected mode has a nonzero spatial frequency. -/
theorem selectedFrequencySq_pos {C : Coefficients} (h : Conditions C) :
    0 < C.selectedFrequencySq := by
  exact div_pos h.weighted_trace_pos
    (mul_pos (mul_pos (by norm_num) h.diffusion₁_pos) h.diffusion₂_pos)

/-- The determinant at the selected wave number, in its completed-square form. -/
theorem selected_mode_det {C : Coefficients} (h : Conditions C) :
    (C.modeMatrix C.selectedFrequencySq).det =
      C.a * C.d - C.b * C.c -
        (C.a * C.diffusion₂ + C.d * C.diffusion₁) ^ 2 /
          (4 * C.diffusion₁ * C.diffusion₂) := by
  have h₁ := ne_of_gt h.diffusion₁_pos
  have h₂ := ne_of_gt h.diffusion₂_pos
  simp only [Coefficients.modeMatrix, Matrix.det_fin_two]
  unfold Coefficients.selectedFrequencySq
  cas

/-- Diffusion gives a negative mode determinant, derived from the raw coefficients. -/
theorem selected_mode_det_neg {C : Coefficients} (h : Conditions C) :
    (C.modeMatrix C.selectedFrequencySq).det < 0 := by
  rw [selected_mode_det h]
  have hden : 0 < 4 * C.diffusion₁ * C.diffusion₂ :=
    mul_pos (mul_pos (by norm_num) h.diffusion₁_pos) h.diffusion₂_pos
  have hquot :
      C.a * C.d - C.b * C.c <
        (C.a * C.diffusion₂ + C.d * C.diffusion₁) ^ 2 /
          (4 * C.diffusion₁ * C.diffusion₂) := by
    apply (lt_div_iff₀ hden).2
    nlinarith [h.discriminant_pos]
  linarith

/-- Strict Turing conditions force a nonzero coupling in the first equation. -/
theorem coupling_ne_zero {C : Coefficients} (h : Conditions C) : C.b ≠ 0 := by
  intro hb
  have had : 0 < C.a * C.d := by simpa [hb] using h.det_pos
  have ha : C.a < 0 := by
    by_contra hna
    have ha0 : 0 ≤ C.a := le_of_not_gt hna
    have hd0 : C.d < 0 := by linarith [h.trace_neg]
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha0 hd0.le)) had
  have hd : C.d < 0 := by
    by_contra hnd
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg ha.le (le_of_not_gt hnd))) had
  have haD := mul_neg_of_neg_of_pos ha h.diffusion₂_pos
  have hdD := mul_neg_of_neg_of_pos hd h.diffusion₁_pos
  linarith [h.weighted_trace_pos]

end ReactionDiffusion.Turing
