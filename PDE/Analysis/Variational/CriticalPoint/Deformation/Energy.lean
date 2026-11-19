/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.CriticalPoint.Deformation.GradientField
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Energy decrease along the constructed field

The derivative of the energy is the inner product of its gradient with the descending
field. It is nonpositive everywhere. In the inner band, a positive gradient gap makes
it uniformly negative. If a trajectory starting below the upper inner level failed to
reach the lower one by time one, monotonicity would keep its whole unit interval in
that band, contradicting the mean-value estimate. These are steps 4 and 5 of the proof of
Evans, §8.5.1, Theorem 1: `fderiv_apply_descendingField` is the computation (12),
`antitone_energy_of_descendingField` gives his assertion (iii),
`fderiv_descendingField_le_neg_sq` is the bound by `-σ²` that he derives from (9) and (4),
and `energy_drop_of_descendingField` is (14), under his condition (7), `2δ < σ²`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.1(a), steps 4 and 5 of the proof of Theorem 1
  (Deformation Theorem), (12)-(15), pp. 504-505. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

open Set
open scoped RealInnerProductSpace

namespace PDE.Analysis.Variational

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The exact dissipation rate for the radially bounded, cut-off gradient field. -/
theorem fderiv_apply_descendingField (I : H → ℝ) (c δ ε : ℝ) (x : H) :
    fderiv ℝ I x (descendingField I c δ ε x) =
      -(energyBandCutoff c δ ε (I x) *
        ((1 / max 1 ‖∇ I x‖) * ‖∇ I x‖ ^ 2)) := by
  rw [← inner_gradient_left]
  unfold descendingField radialProjection
  simp only [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]

/-- The energy derivative in the descending direction is nonpositive everywhere. -/
theorem fderiv_descendingField_nonpos (I : H → ℝ) (c δ ε : ℝ) (x : H) :
    fderiv ℝ I x (descendingField I c δ ε x) ≤ 0 := by
  rw [fderiv_apply_descendingField]
  exact neg_nonpos.mpr (mul_nonneg (energyBandCutoff_nonneg c δ ε (I x))
    (mul_nonneg (div_nonneg zero_le_one ((le_max_left _ _).trans' zero_le_one))
      (sq_nonneg _)))

/-- Within the inner plateau, a gradient gap below one gives a uniform energy
derivative bound by the negative square of that gap. -/
theorem fderiv_descendingField_le_neg_sq {I : H → ℝ} {c δ ε σ : ℝ}
    (hδε : δ < ε) (hσ : σ ∈ Ioo (0 : ℝ) 1) {x : H}
    (hx : |I x - c| ≤ δ) (hG : σ ≤ ‖∇ I x‖) :
    fderiv ℝ I x (descendingField I c δ ε x) ≤ -(σ ^ 2) := by
  rw [fderiv_apply_descendingField, energyBandCutoff_eq_one hδε hx, one_mul]
  apply neg_le_neg
  by_cases hn : ‖∇ I x‖ ≤ 1
  · rw [max_eq_left hn, div_one, one_mul]
    exact sq_le_sq₀ hσ.1.le (norm_nonneg _) |>.mpr hG
  · have hn' : 1 ≤ ‖∇ I x‖ := (lt_of_not_ge hn).le
    have hne : ‖∇ I x‖ ≠ 0 := (zero_lt_one.trans_le hn').ne'
    rw [max_eq_right hn', pow_two ‖∇ I x‖, ← mul_assoc,
      div_mul_cancel₀ _ hne, one_mul]
    have hs : σ ^ 2 ≤ σ := by
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hσ.2.le hσ.1.le
    exact hs.trans hG

/-- Every solution of the descending-field ODE has nonincreasing energy. -/
theorem antitone_energy_of_descendingField {I : H → ℝ} (hI : Differentiable ℝ I)
    {c δ ε : ℝ} {u : ℝ → H}
    (hu : ∀ t, HasDerivAt u (descendingField I c δ ε (u t)) t) :
    Antitone (I ∘ u) := by
  apply antitone_of_hasDerivAt_nonpos
    (fun t ↦ (hI (u t)).hasFDerivAt.comp_hasDerivAt t (hu t))
  intro t
  exact fderiv_descendingField_nonpos I c δ ε (u t)

/-- A unit-time trajectory drops from the upper to the lower inner sublevel whenever
the band width is smaller than the available uniform dissipation. -/
theorem energy_drop_of_descendingField {I : H → ℝ} (hI : Differentiable ℝ I)
    {c δ ε σ : ℝ} (hδε : δ < ε) (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (hwidth : 2 * δ < σ ^ 2)
    (hgap : ∀ x, |I x - c| ≤ δ → σ ≤ ‖∇ I x‖)
    {u : ℝ → H} (hu : ∀ t, HasDerivAt u (descendingField I c δ ε (u t)) t)
    (hstart : I (u 0) ≤ c + δ) : I (u 1) ≤ c - δ := by
  by_contra! hend
  have hm := antitone_energy_of_descendingField hI hu
  have hd (t : ℝ) :=
    (hI (u t)).hasFDerivAt.comp_hasDerivAt t (hu t)
  have hband (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |I (u t) - c| ≤ δ := by
    have hlo := hm ht.2
    have hhi := hm ht.1
    change I (u 1) ≤ I (u t) at hlo
    change I (u t) ≤ I (u 0) at hhi
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hdiff : Differentiable ℝ (I ∘ u) := fun t ↦ (hd t).differentiableAt
  have hdrop := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (C := -(σ ^ 2)) (fun t ht ↦ by
      rw [(hd t).deriv]
      exact fderiv_descendingField_le_neg_sq hδε hσ
        (hband t (interior_subset ht)) (hgap _ (hband t (interior_subset ht))))
    0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [Function.comp_apply, sub_zero, mul_one] at hdrop
  linarith

end PDE.Analysis.Variational
