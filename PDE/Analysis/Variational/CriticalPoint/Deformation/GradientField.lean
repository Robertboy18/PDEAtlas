/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.CriticalPoint.Deformation.Cutoff
public import PDE.Analysis.Calculus.Gradient.Bounded
public import PDE.Analysis.Normed.Module.Ball.RadialProjection

/-!
# The bounded descending gradient field

We multiply the radial projection `radialProjection` of the gradient onto the unit ball by
an energy-band cutoff. The resulting field has speed at most one. A Lipschitz gradient on
each ball makes the energy Lipschitz there, by the mean value theorem on the convex ball, so
the cutoff field is also Lipschitz on each ball, which is what the global-flow construction
needs. This is the field `V(u) = -g(u) h(‖I'[u]‖) I'[u]` of (10) in step 2 of the proof of
Evans, §8.5.1, Theorem 1: `radialProjection 1 v` is `h(‖v‖) v` with `h` as in his (9), and
`energyBandCutoff` replaces his `g`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.1(a), step 2 of the proof of Theorem 1
  (Deformation Theorem), (8)-(10), p. 504. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Gradient

open Metric Set

namespace PDE.Analysis.Variational

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The negative gradient, projected onto the unit ball and cut off in energy. -/
def descendingField (I : H → ℝ) (c δ ε : ℝ) (x : H) : H :=
  -(energyBandCutoff c δ ε (I x) • radialProjection 1 (∇ I x))

/-- The constructed field is bounded everywhere, independently of the state. -/
theorem norm_descendingField_le (I : H → ℝ) (c δ ε : ℝ) (x : H) :
    ‖descendingField I c δ ε x‖ ≤ 1 := by
  have hN : ‖radialProjection 1 (∇ I x)‖ ≤ 1 := by
    simpa using radialProjection_mem_closedBall (E := H) zero_lt_one (∇ I x)
  rw [descendingField, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (energyBandCutoff_nonneg c δ ε (I x))]
  calc
    _ ≤ 1 * 1 := mul_le_mul (energyBandCutoff_le_one c δ ε (I x)) hN
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- States outside the outer energy band are stationary for this field. -/
theorem descendingField_eq_zero {I : H → ℝ} {c δ ε : ℝ} (hδε : δ < ε) {x : H}
    (hx : ε ≤ |I x - c|) : descendingField I c δ ε x = 0 := by
  simp only [descendingField, energyBandCutoff_eq_zero hδε hx, zero_smul, neg_zero]

/-- On a ball, the cutoff field has a Lipschitz constant depending only on the
gradient's Lipschitz bound, its value at the center, and the band widths. -/
theorem lipschitzOnWith_descendingField {I : H → ℝ} (hI : Differentiable ℝ I)
    {R K : NNReal} (hG : LipschitzOnWith K (∇ I) (closedBall (0 : H) R))
    (c δ ε : ℝ) :
    LipschitzOnWith
      (2 * K + ‖(ε - δ)⁻¹‖₊ * (‖∇ I 0‖₊ + K * R))
      (descendingField I c δ ε) (closedBall 0 R) := by
  let N := fun x : H ↦ radialProjection 1 (∇ I x)
  let ρ := fun x : H ↦ energyBandCutoff c δ ε (I x)
  have hN := (lipschitzWith_radialProjection (E := H) zero_lt_one).comp_lipschitzOnWith hG
  have hρ := (lipschitzWith_energyBandCutoff c δ ε).comp_lipschitzOnWith
    (lipschitzOnWith_of_gradient_lipschitzOn_closedBall hI hG)
  have hNnorm (x : H) : ‖N x‖ ≤ 1 := by
    simpa [N] using radialProjection_mem_closedBall (E := H) zero_lt_one (∇ I x)
  have hρnorm (x : H) : ‖ρ x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (energyBandCutoff_nonneg c δ ε (I x))]
    exact energyBandCutoff_le_one c δ ε (I x)
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro x hx y hy
  have hdecomp : ρ x • N x - ρ y • N y =
      ρ x • (N x - N y) + (ρ x - ρ y) • N y := by
    simp only [smul_sub, sub_smul]
    abel
  change ‖-(ρ x • N x) - -(ρ y • N y)‖ ≤ _
  rw [neg_sub_neg, norm_sub_rev, hdecomp]
  calc
    _ ≤ ‖ρ x • (N x - N y)‖ + ‖(ρ x - ρ y) • N y‖ := norm_add_le _ _
    _ ≤ ‖N x - N y‖ + ‖ρ x - ρ y‖ := by
      rw [norm_smul, norm_smul]
      exact add_le_add
        (by simpa using mul_le_mul_of_nonneg_right (hρnorm x) (norm_nonneg (N x - N y)))
        (by simpa using mul_le_mul_of_nonneg_left (hNnorm y) (norm_nonneg (ρ x - ρ y)))
    _ ≤ (2 * (K : ℝ)) * ‖x - y‖ +
        (‖(ε - δ)⁻¹‖ * (‖∇ I 0‖ + (K : ℝ) * R)) * ‖x - y‖ :=
      add_le_add (hN.norm_sub_le hx hy) (hρ.norm_sub_le hx hy)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat,
      coe_nnnorm, add_mul]

/-- Raw Lipschitz bounds for the gradient on balls pass to the bounded cutoff field. -/
theorem descendingField_lipschitzOn_balls {I : H → ℝ} (hI : Differentiable ℝ I)
    (hG : ∀ R : ℝ, 0 < R →
      ∃ K : NNReal, LipschitzOnWith K (∇ I) (closedBall 0 R))
    (c δ ε : ℝ) :
    ∀ R : ℝ, 0 < R →
      ∃ K : NNReal, LipschitzOnWith K (descendingField I c δ ε) (closedBall 0 R) := by
  intro R hR
  obtain ⟨K, hK⟩ := hG R hR
  exact ⟨_, lipschitzOnWith_descendingField (R := ⟨R, hR.le⟩) hI hK c δ ε⟩

end PDE.Analysis.Variational
