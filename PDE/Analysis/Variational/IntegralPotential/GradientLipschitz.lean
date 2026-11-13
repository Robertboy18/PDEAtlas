/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.IntegralPotential.Hilbert
public import PDE.Analysis.MeasureTheory.Lp.Superposition.ConjugateDifference

/-!
# Bounded-ball Lipschitz continuity of integral-energy gradients

The derivative growth of the scalar reaction gives a conjugate-space
superposition estimate. Composing with the inclusion and its Riesz lift gives
the bounded-ball Lipschitz hypothesis of the Hilbert mountain-pass theorem. This is the end
of step 3 of the proof of Evans, §8.5.2, Theorem 3, where the bound (23) on `f'` shows that
`I₂'` is Lipschitz on bounded sets, so that `I` belongs to the class `C` of §8.5.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.2, the growth conditions (23), p. 507, and step 3
  of the proof of Theorem 3 (Existence), p. 509. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ENNReal

namespace PDE.Analysis.Variational.IntegralPotential

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure α} [IsFiniteMeasure μ]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
  {G g dg : ℝ → ℝ} {A B C D : ℝ}

include q in
/-- First-derivative power growth of the reaction implies that the
Hilbert gradient is Lipschitz on each bounded ball. -/
theorem exists_lipschitzOnWith_gradient_energy
    (J : H →L[ℝ] Lp ℝ p μ) (hp2 : 2 < p.toReal)
    (hd : ∀ z, HasDerivAt G (g z) z) (hc : Continuous g)
    (hG : ∀ z, |G z| ≤ A + B * |z| ^ p.toReal)
    (hg : ∀ z, |g z| ≤ C * (1 + |z| ^ (p.toReal - 1)))
    (hdg : ∀ z, HasDerivAt g (dg z) z)
    (hbound : ∀ z, ‖dg z‖ ≤ D * (1 + ‖z‖ ^ (p.toReal - 2)))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : NNReal, LipschitzOnWith K (∇ (energy J G))
      (Metric.closedBall 0 R) := by
  have hp_top : p ≠ ∞ := by
    rintro rfl
    norm_num at hp2
  have hp : 1 < p := by
    by_contra h
    have := ENNReal.toReal_mono ENNReal.one_ne_top (not_lt.mp h)
    rw [ENNReal.toReal_one] at this
    linarith
  have hD : 0 ≤ D := by
    have h0 := hbound 0
    rw [norm_zero, Real.zero_rpow (by linarith), add_zero, mul_one] at h0
    exact (norm_nonneg _).trans h0
  let N := Lp.superposition (fun _ : α ↦ g)
    (memLp_comp_of_conjugate_growth (μ := μ) (q := q) hc hg)
  obtain ⟨K, hK⟩ := Lp.exists_lipschitzOnWith_superposition_of_deriv_growth
    hp_top hp2 hD hdg hbound
    (memLp_comp_of_conjugate_growth (μ := μ) (q := q) hc hg)
    (mul_nonneg (norm_nonneg J) hR)
  refine ⟨1 + ‖dualLift (q := q) J‖₊ * K * ‖J‖₊, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  have hJu : J u ∈ Metric.closedBall 0 (‖J‖ * R) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (J.le_opNorm u).trans (mul_le_mul_of_nonneg_left
      (by simpa using hu) (norm_nonneg J))
  have hJv : J v ∈ Metric.closedBall 0 (‖J‖ * R) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (J.le_opNorm v).trans (mul_le_mul_of_nonneg_left
      (by simpa using hv) (norm_nonneg J))
  have hN : ‖N (J u) - N (J v)‖ ≤ K * ‖J‖ * ‖u - v‖ := by
    calc
      ‖N (J u) - N (J v)‖ ≤ K * ‖J u - J v‖ :=
        hK.norm_sub_le hJu hJv
      _ ≤ K * (‖J‖ * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [map_sub] using J.le_opNorm (u - v))
          K.coe_nonneg
      _ = _ := (mul_assoc _ _ _).symm
  rw [dist_eq_norm, gradient_energy (q := q) J hp hp_top hd hc hG hg,
    gradient_energy (q := q) J hp hp_top hd hc hG hg, dist_eq_norm]
  change ‖(u - dualLift J (N (J u))) - (v - dualLift J (N (J v)))‖ ≤ _
  rw [sub_sub_sub_comm, ← map_sub]
  calc
    _ ≤ ‖u - v‖ + ‖dualLift (q := q) J (N (J u) - N (J v))‖ :=
      norm_sub_le _ _
    _ ≤ ‖u - v‖ + ‖dualLift (q := q) J‖ * (K * ‖J‖ * ‖u - v‖) :=
      add_le_add le_rfl (((dualLift J).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hN (norm_nonneg _)))
    _ = _ := by
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, coe_nnnorm]
      ring

end PDE.Analysis.Variational.IntegralPotential
