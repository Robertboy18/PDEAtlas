/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Deriv.PowerGrowth
public import PDE.Analysis.MeasureTheory.Lp.Superposition.PowerDifference

/-!
# Local Lipschitz bounds into a conjugate Lebesgue space

For `p > 2`, a scalar first derivative of growth `1 + |z|^(p - 2)`
makes superposition locally Lipschitz from `Lᵖ` to its conjugate space.
The proof retains the constant offset through the finite-measure norm estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- A first-derivative power bound gives Lipschitz continuity on every bounded
`Lᵖ` ball, with values in the conjugate space. No Hessian of the superposition
operator is assumed. -/
theorem exists_lipschitzOnWith_superposition_of_deriv_growth
    (hp : p ≠ ∞) (hp2 : 2 < p.toReal) {C : ℝ} (hC : 0 ≤ C)
    {g dg : ℝ → ℝ} (hd : ∀ z, HasDerivAt g (dg z) z)
    (hbound : ∀ z, ‖dg z‖ ≤ C * (1 + ‖z‖ ^ (p.toReal - 2)))
    (hmem : ∀ u : Lp ℝ p μ, MemLp (fun x ↦ g (u x)) q μ)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : NNReal, LipschitzOnWith K (superposition (fun _ ↦ g) hmem)
      (Metric.closedBall 0 R) := by
  have hr : 1 < p.toReal - 1 := by linarith
  have hs : 0 < p.toReal - 1 - 1 := by linarith
  have he : p.toReal - 1 - 1 = p.toReal - 2 := by ring
  have ht : 1 ≤ p / ENNReal.ofReal (p.toReal - 1 - 1) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
      (Or.inl ENNReal.ofReal_ne_top)).mpr
    rw [one_mul]
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans_eq (ENNReal.ofReal_toReal hp)
  let : Fact (1 ≤ p / ENNReal.ofReal (p.toReal - 1 - 1)) := ⟨ht⟩
  have hg (x y : ℝ) :
      ‖g x - g y‖ ≤
        (C + C * (‖x‖ + ‖y‖) ^ (p.toReal - 1 - 1)) * ‖x - y‖ := by
    rw [he]
    exact PDE.Analysis.norm_sub_le_of_deriv_power_growth
      hC (by linarith) hd hbound x y
  exact ⟨_, lipschitzOnWith_superposition_of_twoPointGrowth_add_const
    hp hr (ENNReal.HolderConjugate.div_ofReal_toReal_sub_one p q hp)
    hC hC hmem hg hR⟩

end MeasureTheory.Lp
