/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Form.Operator
public import PDE.Elliptic.Variational.ShiftedDivergenceForm
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2

/-!
# The full variational Dirichlet operator

The partial linear map associated with the full Dirichlet form represents `-L`
on `L²`. Its graph is exactly the distributional equation with zero boundary data.
This common elliptic operator can be used in both parabolic and wave generators.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open PDE.Analysis.Evolution
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

variable (hopen : IsOpen Ω)
variable (a : Fin n → Fin n → DerivLp n ∞ Ω)
  (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)

/-- The negative full Dirichlet operator, represented by its variational graph in `L²`. -/
def negativeDirichletOperator : L2 →ₗ.[ℝ] L2 :=
  (h10L2GelfandTriple hopen).formOperator
    (fullDivergenceForm (multiplicationCoefficientOperator a)
      (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c))

/-- The generator graph is exactly the full distributional Dirichlet equation with load `-f`. -/
theorem mem_negativeDirichletOperator_graph_iff (x f : L2) :
    (x, f) ∈ (negativeDirichletOperator hopen a b c).graph ↔
      ∃ u : H¹₀(Ω), baseCoordCLM u = x ∧
        IsWeakShiftedFullDivergenceSolution a b c 0 (-f) 0 u := by
  rw [negativeDirichletOperator, GelfandTriple.mem_formOperator_graph_iff]
  apply exists_congr
  intro u
  change baseCoordCLM u = x ∧ _ ↔ _
  apply and_congr_right
  intro _
  rw [← isWeakSolution_iff_isWeakShiftedFullDivergenceSolution hopen]
  constructor
  · intro h v
    have hv := DFunLike.congr_fun h v
    simpa only [shiftedDivergenceForm_apply, generalizedLoad_apply, zero_mul, add_zero,
      Pi.zero_apply, inner_zero_left, Finset.sum_const_zero, inner_neg_left, neg_apply,
      GelfandTriple.pivotToDual_apply, h10L2GelfandTriple_inclusion_apply] using hv
  · intro h
    ext v
    have hv := h v
    simpa only [shiftedDivergenceForm_apply, generalizedLoad_apply, zero_mul, add_zero,
      Pi.zero_apply, inner_zero_left, Finset.sum_const_zero, inner_neg_left, neg_apply,
      GelfandTriple.pivotToDual_apply, h10L2GelfandTriple_inclusion_apply] using hv

end SobolevSpace.GraphSpace
