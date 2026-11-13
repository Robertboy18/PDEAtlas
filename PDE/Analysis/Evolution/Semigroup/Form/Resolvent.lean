/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Form.Operator
public import PDE.Analysis.Evolution.Semigroup.Generation.Resolvent
public import PDE.Analysis.Variational.Spectral

/-!
# Resolvents of nonnegative energy forms

Suppose `B u u ≥ 0` and the form obtained by adding the pivot inner product is coercive
on `V`. Lax–Milgram (Mathlib's `IsCoercive.continuousLinearEquivOfBilin`) solves every
positive shift. Testing with the solution proves the Hille–Yosida bound in `H`. These are
steps 3 and 4 of the proof of Evans §7.4.3, Theorem 5; since `B u u ≥ 0`, the bound is
`‖R_λ‖ ≤ λ⁻¹` rather than Evans's `(λ - γ)⁻¹`.

The domain is dense: a vector orthogonal to it is orthogonal to its own variational
resolvent, contradicting strict positivity unless the vector vanishes. This argument
does not require symmetry, compactness, or a bounded domain. Evans, whose domain is
`H¹₀(U) ∩ H²(U)`, gets density for free and uses elliptic regularity instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.3, Theorem 5 and its proof, (27)-(32), pp. 442-443.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Evolution.GelfandTriple

open PDE.Analysis.Variational
open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (T : GelfandTriple (V := V) (H := H)) (B : V →L[ℝ] StrongDual ℝ V)

omit [CompleteSpace V] [CompleteSpace H] in
/-- Coercivity at one positive shift and nonnegativity give coercivity at every positive shift. -/
theorem isCoercive_add_smul_energyToDual
    (hnonneg : ∀ u, 0 ≤ B u u) (hcoercive : IsCoercive (B + T.energyToDual))
    {lambda : ℝ} (hlambda : 0 < lambda) :
    IsCoercive (B + lambda • T.energyToDual) := by
  obtain ⟨c, hc, hbound⟩ := hcoercive
  refine ⟨min 1 lambda * c, mul_pos (lt_min zero_lt_one hlambda) hc, fun u ↦ ?_⟩
  have hmass : 0 ≤ ⟪T.inclusion u, T.inclusion u⟫_ℝ := real_inner_self_nonneg
  have hbound' : c * ‖u‖ * ‖u‖ ≤ B u u + ⟪T.inclusion u, T.inclusion u⟫_ℝ :=
    hbound u
  change min 1 lambda * c * ‖u‖ * ‖u‖ ≤
    B u u + lambda * ⟪T.inclusion u, T.inclusion u⟫_ℝ
  have hscaled := mul_le_mul_of_nonneg_left hbound' (le_of_lt (lt_min zero_lt_one hlambda))
  have hB := mul_le_mul_of_nonneg_right (min_le_left 1 lambda) (hnonneg u)
  have hM := mul_le_mul_of_nonneg_right (min_le_right 1 lambda) hmass
  nlinarith

/-- A variational solution of the shifted form belongs to the exact weak operator graph. -/
theorem pivotSolutionOperator_mem_formOperator_graph (lambda : ℝ)
    (hcoercive : IsCoercive (B + lambda • T.energyToDual)) (f : H) :
    (pivotSolutionOperator (B + lambda • T.energyToDual) hcoercive T.inclusion f,
      lambda • pivotSolutionOperator (B + lambda • T.energyToDual) hcoercive T.inclusion f
        - f) ∈ (T.formOperator B).graph := by
  let u := solveCLM (B + lambda • T.energyToDual) hcoercive (pivotLoadCLM T.inclusion f)
  apply (T.mem_formOperator_graph_iff B _ _).2
  refine ⟨u, rfl, ?_⟩
  ext v
  have h := solveCLM.isWeakSolution (B + lambda • T.energyToDual) hcoercive
    (pivotLoadCLM T.inclusion f) v
  change B u v + lambda * ⟪T.inclusion u, T.inclusion v⟫_ℝ =
    pivotLoadCLM T.inclusion f v at h
  simp only [pivotLoadCLM_apply] at h
  change B u v = -⟪lambda • T.inclusion u - f, T.inclusion v⟫_ℝ
  rw [inner_sub_left, real_inner_smul_left]
  linarith

omit [CompleteSpace V] [CompleteSpace H] in
/-- Nonnegativity of the energy form is dissipativity of its negative pivot operator. -/
theorem inner_formOperator_nonpos (hnonneg : ∀ u, 0 ≤ B u u)
    (x : (T.formOperator B).domain) :
    ⟪T.formOperator B x, (x : H)⟫_ℝ ≤ 0 := by
  obtain ⟨u, hu, hBu⟩ := T.formOperator_spec B x
  have h := DFunLike.congr_fun hBu u
  change B u u = -⟪T.formOperator B x, T.inclusion u⟫_ℝ at h
  rw [hu] at h
  linarith [hnonneg u]

/-- The Hille–Yosida range and norm conditions follow from the energy-form hypotheses. -/
theorem hasContractionResolvent_formOperator
    (hnonneg : ∀ u, 0 ≤ B u u) (hcoercive : IsCoercive (B + T.energyToDual)) :
    HasContractionResolvent (T.formOperator B) where
  surjective := by
    intro lambda hlambda f
    have hC := T.isCoercive_add_smul_energyToDual B hnonneg hcoercive hlambda
    obtain ⟨x, hx, hAx⟩ := (LinearPMap.mem_graph_iff _).1
      (T.pivotSolutionOperator_mem_formOperator_graph B lambda hC f)
    refine ⟨x, ?_⟩
    change lambda • (x : H) - T.formOperator B x = f
    rw [hx, hAx, sub_sub_cancel]
  bound := by
    intro lambda hlambda x
    have hinner := T.inner_formOperator_nonpos B hnonneg x
    have hbound := real_inner_le_norm (lambda • (x : H) - T.formOperator B x) (x : H)
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hbound
    by_cases hx : ‖(x : H)‖ = 0
    · rw [hx]
      positivity
    · have hxpos : 0 < ‖(x : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      have hcancel : lambda * ‖(x : H)‖ ≤
          ‖lambda • (x : H) - T.formOperator B x‖ := by
        nlinarith
      rw [← div_eq_inv_mul, le_div_iff₀ hlambda]
      simpa [mul_comm] using hcancel

/-- The form operator has dense domain, proved using the coercive resolvent at one. -/
theorem dense_formOperator_domain (hcoercive : IsCoercive (B + T.energyToDual)) :
    Dense ((T.formOperator B).domain : Set H) := by
  have horth : (T.formOperator B).domainᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).2
    intro f hf
    change f = 0
    by_contra hzero
    have hpos := inner_pivotSolutionOperator_pos (B + T.energyToDual)
      hcoercive T.inclusion T.denseRange hzero
    have hgraph := T.pivotSolutionOperator_mem_formOperator_graph B 1
      (by simpa using hcoercive) f
    obtain ⟨x, hx, _⟩ := (LinearPMap.mem_graph_iff _).1 hgraph
    have hz := hf x x.property
    rw [hx] at hz
    simp only [one_smul] at hz
    rw [real_inner_comm] at hz
    exact (ne_of_gt hpos) hz
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]

/-- The generated resolvent is the variational solution operator. -/
theorem resolvent_formOperator_eq_pivotSolutionOperator
    (hnonneg : ∀ u, 0 ≤ B u u) (hcoercive : IsCoercive (B + T.energyToDual))
    {lambda : ℝ} (hlambda : 0 < lambda) :
    (T.hasContractionResolvent_formOperator B hnonneg hcoercive).resolvent hlambda =
      pivotSolutionOperator (B + lambda • T.energyToDual)
        (T.isCoercive_add_smul_energyToDual B hnonneg hcoercive hlambda) T.inclusion := by
  ext f
  let hA := T.hasContractionResolvent_formOperator B hnonneg hcoercive
  obtain ⟨x, hx, hAx⟩ := (LinearPMap.mem_graph_iff _).1
    (T.pivotSolutionOperator_mem_formOperator_graph B lambda
      (T.isCoercive_add_smul_energyToDual B hnonneg hcoercive hlambda) f)
  have hshift : lambda • (x : H) - T.formOperator B x = f := by
    rw [hx, hAx, sub_sub_cancel]
  calc
    hA.resolvent hlambda f =
        hA.resolvent hlambda (lambda • (x : H) - T.formOperator B x) :=
      congrArg _ hshift.symm
    _ = (x : H) := hA.resolvent_shift hlambda x
    _ = _ := hx

end PDE.Analysis.Evolution.GelfandTriple
