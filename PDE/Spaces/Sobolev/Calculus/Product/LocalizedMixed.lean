/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Algebra
import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction

/-!
# Mixed derivatives of localized gradients

A weak derivative of `η ∂ⱼu` in direction `i` gives a weak derivative of `η ∂ᵢu`
in direction `j`. The cutoff prevents a bare interchange of these expressions.
Instead, commute the derivatives of the function `ηu`, then subtract the
known derivatives of `(∂ᵢη)u`. Both correction terms are first-order Sobolev
functions, so this argument needs no second derivative of `u` in advance.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- The exact stored-coordinate product rule, separating the derivative of the
unknown from the lower-order cutoff term. -/
theorem cutoffCLM_singleDeriv_eq
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{1,p}(Ω)) (i : Fin n) :
    (cutoffCLM η U).val (singleDerivIndex n i) =
      testFunctionLpTop (Ω := Ω) η • U.val (singleDerivIndex n i) +
        (cutoffCLM (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i 1) η) U).val (baseIndex n 1) := by
  apply Lp.ext
  filter_upwards [cutoffCLM_singleDeriv_apply_ae η U i,
    cutoffCLM_base_apply_ae (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i 1) η) U,
    Lp.coeFn_lpSMul (r := p) (testFunctionLpTop (Ω := Ω) η) (U.val (singleDerivIndex n i)),
    testFunctionLpTop_apply_ae (Ω := Ω) η,
    Lp.coeFn_add (testFunctionLpTop (Ω := Ω) η • U.val (singleDerivIndex n i))
      ((cutoffCLM (_root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single i 1) η) U).val (baseIndex n 1))] with x hd hb hm hη ha
  rw [hd, ha, Pi.add_apply, hm, hb]
  simp only [smul_eq_mul, Pi.mul_apply, hη]
  change _ = η.toFun x * U.val (singleDerivIndex n i) x +
    (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) η) x *
      U.val (baseIndex n 1) x
  rw [testFunction_lineDerivCLM_apply]
  rfl

/-- Localized mixed derivative recovery, including its two cutoff corrections.
The norm bound uses only the known derivative and fixed cutoff operators. -/
theorem exists_localized_mixed_weakDerivative
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{1,p}(Ω))
    (i j : Fin n) (g : DerivLp n p Ω)
    (hg : HasWeakDerivativeOn Ω [i]
      (testFunctionLpTop (Ω := Ω) η • U.val (singleDerivIndex n j) : DerivLp n p Ω)
      (g : ℝ^n → ℝ)) :
    ∃ v : DerivLp n p Ω,
      ‖v‖ ≤ ‖g‖ +
        (‖cutoffCLM (p := p) (Ω := Ω) (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single j 1) η)‖ +
         ‖cutoffCLM (p := p) (Ω := Ω) (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i 1) η)‖) * ‖U‖ ∧
      HasWeakDerivativeOn Ω [j]
        (testFunctionLpTop (Ω := Ω) η • U.val (singleDerivIndex n i) : DerivLp n p Ω)
        (v : ℝ^n → ℝ) := by
  let W (k : Fin n) := cutoffCLM (p := p) (Ω := Ω)
    (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single k 1) η) U
  let d (k l : Fin n) := (W k).val (singleDerivIndex n l)
  have hw (k l : Fin n) : HasWeakDerivativeOn Ω [l]
      ((W k).val (baseIndex n 1) : ℝ^n → ℝ) (d k l : ℝ^n → ℝ) := by
    simpa only [singleDerivIndex_toList] using (W k).property (singleDerivIndex n l)
  have hsum : HasWeakDerivativeOn Ω [i]
      ((cutoffCLM η U).val (singleDerivIndex n j) : ℝ^n → ℝ)
      (g + d j i : DerivLp n p Ω) := by
    rw [cutoffCLM_singleDeriv_eq]
    exact hasWeakDerivativeOn_lp_add hg (hw j i)
  have hswap := hasWeakDerivativeOn_mixed_of_first (cutoffCLM η U) i j _ hsum
  have hsub := hasWeakDerivativeOn_lp_sub hswap (hw i j)
  rw [cutoffCLM_singleDeriv_eq, add_sub_cancel_right] at hsub
  refine ⟨g + d j i - d i j, ?_, hsub⟩
  have hd (k l : Fin n) : ‖d k l‖ ≤
      ‖cutoffCLM (p := p) (Ω := Ω) (_root_.TestFunction.lineDerivCLM ℝ
        (EuclideanSpace.single k 1) η)‖ * ‖U‖ :=
    (wkpCoordinateCLM_norm_le (singleDerivIndex n l) (W k)).trans
      ((cutoffCLM _).le_opNorm U)
  calc
    ‖g + d j i - d i j‖ ≤ ‖g‖ + ‖d j i‖ + ‖d i j‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖g‖ + _ + _ := add_le_add (add_le_add le_rfl (hd j i)) (hd i j)
    _ = _ := by ring

end SobolevSpace.GraphSpace
