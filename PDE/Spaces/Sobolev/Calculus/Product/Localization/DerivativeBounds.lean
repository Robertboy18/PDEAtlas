/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.LocalizedMixed
public import PDE.Spaces.Sobolev.GraphSpace.Norms.WeakDerivativeBounds

/-!
# Norm bounds for localized transverse derivatives

Commutation supplies the missing normal derivative of a transverse
gradient component. The two cutoff corrections have fixed operator
norms, so a transverse weak-derivative bound gives a full H¹ estimate.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The fixed cutoff constant in a localized first-derivative H¹
estimate. It depends on the cutoff, domain, and dimension only. -/
def localizedDerivativeCutoffConstant (Ω : Set (ℝ^n))
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ :=
  ‖testFunctionLpTop (Ω := Ω) η‖ + 2 * n *
    ∑ j : Fin n, ‖cutoffCLM (p := 2) (Ω := Ω)
      (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) η)‖

/-- The cutoff constant is nonnegative. -/
theorem localizedDerivativeCutoffConstant_nonneg
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    0 ≤ localizedDerivativeCutoffConstant Ω η := by
  unfold localizedDerivativeCutoffConstant
  positivity

/-- Bounds for all transverse derivatives control the full H¹ norm of
each localized transverse gradient component. -/
theorem norm_localized_transverse_derivative_H1_le
    (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{1,2}(Ω)) (normal i : Fin n) (hi : i ≠ normal)
    {B : ℝ} (hderiv : ∀ k : Fin n, k ≠ normal → ∀ j : Fin n,
      ∃ g : DerivLp n 2 Ω, ‖g‖ ≤ B ∧
        HasWeakDerivativeOn Ω [k]
          (testFunctionLpTop (Ω := Ω) η • U.val (singleDerivIndex n j) :
            DerivLp n 2 Ω) (g : ℝ^n → ℝ))
    (W : W^{1,2}(Ω))
    (hW : wkpBaseCoordinateCLM W =
      testFunctionLpTop (Ω := Ω) η • U.val (singleDerivIndex n i)) :
    ‖W‖ ≤ n * B + localizedDerivativeCutoffConstant Ω η * ‖U‖ := by
  let S : ℝ := ∑ j : Fin n, ‖cutoffCLM (p := 2) (Ω := Ω)
    (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) η)‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ ↦
    (cutoffCLM (p := 2) (Ω := Ω)
      (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) η)).opNorm_nonneg
  have hcut (j : Fin n) : ‖cutoffCLM (p := 2) (Ω := Ω)
      (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) η)‖ ≤ S :=
    Finset.single_le_sum (f := fun j : Fin n ↦ ‖cutoffCLM (p := 2) (Ω := Ω)
      (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) η)‖)
      (fun j _ ↦ (cutoffCLM (p := 2) (Ω := Ω)
        (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) η)).opNorm_nonneg)
      (Finset.mem_univ j)
  have hbase : ‖wkpBaseCoordinateCLM W‖ ≤ ‖testFunctionLpTop (Ω := Ω) η‖ * ‖U‖ := by
    rw [hW]
    exact (Lp.norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
      (wkpCoordinateCLM_norm_le (singleDerivIndex n i) U) (norm_nonneg _))
  have hnorm : ‖W‖ ≤ ‖wkpBaseCoordinateCLM W‖ + ∑ _ : Fin n, (B + 2 * S * ‖U‖) := by
    apply norm_le_base_add_sum_of_weakDerivative_bounds hΩ W
    intro k
    have hb : baseRepresentative W =
        (testFunctionLpTop (Ω := Ω) η • U.val (singleDerivIndex n i) :
          DerivLp n 2 Ω) :=
      congrArg (fun v : DerivLp n 2 Ω ↦ (v : ℝ^n → ℝ)) hW
    rw [hb]
    by_cases hk : k = normal
    · obtain ⟨g, hg, hweak⟩ := hderiv i hi k
      obtain ⟨v, hv, hvweak⟩ := exists_localized_mixed_weakDerivative η U i k g hweak
      refine ⟨v, hv.trans ?_, hvweak⟩
      have hsum : ‖cutoffCLM (p := 2) (Ω := Ω)
          (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single k 1) η)‖ +
          ‖cutoffCLM (p := 2) (Ω := Ω)
          (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) η)‖ ≤ 2 * S := by
        simpa only [two_mul] using add_le_add (hcut k) (hcut i)
      exact add_le_add hg (mul_le_mul_of_nonneg_right hsum (norm_nonneg U))
    · obtain ⟨g, hg, hweak⟩ := hderiv k hk i
      exact ⟨g, hg.trans (le_add_of_nonneg_right (by positivity)), hweak⟩
  calc
    ‖W‖ ≤ ‖testFunctionLpTop (Ω := Ω) η‖ * ‖U‖ +
        ∑ _ : Fin n, (B + 2 * S * ‖U‖) := hnorm.trans (add_le_add hbase le_rfl)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        localizedDerivativeCutoffConstant, S]
      ring

end SobolevSpace.GraphSpace
