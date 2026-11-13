/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.LocalizedCoercivity
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Coercivity with a controlled cutoff-test remainder

Let `a ∈ W¹,∞` have positive lower bound `c`, and let `v = ∂ⱼ(μ_ε * u)` for an
L² input `u`. The mollified distributional flux is
`F = ∂ⱼ(μ_ε * (a u)) - μ_ε * ((∂ⱼa) u)`.
Testing against `b² v + b r` retains `c / 4` times the squared norm of `b v`
when `b` is a bounded real multiplier and the L² remainder satisfies `‖r‖ ≤ K N`,
where `‖u‖ ≤ N`. The error is `C N²`, uniformly over positive mollifier scales.

The squared-cutoff estimate comes from `LocalizedCoercivity`. The additional term
uses the Friedrichs commutator bound and Young's inequality. No derivative of `u`,
regularity or positivity of `b`, or particular Sobolev order of the test is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n : ℕ}

/-- Testing the mollified distribution `a ∂ⱼu` against a squared multiplier times
`∂ⱼ(μ_ε * u)`, plus a multiplier times an L² remainder, retains one quarter of the
coefficient's positive lower bound. The constant depends only on the mollifier,
coefficient, direction, multiplier, positive floor `c`, and remainder bound `K`.
It is chosen before the positive scale, input, remainder, and common bound `N`. -/
theorem exists_cutoff_mollified_flux_coercivity
    (μ : Mollifier n) (A : W^{1,∞}(ℝ^n)) (j : Fin n)
    (b : DerivLp n ∞ univ) {c K : ℝ} (hc : 0 < c)
    (hA : ∀ᵐ x ∂domainMeasure n univ,
      c ≤ (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) x)
    (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε)
      (u r : DerivLp n 2 univ) (N : ℝ), ‖u‖ ≤ N → ‖r‖ ≤ K * N →
      c / 4 * ‖b • mollifierDerivativeRowCLM μ hε j u‖ ^ 2 ≤
        ⟪mollifierDerivativeRowCLM μ hε j
            (((A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) • u) -
          mollifierRowCLM μ hε
            (((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u),
          b • (b • mollifierDerivativeRowCLM μ hε j u) + b • r⟫_ℝ + C * N ^ 2 := by
  let a := (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  let B : ℝ :=
    (∑ l : Fin n, ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) *
        (∫ x, ‖x‖ * ‖(∂[j] μ.ρ) x‖) +
      ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖
  have hB : 0 ≤ B := by positivity
  obtain ⟨D, hD, hcoerc⟩ := exists_localized_mollified_flux_coercivity μ A j hc hA
  let M := ‖a‖ * K
  let E := ‖b‖ * B * K
  refine ⟨D * ‖b‖ ^ 2 + M ^ 2 / c + E, by positivity, fun ε hε u r N hu hr ↦ ?_⟩
  have hN : 0 ≤ N := (norm_nonneg u).trans hu
  let v := mollifierDerivativeRowCLM μ hε j u
  let e := mollifierTransportCommutatorCLM μ hε A j u
  let F := mollifierDerivativeRowCLM μ hε j (a • u) -
    mollifierRowCLM μ hε (((A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • u)
  have he : ‖e‖ ≤ B * N :=
    (norm_mollifierTransportCommutatorCLM_apply_le μ hε A j u).trans
      (mul_le_mul_of_nonneg_left hu hB)
  have hab : b • (a • v) = a • (b • v) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_lpSMul (r := 2) b (a • v),
      Lp.coeFn_lpSMul (r := 2) a (b • v),
      Lp.coeFn_lpSMul (r := 2) a v, Lp.coeFn_lpSMul (r := 2) b v]
      with x hba hab ha hb
    simp only [Pi.smul_apply', smul_eq_mul] at hba hab ha hb
    rw [hba, hab, ha, hb]
    ac_rfl
  have hF : F = a • v - e := by
    dsimp only [F, a, v, e]
    rw [mollifierTransportCommutatorCLM_apply]
    abel
  have hprincipal : |⟪a • v, b • r⟫_ℝ| ≤ M * ‖b • v‖ * N := by
    rw [← Lp.inner_lpSMul_left b, hab]
    calc
      _ ≤ ‖a • (b • v)‖ * ‖r‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖a‖ * ‖b • v‖) * (K * N) := by gcongr; exact Lp.norm_smul_le _ _
      _ = M * ‖b • v‖ * N := by dsimp only [M]; ring
  have herror : |⟪e, b • r⟫_ℝ| ≤ E * N ^ 2 := by
    rw [← Lp.inner_lpSMul_left b]
    calc
      _ ≤ ‖b • e‖ * ‖r‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖b‖ * (B * N)) * (K * N) := by
        gcongr
        exact (Lp.norm_smul_le _ _).trans (by gcongr)
      _ = E * N ^ 2 := by dsimp only [E]; ring
  have hyoung : M * ‖b • v‖ * N ≤
      c / 4 * ‖b • v‖ ^ 2 + M ^ 2 / c * N ^ 2 := by
    apply (mul_le_mul_iff_right₀ hc).mp
    field_simp
    nlinarith [sq_nonneg (c * ‖b • v‖ - 2 * M * N)]
  have hpair : |⟪F, b • r⟫_ℝ| ≤ c / 4 * ‖b • v‖ ^ 2 +
      (M ^ 2 / c + E) * N ^ 2 := by
    rw [hF, inner_sub_left]
    exact (abs_sub _ _).trans (by linarith)
  have hcoerc' := hcoerc b ε hε u
  change c / 2 * ‖b • v‖ ^ 2 ≤ ⟪F, b • (b • v)⟫_ℝ + D * ‖b‖ ^ 2 * ‖u‖ ^ 2
    at hcoerc'
  have hsmall : D * ‖b‖ ^ 2 * ‖u‖ ^ 2 ≤ D * ‖b‖ ^ 2 * N ^ 2 := by gcongr
  rw [inner_add_right]
  change c / 4 * ‖b • v‖ ^ 2 ≤ ⟪F, b • (b • v)⟫_ℝ + ⟪F, b • r⟫_ℝ +
    (D * ‖b‖ ^ 2 + M ^ 2 / c + E) * N ^ 2
  linarith [neg_abs_le ⟪F, b • r⟫_ℝ]

end SobolevSpace.Approximation
