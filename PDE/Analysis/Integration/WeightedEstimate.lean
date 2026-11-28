/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Integration.WeightedEnergyLimit
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# A weighted energy estimate for the self-similar operator with a pressure

A divergence-free field `v` on `ℝⁿ` solves `c v - ½ x·∇v + W·∇v - Δv = G - ∇Q`, with a
divergence-free drift `W` bounded by `M`. For a weight `ω ≥ 0` with a size function `σ ≥ 0`
such that `|∇ω| ≤ C σ √ω`, `|Δω| ≤ C' σ²` and `γ ω ≤ (c + n/4) ω + ¼ x·∇ω`, the weighted energy
is bounded by weighted norms of the data:

`∫ ω |∇v|² + (γ - 3/16) ∫ ω |v|² ≤ 4 ∫ ω |G|² + 4 C² ∫ σ² Q² + (M² C² + C'/2) ∫ σ² |v|²`.

Hou, Wang and Yang use such an estimate three times in their proof of Proposition 4, for the
near field with the weight `φ_L` and for its gradient with the weights `φ_L` and `φ_L |ξ|²`.
The three are this one estimate with different data.

## Main results

* `integral_weight_mul_energy_le`: the estimate, in every dimension, for all data `(v, W, G, Q)`
  and weights `(ω, σ)` with the hypotheses above, when all the integrals in it converge.

## How it works

Pair the equation with `χ_R ω v` and let `R → ∞`
(`integral_energyDensity_le_of_forall_radialCutoff`). The pressure is integrated by parts onto
the weight, which is legitimate because `div v = 0`
(`integral_mul_fderiv_apply_eq_neg_of_divergence_eq_zero`). The drift produces the coefficient
`(c + n/4) ω + ¼ x·∇ω`, which is at least `γ ω`, and the terms with derivatives of the cutoff
are `O(1/R)` (`exists_norm_fderiv_radialCutoff_le`). Each remaining product is split by Young's
inequality with fixed constants, which uses up three sixteenths of `∫ ω |v|²`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Proposition 4 and Steps 1
  and 2 of its proof in Appendix F. <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace.Approximation
open scoped InnerProductSpace Topology

namespace PDE.Analysis

variable {n : ℕ}

/-- **The weighted energy estimate of the self-similar operator.** Let `v` be a divergence-free
`C²` field with `c v - ½ x·∇v + W·∇v - Δv = G - ∇Q` in the paired form
`similarityPairing c v W = ⟨G, v⟩ - ∇Q·v`, with a bounded divergence-free drift `W`, `‖W‖ ≤ M`.
Let `ω ≥ 0` be a `C²` weight and `σ ≥ 0` a size function with `|∇ω| ≤ C σ √ω`,
`|Δω| ≤ C' σ²` and `γ ω ≤ (c + n/4) ω + ¼ x·∇ω`. Then, when all the integrals below converge,

`∫ ω Σᵢ|∂ᵢv|² + (γ - 3/16) ∫ ω |v|² ≤ 4 ∫ ω |G|² + 4 C² ∫ σ² Q² + (M² C² + C'/2) ∫ σ² |v|²`. -/
theorem integral_weight_mul_energy_le {v W G : ℝ^n → ℝ^n} {Q ω σ : ℝ^n → ℝ}
    {c M Ce CΔ γ : ℝ} (hv : ContDiff ℝ 2 v) (hdivv : ∀ x, ∇· v x = 0) (hW : ContDiff ℝ 1 W)
    (hdivW : ∀ x, ∇· W x = 0) (hWb : ∀ x, ‖W x‖ ≤ M) (hQ : ContDiff ℝ 1 Q) (hG : Continuous G)
    (heq : ∀ x, similarityPairing c v W x = ⟪G x, v x⟫_ℝ - fderiv ℝ Q x (v x))
    (hω : ContDiff ℝ 2 ω) (hω0 : ∀ x, 0 ≤ ω x) (hσ0 : ∀ x, 0 ≤ σ x) (hCe0 : 0 ≤ Ce)
    (hgrad : ∀ x, ‖fderiv ℝ ω x‖ ≤ Ce * (σ x * √(ω x)))
    (hlap : ∀ x, |laplacian ω x| ≤ CΔ * σ x ^ 2)
    (hγ : ∀ x, γ * ω x ≤ (c + n / 4) * ω x + (1 / 4 : ℝ) * fderiv ℝ ω x x)
    (h₁ : Integrable fun x ↦ ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2)
    (h₂ : Integrable fun x ↦ ω x * ‖v x‖ ^ 2)
    (h₃ : Integrable fun x ↦ ‖fderiv ℝ ω x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2)
    (h₄ : Integrable fun x ↦ |laplacian ω x| * ‖v x‖ ^ 2)
    (h₅ : Integrable fun x ↦ ω x * ‖G x‖ ^ 2)
    (h₆ : Integrable fun x ↦ σ x ^ 2 * Q x ^ 2)
    (h₇ : Integrable fun x ↦ σ x ^ 2 * ‖v x‖ ^ 2)
    (h₈ : Integrable fun x ↦ ω x * Q x ^ 2) :
    (∫ x, ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) + (γ - 3 / 16) * ∫ x, ω x * ‖v x‖ ^ 2 ≤
      4 * (∫ x, ω x * ‖G x‖ ^ 2) + 4 * Ce ^ 2 * (∫ x, σ x ^ 2 * Q x ^ 2) +
        (M ^ 2 * Ce ^ 2 + CΔ / 2) * ∫ x, σ x ^ 2 * ‖v x‖ ^ 2 := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_norm_fderiv_radialCutoff_le n
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hω1 : ContDiff ℝ 1 ω := hω.of_le (by norm_num)
  -- The pairing with each cutoff weight.
  have hK : ∀ R : ℝ, 1 ≤ R → (∫ x, radialCutoff R x * ω x * similarityPairing c v W x) ≤
      (∫ x, (4 * (ω x * ‖G x‖ ^ 2) + 4 * Ce ^ 2 * (σ x ^ 2 * Q x ^ 2) +
        (1 / 8 : ℝ) * (ω x * ‖v x‖ ^ 2))) +
        (∫ x, B₁ / 2 * (ω x * Q x ^ 2 + ω x * ‖v x‖ ^ 2)) / R := by
    intro R hR
    have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
    have hχc : ContDiff ℝ 1 (radialCutoff (n := n) R) := (radialCutoff_contDiff R).of_le (by simp)
    have hψc : ContDiff ℝ 1 (fun x : ℝ^n ↦ radialCutoff R x * ω x) := hχc.mul hω1
    have hψs : HasCompactSupport (fun x : ℝ^n ↦ radialCutoff R x * ω x) :=
      (radialCutoff_hasCompactSupport hRpos).mul_right
    have hi₁ : Integrable fun x ↦ radialCutoff R x * ω x * ⟪G x, v x⟫_ℝ :=
      (hψc.continuous.mul (hG.inner hv.continuous)).integrable_of_hasCompactSupport
        hψs.mul_right
    have hi₂ : Integrable fun x ↦ radialCutoff R x * ω x * fderiv ℝ Q x (v x) :=
      (hψc.continuous.mul ((hQ.continuous_fderiv one_ne_zero).clm_apply
        hv.continuous)).integrable_of_hasCompactSupport hψs.mul_right
    have hi₃ : Integrable fun x ↦ Q x *
        fderiv ℝ (fun y : ℝ^n ↦ radialCutoff R y * ω y) x (v x) :=
      (hQ.continuous.mul ((hψc.continuous_fderiv one_ne_zero).clm_apply
        hv.continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_left (HasCompactSupport.intro hψs.isCompact fun x hx ↦ by
          change fderiv ℝ (fun y : ℝ^n ↦ radialCutoff R y * ω y) x (v x) = 0
          rw [fderiv_of_notMem_tsupport ℝ hx]
          simp))
    -- The pressure moves onto the weight.
    have hparts := integral_mul_fderiv_apply_eq_neg_of_divergence_eq_zero hQ hv1 hdivv hψc hψs
    have hI : Integrable fun x ↦ radialCutoff R x * ω x * ⟪G x, v x⟫_ℝ +
        Q x * fderiv ℝ (fun y : ℝ^n ↦ radialCutoff R y * ω y) x (v x) := hi₁.add hi₃
    have hleft : (∫ x, radialCutoff R x * ω x * similarityPairing c v W x) =
        ∫ x, (radialCutoff R x * ω x * ⟪G x, v x⟫_ℝ +
          Q x * fderiv ℝ (fun y : ℝ^n ↦ radialCutoff R y * ω y) x (v x)) := by
      have h₀ : (fun x ↦ radialCutoff R x * ω x * similarityPairing c v W x) =
          fun x ↦ radialCutoff R x * ω x * ⟪G x, v x⟫_ℝ -
            radialCutoff R x * ω x * fderiv ℝ Q x (v x) := funext fun x ↦ by
        rw [heq]
        ring
      rw [h₀, integral_sub hi₁ hi₂, integral_add hi₁ hi₃, hparts]
      ring
    have hm₁ : Integrable fun x ↦ 4 * (ω x * ‖G x‖ ^ 2) + 4 * Ce ^ 2 * (σ x ^ 2 * Q x ^ 2) +
        (1 / 8 : ℝ) * (ω x * ‖v x‖ ^ 2) :=
      ((h₅.const_mul 4).add (h₆.const_mul _)).add (h₂.const_mul _)
    have hm₂ : Integrable fun x ↦ B₁ / 2 * (ω x * Q x ^ 2 + ω x * ‖v x‖ ^ 2) :=
      (h₈.add h₂).const_mul _
    have hMaj : Integrable fun x ↦ 4 * (ω x * ‖G x‖ ^ 2) + 4 * Ce ^ 2 * (σ x ^ 2 * Q x ^ 2) +
        (1 / 8 : ℝ) * (ω x * ‖v x‖ ^ 2) +
        B₁ / 2 * (ω x * Q x ^ 2 + ω x * ‖v x‖ ^ 2) / R := hm₁.add (hm₂.div_const R)
    rw [hleft, ← integral_div, ← integral_add hm₁ (hm₂.div_const R)]
    refine integral_mono hI hMaj fun x ↦ ?_
    -- The pointwise bound, by Young's inequality.
    obtain ⟨hχ0, hχ1⟩ := radialCutoff_mem_Icc (n := n) R x
    have hφ0 := hω0 x
    have hs0 : 0 ≤ √(ω x) := Real.sqrt_nonneg _
    have hs2 : √(ω x) ^ 2 = ω x := Real.sq_sqrt hφ0
    have ha0 : 0 ≤ ‖G x‖ := norm_nonneg _
    have hc0 : 0 ≤ ‖v x‖ := norm_nonneg _
    have hp0 : 0 ≤ |Q x| := abs_nonneg _
    have hp2 : |Q x| ^ 2 = Q x ^ 2 := sq_abs _
    have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
    have hfd : fderiv ℝ (fun y : ℝ^n ↦ radialCutoff R y * ω y) x =
        radialCutoff R x • fderiv ℝ ω x + ω x • fderiv ℝ (radialCutoff R) x :=
      fderiv_fun_mul (hχc.differentiable one_ne_zero x) (hω1.differentiable one_ne_zero x)
    have h₁' : radialCutoff R x * ω x * ⟪G x, v x⟫_ℝ ≤
        4 * (ω x * ‖G x‖ ^ 2) + (1 / 16 : ℝ) * (ω x * ‖v x‖ ^ 2) := by
      have hin := abs_le.mp (abs_real_inner_le_norm (G x) (v x))
      have hχφ : 0 ≤ radialCutoff R x * ω x := mul_nonneg hχ0 hφ0
      have hχφ' : radialCutoff R x * ω x ≤ ω x := mul_le_of_le_one_left hφ0 hχ1
      have hac : 0 ≤ ‖G x‖ * ‖v x‖ := mul_nonneg ha0 hc0
      have hyoung : ‖G x‖ * ‖v x‖ ≤ 4 * ‖G x‖ ^ 2 + ‖v x‖ ^ 2 / 16 := by
        nlinarith [sq_nonneg (2 * ‖G x‖ - ‖v x‖ / 4)]
      calc radialCutoff R x * ω x * ⟪G x, v x⟫_ℝ
          ≤ radialCutoff R x * ω x * (‖G x‖ * ‖v x‖) := mul_le_mul_of_nonneg_left hin.2 hχφ
        _ ≤ ω x * (‖G x‖ * ‖v x‖) := mul_le_mul_of_nonneg_right hχφ' hac
        _ ≤ ω x * (4 * ‖G x‖ ^ 2 + ‖v x‖ ^ 2 / 16) := mul_le_mul_of_nonneg_left hyoung hφ0
        _ = 4 * (ω x * ‖G x‖ ^ 2) + (1 / 16 : ℝ) * (ω x * ‖v x‖ ^ 2) := by ring
    have h₂' : Q x * (radialCutoff R x * fderiv ℝ ω x (v x)) ≤
        4 * Ce ^ 2 * (σ x ^ 2 * Q x ^ 2) + (1 / 16 : ℝ) * (ω x * ‖v x‖ ^ 2) := by
      have hd : |fderiv ℝ ω x (v x)| ≤ Ce * (σ x * √(ω x)) * ‖v x‖ :=
        ((fderiv ℝ ω x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hgrad x) hc0)
      have hχd : |radialCutoff R x * fderiv ℝ ω x (v x)| ≤ Ce * (σ x * √(ω x)) * ‖v x‖ := by
        rw [abs_mul, abs_of_nonneg hχ0]
        exact (mul_le_of_le_one_left (abs_nonneg _) hχ1).trans hd
      have hprod : Q x * (radialCutoff R x * fderiv ℝ ω x (v x)) ≤
          |Q x| * (Ce * (σ x * √(ω x)) * ‖v x‖) :=
        (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hχd hp0)
      have hyoung : |Q x| * (Ce * (σ x * √(ω x)) * ‖v x‖) ≤
          4 * Ce ^ 2 * (σ x ^ 2 * |Q x| ^ 2) + (√(ω x) ^ 2 * ‖v x‖ ^ 2) / 16 := by
        nlinarith [sq_nonneg (2 * Ce * σ x * |Q x| - √(ω x) * ‖v x‖ / 4)]
      rw [hp2, hs2] at hyoung
      linarith
    have h₃' : Q x * (ω x * fderiv ℝ (radialCutoff R) x (v x)) ≤
        B₁ / 2 * (ω x * Q x ^ 2 + ω x * ‖v x‖ ^ 2) / R := by
      have hd : |fderiv ℝ (radialCutoff R) x (v x)| ≤ B₁ * R⁻¹ * ‖v x‖ :=
        ((fderiv ℝ (radialCutoff R) x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hB₁ R hRpos x) hc0)
      have hφd : |ω x * fderiv ℝ (radialCutoff R) x (v x)| ≤ ω x * (B₁ * R⁻¹ * ‖v x‖) := by
        rw [abs_mul, abs_of_nonneg hφ0]
        exact mul_le_mul_of_nonneg_left hd hφ0
      have hprod : Q x * (ω x * fderiv ℝ (radialCutoff R) x (v x)) ≤
          |Q x| * (ω x * (B₁ * R⁻¹ * ‖v x‖)) :=
        (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hφd hp0)
      have hyoung : |Q x| * ‖v x‖ ≤ (|Q x| ^ 2 + ‖v x‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (|Q x| - ‖v x‖)]
      rw [hp2] at hyoung
      have hcoef : 0 ≤ ω x * (B₁ * R⁻¹) := mul_nonneg hφ0 (mul_nonneg hB₁0 hRinv)
      calc Q x * (ω x * fderiv ℝ (radialCutoff R) x (v x))
          ≤ |Q x| * (ω x * (B₁ * R⁻¹ * ‖v x‖)) := hprod
        _ = ω x * (B₁ * R⁻¹) * (|Q x| * ‖v x‖) := by ring
        _ ≤ ω x * (B₁ * R⁻¹) * ((Q x ^ 2 + ‖v x‖ ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hyoung hcoef
        _ = B₁ / 2 * (ω x * Q x ^ 2 + ω x * ‖v x‖ ^ 2) / R := by
            field_simp
    rw [hfd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    linarith
  -- The limit `R → ∞` of the weighted energy identity.
  have hE := integral_energyDensity_le_of_forall_radialCutoff hv hW hdivW hWb hω hω0 h₁ h₂ h₃ h₄ hK
  have hEint := integrable_energyDensity_of_integrable hv hW.continuous hWb hω h₁ h₂ h₃ h₄ c
  -- The energy density from below, at every point.
  have hlowPt : ∀ x, ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 + (γ - 1 / 16) * (ω x * ‖v x‖ ^ 2) -
      (M ^ 2 * Ce ^ 2 + CΔ / 2) * (σ x ^ 2 * ‖v x‖ ^ 2) ≤ energyDensity c v W ω x := by
    intro x
    have hq0 : 0 ≤ ‖v x‖ ^ 2 := by positivity
    have hs0 : 0 ≤ √(ω x) := Real.sqrt_nonneg _
    have hs2 : √(ω x) ^ 2 = ω x := Real.sq_sqrt (hω0 x)
    have hWx : |fderiv ℝ ω x (W x)| ≤ Ce * (σ x * √(ω x)) * M :=
      ((fderiv ℝ ω x).le_opNorm _).trans
        (mul_le_mul (hgrad x) (hWb x) (norm_nonneg _)
          (mul_nonneg hCe0 (mul_nonneg (hσ0 x) hs0)))
    have eW := abs_le.mp hWx
    have eΔ := abs_le.mp (hlap x)
    have hcoef : (γ - 1 / 16) * ω x - (M ^ 2 * Ce ^ 2 + CΔ / 2) * σ x ^ 2 ≤
        (c + n / 4) * ω x + (1 / 4 : ℝ) * fderiv ℝ ω x x -
          (1 / 2 : ℝ) * fderiv ℝ ω x (W x) - (1 / 2 : ℝ) * laplacian ω x := by
      nlinarith [sq_nonneg (√(ω x) / 4 - Ce * M * σ x), eW.1, eW.2, eΔ.1, eΔ.2, hγ x]
    have h := mul_le_mul_of_nonneg_right hcoef hq0
    unfold energyDensity
    linarith
  have hlowInt : Integrable fun x ↦ ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 +
      (γ - 1 / 16) * (ω x * ‖v x‖ ^ 2) - (M ^ 2 * Ce ^ 2 + CΔ / 2) * (σ x ^ 2 * ‖v x‖ ^ 2) :=
    (h₁.add (h₂.const_mul _)).sub (h₇.const_mul _)
  have hlow := integral_mono hlowInt hEint hlowPt
  have hYX : Integrable fun x ↦ ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 +
      (γ - 1 / 16) * (ω x * ‖v x‖ ^ 2) := h₁.add (h₂.const_mul _)
  rw [integral_sub hYX (h₇.const_mul _), integral_add h₁ (h₂.const_mul _), integral_const_mul,
    integral_const_mul] at hlow
  -- The right side of the pairing bound, by linearity.
  have hA : Integrable fun x ↦ 4 * (ω x * ‖G x‖ ^ 2) := h₅.const_mul 4
  have hB : Integrable fun x ↦ 4 * Ce ^ 2 * (σ x ^ 2 * Q x ^ 2) := h₆.const_mul _
  have hAB : Integrable fun x ↦ 4 * (ω x * ‖G x‖ ^ 2) + 4 * Ce ^ 2 * (σ x ^ 2 * Q x ^ 2) :=
    hA.add hB
  rw [integral_add hAB (h₂.const_mul _), integral_add hA hB, integral_const_mul,
    integral_const_mul, integral_const_mul] at hE
  linarith

end PDE.Analysis
