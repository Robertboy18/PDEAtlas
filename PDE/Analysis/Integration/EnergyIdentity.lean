/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Integration.WeightedEnergyLimit
import Mathlib.MeasureTheory.Function.L2Space
import PDE.FDeriv.Calculus
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Smooth
import PDE.FDeriv.PartialDeriv.Support

/-!
# The energy identity of the self-similar operator with a drift

Let `v` be a divergence-free field on `ℝⁿ` that solves

`c v - ½ x·∇v + W·∇v - Δv = G - ∇Q`

with a bounded divergence-free drift `W`. Pairing the equation with `v` gives the energy
identity `∫ |∇v|² + (c + n/4) ∫ |v|² = ∫ ⟨G, v⟩`: the transport by `W` and the pressure gradient
`∇Q` do no work. We only assume that `v` and `∇v` are square integrable, so `v` cannot be paired
with itself directly. We pair with `χ_R v` for a radial cutoff `χ_R` and let `R → ∞`. Hou, Wang
and Yang obtain their identity (2.14) this way, for a difference quotient of the near field.

## Main results

* `integral_energy_eq_of_similarityPairing`: `∫ Σᵢ |∂ᵢv|² + (c + n/4) ∫ |v|² = ∫ ⟨G, v⟩` in
  every dimension, for a divergence-free `C²` field `v` with `v` and `∇v` square integrable, a
  bounded divergence-free `C¹` drift `W`, a continuous `G` and a `C¹` function `Q` with
  `⟨G, v⟩` and `|Q| |v|` integrable.

## How it works

The left side tested against `χ_R` converges to `∫ Σᵢ |∂ᵢv|² + (c + n/4) ∫ |v|²`
(`tendsto_integral_radialCutoff_mul_similarityPairing` with the weight `1`). The drift `W·∇v`
contributes `-½ ∫ W·∇χ_R |v|²` there, which tends to zero. On the right, `∫ χ_R ⟨G, v⟩` tends to
`∫ ⟨G, v⟩` (`tendsto_integral_radialCutoff_mul`). The pressure term moves its derivative onto
the cutoff (`integral_mul_fderiv_apply_eq_neg_of_divergence_eq_zero`) and is `O(1/R)`. For data
in divergence form and no drift, `integral_energy_le_of_divergence_form` gives the inequality.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, the energy
  identity (2.14) in the proof of Proposition 3. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace.Approximation
open scoped InnerProductSpace Topology

namespace PDE.Analysis

variable {n : ℕ}

/-- **The energy identity of the self-similar operator with a drift.** Let `v` be a
divergence-free `C²` field on `ℝⁿ` with `v` and `∇v` square integrable, `W` a bounded
divergence-free `C¹` drift, and suppose that

`c v - ½ x·∇v + W·∇v - Δv = G - ∇Q`

in the paired form `similarityPairing c v W = ⟨G, v⟩ - ∇Q·v`, with `G` continuous, `Q` of class
`C¹`, and `⟨G, v⟩`, `|Q| |v|` integrable. Then

`∫ Σᵢ|∂ᵢv|² + (c + n/4) ∫ |v|² = ∫ ⟨G, v⟩`.

The transport by `W` and the gradient `∇Q` do not contribute, because `W` and `v` are divergence
free. -/
theorem integral_energy_eq_of_similarityPairing {v W G : ℝ^n → ℝ^n} {Q : ℝ^n → ℝ} {c M : ℝ}
    (hv : ContDiff ℝ 2 v) (hdivv : ∀ x, ∇· v x = 0) (hW : ContDiff ℝ 1 W)
    (hdivW : ∀ x, ∇· W x = 0) (hWb : ∀ x, ‖W x‖ ≤ M) (hQ : ContDiff ℝ 1 Q) (hG : Continuous G)
    (heq : ∀ x, similarityPairing c v W x = ⟪G x, v x⟫_ℝ - fderiv ℝ Q x (v x))
    (hv2 : Integrable fun x ↦ ‖v x‖ ^ 2)
    (hDv : Integrable fun x ↦ ∑ i : Fin n, ‖∂[i] v x‖ ^ 2)
    (hGv : Integrable fun x ↦ ⟪G x, v x⟫_ℝ) (hQv : Integrable fun x ↦ |Q x| * ‖v x‖) :
    (∫ x, ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) + (c + n / 4) * ∫ x, ‖v x‖ ^ 2 =
      ∫ x, ⟪G x, v x⟫_ℝ := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_norm_fderiv_radialCutoff_le n
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  -- The left side is the limit of the pairings with the cutoffs.
  have hT := tendsto_integral_radialCutoff_mul_similarityPairing (v := v) (W := W)
    (ω := fun _ ↦ 1) (c := c) (M := M) hv hW hdivW hWb contDiff_const (fun _ ↦ zero_le_one)
    (by simpa only [one_mul] using hDv) (by simpa only [one_mul] using hv2) (by simp) (by simp)
  have hE : (fun x ↦ energyDensity c v W (fun _ ↦ 1) x) =
      fun x ↦ (∑ i : Fin n, ‖∂[i] v x‖ ^ 2) + (c + n / 4) * ‖v x‖ ^ 2 := funext fun x ↦ by
    simp [energyDensity]
  rw [hE, integral_add hDv (hv2.const_mul _), integral_const_mul] at hT
  -- The pairings split into the term with `G` and the term with `Q` on the cutoff.
  have hsplit : ∀ k : ℕ, (∫ x, radialCutoff ((k : ℝ) + 1) x * (fun _ : ℝ^n ↦ (1 : ℝ)) x *
      similarityPairing c v W x) = (∫ x, radialCutoff ((k : ℝ) + 1) x * ⟪G x, v x⟫_ℝ) +
        ∫ x, Q x * fderiv ℝ (radialCutoff ((k : ℝ) + 1)) x (v x) := fun k ↦ by
    have hRpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hχc : ContDiff ℝ 1 (radialCutoff (n := n) ((k : ℝ) + 1)) :=
      (radialCutoff_contDiff _).of_le (by simp)
    have hχs : HasCompactSupport (radialCutoff (n := n) ((k : ℝ) + 1)) :=
      radialCutoff_hasCompactSupport hRpos
    have i0 : Integrable fun x ↦ radialCutoff ((k : ℝ) + 1) x * ⟪G x, v x⟫_ℝ :=
      (hχc.continuous.mul (hG.inner hv.continuous)).integrable_of_hasCompactSupport
        hχs.mul_right
    have i2 : Integrable fun x ↦ radialCutoff ((k : ℝ) + 1) x * fderiv ℝ Q x (v x) :=
      (hχc.continuous.mul ((hQ.continuous_fderiv one_ne_zero).clm_apply
        hv.continuous)).integrable_of_hasCompactSupport hχs.mul_right
    have hparts := integral_mul_fderiv_apply_eq_neg_of_divergence_eq_zero hQ hv1 hdivv hχc hχs
    have h₀ : (fun x ↦ radialCutoff ((k : ℝ) + 1) x * (fun _ : ℝ^n ↦ (1 : ℝ)) x *
        similarityPairing c v W x) = fun x ↦ radialCutoff ((k : ℝ) + 1) x * ⟪G x, v x⟫_ℝ -
          radialCutoff ((k : ℝ) + 1) x * fderiv ℝ Q x (v x) := funext fun x ↦ by
      rw [heq, mul_one, mul_sub]
    rw [h₀, integral_sub i0 i2, hparts, sub_neg_eq_add]
  have hA := tendsto_integral_radialCutoff_mul hGv
  have hB : Tendsto (fun k : ℕ ↦ ∫ x, Q x * fderiv ℝ (radialCutoff ((k : ℝ) + 1)) x (v x))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k : ℕ ↦
      B₁ * (1 / ((k : ℝ) + 1)) * ∫ x, |Q x| * ‖v x‖) (fun k ↦ ?_) ?_
    · have hRpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [← integral_const_mul]
      refine (norm_integral_le_integral_norm _).trans
        (integral_mono_of_nonneg (.of_forall fun x ↦ norm_nonneg _) (hQv.const_mul _)
          (.of_forall fun x ↦ ?_))
      have hd : |fderiv ℝ (radialCutoff ((k : ℝ) + 1)) x (v x)| ≤
          B₁ * ((k : ℝ) + 1)⁻¹ * ‖v x‖ :=
        ((fderiv ℝ (radialCutoff ((k : ℝ) + 1)) x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hB₁ _ hRpos x) (norm_nonneg _))
      beta_reduce
      rw [Real.norm_eq_abs, abs_mul, one_div]
      calc |Q x| * |fderiv ℝ (radialCutoff ((k : ℝ) + 1)) x (v x)|
          ≤ |Q x| * (B₁ * ((k : ℝ) + 1)⁻¹ * ‖v x‖) :=
            mul_le_mul_of_nonneg_left hd (abs_nonneg _)
        _ = B₁ * ((k : ℝ) + 1)⁻¹ * (|Q x| * ‖v x‖) := by ring
    · simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul B₁).mul_const
        (∫ x, |Q x| * ‖v x‖))
  have hT2 : Tendsto (fun k : ℕ ↦ ∫ x, radialCutoff ((k : ℝ) + 1) x *
      (fun _ : ℝ^n ↦ (1 : ℝ)) x * similarityPairing c v W x) atTop
      (𝓝 (∫ x, ⟪G x, v x⟫_ℝ)) := by
    have h := hA.add hB
    rw [add_zero] at h
    exact h.congr fun k ↦ (hsplit k).symm
  exact tendsto_nhds_unique hT hT2

end PDE.Analysis
