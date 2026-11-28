/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Integration.WeightedEnergyLimit
import Mathlib.MeasureTheory.Function.L2Space
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import PDE.FDeriv.Calculus
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Smooth
import PDE.FDeriv.PartialDeriv.Support
import PDE.FDeriv.PartialDeriv.Transport

/-!
# The energy estimate of the self-similar operator with data in divergence form

A divergence-free field `v` on `ℝⁿ` solves `c v - ½ x·∇v - Δv = G₀ + Σₘ ∂_{d(m)} Gₘ - ∇q`, where
`G₀`, the `Gₘ` and `q` are square integrable but nothing is known about the size of the
derivatives `∂_{d(m)} Gₘ` or of `∇q`. The energy estimate still holds:

`∫ Σᵢ |∂ᵢv|² + (c + n/4) ∫ |v|² ≤ ‖G₀‖ ‖v‖ + Σₘ ‖Gₘ‖ ‖∂_{d(m)} v‖`,

with `L²` norms. Hou, Wang and Yang use this estimate in their proof of the smoothness of the
near field (Proposition 3), for the derivatives of its mollifications, where the commutator and
the nonlinear term are derivatives of functions that are bounded in `L²` uniformly in the
mollification. The estimate with a weight and data that are not differentiated is
`integral_weight_mul_energy_le`.

## Main results

* `integral_energy_le_of_divergence_form`: the estimate above, in every dimension, for a
  divergence-free `C²` field `v` with `v` and `∇v` square integrable, a continuous `G₀`, a
  finite family of `C¹` fields `Gₘ` with directions `d(m)` and a `C¹` function `q`, all square
  integrable.
* `integral_energy_le_of_divergence_form_components`: the same estimate for a field given by its
  scalar components, with the equation written for each component.

## How it works

Pair the equation with `χ_R v` and let `R → ∞`, by the limit of the weighted energy identity
`integral_energyDensity_le_of_forall_radialCutoff` with the weight `1` and no drift. The left side
gives `∫ |∇v|² + (c + n/4) ∫ |v|²`: the drift contributes `n/4`, and the terms with derivatives
of the cutoff are `O(1/R)`. On the right, the derivative of `Gₘ` moves onto `χ_R v`
(`integral_fderiv_apply_eq_neg_integral_mul_divergence`), which costs `‖Gₘ‖ ‖∂_{d(m)} v‖` and a
term `O(1/R)`. The gradient `∇q` moves onto the cutoff because `v` is divergence free
(`integral_mul_fderiv_apply_eq_neg_of_divergence_eq_zero`), and is `O(1/R)` too.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Proposition 3 and its proof in
  Appendix F, the estimates after (F.10). <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace.Approximation
open scoped InnerProductSpace Topology

namespace PDE.Analysis

variable {n : ℕ}

/-- **The energy estimate with data in divergence form.** Let `v` be a divergence-free `C²`
field on `ℝⁿ` with `v` and `∇v` square integrable, and suppose that

`c v - ½ x·∇v - Δv = G₀ + Σₘ ∂_{d(m)} Gₘ - ∇q`

in the paired form `similarityPairing c v 0 = ⟨G₀, v⟩ + Σₘ ⟨∂_{d(m)} Gₘ, v⟩ - ∇q·v`, with `G₀`
continuous, `Gₘ` and `q` of class `C¹`, all square integrable. Then

`∫ Σᵢ|∂ᵢv|² + (c + n/4) ∫ |v|² ≤ √(∫|G₀|²) √(∫|v|²) + Σₘ √(∫|Gₘ|²) √(∫|∂_{d(m)}v|²)`.

No bound on the derivatives of `Gₘ` or on `∇q` enters. -/
theorem integral_energy_le_of_divergence_form {ι : Type*} [Fintype ι] {v G₀ : ℝ^n → ℝ^n}
    {G : ι → ℝ^n → ℝ^n} {q : ℝ^n → ℝ} {c : ℝ} (d : ι → Fin n)
    (hv : ContDiff ℝ 2 v) (hdiv : ∀ x, ∇· v x = 0) (hG₀ : Continuous G₀)
    (hG : ∀ m, ContDiff ℝ 1 (G m)) (hq : ContDiff ℝ 1 q)
    (heq : ∀ x, similarityPairing c v (fun _ ↦ 0) x =
      ⟪G₀ x, v x⟫_ℝ + (∑ m, ⟪∂[d m] (G m) x, v x⟫_ℝ) - fderiv ℝ q x (v x))
    (hv2 : Integrable fun x ↦ ‖v x‖ ^ 2)
    (hDv : Integrable fun x ↦ ∑ i : Fin n, ‖∂[i] v x‖ ^ 2)
    (hG₀2 : Integrable fun x ↦ ‖G₀ x‖ ^ 2) (hG2 : ∀ m, Integrable fun x ↦ ‖G m x‖ ^ 2)
    (hq2 : Integrable fun x ↦ q x ^ 2) :
    (∫ x, ∑ i : Fin n, ‖∂[i] v x‖ ^ 2) + (c + n / 4) * ∫ x, ‖v x‖ ^ 2 ≤
      √(∫ x, ‖G₀ x‖ ^ 2) * √(∫ x, ‖v x‖ ^ 2) +
        ∑ m, √(∫ x, ‖G m x‖ ^ 2) * √(∫ x, ‖∂[d m] v x‖ ^ 2) := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_norm_fderiv_radialCutoff_le n
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hDvc : ∀ l : Fin n, Continuous (∂[l] v) := fun l ↦ hv1.continuous_partialDeriv l
  -- Square integrability, as membership in `L²`.
  have mv : MemLp (fun x ↦ ‖v x‖) 2 volume :=
    (memLp_two_iff_integrable_sq hv.continuous.norm.aestronglyMeasurable).mpr hv2
  have mG₀ : MemLp (fun x ↦ ‖G₀ x‖) 2 volume :=
    (memLp_two_iff_integrable_sq hG₀.norm.aestronglyMeasurable).mpr hG₀2
  have mG : ∀ m, MemLp (fun x ↦ ‖G m x‖) 2 volume := fun m ↦
    (memLp_two_iff_integrable_sq (hG m).continuous.norm.aestronglyMeasurable).mpr (hG2 m)
  have mq : MemLp (fun x ↦ |q x|) 2 volume :=
    (memLp_two_iff_integrable_sq hq.continuous.abs.aestronglyMeasurable).mpr
      (by simpa only [sq_abs] using hq2)
  have hDvl : ∀ l : Fin n, Integrable fun x ↦ ‖∂[l] v x‖ ^ 2 := fun l ↦
    hDv.mono' ((hDvc l).norm.pow 2).aestronglyMeasurable (.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact Finset.single_le_sum (f := fun i ↦ ‖∂[i] v x‖ ^ 2) (fun i _ ↦ sq_nonneg _)
        (Finset.mem_univ l))
  have mDv : ∀ l : Fin n, MemLp (fun x ↦ ‖∂[l] v x‖) 2 volume := fun l ↦
    (memLp_two_iff_integrable_sq (hDvc l).norm.aestronglyMeasurable).mpr (hDvl l)
  have iGv : ∀ m, Integrable fun x ↦ ‖G m x‖ * ‖v x‖ := fun m ↦ (mG m).integrable_mul mv
  have iqv : Integrable fun x ↦ |q x| * ‖v x‖ := mq.integrable_mul mv
  have iG₀v : Integrable fun x ↦ ‖G₀ x‖ * ‖v x‖ := mG₀.integrable_mul mv
  have iGDv : ∀ m, Integrable fun x ↦ ‖G m x‖ * ‖∂[d m] v x‖ := fun m ↦
    (mG m).integrable_mul (mDv (d m))
  -- Cauchy–Schwarz for the two kinds of terms.
  have cs₀ : (∫ x, ‖G₀ x‖ * ‖v x‖) ≤ √(∫ x, ‖G₀ x‖ ^ 2) * √(∫ x, ‖v x‖ ^ 2) := by
    refine le_trans (integral_mono iG₀v iG₀v.abs fun x ↦ le_abs_self _) ?_
    exact integral_abs_mul_le_sqrt_integral_sq mG₀ mv
  have cs : ∀ m, (∫ x, ‖G m x‖ * ‖∂[d m] v x‖) ≤
      √(∫ x, ‖G m x‖ ^ 2) * √(∫ x, ‖∂[d m] v x‖ ^ 2) := fun m ↦ by
    refine le_trans (integral_mono (iGDv m) (iGDv m).abs fun x ↦ le_abs_self _) ?_
    exact integral_abs_mul_le_sqrt_integral_sq (mG m) (mDv (d m))
  -- The pairing with each cutoff.
  have hK : ∀ R : ℝ, 1 ≤ R →
      (∫ x, radialCutoff R x * (fun _ : ℝ^n ↦ (1 : ℝ)) x *
        similarityPairing c v (fun _ ↦ 0) x) ≤
      (√(∫ x, ‖G₀ x‖ ^ 2) * √(∫ x, ‖v x‖ ^ 2) +
        ∑ m, √(∫ x, ‖G m x‖ ^ 2) * √(∫ x, ‖∂[d m] v x‖ ^ 2)) +
        B₁ * ((∑ m, ∫ x, ‖G m x‖ * ‖v x‖) + ∫ x, |q x| * ‖v x‖) / R := by
    intro R hR
    have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
    have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
    have hχc : ContDiff ℝ 1 (radialCutoff (n := n) R) := (radialCutoff_contDiff R).of_le (by simp)
    have hχs : HasCompactSupport (radialCutoff (n := n) R) := radialCutoff_hasCompactSupport hRpos
    have hDχ : ∀ x : ℝ^n, ‖fderiv ℝ (radialCutoff R) x‖ ≤ B₁ * R⁻¹ := hB₁ R hRpos
    have hDχc : Continuous (fderiv ℝ (radialCutoff (n := n) R)) :=
      hχc.continuous_fderiv one_ne_zero
    -- The integrable pieces.
    have i0 : Integrable fun x ↦ radialCutoff R x * ⟪G₀ x, v x⟫_ℝ :=
      (hχc.continuous.mul (hG₀.inner hv.continuous)).integrable_of_hasCompactSupport
        hχs.mul_right
    have i1 : ∀ m, Integrable fun x ↦ radialCutoff R x * ⟪∂[d m] (G m) x, v x⟫_ℝ := fun m ↦
      (hχc.continuous.mul (((hG m).continuous_partialDeriv (d m)).inner
        hv.continuous)).integrable_of_hasCompactSupport hχs.mul_right
    have i1' : ∀ m, Integrable fun x ↦ radialCutoff R x * ⟪G m x, ∂[d m] v x⟫_ℝ := fun m ↦
      (hχc.continuous.mul ((hG m).continuous.inner
        (hDvc (d m)))).integrable_of_hasCompactSupport hχs.mul_right
    have i1'' : ∀ m, Integrable fun x ↦ ⟪G m x, v x⟫_ℝ * ∂[d m] (radialCutoff R) x := fun m ↦
      (((hG m).continuous.inner hv.continuous).mul
        (hχc.continuous_partialDeriv (d m))).integrable_of_hasCompactSupport
        (hχs.partialDeriv (d m)).mul_left
    have i2 : Integrable fun x ↦ radialCutoff R x * fderiv ℝ q x (v x) :=
      (hχc.continuous.mul ((hq.continuous_fderiv one_ne_zero).clm_apply
        hv.continuous)).integrable_of_hasCompactSupport hχs.mul_right
    have i3 : Integrable fun x ↦ q x * fderiv ℝ (radialCutoff R) x (v x) :=
      (hq.continuous.mul (hDχc.clm_apply hv.continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_left (HasCompactSupport.intro hχs.isCompact fun x hx ↦ by
          rw [fderiv_of_notMem_tsupport ℝ hx, zero_apply]))
    -- The derivative of `Gₘ` moves to the cutoff and to `v`.
    have hparts : ∀ m, (∫ x, radialCutoff R x * ⟪∂[d m] (G m) x, v x⟫_ℝ) =
        -(∫ x, radialCutoff R x * ⟪G m x, ∂[d m] v x⟫_ℝ) -
          ∫ x, ⟪G m x, v x⟫_ℝ * ∂[d m] (radialCutoff R) x := fun m ↦ by
      have hφ : ContDiff ℝ 1 (fun x ↦ ⟪G m x, v x⟫_ℝ) := (hG m).inner ℝ hv1
      have h := integral_fderiv_apply_eq_neg_integral_mul_divergence
        (B := fun x ↦ radialCutoff R x • EuclideanSpace.single (d m) (1 : ℝ)) hφ
        (hχc.smul contDiff_const) hχs.smul_right
      have hpt : ∀ x, fderiv ℝ (fun x ↦ ⟪G m x, v x⟫_ℝ) x
          (radialCutoff R x • EuclideanSpace.single (d m) (1 : ℝ)) =
          radialCutoff R x * ⟪∂[d m] (G m) x, v x⟫_ℝ +
            radialCutoff R x * ⟪G m x, ∂[d m] v x⟫_ℝ := fun x ↦ by
        rw [map_smul, smul_eq_mul, fderiv_inner_apply ℝ ((hG m).differentiable one_ne_zero x)
          (hv1.differentiable one_ne_zero x)]
        change radialCutoff R x * (⟪G m x, ∂[d m] v x⟫_ℝ + ⟪∂[d m] (G m) x, v x⟫_ℝ) = _
        ring
      simp only [hpt, PDE.divergence_smul_single] at h
      rw [integral_add (i1 m) (i1' m)] at h
      linarith
    have hpartsq := integral_mul_fderiv_apply_eq_neg_of_divergence_eq_zero hq hv1 hdiv hχc hχs
    have hleft : (∫ x, radialCutoff R x * (fun _ : ℝ^n ↦ (1 : ℝ)) x *
        similarityPairing c v (fun _ ↦ 0) x) =
        (∫ x, radialCutoff R x * ⟪G₀ x, v x⟫_ℝ) +
          (∑ m, (-(∫ x, radialCutoff R x * ⟪G m x, ∂[d m] v x⟫_ℝ) -
            ∫ x, ⟪G m x, v x⟫_ℝ * ∂[d m] (radialCutoff R) x)) +
          ∫ x, q x * fderiv ℝ (radialCutoff R) x (v x) := by
      have h₀ : (fun x ↦ radialCutoff R x * (fun _ : ℝ^n ↦ (1 : ℝ)) x *
          similarityPairing c v (fun _ ↦ 0) x) =
          fun x ↦ radialCutoff R x * ⟪G₀ x, v x⟫_ℝ +
            (∑ m, radialCutoff R x * ⟪∂[d m] (G m) x, v x⟫_ℝ) -
            radialCutoff R x * fderiv ℝ q x (v x) := funext fun x ↦ by
        rw [heq, mul_one, mul_sub, mul_add, Finset.mul_sum]
      have iSum : Integrable fun x ↦ ∑ m, radialCutoff R x * ⟪∂[d m] (G m) x, v x⟫_ℝ :=
        integrable_finsetSum _ fun m _ ↦ i1 m
      have iS : Integrable fun x ↦ radialCutoff R x * ⟪G₀ x, v x⟫_ℝ +
          ∑ m, radialCutoff R x * ⟪∂[d m] (G m) x, v x⟫_ℝ := i0.add iSum
      rw [h₀, integral_sub iS i2, integral_add i0 iSum, integral_finsetSum _ fun m _ ↦ i1 m,
        hpartsq]
      simp only [hparts]
      ring
    -- The three bounds.
    have b0 : (∫ x, radialCutoff R x * ⟪G₀ x, v x⟫_ℝ) ≤
        √(∫ x, ‖G₀ x‖ ^ 2) * √(∫ x, ‖v x‖ ^ 2) :=
      (integral_mono i0 iG₀v fun x ↦ by
        obtain ⟨hχ0, hχ1⟩ := radialCutoff_mem_Icc (n := n) R x
        calc radialCutoff R x * ⟪G₀ x, v x⟫_ℝ ≤ radialCutoff R x * (‖G₀ x‖ * ‖v x‖) :=
              mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hχ0
          _ ≤ ‖G₀ x‖ * ‖v x‖ := mul_le_of_le_one_left (by positivity) hχ1).trans cs₀
    have b1 : ∀ m, -(∫ x, radialCutoff R x * ⟪G m x, ∂[d m] v x⟫_ℝ) ≤
        √(∫ x, ‖G m x‖ ^ 2) * √(∫ x, ‖∂[d m] v x‖ ^ 2) := fun m ↦ by
      rw [← integral_neg]
      refine (integral_mono (i1' m).neg (iGDv m) fun x ↦ ?_).trans (cs m)
      obtain ⟨hχ0, hχ1⟩ := radialCutoff_mem_Icc (n := n) R x
      have hin := abs_le.mp (abs_real_inner_le_norm (G m x) (∂[d m] v x))
      calc -(radialCutoff R x * ⟪G m x, ∂[d m] v x⟫_ℝ)
          = radialCutoff R x * -⟪G m x, ∂[d m] v x⟫_ℝ := by ring
        _ ≤ radialCutoff R x * (‖G m x‖ * ‖∂[d m] v x‖) :=
            mul_le_mul_of_nonneg_left (by linarith [hin.1]) hχ0
        _ ≤ ‖G m x‖ * ‖∂[d m] v x‖ := mul_le_of_le_one_left (by positivity) hχ1
    have b2 : ∀ m, -(∫ x, ⟪G m x, v x⟫_ℝ * ∂[d m] (radialCutoff R) x) ≤
        B₁ * R⁻¹ * ∫ x, ‖G m x‖ * ‖v x‖ := fun m ↦ by
      rw [← integral_neg, ← integral_const_mul]
      refine integral_mono (i1'' m).neg ((iGv m).const_mul _) fun x ↦ ?_
      have hin := abs_le.mp (abs_real_inner_le_norm (G m x) (v x))
      have hd : |∂[d m] (radialCutoff R) x| ≤ B₁ * R⁻¹ := by
        rw [← Real.norm_eq_abs]
        exact (norm_partialDeriv_le_norm_fderiv (d m) _ x).trans (hDχ x)
      have hd' := abs_le.mp hd
      have hp : 0 ≤ ‖G m x‖ * ‖v x‖ := by positivity
      have habs : |⟪G m x, v x⟫_ℝ * ∂[d m] (radialCutoff R) x| ≤
          ‖G m x‖ * ‖v x‖ * (B₁ * R⁻¹) := by
        rw [abs_mul]
        exact mul_le_mul (abs_real_inner_le_norm _ _) hd (abs_nonneg _) hp
      calc -(⟪G m x, v x⟫_ℝ * ∂[d m] (radialCutoff R) x)
          ≤ |⟪G m x, v x⟫_ℝ * ∂[d m] (radialCutoff R) x| := neg_le_abs _
        _ ≤ ‖G m x‖ * ‖v x‖ * (B₁ * R⁻¹) := habs
        _ = B₁ * R⁻¹ * (‖G m x‖ * ‖v x‖) := by ring
    have b3 : (∫ x, q x * fderiv ℝ (radialCutoff R) x (v x)) ≤
        B₁ * R⁻¹ * ∫ x, |q x| * ‖v x‖ := by
      rw [← integral_const_mul]
      refine integral_mono i3 (iqv.const_mul _) fun x ↦ ?_
      have hd : |fderiv ℝ (radialCutoff R) x (v x)| ≤ B₁ * R⁻¹ * ‖v x‖ :=
        ((fderiv ℝ (radialCutoff R) x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hDχ x) (norm_nonneg _))
      calc q x * fderiv ℝ (radialCutoff R) x (v x)
          ≤ |q x * fderiv ℝ (radialCutoff R) x (v x)| := le_abs_self _
        _ = |q x| * |fderiv ℝ (radialCutoff R) x (v x)| := abs_mul _ _
        _ ≤ |q x| * (B₁ * R⁻¹ * ‖v x‖) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
        _ = B₁ * R⁻¹ * (|q x| * ‖v x‖) := by ring
    rw [hleft]
    have hsum : (∑ m, (-(∫ x, radialCutoff R x * ⟪G m x, ∂[d m] v x⟫_ℝ) -
        ∫ x, ⟪G m x, v x⟫_ℝ * ∂[d m] (radialCutoff R) x)) ≤
        (∑ m, √(∫ x, ‖G m x‖ ^ 2) * √(∫ x, ‖∂[d m] v x‖ ^ 2)) +
          B₁ * R⁻¹ * ∑ m, ∫ x, ‖G m x‖ * ‖v x‖ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun m _ ↦ by linarith [b1 m, b2 m]
    have e : B₁ * ((∑ m, ∫ x, ‖G m x‖ * ‖v x‖) + ∫ x, |q x| * ‖v x‖) / R =
        B₁ * R⁻¹ * (∑ m, ∫ x, ‖G m x‖ * ‖v x‖) + B₁ * R⁻¹ * ∫ x, |q x| * ‖v x‖ := by
      rw [div_eq_mul_inv]
      ring
    rw [e]
    linarith
  -- The limit `R → ∞`, with the weight `1` and no drift.
  have key := integral_energyDensity_le_of_forall_radialCutoff (v := v) (W := fun _ ↦ 0)
    (ω := fun _ ↦ 1) (c := c) (M := 0) hv contDiff_const
    (fun x ↦ by simp [PDE.divergence_eq_sum, PDE.partialDeriv_const]) (fun x ↦ by simp)
    contDiff_const (fun _ ↦ zero_le_one) (by simpa only [one_mul] using hDv)
    (by simpa only [one_mul] using hv2) (by simp) (by simp) hK
  have hE : (fun x ↦ energyDensity c v (fun _ ↦ 0) (fun _ ↦ 1) x) =
      fun x ↦ (∑ i : Fin n, ‖∂[i] v x‖ ^ 2) + (c + n / 4) * ‖v x‖ ^ 2 := funext fun x ↦ by
    simp [energyDensity]
  rw [hE, integral_add hDv (hv2.const_mul _), integral_const_mul] at key
  exact key

/-- **The energy estimate with data in divergence form, by components.** Let `w₁, …, wₙ` be
`C²` functions on `ℝⁿ` with `Σᵢ ∂ᵢwᵢ = 0`, square integrable with their first derivatives, and
suppose that for every `i`

`c wᵢ - ½ x·∇wᵢ - Δwᵢ = g₀ᵢ + Σₘ ∂_{d(m)} gₘᵢ - ∂ᵢq`,

with `g₀ᵢ` continuous, `gₘᵢ` and `q` of class `C¹`, all square integrable. Then

`Σᵢ Σₗ ∫ (∂ₗwᵢ)² + (c + n/4) Σᵢ ∫ wᵢ² ≤ √(Σᵢ ∫ g₀ᵢ²) √(Σᵢ ∫ wᵢ²)
  + Σₘ √(Σᵢ ∫ gₘᵢ²) √(Σᵢ ∫ (∂_{d(m)}wᵢ)²)`.

It is `integral_energy_le_of_divergence_form` for the field with components `wᵢ`. -/
theorem integral_energy_le_of_divergence_form_components {ι : Type*} [Fintype ι]
    {w g₀ : Fin n → ℝ^n → ℝ} {g : ι → Fin n → ℝ^n → ℝ} {q : ℝ^n → ℝ} {c : ℝ} (d : ι → Fin n)
    (hw : ∀ i, ContDiff ℝ 2 (w i)) (hdiv : ∀ x, ∑ i, ∂[i] (w i) x = 0)
    (hg₀ : ∀ i, Continuous (g₀ i)) (hg : ∀ m i, ContDiff ℝ 1 (g m i)) (hq : ContDiff ℝ 1 q)
    (heq : ∀ i x, c * w i x - (1 / 2 : ℝ) * fderiv ℝ (w i) x x - laplacian (w i) x =
      g₀ i x + (∑ m, ∂[d m] (g m i) x) - ∂[i] q x)
    (hw2 : ∀ i, Integrable fun x ↦ w i x ^ 2)
    (hDw : ∀ i l, Integrable fun x ↦ ∂[l] (w i) x ^ 2)
    (hg₀2 : ∀ i, Integrable fun x ↦ g₀ i x ^ 2) (hg2 : ∀ m i, Integrable fun x ↦ g m i x ^ 2)
    (hq2 : Integrable fun x ↦ q x ^ 2) :
    (∑ i, ∑ l, ∫ x, ∂[l] (w i) x ^ 2) + (c + n / 4) * ∑ i, ∫ x, w i x ^ 2 ≤
      √(∑ i, ∫ x, g₀ i x ^ 2) * √(∑ i, ∫ x, w i x ^ 2) +
        ∑ m, √(∑ i, ∫ x, g m i x ^ 2) * √(∑ i, ∫ x, ∂[d m] (w i) x ^ 2) := by
  -- The fields with these components.
  set v : ℝ^n → ℝ^n := fun x ↦ WithLp.toLp 2 fun i ↦ w i x with hvdef
  set G₀ : ℝ^n → ℝ^n := fun x ↦ WithLp.toLp 2 fun i ↦ g₀ i x with hG₀def
  set G : ι → ℝ^n → ℝ^n := fun m x ↦ WithLp.toLp 2 fun i ↦ g m i x with hGdef
  have hv : ContDiff ℝ 2 v := contDiff_euclidean.2 hw
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hG₀ : Continuous G₀ :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ hg₀ i)
  have hG : ∀ m, ContDiff ℝ 1 (G m) := fun m ↦ contDiff_euclidean.2 (hg m)
  have hGd : ∀ m, Differentiable ℝ (G m) := fun m ↦ (hG m).differentiable one_ne_zero
  -- Derivatives by components.
  have hpd : ∀ (l i : Fin n) (x : ℝ^n), ∂[l] v x i = ∂[l] (w i) x := fun l i x ↦
    partialDeriv_apply l i (hvd x)
  have hpdG : ∀ m (l i : Fin n) (x : ℝ^n), ∂[l] (G m) x i = ∂[l] (g m i) x := fun m l i x ↦
    partialDeriv_apply l i (hGd m x)
  have hfd : ∀ (i : Fin n) (x h : ℝ^n), (fderiv ℝ v x h) i = fderiv ℝ (w i) x h :=
    fun i x h ↦ by
      have h1 := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
        (hvd x).hasFDerivAt).fderiv
      exact (congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L h) h1).symm
  -- Norms by components.
  have hn : ∀ x, ‖v x‖ ^ 2 = ∑ i, w i x ^ 2 := fun x ↦ EuclideanSpace.real_norm_sq_eq _
  have hnD : ∀ l x, ‖∂[l] v x‖ ^ 2 = ∑ i, ∂[l] (w i) x ^ 2 := fun l x ↦ by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [hpd]
  have hnG₀ : ∀ x, ‖G₀ x‖ ^ 2 = ∑ i, g₀ i x ^ 2 := fun x ↦ EuclideanSpace.real_norm_sq_eq _
  have hnG : ∀ m x, ‖G m x‖ ^ 2 = ∑ i, g m i x ^ 2 := fun m x ↦
    EuclideanSpace.real_norm_sq_eq _
  -- The paired equation.
  have heqv : ∀ x, similarityPairing c v (fun _ ↦ 0) x =
      ⟪G₀ x, v x⟫_ℝ + (∑ m, ⟪∂[d m] (G m) x, v x⟫_ℝ) - fderiv ℝ q x (v x) := fun x ↦ by
    have hq' : fderiv ℝ q x (v x) = ∑ i, ∂[i] q x * w i x :=
      fderiv_apply_eq_sum_partialDeriv_mul q x (v x)
    have hin : ∀ m, ⟪∂[d m] (G m) x, v x⟫_ℝ = ∑ i, ∂[d m] (g m i) x * w i x := fun m ↦ by
      rw [EuclideanSpace.real_inner_eq_sum]
      simp only [hpdG]
      rfl
    rw [similarityPairing, EuclideanSpace.real_inner_eq_sum, EuclideanSpace.real_inner_eq_sum,
      hq']
    simp only [hin]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi := heq i x
    have hc : (c • v x - (1 / 2 : ℝ) • fderiv ℝ v x x + fderiv ℝ v x ((fun _ ↦ 0) x) -
        laplacian v x) i = c * w i x - (1 / 2 : ℝ) * fderiv ℝ (w i) x x - laplacian (w i) x := by
      rw [map_zero, add_zero]
      change c * v x i - (1 / 2 : ℝ) * (fderiv ℝ v x x) i - (laplacian v x) i = _
      rw [hfd, laplacian_apply_of_contDiff hv x i]
    rw [hc, hi, ← Finset.sum_mul]
    change _ = g₀ i x * w i x + (∑ m, ∂[d m] (g m i) x) * w i x - ∂[i] q x * w i x
    ring
  -- The integrals by components.
  have hvint : Integrable fun x ↦ ‖v x‖ ^ 2 := by
    simp only [hn]
    exact integrable_finsetSum _ fun i _ ↦ hw2 i
  have hDvint : Integrable fun x ↦ ∑ l : Fin n, ‖∂[l] v x‖ ^ 2 := by
    simp only [hnD]
    exact integrable_finsetSum _ fun l _ ↦ integrable_finsetSum _ fun i _ ↦ hDw i l
  have hG₀int : Integrable fun x ↦ ‖G₀ x‖ ^ 2 := by
    simp only [hnG₀]
    exact integrable_finsetSum _ fun i _ ↦ hg₀2 i
  have hGint : ∀ m, Integrable fun x ↦ ‖G m x‖ ^ 2 := fun m ↦ by
    simp only [hnG]
    exact integrable_finsetSum _ fun i _ ↦ hg2 m i
  have hdivv : ∀ x, ∇· v x = 0 := fun x ↦ by
    rw [PDE.divergence_eq_sum]
    exact hdiv x
  have key := integral_energy_le_of_divergence_form d hv hdivv hG₀ hG hq heqv hvint hDvint
    hG₀int hGint hq2
  simp only [hn, hnD, hnG₀, hnG] at key
  rw [integral_finsetSum _ fun l _ ↦ integrable_finsetSum _ fun i _ ↦ hDw i l,
    integral_finsetSum _ fun i _ ↦ hw2 i, integral_finsetSum _ fun i _ ↦ hg₀2 i] at key
  simp only [integral_finsetSum _ fun i _ ↦ hDw i _,
    integral_finsetSum _ fun i _ ↦ hg2 _ i] at key
  rw [Finset.sum_comm]
  exact key

end PDE.Analysis
