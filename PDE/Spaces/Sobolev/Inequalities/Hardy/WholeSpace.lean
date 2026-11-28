/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Complex
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
public import PDE.Spaces.Sobolev.Inequalities.Hardy.Ball

/-!
# Hardy's inequality on the whole space

In dimension `n ≥ 3`, every `u ∈ L²(ℝⁿ)` whose weak partial derivatives are in `L²` satisfies

`∫ u² / |x|² ≤ 4 ∫ |∇u|²`,

and in particular `u / |x|` is square integrable. The same holds for complex functions, with
`|u|²` on the left. The constant `4` is the sharp constant `4 / (n - 2)²` only for `n = 3`; the
sharp constant in higher dimensions is not proved here.

## Main results

* `SobolevSpace.Hardy.integrable_hardy_and_bound`: for `n ≥ 3` and a real `f ∈ L²(ℝⁿ)` with weak
  partial derivatives `g i ∈ L²`, `f² / |x|²` is integrable and `∫ f² / |x|² ≤ 4 ∑ᵢ ∫ (g i)²`.
* `SobolevSpace.Hardy.integrable_hardy_complex`: for `n ≥ 3` and `G ∈ L²(ℝⁿ; ℂ)` with complex weak
  partial derivatives `D l ∈ L²`, `|G|² / |x|²` is integrable and `∫ |G|² / |x|² ≤ 4 ∑ₗ ‖D l‖²`.

## How it works

On the ball of radius `r` the inequality holds with the extra term `2n r⁻² ∫ u²`
(`integrable_hardy_ball_and_bound`, Evans's Theorem 7 in §5.8.4). Apply it to `u` restricted to
the balls of radius `k + 1` and let `k → ∞`: the extra term goes away and the left side
increases to the integral over `ℝⁿ`. A complex function is treated through its real and
imaginary parts.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.4, Theorem 7, pp. 296-297: the inequality on a
  ball. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology Sobolev

namespace SobolevSpace.Hardy

open GraphSpace

variable {n : ℕ}

/-- **Hardy's inequality on `ℝⁿ`**, `n ≥ 3`. If `f ∈ L²` has weak partial derivatives
`g i ∈ L²`, then `f² / |x|²` is integrable and `∫ f² / |x|² ≤ 4 ∑ᵢ ∫ (g i)²`. The proof applies
the inequality on the balls of radius `k + 1` and lets `k → ∞`. -/
theorem integrable_hardy_and_bound (hn : 3 ≤ n) {f : ℝ^n → ℝ} {g : Fin n → ℝ^n → ℝ}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakDerivativeOn univ [i] f (g i)) :
    Integrable (fun x ↦ f x ^ 2 / ‖x‖ ^ 2) ∧
      ∫ x, f x ^ 2 / ‖x‖ ^ 2 ≤ 4 * ∑ i, ∫ x, g i x ^ 2 := by
  -- the gradient as one vector field
  set G : ℝ^n → ℝ^n := fun x ↦ WithLp.toLp 2 fun i ↦ g i x with hGdef
  have hG : MemLp G 2 volume := memLp_piLp_iff.2 hg
  have hGnorm (x : ℝ^n) : ‖G x‖ ^ 2 = ∑ i, g i x ^ 2 := EuclideanSpace.real_norm_sq_eq _
  have hf2 : Integrable (fun x ↦ f x ^ 2) := hf.integrable_sq
  have hg2 (i : Fin n) : Integrable (fun x ↦ g i x ^ 2) := (hg i).integrable_sq
  have hG2 : Integrable (fun x ↦ ‖G x‖ ^ 2) := by
    simp_rw [hGnorm]
    exact integrable_finsetSum _ fun i _ ↦ hg2 i
  have hGint : ∫ x, ‖G x‖ ^ 2 = ∑ i, ∫ x, g i x ^ 2 := by
    simp_rw [hGnorm]
    exact integral_finsetSum _ fun i _ ↦ hg2 i
  rw [← hGint]
  -- the inequality on the ball of radius `k + 1`
  have hball (k : ℕ) : IntegrableOn (fun x ↦ f x ^ 2 / ‖x‖ ^ 2) (ball (0 : ℝ^n) ((k : ℝ) + 1)) ∧
      ∫ x in ball (0 : ℝ^n) ((k : ℝ) + 1), f x ^ 2 / ‖x‖ ^ 2 ≤
        4 * (∫ x, ‖G x‖ ^ 2) + 2 * (n : ℝ) / ((k : ℝ) + 1) ^ 2 * ∫ x, f x ^ 2 := by
    have hr : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    obtain ⟨U, hU, hDU⟩ := exists_of_weakGradient (Ω := ball (0 : ℝ^n) ((k : ℝ) + 1)) (p := 2)
      (hf.restrict _) (hG.restrict _)
      (fun i ↦ (hweak i).mono measurableSet_ball (subset_univ _))
    obtain ⟨hint, hle⟩ := integrable_hardy_ball_and_bound hn hr U
    have hsq : (fun x ↦ baseRepresentative U x ^ 2 / ‖x‖ ^ 2)
        =ᵐ[volume.restrict (ball (0 : ℝ^n) ((k : ℝ) + 1))] fun x ↦ f x ^ 2 / ‖x‖ ^ 2 := by
      filter_upwards [hU] with x hx
      rw [hx]
    have hgrad : ‖∇ U‖ ^ 2 ≤ ∫ x, ‖G x‖ ^ 2 := by
      rw [Lp.norm_sq_eq_integral_norm_sq]
      calc ∫ x, ‖∇ U x‖ ^ 2 ∂domainMeasure n (ball (0 : ℝ^n) ((k : ℝ) + 1))
          = ∫ x in ball (0 : ℝ^n) ((k : ℝ) + 1), ‖G x‖ ^ 2 := by
            refine integral_congr_ae ?_
            filter_upwards [hDU] with x hx
            rw [hx]
        _ ≤ ∫ x, ‖G x‖ ^ 2 :=
            setIntegral_le_integral hG2 (Eventually.of_forall fun x ↦ sq_nonneg _)
    have hbase : ‖wkpBaseCoordinateCLM U‖ ^ 2 ≤ ∫ x, f x ^ 2 := by
      rw [Lp.norm_sq_eq_integral_sq]
      calc ∫ x, wkpBaseCoordinateCLM U x ^ 2 ∂domainMeasure n (ball (0 : ℝ^n) ((k : ℝ) + 1))
          = ∫ x in ball (0 : ℝ^n) ((k : ℝ) + 1), f x ^ 2 := by
            refine integral_congr_ae ?_
            filter_upwards [hU] with x hx
            exact congrArg (· ^ 2) hx
        _ ≤ ∫ x, f x ^ 2 :=
            setIntegral_le_integral hf2 (Eventually.of_forall fun x ↦ sq_nonneg _)
    refine ⟨hint.congr_fun_ae hsq, ?_⟩
    calc ∫ x in ball (0 : ℝ^n) ((k : ℝ) + 1), f x ^ 2 / ‖x‖ ^ 2
        = ∫ x in ball (0 : ℝ^n) ((k : ℝ) + 1), baseRepresentative U x ^ 2 / ‖x‖ ^ 2 :=
          (integral_congr_ae hsq).symm
      _ ≤ 4 * ‖∇ U‖ ^ 2 + 2 * (n : ℝ) / ((k : ℝ) + 1) ^ 2 * ‖wkpBaseCoordinateCLM U‖ ^ 2 := hle
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hgrad (by norm_num))
          (mul_le_mul_of_nonneg_left hbase (by positivity))
  refine integrable_and_integral_le_of_ae_limit_nonneg_of_tendsto_bound
    (u := fun k ↦ (ball (0 : ℝ^n) ((k : ℝ) + 1)).indicator fun x ↦ f x ^ 2 / ‖x‖ ^ 2)
    (b := fun k ↦ 4 * (∫ x, ‖G x‖ ^ 2) + 2 * (n : ℝ) / ((k : ℝ) + 1) ^ 2 * ∫ x, f x ^ 2)
    (fun k ↦ (integrable_indicator_iff measurableSet_ball).2 (hball k).1)
    (fun k ↦ Eventually.of_forall fun x ↦ indicator_nonneg (fun y _ ↦ by positivity) x)
    (fun k ↦ by rw [integral_indicator measurableSet_ball]; exact (hball k).2)
    ?_ (Eventually.of_forall fun x ↦ ?_)
  · have h1 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := ((h1.pow 2).const_mul (2 * (n : ℝ))).mul_const (∫ x, f x ^ 2)
    have h3 := (tendsto_const_nhds (x := 4 * ∫ x, ‖G x‖ ^ 2)).add h2
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
      add_zero] at h3
    refine h3.congr fun k ↦ ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
  · obtain ⟨k₀, hk₀⟩ := exists_nat_gt ‖x‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k₀] with k hk
    rw [indicator_of_mem]
    have : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    exact mem_ball_zero_iff.2 (by linarith)

/-- **Hardy's inequality on `ℝⁿ` for complex functions**, `n ≥ 3`: if `G ∈ L²(ℝⁿ; ℂ)` has
complex weak partial derivatives `D l ∈ L²`, then `|G|² / |x|²` is integrable and
`∫ |G|² / |x|² ≤ 4 ∑ₗ ‖D l‖²`. This is `integrable_hardy_and_bound` for the real and the
imaginary part. -/
theorem integrable_hardy_complex (hn : 3 ≤ n) (G : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (D : Fin n → Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hD : ∀ l, HasComplexWeakDerivativeOn univ [l] G (D l)) :
    Integrable (fun x ↦ ‖G x‖ ^ 2 / ‖x‖ ^ 2) ∧
      ∫ x, ‖G x‖ ^ 2 / ‖x‖ ^ 2 ≤ 4 * ∑ l, ‖D l‖ ^ 2 := by
  obtain ⟨hre, hre'⟩ := integrable_hardy_and_bound hn (f := fun x ↦ (G x).re)
    (g := fun l x ↦ (D l x).re) (Lp.memLp G).re (fun l ↦ (Lp.memLp (D l)).re) fun l ↦ (hD l).1
  obtain ⟨him, him'⟩ := integrable_hardy_and_bound hn (f := fun x ↦ (G x).im)
    (g := fun l x ↦ (D l x).im) (Lp.memLp G).im (fun l ↦ (Lp.memLp (D l)).im) fun l ↦ (hD l).2
  have hsplit (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hfun : (fun x ↦ ‖G x‖ ^ 2 / ‖x‖ ^ 2) =
      fun x ↦ (G x).re ^ 2 / ‖x‖ ^ 2 + (G x).im ^ 2 / ‖x‖ ^ 2 :=
    funext fun x ↦ by rw [hsplit, add_div]
  have hDl (l : Fin n) : ‖D l‖ ^ 2 = (∫ x, (D l x).re ^ 2) + ∫ x, (D l x).im ^ 2 := by
    have hre2 : Integrable (fun x ↦ (D l x).re ^ 2) := (Lp.memLp (D l)).re.integrable_sq
    have him2 : Integrable (fun x ↦ (D l x).im ^ 2) := (Lp.memLp (D l)).im.integrable_sq
    rw [Lp.norm_sq_eq_integral_norm_sq, ← integral_add hre2 him2]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ hsplit _)
  rw [hfun]
  refine ⟨hre.add him, ?_⟩
  rw [integral_add hre him]
  simp_rw [hDl]
  rw [Finset.sum_add_distrib, mul_add]
  exact add_le_add hre' him'

end SobolevSpace.Hardy
