/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Mollification.Relative
import CAS.ExactTactic

/-!
# Singular weighted error of relative mollification

The constructed mollification error vanishes on fixed neighborhoods of the origin
and the outer endpoints. Only upper comparisons for the input weights on the remaining
compact annulus are needed. In particular, weights may have infinite mass at zero.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace PDE.Analysis.Calculus

/-- Uniform control of the value and derivative on a fixed error annulus
bounds the singular weighted energy by a finite constant times the squared tolerance. -/
theorem singularWeightedH1Error_le_of_uniform_jet_bound {q w v : ℝ → ℝ}
    {a b L A B ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hzero : ∀ x, 0 < x → x < a ∨ b < x → q x = 0)
    (hvalue : ∀ x, |q x| ≤ ε) (hderiv : ∀ x, |deriv q x| ≤ ε)
    (hw : ∀ x ∈ Icc a b, w x ≤ A) (hv : ∀ x ∈ Icc a b, v x ≤ B) :
    singularWeightedH1Error w v q L ≤ ENNReal.ofReal (L * (ε ^ 2 * (A + B))) := by
  have hzero' : ∀ x, 0 < x → x < a ∨ b < x → deriv q x = 0 := by
    intro x hx0 hx
    have heq : q =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      rcases hx with hx | hx
      · filter_upwards [eventually_gt_nhds hx0, eventually_lt_nhds hx] with y hy0 hy
        exact hzero y hy0 (Or.inl hy)
      · filter_upwards [eventually_gt_nhds hx0, eventually_gt_nhds hx] with y hy0 hy
        exact hzero y hy0 (Or.inr hy)
    rw [heq.deriv_eq, deriv_const]
  have hdensity : ∀ x, 0 < x →
      q x ^ 2 * w x + deriv q x ^ 2 * v x ≤ ε ^ 2 * (A + B) := by
    intro x hx0
    by_cases hx : x ∈ Icc a b
    · have hq : q x ^ 2 ≤ ε ^ 2 := sq_le_sq.2 ((hvalue x).trans (le_abs_self ε))
      have hd : deriv q x ^ 2 ≤ ε ^ 2 :=
        sq_le_sq.2 ((hderiv x).trans (le_abs_self ε))
      calc
        _ ≤ q x ^ 2 * A + deriv q x ^ 2 * B :=
          add_le_add (mul_le_mul_of_nonneg_left (hw x hx) (sq_nonneg _))
            (mul_le_mul_of_nonneg_left (hv x hx) (sq_nonneg _))
        _ ≤ ε ^ 2 * A + ε ^ 2 * B :=
          add_le_add (mul_le_mul_of_nonneg_right hq hA) (mul_le_mul_of_nonneg_right hd hB)
        _ = _ := by cas
    · have hx' : x < a ∨ b < x := by
        simpa only [mem_Icc, not_and_or, not_le] using hx
      rw [hzero x hx0 hx', hzero' x hx0 hx']
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        add_zero]
      exact mul_nonneg (sq_nonneg _) (add_nonneg hA hB)
  calc
    singularWeightedH1Error w v q L ≤
        ∫⁻ _ in Ioo 0 L, ENNReal.ofReal (ε ^ 2 * (A + B)) :=
      setLIntegral_mono' measurableSet_Ioo
        (fun x hx ↦ ENNReal.ofReal_le_ofReal (hdensity x hx.1))
    _ = ENNReal.ofReal (L * (ε ^ 2 * (A + B))) := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
        ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (add_nonneg hA hB))]
      congr 1
      cas

/-- Compact smooth odd approximations with arbitrarily small singular weighted
`H¹` error, exact origin germ, and unchanged origin derivative. The input is compact `C¹`;
the weight assumptions concern only a fixed compact annulus away from the singularities. -/
theorem exists_smooth_odd_relative_weighted_approximation {f p w v : ℝ → ℝ}
    {r R s L A B ε : ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hp : ContDiff ℝ ∞ p) (hfodd : ∀ x, f (-x) = -f x)
    (hpodd : ∀ x, p (-x) = -p x)
    (hr : 0 < r) (hrR : r < R) (hs : 0 < s) (hRL : R + s < L)
    (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfp : ∀ x, |x| < r → f x = p x)
    (hfzero : ∀ x, R ≤ |x| → f x = 0)
    (hw : ∀ x ∈ Icc (r / 4) (R + s), w x ≤ A)
    (hv : ∀ x ∈ Icc (r / 4) (R + s), v x ≤ B) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x, g (-x) = -g x) ∧ tsupport g ⊆ Icc (-(R + s)) (R + s) ∧
      g =ᶠ[𝓝 0] f ∧ deriv g 0 = deriv f 0 ∧
      deriv (fun x ↦ g x - f x) 0 = 0 ∧
      singularWeightedH1Error w v (fun x ↦ g x - f x) L < ENNReal.ofReal ε := by
  have hL : 0 < L := by cas
  let M := L * (A + B)
  have hM : 0 ≤ M := mul_nonneg hL.le (add_nonneg hA hB)
  let η := min 1 (ε / (2 * (M + 1)))
  have hden : 0 < 2 * (M + 1) := by positivity
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηbound : η * (2 * (M + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have henergy : L * (η ^ 2 * (A + B)) < ε := by
    have hsquare : η ^ 2 ≤ η := by cas
    have hmultiply := mul_le_mul_of_nonneg_right hsquare hM
    change η ^ 2 * (L * (A + B)) ≤ η * (L * (A + B)) at hmultiply
    dsimp only [M] at hηbound
    cas
  obtain ⟨g, hg, hgc, hgodd, hginner, hgouter, hvalue, hderiv⟩ :=
    exists_smooth_odd_relative_approximation hf hfc hp hfodd hpodd hr hrR hs hη hfp hfzero
  have hlocal := origin_deriv_eq_of_eq_on_ball (show 0 < r / 4 by positivity)
    (fun x hx ↦ hginner x hx.le)
  refine ⟨g, hg, hgc, hgodd, ?_, hlocal.1, hlocal.2.1, hlocal.2.2, ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hn
    have hle : R + s ≤ |x| := le_of_not_gt (fun h ↦ hn (abs_le.mp h.le))
    exact hx (hgouter x hle)
  · have hzero : ∀ x, 0 < x → x < r / 4 ∨ R + s < x → g x - f x = 0 := by
      intro x hx0 hx
      rcases hx with hx | hx
      · exact sub_eq_zero.mpr (hginner x (by rw [abs_of_pos hx0]; exact hx.le))
      · rw [hgouter x (hx.le.trans (le_abs_self x)),
          hfzero x (by have := le_abs_self x; cas), sub_self]
    have hbound := singularWeightedH1Error_le_of_uniform_jet_bound (L := L) hA hB hzero hvalue
      (fun x ↦ ?_) hw hv
    · exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 henergy)
    · have hd : deriv (fun x ↦ g x - f x) x = deriv g x - deriv f x :=
        deriv_sub ((hg.differentiable (by simp)) x) (hf.differentiable one_ne_zero x)
      rw [hd]
      exact hderiv x

end PDE.Analysis.Calculus
