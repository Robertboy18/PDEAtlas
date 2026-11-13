/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.GaussianGrowth.Barrier
public import PDE.Parabolic.Heat.MaximumPrinciple
import CAS.ExactTactic
import PDE.FDeriv.Calculus

/-!
# Comparison under one-sided Gaussian growth

Subtract a positive multiple of a growing Gaussian and compare on a sufficiently large ball. The
radius is chosen from the growth bound and the perturbation size. Letting the perturbation tend to
zero gives comparison with the initial data. This is the comparison step (25)-(29) of Evans's proof
of §2.3.3(a), Theorem 6, with `growingGaussian` in place of his barrier
`μ(T + ε - t)^(-n/2) exp(|x - y|² / (4(T + ε - t)))`.

## Main results

* `heat_subsolution_le_of_gaussian_growth_short`: the comparison when `(4 + 2n)(a + 1)T < 1`.
* `heat_subsolution_le_of_gaussian_growth`: the comparison for every `T > 0`, from successive short
  intervals.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.3(a), Theorem 6 (Maximum principle for the Cauchy
  problem) and its proof, (23)-(29), pp. 57-58.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HeatEquation

open Set ParabolicMaximum Metric

/-- Initial upper bounds propagate for a short time under one-sided Gaussian growth.
The time restriction comes only from the chosen barrier's denominator. -/
theorem heat_subsolution_le_of_gaussian_growth_short {n : ℕ} {A a T M : ℝ}
    (ha : 0 ≤ a) (hT : 0 < T)
    (hsmall : (4 + 2 * (n : ℝ)) * (a + 1) * T < 1)
    (u : ℝ^n → ℝ → ℝ)
    (hucont : ContinuousOn (fun p ↦ u p.1 p.2) (univ ×ˢ Icc 0 T))
    (huspace : ∀ x, ∀ t ∈ Ioc 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x, ∀ t ∈ Ioc 0 T, heatParabolicOperator u x t ≤ 0)
    (hgrowth : ∀ x, ∀ t ∈ Icc 0 T, u x t ≤ A * Real.exp (a * ‖x‖ ^ 2))
    (hinitial : ∀ x, u x 0 ≤ M) :
    ∀ x, ∀ t ∈ Icc 0 T, u x t ≤ M := by
  let b := a + 1
  let c := (4 + 2 * (n : ℝ)) * b
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hc₁ : 4 * b ≤ c := by dsimp only [c]; nlinarith
  have hc₂ : 2 * (n : ℝ) * b ≤ c := by dsimp only [c]; nlinarith
  have hden {t : ℝ} (ht : t ∈ Icc 0 T) : 0 < 1 - c * t := by
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hc, show c * T < 1 from hsmall]
  have hBcont : ContinuousOn (fun p : ℝ^n × ℝ ↦ growingGaussian b c p.1 p.2)
      (univ ×ˢ Icc 0 T) := by
    unfold growingGaussian
    apply Real.continuous_exp.comp_continuousOn
    exact (by fun_prop : ContinuousOn (fun p : ℝ^n × ℝ ↦ b * ‖p.1‖ ^ 2 + 1)
      (univ ×ˢ Icc 0 T)).div (by fun_prop) (fun p hp ↦ (hden hp.2).ne')
  intro x t ht
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  let δ := ε / growingGaussian b c x t
  have hδ : 0 < δ := div_pos hε (growingGaussian_pos b c x t)
  obtain ⟨R, hR⟩ := exists_gt (max ‖x‖ (max 1 ((A + |M|) / δ)))
  simp only [max_lt_iff] at hR
  obtain ⟨hxR, hRone, hRlarge⟩ := hR
  have hRpos : 0 < R := zero_lt_one.trans hRone
  have hdom : A + |M| ≤ δ * Real.exp (R ^ 2) := by
    have hexp : R ≤ Real.exp (R ^ 2) := by nlinarith [Real.add_one_le_exp (R ^ 2)]
    nlinarith [(div_lt_iff₀ hδ).mp hRlarge]
  let v : ℝ^n → ℝ → ℝ := fun y s ↦ u y s - δ * growingGaussian b c y s
  have hvcont : ContinuousOn (fun p ↦ v p.1 p.2) (closedCylinder (ball 0 R) T) :=
    (hucont.sub (hBcont.const_mul δ)).mono fun p hp ↦ ⟨mem_univ _, hp.2⟩
  have hBspace (y : ℝ^n) (s : ℝ) :
      ContDiffAt ℝ 2 (fun z ↦ growingGaussian b c z s) y :=
    (growingGaussian_contDiff_space b c s).contDiffAt.of_le (by simp)
  have hBtime (y : ℝ^n) {s : ℝ} (hs : s ∈ Ioc 0 T) :
      DifferentiableAt ℝ (growingGaussian b c y) s :=
    (growingGaussian_hasDerivAt b c y s (hden ⟨hs.1.le, hs.2⟩).ne').differentiableAt
  have hvsub (y : ℝ^n) (s : ℝ) (hs : s ∈ Ioc 0 T) :
      heatParabolicOperator v y s ≤ 0 := by
    have hu := hsub y s hs
    have hB := growingGaussian_supersolution y hb hc₁ hc₂ hs.1.le
      (hden ⟨hs.1.le, hs.2⟩)
    have hderiv : deriv (fun r ↦ u y r - δ * growingGaussian b c y r) s =
        deriv (u y) s - δ * deriv (growingGaussian b c y) s :=
      ((hutime y s hs).hasDerivAt.sub ((hBtime y hs).hasDerivAt.const_mul δ)).deriv
    unfold heatParabolicOperator at *
    dsimp only [v]
    rw [hderiv,
      PDE.laplacian_sub _ _ y (huspace y s hs) (contDiffAt_const.mul (hBspace y s)),
      PDE.laplacian_const_smul]
    nlinarith [mul_nonneg hδ.le hB]
  have hvboundary : ∀ p ∈ parabolicBoundary (ball 0 R) T, v p.1 p.2 ≤ M := by
    intro p hp
    rcases hp with hp | hp
    · have hnorm : ‖p.1‖ = R := by
        simpa only [frontier_ball _ hRpos.ne', mem_sphere, dist_zero_right] using hp.1
      have he : 1 ≤ Real.exp (a * R ^ 2) :=
        Real.one_le_exp_iff.mpr (mul_nonneg ha (sq_nonneg _))
      have hB := exp_norm_sq_le_growingGaussian p.1 hb hc hp.2.1 (hden hp.2)
      have hsplit : Real.exp (b * ‖p.1‖ ^ 2) =
          Real.exp (a * R ^ 2) * Real.exp (R ^ 2) := by
        rw [hnorm]
        dsimp only [b]
        cas
      rw [hsplit] at hB
      have hu := hgrowth p.1 p.2 hp.2
      rw [hnorm] at hu
      have hM : -M ≤ |M| * Real.exp (a * R ^ 2) :=
        (neg_le_abs M).trans (le_mul_of_one_le_right (abs_nonneg _) he)
      have hbound := mul_le_mul_of_nonneg_left hdom
        (Real.exp_pos (a * R ^ 2)).le
      dsimp only [v]
      nlinarith [mul_le_mul_of_nonneg_left hB hδ.le]
    · simp only [v, show p.2 = 0 from hp.2]
      exact (sub_le_self _ (mul_nonneg hδ.le (growingGaussian_pos b c p.1 0).le)).trans
        (hinitial p.1)
  have hv := heat_subsolution_le_of_boundary_le isOpen_ball
    (nonempty_ball.mpr hRpos)
    (by rw [closure_ball _ hRpos.ne']; exact isCompact_closedBall _ _) hT v hvcont
    (fun y _ s hs ↦ (huspace y s ⟨hs.1, hs.2.le⟩).sub
      (contDiffAt_const.mul (hBspace y s)))
    (fun y _ s hs ↦ (hutime y s ⟨hs.1, hs.2.le⟩).sub
      ((hBtime y ⟨hs.1, hs.2.le⟩).const_mul δ))
    (fun y _ s hs ↦ hvsub y s ⟨hs.1, hs.2.le⟩) hvboundary (x, t)
    ⟨subset_closure (by simpa using hxR), ht⟩
  have hδB : δ * growingGaussian b c x t = ε :=
    div_mul_cancel₀ _ (growingGaussian_pos b c x t).ne'
  dsimp only [v] at hv
  linarith

/-- The comparison on `[0, T]` for any `T`, obtained by applying the short-time comparison on
successive intervals of length at most `1 / (2 * (4 + 2n) * (a + 1))`. -/
private theorem le_of_gaussian_growth_on_Ioc {n : ℕ} {A a T M : ℝ}
    (ha : 0 ≤ a) (u : ℝ^n → ℝ → ℝ)
    (hucont : ContinuousOn (fun p ↦ u p.1 p.2) (univ ×ˢ Icc 0 T))
    (huspace : ∀ x, ∀ t ∈ Ioc 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x, ∀ t ∈ Ioc 0 T, heatParabolicOperator u x t ≤ 0)
    (hgrowth : ∀ x, ∀ t ∈ Icc 0 T, u x t ≤ A * Real.exp (a * ‖x‖ ^ 2))
    (hinitial : ∀ x, u x 0 ≤ M) :
    ∀ x, ∀ t ∈ Icc 0 T, u x t ≤ M := by
  let c := (4 + 2 * (n : ℝ)) * (a + 1)
  let d := 1 / (2 * c)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hcd : c * d = 1 / 2 := by
    dsimp only [d]
    cas using hc.ne'
  have hsteps (k : ℕ) : ∀ x, ∀ t ∈ Icc 0 T, t ≤ k * d → u x t ≤ M := by
    induction k with
    | zero =>
      intro x t ht htk
      simpa [le_antisymm (by simpa using htk) ht.1] using hinitial x
    | succ k ih =>
      intro x t ht htk
      by_cases hearly : t ≤ k * d
      · exact ih x t ht hearly
      have hs : 0 ≤ (k : ℝ) * d := mul_nonneg (Nat.cast_nonneg _) hd.le
      have hst : (k : ℝ) * d < t := lt_of_not_ge hearly
      have hlength : 0 < t - k * d := sub_pos.mpr hst
      have hlength_le : t - k * d ≤ d := by
        rw [Nat.cast_add, Nat.cast_one] at htk
        nlinarith
      have hsmall : c * (t - k * d) < 1 := by
        linarith [mul_le_mul_of_nonneg_left hlength_le hc.le]
      have hshift {r : ℝ} (hr : r ∈ Icc 0 (t - k * d)) : (k : ℝ) * d + r ∈ Icc 0 T :=
        ⟨add_nonneg hs hr.1, by linarith [hr.2, ht.2]⟩
      have hshift_pos {r : ℝ} (hr : r ∈ Ioc 0 (t - k * d)) : (k : ℝ) * d + r ∈ Ioc 0 T :=
        ⟨by linarith [hr.1], (hshift ⟨hr.1.le, hr.2⟩).2⟩
      have htime (y : ℝ^n) {r : ℝ} (hr : r ∈ Ioc 0 (t - k * d)) :
          HasDerivAt (fun q ↦ u y (k * d + q)) (deriv (u y) (k * d + r)) r := by
        simpa only [Function.comp_def, mul_one] using
          (hutime y _ (hshift_pos hr)).hasDerivAt.comp r
          ((hasDerivAt_id r).const_add (k * d))
      have hcont : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.1 (k * d + p.2))
          (univ ×ˢ Icc 0 (t - k * d)) :=
        hucont.comp (f := fun p : ℝ^n × ℝ ↦ (p.1, k * d + p.2))
          (by fun_prop) (fun p hp ↦ ⟨mem_univ _, hshift hp.2⟩)
      have hbound := heat_subsolution_le_of_gaussian_growth_short ha hlength hsmall
        (fun y r ↦ u y (k * d + r)) hcont
        (fun y r hr ↦ huspace y _ (hshift_pos hr))
        (fun y _ hr ↦ (htime y hr).differentiableAt)
        (fun y r hr ↦ by
          unfold heatParabolicOperator
          rw [(htime y hr).deriv]
          exact hsub y _ (hshift_pos hr))
        (fun y r hr ↦ hgrowth y _ (hshift hr))
        (fun y ↦ by
          simpa using ih y (k * d) ⟨hs, hst.le.trans ht.2⟩ le_rfl)
        x (t - k * d) ⟨hlength.le, le_rfl⟩
      simpa using hbound
  intro x t ht
  obtain ⟨k, hk⟩ := exists_nat_gt (t / d)
  exact hsteps k x t ht ((div_lt_iff₀ hd).mp hk).le

/-- A classical heat subsolution with one-sided Gaussian growth stays below each
upper bound of its initial data, for every finite final time.

Only interior positive times require derivatives and the differential inequality.
Continuity supplies the growth bound at both time faces and the terminal comparison.
The initial data need only be bounded above by `M`; no lower bound is assumed. -/
theorem heat_subsolution_le_of_gaussian_growth {n : ℕ} {A a T M : ℝ}
    (ha : 0 ≤ a) (hT : 0 < T) (u : ℝ^n → ℝ → ℝ)
    (hucont : ContinuousOn (fun p ↦ u p.1 p.2) (univ ×ˢ Icc 0 T))
    (huspace : ∀ x, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x, ∀ t ∈ Ioo 0 T, heatParabolicOperator u x t ≤ 0)
    (hgrowth : ∀ x, ∀ t ∈ Ioo 0 T, u x t ≤ A * Real.exp (a * ‖x‖ ^ 2))
    (hinitial : ∀ x, u x 0 ≤ M) :
    ∀ x, ∀ t ∈ Icc 0 T, u x t ≤ M := by
  have hcont (x : ℝ^n) : ContinuousOn (u x) (Icc 0 T) :=
    hucont.comp (f := fun s ↦ (x, s)) (by fun_prop) (fun s hs ↦ ⟨mem_univ _, hs⟩)
  have hgrowthClosed (x : ℝ^n) :
      ∀ t ∈ Icc 0 T, u x t ≤ A * Real.exp (a * ‖x‖ ^ 2) := by
    simpa only [closure_Ioo hT.ne] using le_on_closure (hgrowth x)
      (by simpa only [closure_Ioo hT.ne] using hcont x) continuousOn_const
  have hinterior (x : ℝ^n) (t : ℝ) (ht : t ∈ Ico 0 T) : u x t ≤ M :=
    le_of_gaussian_growth_on_Ioc ha u
      (hucont.mono (prod_mono Subset.rfl (Icc_subset_Icc_right ht.2.le)))
      (fun y s hs ↦ huspace y s ⟨hs.1, hs.2.trans_lt ht.2⟩)
      (fun y s hs ↦ hutime y s ⟨hs.1, hs.2.trans_lt ht.2⟩)
      (fun y s hs ↦ hsub y s ⟨hs.1, hs.2.trans_lt ht.2⟩)
      (fun y s hs ↦ hgrowthClosed y s ⟨hs.1, hs.2.trans ht.2.le⟩)
      hinitial x t ⟨ht.1, le_rfl⟩
  intro x t ht
  exact le_on_closure (hinterior x) (by simpa only [closure_Ico hT.ne] using hcont x)
    continuousOn_const (by simpa only [closure_Ico hT.ne] using ht)

end HeatEquation
