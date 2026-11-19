/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.FDeriv.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Truncating a classical supersolution

A function need only be superharmonic below the truncation level to make its
truncated gradient nonnegative against nonnegative compact tests. The proof
uses smooth decreasing cutoffs of its values, integrates by parts, and passes
to the sublevel indicator by dominated convergence. Regularity is local near
the test support, so singularities at the boundary are allowed.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic

open Filter MeasureTheory Set
open scoped Topology

variable {n : ℕ}

private theorem partialDeriv_sublevel_weight {b : ℝ^n → ℝ} {x : ℝ^n}
    (hb : DifferentiableAt ℝ b x) (a c : ℝ) (i : Fin n) :
    (∂[i] (fun y ↦ Real.smoothTransition (a * (c - b y)))) x =
      -(a * deriv Real.smoothTransition (a * (c - b x))) * (∂[i] b) x := by
  have harg := ((hasFDerivAt_const c x).sub hb.hasFDerivAt).const_mul a
  have h := ((Real.smoothTransition.contDiff (n := 1)).differentiable_one
    (a * (c - b x))).hasDerivAt.comp_hasFDerivAt x harg
  simp only [Function.comp_def, Pi.sub_apply] at h
  unfold partialDeriv
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, zero_sub, neg_apply]
  ring

private theorem smooth_sublevel_gradient_nonneg
    {b φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcpt : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hb : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 b x)
    {c a : ℝ} (ha : 0 ≤ a)
    (hΔ : ∀ x ∈ tsupport φ, b x < c → laplacian b x ≤ 0) :
    0 ≤ ∑ i : Fin n, ∫ x, Real.smoothTransition (a * (c - b x)) *
      (∂[i] b) x * (∂[i] φ) x := by
  let θ : ℝ^n → ℝ := fun x ↦ Real.smoothTransition (a * (c - b x))
  let Q (i : Fin n) : ℝ^n → ℝ := fun x ↦ θ x * (∂[i] b) x
  have hθ (x : ℝ^n) (hx : x ∈ tsupport φ) : ContDiffAt ℝ 1 θ x :=
    Real.smoothTransition.contDiffAt.comp x
      (contDiffAt_const.mul (contDiffAt_const.sub ((hb x hx).of_le (by norm_num))))
  have hQ (i : Fin n) (x : ℝ^n) (hx : x ∈ tsupport φ) :
      ContDiffAt ℝ 1 (Q i) x :=
    (hθ x hx).mul (contDiffAt_partialDeriv 1 (hb x hx) i)
  have hDQ (i : Fin n) (x : ℝ^n) (hx : x ∈ tsupport φ) :
      (∂[i] (Q i)) x =
        θ x * (∂[i] (∂[i] b)) x -
          (a * deriv Real.smoothTransition (a * (c - b x))) * ((∂[i] b) x) ^ 2 := by
    rw [show Q i = fun y ↦ θ y * (∂[i] b) y from rfl,
      partialDeriv_mul ((hθ x hx).differentiableAt_one)
        ((contDiffAt_partialDeriv 1 (hb x hx) i).differentiableAt_one)]
    rw [show (∂[i] θ) x =
      -(a * deriv Real.smoothTransition (a * (c - b x))) * (∂[i] b) x from
        partialDeriv_sublevel_weight ((hb x hx).differentiableAt (by norm_num)) a c i]
    ring
  have hdiv (x : ℝ^n) (hx : x ∈ tsupport φ) :
      ∑ i : Fin n, (∂[i] (Q i)) x ≤ 0 := by
    have hfirst : θ x * laplacian b x ≤ 0 := by
      by_cases hxc : b x < c
      · exact mul_nonpos_of_nonneg_of_nonpos (Real.smoothTransition.nonneg _) (hΔ x hx hxc)
      · have hzero : θ x = 0 :=
          Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha
            (sub_nonpos.mpr (le_of_not_gt hxc)))
        simp only [hzero, zero_mul, le_refl]
    calc
      _ = θ x * laplacian b x -
          ∑ i : Fin n, (a * deriv Real.smoothTransition (a * (c - b x))) *
            ((∂[i] b) x) ^ 2 := by
        simp only [hDQ _ x hx, laplacian, Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ 0 := sub_nonpos.mpr (hfirst.trans (Finset.sum_nonneg fun i _ ↦
        mul_nonneg (mul_nonneg ha Real.smoothTransition.monotone.deriv_nonneg) (sq_nonneg _)))
  have hint (i : Fin n) : Integrable (fun x ↦ φ x * (∂[i] (Q i)) x) :=
    (ContinuousOn.integrableOn_compact hcpt fun x hx ↦ hφ.continuous.continuousWithinAt.mul
      ((contDiffAt_partialDeriv 0 (hQ i x hx) i).continuousAt.continuousWithinAt)
      ).integrable_of_forall_notMem_eq_zero fun x hx ↦ by
        simp [image_eq_zero_of_notMem_tsupport hx]
  have hnegative : (∫ x, ∑ i : Fin n, φ x * (∂[i] (Q i)) x) ≤ 0 := by
    apply integral_nonpos
    intro x
    change (∑ i : Fin n, φ x * (∂[i] (Q i)) x) ≤ 0
    rw [← Finset.mul_sum]
    by_cases hx : x ∈ tsupport φ
    · exact mul_nonpos_of_nonneg_of_nonpos (hφ0 x) (hdiv x hx)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [integral_finsetSum _ (fun i _ ↦ hint i)] at hnegative
  have hibp (i : Fin n) :
      (∫ x, φ x * (∂[i] (Q i)) x) =
        -(∫ x, θ x * (∂[i] b) x * (∂[i] φ) x) := by
    rw [PDE.Analysis.integral_mul_partialDeriv_eq_neg_of_contDiffAt i hφ (hQ i) hcpt]
    exact congrArg _ (integral_congr_ae (.of_forall fun x ↦ by dsimp only [Q]; ring))
  simpa only [hibp, Finset.sum_neg_distrib, neg_nonpos] using hnegative

/-- Truncating above level `c` preserves the weak supersolution inequality,
provided the classical Laplacian is nonpositive below that level.
Only a `C²` germ near each point of the compact test support is used. -/
theorem integral_sublevel_gradient_nonneg
    {b φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcpt : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hb : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 b x)
    (c : ℝ) (hΔ : ∀ x ∈ tsupport φ, b x < c → laplacian b x ≤ 0) :
    0 ≤ ∑ i : Fin n, ∫ x, (if b x < c then (∂[i] b) x else 0) *
      (∂[i] φ) x := by
  let F (j : ℕ) (i : Fin n) : ℝ^n → ℝ := fun x ↦
    Real.smoothTransition (((j : ℝ) + 1) * (c - b x)) *
      (∂[i] b) x * (∂[i] φ) x
  have hzero (i : Fin n) (x : ℝ^n) (hx : x ∉ tsupport φ) :
      (∂[i] φ) x = 0 := by
    simp only [partialDeriv, fderiv_of_notMem_tsupport ℝ hx, zero_apply]
  have hcont (i : Fin n) : ContinuousOn (fun x ↦ (∂[i] b) x *
      (∂[i] φ) x) (tsupport φ) :=
    fun x hx ↦ ((contDiffAt_partialDeriv 1 (hb x hx) i).continuousAt.continuousWithinAt).mul
      ((contDiffAt_partialDeriv 0 hφ.contDiffAt i).continuousAt.continuousWithinAt)
  have hint (i : Fin n) : Integrable (fun x ↦ (∂[i] b) x * (∂[i] φ) x) :=
    ((hcont i).integrableOn_compact hcpt).integrable_of_forall_notMem_eq_zero fun x hx ↦ by
      simp only [hzero i x hx, mul_zero]
  have hlim (i : Fin n) : Tendsto (fun j ↦ ∫ x, F j i x) atTop
      (𝓝 (∫ x, (if b x < c then (∂[i] b) x else 0) * (∂[i] φ) x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖(∂[i] b) x * (∂[i] φ) x‖)
      (fun j ↦ ?_) (hint i).norm (fun j ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
    · have hFc : ContinuousOn (F j i) (tsupport φ) := fun x hx ↦
        (((Real.smoothTransition.continuousAt.comp
          (continuousAt_const.mul (continuousAt_const.sub (hb x hx).continuousAt))).mul
            (contDiffAt_partialDeriv 1 (hb x hx) i).continuousAt).mul
              (contDiffAt_partialDeriv 0 hφ.contDiffAt i).continuousAt).continuousWithinAt
      exact ((hFc.integrableOn_compact hcpt).integrable_of_forall_notMem_eq_zero fun x hx ↦ by
        simp only [F, hzero i x hx, mul_zero]).aestronglyMeasurable
    · rw [show F j i x = _ * _ from mul_assoc _ _ _, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)] using
          Real.smoothTransition.le_one (((j : ℝ) + 1) * (c - b x)))
    · by_cases hxc : b x < c
      · obtain ⟨M, hM⟩ := exists_nat_gt (1 / (c - b x))
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop M] with j hj
        have hjR : (M : ℝ) ≤ j := by exact_mod_cast hj
        have harg : 1 ≤ ((j : ℝ) + 1) * (c - b x) := by
          have := (div_lt_iff₀ (sub_pos.mpr hxc)).mp hM
          nlinarith
        simp only [F, ite_eq_left hxc, Real.smoothTransition.one_of_one_le harg, one_mul]
      · refine tendsto_const_nhds.congr' (.of_forall fun j ↦ ?_)
        have harg : ((j : ℝ) + 1) * (c - b x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (le_of_not_gt hxc))
        simp only [F, ite_eq_right hxc, Real.smoothTransition.zero_of_nonpos harg, zero_mul]
  exact isClosed_Ici.mem_of_tendsto (tendsto_finsetSum _ fun i _ ↦ hlim i)
    (.of_forall fun j ↦ smooth_sublevel_gradient_nonneg hφ hcpt hφ0 hb (by positivity) hΔ)

end PDE.Elliptic
