/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.Barrier.PowerExpansion
public import PDE.Parabolic.MaximumPrinciple.TimeSlab
import CAS.ExactTactic

/-!
# Polynomial propagation of an initial ball lower bound

Comparison with the normalized expanding profile gives an explicit lower bound
on its growing half-ball. The exponent is independent of the initial radius and
the supersolution. Separate spatial C² and temporal differentiability suffice;
continuity supplies both ends of the time slab.
-/

@[expose] public noncomputable section

namespace ParabolicMaximum

open PDE.Analysis Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A lower bound on a small initial ball propagates with a power loss to an
expanding half-ball. This includes the terminal time and zero-dimensional space. -/
theorem lower_bound_on_expanding_halfBall
    {z : ℝ^n} {r R t θ η A B : ℝ} (p : ℕ)
    (hr : 0 < r) (hR : 0 < R) (ht : 0 < t) (hθ : 0 < θ) (hη : 0 ≤ η)
    (hradius : r ^ 2 + t ≤ R ^ 2)
    (hdecay : (3 + 6 * (A + R * B) + 24 * θ) ^ 2 / (4 * (24 * θ)) ≤ (p : ℝ) + 3)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n)
    (ha : ∀ x ∈ ball z R, ∀ q ∈ Ioo 0 t, (a x q).PosSemidef)
    (hell : ∀ x ∈ ball z R, ∀ q ∈ Ioo 0 t, ∀ d : ℝ^n,
      θ * ‖d‖ ^ 2 ≤ ⟪d, (a x q).toEuclideanLin d⟫)
    (htrace : ∀ x ∈ ball z R, ∀ q ∈ Ioo 0 t, (a x q).trace ≤ A)
    (hdrift : ∀ x ∈ ball z R, ∀ q ∈ Ioo 0 t, ‖b x q‖ ≤ B)
    (w : ℝ^n → ℝ → ℝ)
    (hwcont : ContinuousOn (Function.uncurry w) (closedBall z R ×ˢ Icc 0 t))
    (hwspace : ∀ x ∈ ball z R, ∀ q ∈ Ioo 0 t,
      ContDiffAt ℝ 2 (fun y ↦ w y q) x)
    (hwtime : ∀ x ∈ ball z R, ∀ q ∈ Ioo 0 t, DifferentiableAt ℝ (w x) q)
    (hwsuper : ∀ x ∈ ball z R, ∀ q ∈ Ioo 0 t,
      0 ≤ matrixParabolicOperator a b (fun _ _ ↦ 0) w x q)
    (hwnonneg : ∀ x ∈ closedBall z R, ∀ q ∈ Icc 0 t, 0 ≤ w x q)
    (hinitial : ∀ x ∈ closedBall z r, η ≤ w x 0) :
    ∀ q ∈ Icc 0 t, ∀ x ∈ closedBall z (Real.sqrt (r ^ 2 + q) / 2),
      η / 8 * (r ^ 2 / (r ^ 2 + q)) ^ p ≤ w x q := by
  let φ := fun x q ↦ η * powerExpandingPolynomialBump z r p x q
  have hpositive {q : ℝ} (hq : 0 ≤ q) : 0 < r ^ 2 + q :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) hq
  have hbound {q : ℝ} (hq : q ≤ t) : r ^ 2 + q ≤ R ^ 2 :=
    (add_le_add le_rfl hq).trans hradius
  have hφreg (x : ℝ^n) {q : ℝ} (hq : 0 ≤ q) :
      ContDiffAt ℝ 2 (Function.uncurry φ) (x, q) :=
    contDiffAt_const.mul (contDiffAt_powerExpandingPolynomialBump z r p x (hpositive hq))
  have hspace (x : ℝ^n) {q : ℝ} (hq : 0 ≤ q) :
      ContDiffAt ℝ 2 (fun y ↦ φ y q) x :=
    (hφreg x hq).comp x (f := fun y : ℝ^n ↦ (y, q))
      (contDiffAt_id.prodMk contDiffAt_const)
  have htime (x : ℝ^n) {q : ℝ} (hq : 0 ≤ q) :
      DifferentiableAt ℝ (φ x) q := by
    have h := hasDerivAt_powerExpandingPolynomialBump z r p x (hpositive hq).ne'
    exact (h.const_mul η).differentiableAt
  have hφsub (x : ℝ^n) (hx : x ∈ ball z R) (q : ℝ) (hq : q ∈ Ioo 0 t) :
      matrixParabolicOperator a b (fun _ _ ↦ 0) φ x q ≤ 0 := by
    have hbase := contDiffAt_powerExpandingPolynomialBump z r p x (hpositive hq.1.le)
    rw [matrixParabolicOperator_const_mul a b (fun _ _ ↦ 0)
      ((hbase.comp x (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num))
      (hasDerivAt_powerExpandingPolynomialBump z r p x (hpositive hq.1.le).ne').differentiableAt]
    exact mul_nonpos_of_nonneg_of_nonpos hη
      (matrixParabolicOperator_powerExpandingPolynomialBump_nonpos a b z r p x hR.le hθ
        (hpositive hq.1.le) (hbound hq.2.le) hdecay (ha x hx q hq) (hell x hx q hq)
        (htrace x hx q hq) (hdrift x hx q hq))
  have hφinitial (x : ℝ^n) (hx : x ∈ closure (ball z R)) : φ x 0 ≤ w x 0 := by
    by_cases hxr : x ∈ closedBall z r
    · exact (mul_le_of_le_one_right hη (powerExpandingPolynomialBump_start_le_one z hr p x)).trans
        (hinitial x hxr)
    · have hxnorm : r < ‖x - z‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hxr
      have hout : r ^ 2 + 0 ≤ ‖x - z‖ ^ 2 := by
        rw [add_zero]
        exact pow_le_pow_left₀ hr.le hxnorm.le 2
      change η * powerExpandingPolynomialBump z r p x 0 ≤ _
      rw [powerExpandingPolynomialBump_eq_zero z p x hout, mul_zero]
      exact hwnonneg x (closure_ball_subset_closedBall hx) 0 ⟨le_rfl, ht.le⟩
  have hφlateral (x : ℝ^n) (hx : x ∈ frontier (ball z R))
      (q : ℝ) (hq : q ∈ Icc 0 t) : φ x q ≤ w x q := by
    have hout : r ^ 2 + q ≤ ‖x - z‖ ^ 2 := by
      rw [← dist_eq_norm, mem_sphere.1 (frontier_ball_subset_sphere hx)]
      exact hbound hq.2
    change η * powerExpandingPolynomialBump z r p x q ≤ _
    rw [powerExpandingPolynomialBump_eq_zero z p x hout, mul_zero]
    exact hwnonneg x (closure_ball_subset_closedBall (frontier_subset_closure hx)) q hq
  have hΩcompact : IsCompact (closure (ball z R)) :=
    (isCompact_closedBall z R).closure_of_subset ball_subset_closedBall
  have hcompare := matrix_comparison_on_timeSlab isOpen_ball (nonempty_ball.mpr hR)
    hΩcompact ht a b (fun _ _ ↦ 0) ha (fun _ _ _ _ ↦ le_rfl) φ w
    (fun y hy ↦ (hφreg y.1 hy.2.1).continuousAt.continuousWithinAt)
    (hwcont.mono (Set.prod_mono closure_ball_subset_closedBall Subset.rfl))
    (fun x _ _ hq ↦ hspace x hq.1.le) hwspace
    (fun x _ _ hq ↦ htime x hq.1.le) hwtime
    (fun x hx q hq ↦ (hφsub x hx q hq).trans (hwsuper x hx q hq))
    hφlateral hφinitial
  intro q hq x hx
  have hsqrt : Real.sqrt (r ^ 2 + q) ≤ R :=
    (Real.sqrt_le_left hR.le).mpr (hbound hq.2)
  have hxΩ : x ∈ closure (ball z R) := subset_closure <| hx.trans_lt
    ((div_le_div_of_nonneg_right hsqrt (by norm_num)).trans_lt (half_lt_self hR))
  calc
    _ = η * ((r ^ 2 / (r ^ 2 + q)) ^ p / 8) := by cas
    _ ≤ φ x q := mul_le_mul_of_nonneg_left
      (powerExpandingPolynomialBump_halfBall_le z r p (hpositive hq.1) hx) hη
    _ ≤ _ := hcompare x hxΩ q hq

end ParabolicMaximum
