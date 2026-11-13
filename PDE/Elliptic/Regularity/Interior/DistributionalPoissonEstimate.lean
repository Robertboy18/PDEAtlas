/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DistributionalPoissonEnergy
public import PDE.Elliptic.Regularity.Interior.CutoffLaplacian
public import PDE.Elliptic.Regularity.WholeSpace.RealHessian
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.QuantitativeCutoff

/-!
# A quantitative interior estimate from distributional Poisson data

For real locally L² data satisfying Δu = f, each second derivative on B_R
is bounded by C (‖f‖_{L²(B_{8R})} + R⁻² ‖u‖_{L²(B_{8R})}). The constant
depends only on the dimension and the fixed smooth bump. The large closed ball
must lie in the open equation domain. No trace, boundary regularity, or initial
H¹ membership is assumed.

Local distributional regularity first constructs W²,² membership. Its weak
energy identity gives the scaled Caccioppoli bound; localization and the
homogeneous whole-space Hessian estimate then remove first derivatives from
the right-hand side. The balls have a fixed radius ratio; this is not an
arbitrary pair-of-radii estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff
open scoped ENNReal Distributions InnerProductSpace Sobolev

namespace PDE.Elliptic.Interior

variable {n : ℕ}

/-- Essential-supremum control, without any finite-measure hypothesis. This
converts the analytic cutoff bounds into bounds on their L∞ classes. -/
private theorem norm_top_le_of_ae_bound {V : Set (ℝ^n)} (q : DerivLp n ∞ V)
    {C : ℝ} (hC : 0 ≤ C) (hq : ∀ᵐ x ∂domainMeasure n V, ‖q x‖ ≤ C) :
    ‖q‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable q)]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hq)).trans_eq (ENNReal.toReal_ofReal hC)

/-- A locally L² distributional Poisson solution has second weak
partial derivatives with the scale-correct L² estimate on concentric balls.
The representative and its membership are constructed from u and f; neither
a gradient bound nor an H¹ representative is part of the hypotheses. -/
theorem exists_wkpSpaceOn_two_second_norm_le_of_integral_laplacian_eq :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Opens (ℝ^n)) (u f : ℝ^n → ℝ),
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp u 2 (volume.restrict K)) →
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K)) →
      (∀ φ : 𝓓(Ω, ℝ),
        (∫ x, u x * laplacian (φ : ℝ^n → ℝ) x) = ∫ x, f x * φ x) →
      ∀ (a : ℝ^n) (R : ℝ), 0 < R → closedBall a (8 * R) ⊆ Ω →
        ∃ U : W^{2,2}(ball a R),
          baseRepresentative U =ᵐ[domainMeasure n (ball a R)] u ∧
          ∀ i j : Fin n,
            ‖(U : WkpAmbientOn n 2 2 (ball a R))
              (derivIndexOfList [i, j] (by norm_num))‖ ≤
              C * ((eLpNorm f 2 (domainMeasure n (ball a (8 * R)))).toReal +
                R⁻¹ ^ 2 * (eLpNorm u 2 (domainMeasure n (ball a (8 * R)))).toReal) := by
  classical
  obtain ⟨A, B, hA, hB, hcutoffs⟩ := exists_nested_ball_cutoffs (n := n)
  let K : ℝ := 1 + 4 * n * A ^ 2
  let C : ℝ := (1 + 2 * n * A) + (2 * n * A * K + n * B)
  have hK : 1 ≤ K := le_add_of_nonneg_right (by positivity)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun Ω u f hu hf hweak a R hR hball ↦ ?_⟩
  let V : Set (ℝ^n) := ball a (8 * R)
  have hV : IsOpen V := isOpen_ball
  have hclosure : closure V ⊆ closedBall a (8 * R) :=
    closure_minimal ball_subset_closedBall isClosed_closedBall
  obtain ⟨U, F, hU, hF, hΔ, henergy⟩ := exists_wkpSpaceOn_two_poisson_weakForm
    hu hf hweak hV ((isCompact_closedBall a (8 * R)).of_isClosed_subset
      isClosed_closure hclosure) (hclosure.trans hball)
  obtain ⟨χ, η, hχsupp, hηsupp, hχone, hηone, hvalues, hfirst, hsecond⟩ := hcutoffs a R hR
  have hχV : tsupport χ.toFun ⊆ V := fun x hx ↦
    (mem_closedBall.mp (hχsupp hx)).trans_lt (by linarith)
  have hηV : tsupport η.toFun ⊆ V := fun x hx ↦
    (mem_closedBall.mp (hηsupp hx)).trans_lt (by linarith)
  have hηχ : ∀ x ∈ tsupport χ.toFun, η x = 1 := fun x hx ↦
    hηone _ ((mem_closedBall.mp (hχsupp hx)).trans (by linarith))
  let u₀ : DerivLp n 2 V := (U : WkpAmbientOn n 2 2 V) (baseIndex n 2)
  let u₁ (i : Fin n) : DerivLp n 2 V :=
    (U : WkpAmbientOn n 2 2 V) (firstDerivIndex n 2 (by norm_num) i)
  let g (i : Fin n) : ℝ := ‖testFunctionLpTop (Ω := V) η • u₁ i‖
  have hηnorm : ‖testFunctionLpTop (Ω := V) η‖ ≤ 1 := by
    apply norm_top_le_of_ae_bound _ zero_le_one
    filter_upwards [testFunctionLpTop_apply_ae (Ω := V) η] with x hx
    simpa only [hx, Real.norm_eq_abs, _root_.TestFunction.toFun_eq_coe] using (hvalues x).2
  have hηderiv (i : Fin n) : ‖partialTestFunctionLpTop (Ω := V) η i‖ ≤ A * R⁻¹ := by
    apply norm_top_le_of_ae_bound _ (mul_nonneg hA (inv_nonneg.mpr hR.le))
    filter_upwards [partialTestFunctionLpTop_apply_ae (Ω := V) η i] with x hx
    simpa only [hx, Real.norm_eq_abs, iteratedPartialDeriv] using (hfirst i x).2
  have hηsum : (∑ i : Fin n, ‖partialTestFunctionLpTop (Ω := V) η i‖ ^ 2) ≤
      n * (A * R⁻¹) ^ 2 :=
    (Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hηderiv i) 2).trans_eq
      (by simp)
  have hs : (∑ i : Fin n, g i ^ 2) ≤ R ^ 2 * ‖F‖ ^ 2 + K * R⁻¹ ^ 2 * ‖u₀‖ ^ 2 := by
    have he := poisson_cutoff_gradient_sq_le_scaled hV
      (lowerOrderCLM (by norm_num : 1 ≤ 2) U) (-F) henergy η hηV hηnorm hR
    simp only [norm_neg, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
      DerivIndex.castOrder_singleDerivIndex] at he
    refine he.trans ?_
    calc _ ≤ R ^ 2 * ‖F‖ ^ 2 + (R⁻¹ ^ 2 + 4 * (n * (A * R⁻¹) ^ 2)) * ‖u₀‖ ^ 2 := by gcongr
      _ = _ := by dsimp only [K]; ring
  have hg (i : Fin n) : g i ≤ R * ‖F‖ + K * R⁻¹ * ‖u₀‖ := by
    have hi : g i ^ 2 ≤ ∑ j : Fin n, g j ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (g j)) (Finset.mem_univ i)
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    nlinarith [hi.trans hs, mul_le_mul_of_nonneg_right (show K ≤ K ^ 2 by nlinarith)
      (by positivity : 0 ≤ R⁻¹ ^ 2 * ‖u₀‖ ^ 2), mul_nonneg (mul_nonneg hR.le (norm_nonneg F))
      (by positivity : 0 ≤ K * R⁻¹ * ‖u₀‖)]
  have hgsum : (∑ i : Fin n, g i) ≤ n * (R * ‖F‖ + K * R⁻¹ * ‖u₀‖) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hg i)
  let W : W^{2,2}((univ : Set (ℝ^n))) := extendByCutoff hV (subset_univ V) χ hχV U
  have htrace : ‖∑ i : Fin n, (W : WkpAmbientOn n 2 2 univ) (topPureDerivIndex n 2 i)‖ ≤
      C * (‖F‖ + R⁻¹ ^ 2 * ‖u₀‖) := by
    refine (norm_laplacian_extendByCutoff_le hV U F hΔ χ η hχV hηχ
      (fun x ↦ (hvalues x).1) (fun i x ↦ (hfirst i x).1)
      hsecond).trans ?_
    have hRR : R⁻¹ * R = 1 := inv_mul_cancel₀ hR.ne'
    calc _ ≤ ‖F‖ + 2 * (A * R⁻¹) * (n * (R * ‖F‖ + K * R⁻¹ * ‖u₀‖)) +
          n * (B * R⁻¹ ^ 2) * ‖u₀‖ := by gcongr
      _ = (1 + 2 * n * A * (R⁻¹ * R)) * ‖F‖ +
          (2 * n * A * K + n * B) * (R⁻¹ ^ 2 * ‖u₀‖) := by ring
      _ ≤ C * (‖F‖ + R⁻¹ ^ 2 * ‖u₀‖) := by
        rw [hRR]
        dsimp only [C]
        nlinarith [mul_nonneg (show 0 ≤ 1 + 2 * n * A by positivity)
          (show 0 ≤ R⁻¹ ^ 2 * ‖u₀‖ by positivity),
          mul_nonneg (show 0 ≤ 2 * n * A * K + n * B by positivity) (norm_nonneg F)]
  let Z : W^{2,2}(ball a R) := restrictCLM isOpen_ball.measurableSet (subset_univ (ball a R)) W
  refine ⟨Z, ?_, fun i j ↦ ?_⟩
  · have hW := extendByCutoff_base_ae hV (subset_univ V) χ hχV U
    simp only [domainMeasure, Measure.restrict_univ] at hW
    filter_upwards [restrictCLM_apply_ae isOpen_ball.measurableSet (subset_univ (ball a R)) W
        (baseIndex n 2), ae_restrict_of_ae (s := ball a R) hW,
      ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hU,
      ae_restrict_mem isOpen_ball.measurableSet] with x hx hWx hUx hxin
    rw [show baseRepresentative Z x = baseRepresentative W x from hx, hWx, hUx,
      _root_.TestFunction.toFun_eq_coe, hχone x (ball_subset_closedBall hxin), one_mul]
  · calc _ ≤ ‖(W : WkpAmbientOn n 2 2 univ) (derivIndexOfList [i, j] (by norm_num))‖ :=
          norm_restrictDerivLp_le (subset_univ (ball a R)) _
      _ ≤ ‖∑ k : Fin n, (W : WkpAmbientOn n 2 2 univ) (topPureDerivIndex n 2 k)‖ :=
        PDE.Elliptic.WholeSpace.norm_second_row_le_laplacian W i j
      _ ≤ C * (‖F‖ + R⁻¹ ^ 2 * ‖u₀‖) := htrace
      _ = _ := by
        rw [Lp.norm_def, eLpNorm_congr_ae hF, Lp.norm_def,
          show eLpNorm (u₀ : ℝ^n → ℝ) 2 _ = eLpNorm u 2 _ from eLpNorm_congr_ae hU]

end PDE.Elliptic.Interior
