/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IntegrationByParts.Lipschitz.SpaceTime
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The conservation identity of a Lipschitz potential

For a Lipschitz potential on the closed forward half-plane, its rotated gradient
is divergence free with the actual initial trace. Only the smooth test function
is differentiated twice. This is the integration argument that turns a
Hamilton–Jacobi potential into a conservation law, including the initial datum.
-/

@[expose] public section

open MeasureTheory Measure Set
open scoped NNReal

namespace PDE.Analysis

/-- The rotated actual gradient of a Lipschitz potential satisfies the initial
weak identity. The initial density is its almost-everywhere tangential derivative. -/
theorem integral_halfSpace_rotated_fderiv_add_initial_eq_zero
    {W φ : ℝ × ℝ → ℝ} {g : ℝ → ℝ} {K : ℝ≥0}
    (hW : LipschitzWith K W) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hg : ∀ᵐ x : ℝ, deriv (fun y ↦ W (y, 0)) x = g x) :
    (∫ p in univ ×ˢ Ioi 0,
      fderiv ℝ W p (1, 0) * fderiv ℝ φ p (0, 1) -
        fderiv ℝ W p (0, 1) * fderiv ℝ φ p (1, 0)) +
      (∫ x : ℝ, g x * φ (x, 0)) = 0 := by
  have hφ' : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have htest (v : ℝ × ℝ) : ContDiff ℝ 1 (fun p ↦ fderiv ℝ φ p v) :=
    hφ'.clm_apply contDiff_const
  have hsecond (p v w : ℝ × ℝ) :
      fderiv ℝ (fun q ↦ fderiv ℝ φ q v) p w =
        fderiv ℝ (fderiv ℝ φ) p w v := by
    have hd := (hφ'.differentiable one_ne_zero p).hasFDerivAt.clm_apply
      (hasFDerivAt_const v p)
    simpa using congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ ↦ A w) hd.fderiv
  have hmixed (p : ℝ × ℝ) :
      fderiv ℝ (fun q ↦ fderiv ℝ φ q (0, 1)) p (1, 0) =
        fderiv ℝ (fun q ↦ fderiv ℝ φ q (1, 0)) p (0, 1) := by
    rw [hsecond, hsecond]
    exact (hφ.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (1, 0) (0, 1)
  have hn := integral_halfSpace_fderiv_mul_normal_of_lipschitz hW
    (htest (1, 0)) (hc.fderiv_apply ℝ (1, 0))
  have ht := integral_halfSpace_fderiv_mul_tangent_of_lipschitz hW
    (htest (0, 1)) (hc.fderiv_apply ℝ (0, 1))
  simp_rw [hmixed] at ht
  have hWL : LipschitzWith K (fun x : ℝ ↦ W (x, 0)) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa only [dist_prod_same_right] using hW.dist_le_mul (x, 0) (y, 0)
  have hφC : ContDiff ℝ 1 (fun x : ℝ ↦ φ (x, 0)) :=
    (hφ.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
  have hφK : HasCompactSupport (fun x : ℝ ↦ φ (x, 0)) := by
    apply HasCompactSupport.intro (hc.image continuous_fst)
    intro x hx
    by_contra h
    exact hx ⟨(x, 0), subset_tsupport φ h, rfl⟩
  have htrace (x : ℝ) :
      deriv (fun y : ℝ ↦ φ (y, 0)) x = fderiv ℝ φ (x, 0) (1, 0) :=
    ((hφ.differentiable two_ne_zero (x, 0)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_id x).prodMk (hasDerivAt_const x (0 : ℝ)))).deriv
  have hb := integral_deriv_mul_eq_neg_of_absolutelyContinuous
    (fun a b ↦ hWL.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b))
    hφC hφK
  simp_rw [htrace] at hb
  have hgi : (∫ x : ℝ, deriv (fun y ↦ W (y, 0)) x * φ (x, 0)) =
      ∫ x : ℝ, g x * φ (x, 0) :=
    integral_congr_ae (hg.mono fun x hx ↦ congrArg (· * φ (x, 0)) hx)
  rw [hgi] at hb
  have hI (v w : ℝ × ℝ) :
      IntegrableOn (fun p ↦ fderiv ℝ W p v * fderiv ℝ φ p w)
        (univ ×ˢ Ioi 0) := by
    apply Integrable.integrableOn
    rw [Measure.volume_eq_prod]
    exact integrable_fderiv_mul_test_of_lipschitz hW
      (htest w).continuous (hc.fderiv_apply ℝ w) v
  rw [integral_sub (hI (1, 0) (0, 1)) (hI (0, 1) (1, 0))]
  linarith

end PDE.Analysis
