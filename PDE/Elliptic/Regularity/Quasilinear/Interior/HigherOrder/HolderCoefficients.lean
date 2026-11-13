/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.HolderGradient

/-!
# Hölder coefficients derived from the nonlinear weak equation

De Giorgi regularity gives a Hölder representative of the weak gradient
of a homogeneous Euler–Lagrange solution. For a C³ density, its Hessian is
locally Lipschitz as a function of the gradient variable. Compactness of the
gradient image then gives Hölder continuity of the linearized coefficients.

The coefficient regularity is a conclusion from H¹ solution data. This is the
coefficient composition step before interior Schauder in Evans §8.3.2.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.Elliptic.Regularity.Quasilinear

variable {n : ℕ}

/-- Coordinate Hölder bounds give a Hölder bound for the Euclidean tuple. -/
theorem exists_holder_euclideanTuple {s : Set (ℝ^n)} {γ : ℝ≥0}
    {g : Fin n → ℝ^n → ℝ} {K : Fin n → ℝ≥0}
    (hg : ∀ i, HolderOnWith (K i) γ (g i) s) :
    ∃ M : ℝ≥0, HolderOnWith M γ
      (fun x ↦ (WithLp.toLp 2 (fun i ↦ g i x) : ℝ^n)) s := by
  classical
  have hpi : HolderOnWith (∑ i, K i) γ (fun x i ↦ g i x) s := by
    intro x hx y hy
    apply edist_pi_le_iff.mpr
    intro i
    exact ((hg i).edist_le hx hy).trans (mul_le_mul_of_nonneg_right
      (ENNReal.coe_le_coe.mpr (Finset.single_le_sum (fun _ _ ↦ zero_le)
        (Finset.mem_univ i))) zero_le)
  have h := ((PiLp.lipschitzWith_toLp 2 (fun _ : Fin n ↦ ℝ)).holderWith.holderOnWith
    univ).comp hpi (mapsTo_univ _ _)
  refine ⟨(Fintype.card (Fin n) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal * ∑ i, K i, ?_⟩
  intro x hx y hy
  have hxy := h x hx y hy
  simp only [NNReal.coe_one, NNReal.rpow_one, one_mul] at hxy
  exact hxy

/-- A C³ density evaluated at a continuous Hölder field has Hölder Hessian
entries on every ball where that field has a Hölder bound. The Lipschitz
constant for the Hessian is obtained on the compact gradient image. -/
theorem exists_holder_jacobian_gradient_comp {L : ℝ^n → ℝ}
    (hL : ContDiff ℝ 3 L) {G : ℝ^n → ℝ^n} (hG : Continuous G)
    {z : ℝ^n} {r : ℝ} {K γ : ℝ≥0} (hGh : HolderOnWith K γ G (ball z r)) :
    ∀ i j, ∃ M : ℝ≥0,
      HolderOnWith M γ (fun x ↦ jacobianMatrix (∇ L) (G x) i j) (ball z r) := by
  intro i j
  have hA := contDiff_two_gradient_of_contDiff_three hL
  have hc : ContDiff ℝ 1 (fun p ↦ jacobianMatrix (∇ L) p i j) :=
    (contDiff_pi.mp (contDiff_pi.mp (contDiff_jacobianMatrix (r := 1) hA) i)) j
  obtain ⟨M, hM⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    ((isCompact_closedBall z r).image hG)
    hc.locallyLipschitz.locallyLipschitzOn
  have h := hM.holderOnWith.comp hGh
    (fun x hx ↦ mem_image_of_mem G (ball_subset_closedBall hx))
  refine ⟨M * K, ?_⟩
  intro x hx y hy
  have hxy := h x hx y hy
  simp only [NNReal.coe_one, NNReal.rpow_one, one_mul] at hxy
  exact hxy

variable [Fact (0 < n)] {Ω V : Set (ℝ^n)}

/-- The H¹ homogeneous Euler–Lagrange equation yields both a Hölder
weak gradient and Hölder representatives of its linearized Hessian
coefficients. No regularity of the solution beyond H¹ is assumed. -/
theorem exists_holder_gradient_and_coefficients_of_gradientDensity
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {Λ : ℝ≥0} {θ : ℝ} (hθ : 0 < θ) :
    ∃ γ : ℝ≥0, 0 < γ ∧ γ < 1 ∧
      ∀ (_ : IsOpen Ω), Bornology.IsBounded Ω →
      ∀ (_ : IsOpen V), IsCompact (closure V) → closure V ⊆ Ω →
      ∀ (L : ℝ^n → ℝ), ContDiff ℝ 3 L →
        (∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ) →
        (∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z) →
      ∀ (u : H¹(Ω)),
        (∀ v : H¹₀(Ω),
          (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0) →
      ∀ (z : ℝ^n) (R : ℝ), 0 < R → ball z R ⊆ V →
        ∃ (G : ℝ^n → ℝ^n) (K : ℝ≥0), Continuous G ∧
          HolderOnWith K γ G (ball z (R / 64)) ∧
          G =ᵐ[volume.restrict (ball z (R / 64))] ∇ u ∧
          ∀ i j, ∃ M : ℝ≥0,
            HolderOnWith M γ (fun x ↦ jacobianMatrix (∇ L) (G x) i j)
              (ball z (R / 64)) ∧
            (fun x ↦ jacobianMatrix (∇ L) (G x) i j)
              =ᵐ[volume.restrict (ball z (R / 64))]
                fun x ↦ jacobianMatrix (∇ L) (∇ u x) i j := by
  obtain ⟨γ, hγ, hγ1, hreg⟩ :=
    exists_holder_weakGradient_of_gradientDensity (Ω := Ω) (V := V) hq2 hq hθ
  refine ⟨γ, hγ, hγ1, ?_⟩
  intro hΩ hb hV hVc hVΩ L hL hbound hpos u hu z R hR hball
  choose g K hg hgh hga using
    hreg hΩ hb hV hVc hVΩ L (hL.of_le (by norm_num)) hbound hpos u hu z R hR hball
  let G : ℝ^n → ℝ^n := fun x ↦ WithLp.toLp 2 (fun i ↦ g i x)
  have hG : Continuous G := by fun_prop
  obtain ⟨M, hM⟩ := exists_holder_euclideanTuple hgh
  have hGae : G =ᵐ[volume.restrict (ball z (R / 64))] ∇ u := by
    have hsub : ball z (R / 64) ⊆ Ω :=
      (ball_subset_ball (by linarith : R / 64 ≤ R)).trans
        (hball.trans (subset_closure.trans hVΩ))
    filter_upwards [ae_all_iff.mpr hga,
      (wkpGradientCLM_apply_ae u).filter_mono (ae_mono (domainMeasure_le hsub))]
      with x hx hgx
    exact PiLp.ext fun i ↦ (hx i).trans (hgx i).symm
  refine ⟨G, M, hG, hM, hGae, ?_⟩
  intro i j
  obtain ⟨C, hC⟩ := exists_holder_jacobian_gradient_comp hL hG hM i j
  exact ⟨C, hC, hGae.mono fun x hx ↦
    congrArg (fun p : ℝ^n ↦ jacobianMatrix (∇ L) p i j) hx⟩

end PDE.Elliptic.Regularity.Quasilinear
