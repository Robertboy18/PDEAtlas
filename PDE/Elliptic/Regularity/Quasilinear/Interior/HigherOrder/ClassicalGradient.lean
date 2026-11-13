/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.HolderCoefficients
public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.Classical
import PDE.Elliptic.Regularity.Coefficients.ClassicalEllipticity
import PDE.Elliptic.Regularity.Coefficients.Restriction

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# A classical gradient derived from the nonlinear H¹ equation

For a uniformly convex C³ gradient density with bounded Hessian, the
homogeneous Euler–Lagrange equation first gives H² regularity and measurable
linearized equations. De Giorgi gives a Hölder weak gradient. Composition
with the Hessian then gives Hölder coefficients in those equations.
Interior Schauder and weak derivative reconstruction make that gradient C¹.

This is the De Giorgi–Schauder step in Evans, *Partial Differential
Equations*, §8.3.2, for autonomous homogeneous equations in dimensions
greater than two. The starting solution is only H¹.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.Elliptic.Regularity.Quasilinear

variable {n : ℕ} [Fact (0 < n)] {Ω V : Set ℝ^n}

/-- The homogeneous nonlinear Euler–Lagrange equation with a C³ uniformly
convex density yields a C¹ representative of the weak gradient on every
sufficiently interior ball. No gradient regularity is an input. -/
theorem exists_contDiffOn_one_weakGradient_of_gradientDensity
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ 3 L) {Λ : ℝ≥0}
    (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpos : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    (u : H¹(Ω))
    (hu : ∀ v : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0)
    {z : ℝ^n} {R : ℝ} (hR : 0 < R) (hball : ball z R ⊆ V) :
    ∃ G : ℝ^n → ℝ^n, Continuous G ∧
      ContDiffOn ℝ 1 G (ball z (R / 64)) ∧
      G =ᵐ[volume.restrict (ball z (R / 64))] ∇ u := by
  classical
  obtain ⟨γ, hγ, hγ1, hreg⟩ :=
    exists_holder_gradient_and_coefficients_of_gradientDensity
      (Ω := Ω) (V := V) hq2 hq hθ
  obtain ⟨G, K, hG, _hGh, hGa, hcoeff⟩ :=
    hreg hΩ hb hV hVc hVΩ L hL hbound hpos u hu z R hR hball
  have hL2 : ContDiff ℝ 2 L := hL.of_le (by norm_num)
  have hweakF (v : H¹₀(Ω)) :
      (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) =
        ∫ x, wkpBaseCoordinateCLM (0 : H¹(Ω)) x *
          baseCoordCLM v x ∂domainMeasure n Ω := by
    rw [hu v, map_zero]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx
    simp only [hx, Pi.zero_apply, zero_mul]
  obtain ⟨W, B, hW, hBrep, _hBbound, hB, hlinear, _hdiv⟩ :=
    exists_interior_linearizedEquations_of_gradientDensity
      hΩ hb hV hVc hVΩ hL2 hbound hθ hpos u 0 hweakF
  let T := ball z (R / 64)
  have hT : IsOpen T := isOpen_ball
  have hTV : T ⊆ V := (ball_subset_ball (by linarith : R / 64 ≤ R)).trans hball
  have hTΩ : T ⊆ Ω := hTV.trans (subset_closure.trans hVΩ)
  have hgrad :
      (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) : ℝ^n → ℝ^n)
        =ᵐ[domainMeasure n V] ∇ u := by
    rw [hW]
    have hrows := ae_all_iff.mpr fun i ↦ restrictCLM_apply_ae hV.measurableSet
      (subset_closure.trans hVΩ) u (singleDerivIndex n i)
    filter_upwards [wkpGradientCLM_apply_ae
      (restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u),
      ae_mono (domainMeasure_le (subset_closure.trans hVΩ)) (wkpGradientCLM_apply_ae u),
      hrows] with x hsmall hbig hrow
    exact PiLp.ext fun i ↦ (hsmall i).trans ((hrow i).trans (hbig i).symm)
  let b (i j : Fin n) := restrictDerivLp hTV (B i j)
  let A (i j : Fin n) (x : ℝ^n) := jacobianMatrix (∇ L) (G x) i j
  have hrep (i j : Fin n) :
      (b i j : ℝ^n → ℝ) =ᵐ[domainMeasure n T] A i j := by
    filter_upwards [restrictDerivLp_apply_ae hTV (B i j),
      (hBrep i j).filter_mono (ae_mono (domainMeasure_le hTV)),
      hgrad.filter_mono (ae_mono (domainMeasure_le hTV)), hGa] with x hr hb hg hGx
    change b i j x = jacobianMatrix (∇ L) (G x) i j
    rw [hr, hb, hg, hGx]
  choose M hMh hMa using hcoeff
  let C : ℝ≥0 := ∑ i, ∑ j, M i j
  have hA (i j : Fin n) : HolderOnWith C γ (A i j) T := by
    apply (hMh i j).mono_const
    exact (Finset.single_le_sum (f := M i) (fun _ _ ↦ zero_le)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k ↦ ∑ l, M k l) (fun _ _ ↦ zero_le)
        (Finset.mem_univ i))
  have hAc (i j : Fin n) : ContinuousOn (A i j) T := (hA i j).continuousOn hγ
  have hnorm (x : ℝ^n) (_hx : x ∈ T) (i j : Fin n) : ‖A i j x‖ ≤ Λ := by
    have hgradL := contDiff_gradient_of_contDiff_two hL2
    have hLip := lipschitzWith_gradient_of_hessian_bound hL2 hbound
    dsimp only [A]
    rw [jacobianMatrix_apply_eq_fderiv (hgradL.differentiable_one (G x))]
    exact (PiLp.norm_apply_le _ i).trans
      (((fderiv ℝ (∇ L) (G x)).le_opNorm _).trans
        (by simpa using norm_fderiv_le_of_lipschitz ℝ hLip (x₀ := G x)))
  have hell := (hB.restrict hTV).le_of_continuousOn hT A hrep hAc
  refine ⟨G, hG, ?_, hGa⟩
  apply contDiffOn_piLp' 2
  intro k
  let U : H¹(T) := restrictCLM hT.measurableSet hTV (∂[k] W)
  have hUk : IsInteriorWeakDivergenceSolution b 0 U := by
    simpa only [map_zero] using (by simpa only [map_zero] using hlinear k :
      IsInteriorWeakDivergenceSolution B 0 (∂[k] W)).restrict hT hTV
  have hbase : wkpBaseCoordinateCLM (∂[k] W) =
      wkpCoordinateCLM (singleDerivIndex n k)
        (lowerOrderCLM (by omega : 1 ≤ 2) W) := by
    simp only [wkpBaseCoordinateCLM_apply, partialDerivCLM,
      derivativeWordCLM_apply, derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply,
      lowerOrderCLM_apply, DerivIndex.castOrder_singleDerivIndex]
    rfl
  have hGU : (fun x ↦ G x k) =ᵐ[domainMeasure n T] wkpBaseCoordinateCLM U := by
    have hbaseU := restrictCLM_apply_ae hT.measurableSet hTV (∂[k] W) (baseIndex n 1)
    change (wkpBaseCoordinateCLM U : ℝ^n → ℝ) =ᵐ[domainMeasure n T]
      wkpBaseCoordinateCLM (∂[k] W) at hbaseU
    rw [hbase, hW] at hbaseU
    filter_upwards [hbaseU, hGa,
      (restrictCLM_apply_ae hV.measurableSet (subset_closure.trans hVΩ)
        u (singleDerivIndex n k)).filter_mono (ae_mono (domainMeasure_le hTV)),
      (wkpGradientCLM_apply_ae u).filter_mono (ae_mono (domainMeasure_le hTΩ))]
      with x hx hGx hr hux
    exact (congrArg (fun p : ℝ^n ↦ p k) hGx).trans
      ((hux k).trans (hr.symm.trans hx.symm))
  apply contDiffOn_one_of_holder_coefficients hq2 hq hθ Λ.coe_nonneg hT
    b A hγ hγ1 hA hrep hnorm hell U (fun _ ↦ 0) (fun _ _ ↦ 0)
    (M := 0) (fun _ ↦ HolderWith.const.holderOnWith T) (fun _ ↦ Lp.coeFn_zero ℝ 2 _)
  · intro v
    simpa only [loadFunctional_apply, inner_zero_left, Finset.sum_const_zero] using hUk.2 v
  · fun_prop
  · exact hGU

end PDE.Elliptic.Regularity.Quasilinear
