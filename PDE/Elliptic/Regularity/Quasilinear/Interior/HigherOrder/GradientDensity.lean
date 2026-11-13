/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.GradientDensity
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Linearization
import PDE.Elliptic.Regularity.Interior.H2Compactness
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# A nonlinear interior H³ bootstrap for gradient densities

Let `u ∈ H¹(Ω)` solve `-div(∇L(Du)) = f`, where `f ∈ H¹(Ω)`. For a `C³` density
with bounded uniformly positive Hessian, a locally Lipschitz representative of
`Du` yields `u ∈ H³_loc(Ω)`. The nonlinear `H²` theorem supplies the second weak
derivatives. The weak chain rule then gives a linear equation for each first
derivative, with the Hessian coefficients evaluated at `Du`. Their local
Lipschitz regularity and ellipticity follow from the density and gradient
hypotheses, so the interior linear `H²` theorem supplies the third derivatives.

This is one higher-regularity step in the setting of L. C. Evans,
*Partial Differential Equations*, second edition, §8.3.2. The locally
Lipschitz gradient is a hypothesis here; `HolderGradient` removes it for homogeneous
equations in dimension greater than two. The conclusion is interior and imposes no
boundary condition on the solution or smoothness condition on the domain.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

variable {n : ℕ} {Ω V : Set (ℝ^n)}

private theorem gradient_restrict_ae (hV : IsOpen V) (hVΩ : V ⊆ Ω) (u : H¹(Ω)) :
    (∇ (restrictCLM hV.measurableSet hVΩ u) : ℝ^n → ℝ^n)
      =ᵐ[domainMeasure n V] ∇ u := by
  have hrows := ae_all_iff.mpr fun i ↦
    restrictCLM_apply_ae hV.measurableSet hVΩ u (singleDerivIndex n i)
  filter_upwards [wkpGradientCLM_apply_ae (restrictCLM hV.measurableSet hVΩ u),
    (ae_mono (domainMeasure_le hVΩ)) (wkpGradientCLM_apply_ae u), hrows]
    with x hsmall hbig hrow
  exact PiLp.ext fun i ↦ (hsmall i).trans ((hrow i).trans (hbig i).symm)

private theorem exists_H3_of_firstDerivative_solutions
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) (W : W^{2,2}(Ω))
    (B : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, LocallyLipschitzOn Ω (a i j))
    (hrep : ∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {θ : ℝ} (hB : AEUniformlyElliptic B θ) (f : Fin n → DerivLp n 2 Ω)
    (heq : ∀ k, IsInteriorWeakDivergenceSolution B (f k) (∂[k] W)) :
    ∃ Z : W^{3,2}(V), (wkpBaseCoordinateCLM Z : ℝ^n → ℝ)
      =ᵐ[domainMeasure n V] wkpBaseCoordinateCLM W := by
  have hgain (k : Fin n) := exists_local_h2_of_locallyLipschitzOn hΩ B a ha hrep hB
    (f k) (∂[k] W) (heq k) (closure V) hVc hVΩ
  choose N hN hVN hNΩ X hX using hgain
  let U : W^{2,2}(V) := restrictCLM hV.measurableSet (subset_closure.trans hVΩ) W
  let Y (k : Fin n) : W^{2,2}(V) :=
    restrictCLM hV.measurableSet (subset_closure.trans (hVN k)) (X k)
  have hbase (k : Fin n) :
      wkpBaseCoordinateCLM (∂[k] W) =
        W.val (firstDerivIndex n 2 (by norm_num) k) := by
    simp only [wkpBaseCoordinateCLM_apply, partialDerivCLM, derivativeWordCLM_apply,
      derivativeWordIndex_singleton_baseIndex]
  have hcompat (k : Fin n) :
      (Y k).val (baseIndex n 2) = U.val (firstDerivIndex n 2 (by norm_num) k) := by
    apply Lp.ext
    filter_upwards [restrictCLM_apply_ae hV.measurableSet
      (subset_closure.trans (hVN k)) (X k) (baseIndex n 2),
      (ae_mono (domainMeasure_le (subset_closure.trans (hVN k)))) (hX k),
      restrictCLM_apply_ae hV.measurableSet (subset_closure.trans hVΩ) W
        (firstDerivIndex n 2 (by norm_num) k)] with x hY hXx hU
    exact hY.trans (hXx.trans
      ((congrArg (fun q : DerivLp n 2 Ω ↦ q x) (hbase k)).trans hU.symm))
  obtain ⟨Z, hZ⟩ := exists_succOrder_of_firstDerivatives (by norm_num : 0 < 2) U Y hcompat
  exact ⟨Z, hZ.trans (restrictCLM_apply_ae hV.measurableSet
    (subset_closure.trans hVΩ) W (baseIndex n 2))⟩

private theorem exists_flux_weakEquation (hbounded : Bornology.IsBounded Ω)
    {A : ℝ^n → ℝ^n} {C : ℝ≥0} (hLip : LipschitzWith C A)
    (u : H¹(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ v : H¹₀(Ω),
      (∫ x, ⟪A (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) =
        ∫ x, f x * baseCoordCLM v x ∂domainMeasure n Ω) :
    ∃ q : Fin n → DerivLp n 2 Ω,
      (∀ᵐ x ∂domainMeasure n Ω, A (∇ u x) = Lp.euclideanTuple q x) ∧
      ∀ v : H¹₀(Ω), (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫ := by
  obtain ⟨q, hq, hpair⟩ := exists_L2_flux_pairing_of_lipschitz hbounded hLip u
  refine ⟨q, hq, fun v ↦ ?_⟩
  rw [← (hpair v).2, hweak v, L2.inner_def]
  simp only [RCLike.inner_apply, RCLike.conj_to_real, mul_comm]

private theorem restrict_flux_weakEquation (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hVΩ : V ⊆ Ω) (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hweak : ∀ v : H¹₀(Ω), (∑ i, ⟪q i, derivCoordCLM i v⟫) =
      ⟪f, baseCoordCLM v⟫) (v : H¹₀(V)) :
    (∑ i, ⟪restrictDerivLp hVΩ (q i), derivCoordCLM i v⟫) =
      ⟪restrictDerivLp hVΩ f, baseCoordCLM v⟫ := by
  let vΩ := ZeroTrace.zeroExtendH10ToSuperset hV hΩ hVΩ v
  calc
    _ = ∑ i, ⟪q i, derivCoordCLM i vΩ⟫ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (ZeroTrace.inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
        hV hΩ hVΩ (q i) v (singleDerivIndex n i)).symm
    _ = ⟪f, baseCoordCLM vΩ⟫ := hweak vΩ
    _ = _ := ZeroTrace.inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
      hV hΩ hVΩ f v (baseIndex n 1)

private theorem restrict_flux_rep (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    (A : ℝ^n → ℝ^n) (u : H¹(Ω)) (q : Fin n → DerivLp n 2 Ω)
    (hq : ∀ᵐ x ∂domainMeasure n Ω, A (∇ u x) = Lp.euclideanTuple q x) :
    ∀ᵐ x ∂domainMeasure n V,
      A (∇ (restrictCLM hV.measurableSet hVΩ u) x) =
        Lp.euclideanTuple (fun i ↦ restrictDerivLp hVΩ (q i)) x := by
  have hrestrict := ae_all_iff.mpr fun i ↦ restrictDerivLp_apply_ae hVΩ (q i)
  filter_upwards [gradient_restrict_ae hV hVΩ u, (ae_mono (domainMeasure_le hVΩ)) hq,
    (ae_mono (domainMeasure_le hVΩ)) (Lp.euclideanTuple_apply_ae q),
    Lp.euclideanTuple_apply_ae (fun i ↦ restrictDerivLp hVΩ (q i)), hrestrict]
    with x hgrad hqx htuple htupleV hres
  rw [hgrad, hqx]
  exact PiLp.ext fun i ↦ (htuple i).trans ((hres i).symm.trans (htupleV i).symm)

private theorem exists_H3_of_gradientDensity_H2
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ 3 L)
    {Λ : ℝ≥0} (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpositive : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    (W : W^{2,2}(Ω)) (F : H¹(Ω)) (q : Fin n → DerivLp n 2 Ω)
    (hq : ∀ᵐ x ∂domainMeasure n Ω,
      ∇ L (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) x) = Lp.euclideanTuple q x)
    (hweak : ∀ v : H¹₀(Ω), (∑ i, ⟪q i, derivCoordCLM i v⟫) =
      ⟪wkpBaseCoordinateCLM F, baseCoordCLM v⟫)
    {g : ℝ^n → ℝ^n} (hg : LocallyLipschitzOn Ω g)
    (hgradient : (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) : ℝ^n → ℝ^n)
      =ᵐ[domainMeasure n Ω] g) :
    ∃ Z : W^{3,2}(V), (wkpBaseCoordinateCLM Z : ℝ^n → ℝ)
      =ᵐ[domainMeasure n V] wkpBaseCoordinateCLM W := by
  have hL2 : ContDiff ℝ 2 L := hL.of_le (by norm_num)
  have hA := contDiff_gradient_of_contDiff_two hL2
  have hLip := lipschitzWith_gradient_of_hessian_bound hL2 hbound
  obtain ⟨B, hBrep, hBlip, hB⟩ :=
    exists_linearizedCoefficients_of_gradientDensity hΩ hL hbound hθ hpositive hg
  have heq (k : Fin n) := isInteriorWeakDivergenceSolution_linearized hΩ hbounded
    hA hLip W F q hq hweak hgradient B hBrep k
  exact exists_H3_of_firstDerivative_solutions hΩ hV hVc hVΩ W B
    (fun i j x ↦ jacobianMatrix (∇ L) (g x) i j) hBlip hBrep hB
    (fun k ↦ wkpCoordinateCLM (singleDerivIndex n k) F) heq

/-- A nonlinear Euler–Lagrange solution with an `H¹` source and locally
Lipschitz weak gradient belongs to `H³` on every relatively compact open
subdomain. The density is `C³` with globally bounded uniformly positive Hessian.
The supplied Sobolev bundle has order one; the proof derives the
nonlinear `H²` seed, the differentiated equation, and its coefficient regularity.
The complete order-one restriction, including the original weak gradient, is
preserved. -/
theorem exists_interior_H3_of_gradientDensity
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ 3 L)
    {Λ : ℝ≥0} (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpositive : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    (u F : H¹(Ω))
    (hweak : ∀ v : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) =
        ∫ x, wkpBaseCoordinateCLM F x * baseCoordCLM v x ∂domainMeasure n Ω)
    {g : ℝ^n → ℝ^n} (hg : LocallyLipschitzOn Ω g)
    (hgradient : (∇ u : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] g) :
    ∃ Z : W^{3,2}(V), lowerOrderCLM (by omega : 1 ≤ 3) Z =
      restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u := by
  have hL2 : ContDiff ℝ 2 L := hL.of_le (by norm_num)
  have hLip := lipschitzWith_gradient_of_hessian_bound hL2 hbound
  obtain ⟨q, hq, hweakq⟩ :=
    exists_flux_weakEquation hbounded hLip u (wkpBaseCoordinateCLM F) hweak
  obtain ⟨N, hN, hNΩ, hVN, _hNc, K, _hK, hreg⟩ :=
    exists_H2_near_compact_of_gradientDensity hΩ hbounded hVc hVΩ hθ Λ
  have hNsub : N ⊆ Ω := subset_closure.trans hNΩ
  obtain ⟨W, hW, _hnorm, _hsecond⟩ :=
    hreg L hL2 hbound hpositive u (wkpBaseCoordinateCLM F) hweak
  let FN : H¹(N) := restrictCLM hN.measurableSet hNsub F
  let qN (i : Fin n) : DerivLp n 2 N := restrictDerivLp hNsub (q i)
  have hweakN (v : H¹₀(N)) :
      (∑ i, ⟪qN i, derivCoordCLM i v⟫) =
        ⟪wkpBaseCoordinateCLM FN, baseCoordCLM v⟫ :=
    restrict_flux_weakEquation hΩ hN hNsub q (wkpBaseCoordinateCLM F) hweakq v
  have hgradW :
      (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) : ℝ^n → ℝ^n)
        =ᵐ[domainMeasure n N] ∇ u := by
    rw [hW]
    exact gradient_restrict_ae hN hNsub u
  have hqN : ∀ᵐ x ∂domainMeasure n N,
      ∇ L (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) x) = Lp.euclideanTuple qN x := by
    rw [hW]
    exact restrict_flux_rep hN hNsub (∇ L) u q hq
  obtain ⟨Z, hZ⟩ := exists_H3_of_gradientDensity_H2 hN (hbounded.subset hNsub)
    hV hVc hVN hL hbound hθ hpositive W FN qN hqN hweakN (hg.mono hNsub)
    (hgradW.trans ((ae_mono (domainMeasure_le hNsub)) hgradient))
  have hbaseW : (wkpBaseCoordinateCLM W : ℝ^n → ℝ)
      =ᵐ[domainMeasure n N] wkpBaseCoordinateCLM u := by
    have hbase := restrictCLM_apply_ae hN.measurableSet hNsub u (baseIndex n 1)
    rw [← hW] at hbase
    simpa only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
      wkpBaseCoordinateCLM_apply] using hbase
  refine ⟨Z, wkpBaseCoordinateCLM_injective hV (Lp.ext ?_)⟩
  have hfinal := hZ.trans ((ae_mono (domainMeasure_le (subset_closure.trans hVN))) hbaseW)
  have hres := restrictCLM_apply_ae hV.measurableSet
    (subset_closure.trans hVΩ) u (baseIndex n 1)
  simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex] using hfinal.trans hres.symm

end PDE.Elliptic.Regularity.Quasilinear
