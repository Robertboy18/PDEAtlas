/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianGradient
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Compact C¹ sources and the Newtonian Hessian principal value

The first-gradient kernel is locally integrable in five dimensions. Moving
one source derivative onto this kernel identifies the Hessian pairing for a
compact C¹ source that vanishes at the pole. A smooth bump isolates the value
at the pole, where the spherical principal-value calculation of `PrincipalValueHessian` gives
the diagonal correction `−f(X)/5`.

This argument uses finite regularity throughout. Its translated formula has
the same first-gradient/source-derivative integral as differentiation of the
convolution.
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open MeasureTheory Filter TopologicalSpace
open PDE.Analysis SobolevSpace
open scoped Distributions ENNReal Topology

-- Match the real calculus instances used by the regularized kernel.

namespace PotentialTheory

/-- A compact C¹ source that vanishes at the pole admits one integration by
parts against the Hessian kernel. Both resulting integrals are absolutely
convergent; no principal value is needed for this remainder. -/
theorem fundamentalSolution_five_hessian_pairing_eq_gradient_of_zero
    (i j : Fin 5) (g : ℝ^5 → ℝ) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hg0 : g 0 = 0) :
    Integrable (fun X : ℝ^5 ↦
      iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * g X) ∧
      (∫ X : ℝ^5,
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * g X) =
        -(∫ X : ℝ^5,
          fiveDimensionalGammaGradientKernel j X * (∂[i] g) X) := by
  obtain ⟨hint, hleft⟩ :=
    fiveDimensionalGammaRegularized_hessian_pairing_tendsto_of_zero j i g hg hgc hg0
  have hdg : Continuous (∂[i] g) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hg).continuous
  have hdc : HasCompactSupport (∂[i] g) := hgc.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hparts (n : ℕ) :
      (∫ X : ℝ^5, iteratedPartialDeriv (n := 5) [i, j]
          (fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹)) X * g X) =
        -(∫ X : ℝ^5, (∂[j] (fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹))) X * (∂[i] g) X) := by
    let u : ℝ^5 → ℝ := ∂[j] (fiveDimensionalGammaRegularized ((n + 1 : ℝ)⁻¹))
    have hu : ContDiff ℝ 1 u := (PDE.contDiff_top_partialDeriv (i := j)
      (fiveDimensionalGammaRegularized_contDiff _ (by positivity))).of_le (by simp)
    have h : (∫ X : ℝ^5, u X * (∂[i] g) X) = -(∫ X : ℝ^5, (∂[i] u) X * g X) := by
      simpa only [partialDeriv] using integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure (ℝ^5))) (f := u) (g := g) (v := EuclideanSpace.single i (1 : ℝ))
        (((PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hu).continuous.mul
          hg.continuous).integrable_of_hasCompactSupport hgc.mul_left)
        ((hu.continuous.mul hdg).integrable_of_hasCompactSupport hdc.mul_left)
        ((hu.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left)
        (fun _ _ ↦ (hu.differentiable (by norm_num)).differentiableAt)
        (fun _ _ ↦ (hg.differentiable (by norm_num)).differentiableAt)
    simpa only [u, iteratedPartialDeriv, neg_neg] using (congrArg Neg.neg h).symm
  refine ⟨hint, tendsto_nhds_unique hleft ?_⟩
  simpa only [hparts] using
    (fiveDimensionalGammaRegularized_gradient_pairing_tendsto j (∂[i] g) hdg hdc).neg

/-- Removing a shrinking ball from an absolutely integrable pairing recovers
its full integral. The kernel need not have a value prescribed at the pole. -/
private theorem integral_outside_ball_tendsto
    (F : ℝ^5 → ℝ) (hF : Integrable F) :
    Tendsto (fun ε : ℝ ↦ ∫ X in {X : ℝ^5 | ε < ‖X‖}, F X)
      (𝓝[>] 0) (𝓝 (∫ X : ℝ^5, F X)) := by
  have hm (ε : ℝ) : MeasurableSet {X : ℝ^5 | ε < ‖X‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hlim : Tendsto (fun ε : ℝ ↦ ∫ X : ℝ^5, {X : ℝ^5 | ε < ‖X‖}.indicator F X)
      (𝓝[>] 0) (𝓝 (∫ X : ℝ^5, F X)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun X ↦ ‖F X‖)
      (.of_forall fun ε ↦ hF.aestronglyMeasurable.indicator (hm ε))
      (.of_forall fun ε ↦ .of_forall fun X ↦ norm_indicator_le_norm_self F X) hF.norm ?_
    filter_upwards [(Set.countable_singleton (0 : ℝ^5)).ae_notMem volume] with X hX
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (norm_pos_iff.2 hX)] with ε hε
    exact (Set.indicator_of_mem (s := {Y : ℝ^5 | ε < ‖Y‖}) hε.2 F).symm
  simpa only [integral_indicator (hm _)] using hlim

/-- The spherical principal value of the Hessian kernel against a compact C¹
source equals its absolutely convergent first-gradient pairing, with the
diagonal local correction restored. Subtracting a smooth bump matching `f 0`
reduces the finite-regularity argument to a source that vanishes at the pole. -/
theorem fundamentalSolution_five_hessian_principalValue_of_contDiff_one
    (i j : Fin 5) (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    (∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun X : ℝ^5 ↦
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * f X)
        {X : ℝ^5 | ε < ‖X‖}) ∧
      Tendsto (fun ε : ℝ ↦
        ∫ X in {X : ℝ^5 | ε < ‖X‖},
          iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) X * f X)
        (𝓝[>] 0)
        (𝓝 (-(∫ X : ℝ^5,
          fiveDimensionalGammaGradientKernel j X * (∂[i] f) X) +
          (if i = j then f 0 / 5 else 0))) := by
  let b : ContDiffBump (0 : ℝ^5) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let φ : 𝓓((⊤ : Opens (ℝ^5)), ℝ) := ⟨b, b.contDiff, b.hasCompactSupport, Set.subset_univ _⟩
  have hφ0 : φ.toFun 0 = 1 :=
    b.one_of_mem_closedBall (by simp only [Metric.mem_closedBall, dist_self]; norm_num [b])
  let g : ℝ^5 → ℝ := fun X ↦ f X - f 0 * φ.toFun X
  have hφ1 : ContDiff ℝ 1 (fun Y ↦ f 0 * φ.toFun Y) :=
    contDiff_const.mul (φ.contDiff.of_le (by simp))
  have hgc : HasCompactSupport g := hfc.sub φ.hasCompactSupport.mul_left
  obtain ⟨hgInt, hgEq⟩ := fundamentalSolution_five_hessian_pairing_eq_gradient_of_zero i j g
    (hf.sub hφ1) hgc (by simp only [g, hφ0, mul_one, sub_self])
  obtain ⟨L, hL, hLEq⟩ := fiveDimensionalFundamentalSolution_distributionalHessian i j φ
  have hφd : ContDiff ℝ 1 (∂[i] φ.toFun) :=
    (PDE.contDiff_top_partialDeriv (i := i) φ.contDiff).of_le (by simp)
  have hφdc : HasCompactSupport (∂[i] φ.toFun) :=
    φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hφparts : (∫ X : ℝ^5, fundamentalSolution 5 X *
      iteratedPartialDeriv (n := 5) [i, j] φ.toFun X) =
        -(∫ X : ℝ^5, fiveDimensionalGammaGradientKernel j X * (∂[i] φ.toFun) X) := by
    refine (integral_congr_ae (.of_forall fun X ↦ ?_)).trans
      (fundamentalSolution_five_integral_mul_partialDeriv j (∂[i] φ.toFun) hφd hφdc)
    exact congrArg _ (PDE.partialDeriv_partialDeriv_comm i j
      (φ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) X)
  rw [hφparts, hφ0] at hLEq
  have hlocal := locallyIntegrable_fiveDimensionalGammaGradientKernel j
  have hgradf : Integrable fun X : ℝ^5 ↦ fiveDimensionalGammaGradientKernel j X * (∂[i] f) X := by
    simpa only [smul_eq_mul] using hlocal.integrable_smul_right_of_hasCompactSupport
      (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := i) hf).continuous
      (hfc.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ)))
  have hgradφ : Integrable
      fun X : ℝ^5 ↦ fiveDimensionalGammaGradientKernel j X * (∂[i] φ.toFun) X := by
    simpa only [smul_eq_mul] using
      hlocal.integrable_smul_right_of_hasCompactSupport hφd.continuous hφdc
  have hgd (X : ℝ^5) : (∂[i] g) X = (∂[i] f) X - f 0 * (∂[i] φ.toFun) X := by
    rw [PDE.partialDeriv_sub (hf.differentiable (by norm_num)).differentiableAt
      (hφ1.differentiable (by norm_num)).differentiableAt]
    simpa only [smul_eq_mul] using congrArg ((∂[i] f) X - ·)
      (PDE.partialDeriv_const_smul (i := i) (f := φ.toFun) (x := X) (f 0))
  have hgradEq : (∫ X : ℝ^5, fiveDimensionalGammaGradientKernel j X * (∂[i] g) X) =
      (∫ X : ℝ^5, fiveDimensionalGammaGradientKernel j X * (∂[i] f) X) -
        f 0 * (∫ X : ℝ^5, fiveDimensionalGammaGradientKernel j X * (∂[i] φ.toFun) X) := by
    rw [← integral_const_mul, ← integral_sub hgradf (hgradφ.const_mul (f 0))]
    exact integral_congr_ae (.of_forall fun X ↦ by simp only [hgd]; ring)
  rw [hgradEq] at hgEq
  let K := iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5)
  have hsplit (ε : ℝ) (hε : 0 < ε) :
      IntegrableOn (fun X : ℝ^5 ↦ K X * f X) {X : ℝ^5 | ε < ‖X‖} ∧
        (∫ X in {X : ℝ^5 | ε < ‖X‖}, K X * f X) =
          (∫ X in {X : ℝ^5 | ε < ‖X‖}, K X * g X) +
            f 0 * (∫ X in {X : ℝ^5 | ε < ‖X‖}, K X * φ.toFun X) := by
    have hφInt :=
      (fundamentalSolution_five_classicalHessian_integrableOn ε hε i j φ).const_mul (f 0)
    have hEq : (fun X : ℝ^5 ↦ K X * f X) = fun X ↦ K X * g X + f 0 * (K X * φ.toFun X) := by
      funext X
      simp only [g]
      ring
    rw [hEq, integral_add hgInt.integrableOn hφInt, integral_const_mul]
    exact ⟨hgInt.integrableOn.add hφInt, rfl⟩
  have heq : (∫ X : ℝ^5, K X * g X) + f 0 * L =
      -(∫ X : ℝ^5, fiveDimensionalGammaGradientKernel j X * (∂[i] f) X) +
        (if i = j then f 0 / 5 else 0) := by
    dsimp only [K]
    split_ifs at hLEq ⊢ <;> linear_combination hgEq - f 0 * hLEq
  refine ⟨fun ε hε ↦ (hsplit ε hε).1, ?_⟩
  rw [← heq]
  refine ((integral_outside_ball_tendsto _ hgInt).add (hL.const_mul (f 0))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using (hsplit ε hε).2.symm

/-- The compact C¹ principal-value formula at an arbitrary evaluation point,
written in the displacement variable used by convolution. The derivative on
the source has positive sign because `H ↦ f (X - H)` reverses directions. -/
theorem fundamentalSolution_five_hessian_principalValue_sub_of_contDiff_one
    (i j : Fin 5) (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (X : ℝ^5) :
    (∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun H : ℝ^5 ↦
        iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) H * f (X - H))
        {H : ℝ^5 | ε < ‖H‖}) ∧
      Tendsto (fun ε : ℝ ↦
        ∫ H in {H : ℝ^5 | ε < ‖H‖},
          iteratedPartialDeriv (n := 5) [i, j] (fundamentalSolution 5) H * f (X - H))
        (𝓝[>] 0)
        (𝓝 ((∫ H : ℝ^5,
          fiveDimensionalGammaGradientKernel j H * (∂[i] f) (X - H)) +
          (if i = j then f X / 5 else 0))) := by
  let ψ : ℝ^5 → ℝ := fun H ↦ f (X - H)
  have hψ : ContDiff ℝ 1 ψ := hf.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hfc.comp_homeomorph (Homeomorph.subLeft X)
  have hchain (H : ℝ^5) :
      (∂[i] ψ) H = -(∂[i] f) (X - H) := by
    have hfAt : HasFDerivAt f (fderiv ℝ f (X - H)) (X - H) :=
      (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt ψ
        ((fderiv ℝ f (X - H)).comp (-ContinuousLinearMap.id ℝ (ℝ^5))) H :=
      hfAt.comp H ((hasFDerivAt_id H).const_sub X)
    unfold partialDeriv
    rw [hcomp.fderiv]
    simp
  have h := fundamentalSolution_five_hessian_principalValue_of_contDiff_one i j ψ hψ hψc
  simpa only [hchain, mul_neg, integral_neg, neg_neg, ψ, sub_zero] using h

end PotentialTheory
