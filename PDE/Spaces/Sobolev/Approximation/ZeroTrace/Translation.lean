/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.Rellich.Translation
public import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback

/-!
# Translation of finite-exponent Sobolev functions

Translation acts on every weak derivative coordinate. The affine weak chain
rule identifies the translated derivatives, and continuity of translation in
`Lᵖ`, for finite `p`, gives convergence in the full Sobolev norm.

This is the translation step in approximation of a zero extension by functions
whose support lies strictly inside a half-space.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open Rellich
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weak affine chain rule for a translation at finite exponent. -/
theorem hasWeakDerivativeOn_translate_add_W1p (hp : p ≠ ∞)
    (a : ℝ^n) (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    HasWeakDerivativeOn Set.univ [i]
      (fun x ↦ U.val (baseIndex n 1) (x + a))
      (fun x ↦ U.val (singleDerivIndex n i) (x + a)) := by
  let E : OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
    (Homeomorph.addRight a).toOpenPartialHomeomorph
  let u : ℝ^n → ℝ := U.val (baseIndex n 1)
  let du : Fin n → ℝ^n → ℝ := fun j ↦ U.val (singleDerivIndex n j)
  have hE : ContDiff ℝ 1 (fun x ↦ E x) := by
    simpa [E] using
      ((contDiff_id : ContDiff ℝ 1 (fun x : ℝ^n ↦ x)).add contDiff_const)
  have hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x) := by
    change ContDiff ℝ 1 (fun x : ℝ^n ↦ x + -a)
    exact contDiff_id.add contDiff_const
  have huLp : MemLp u p (domainMeasure n E.target) := by
    simpa [u, E, domainMeasure] using Lp.memLp (U.val (baseIndex n 1))
  have hduLp : ∀ j, MemLp (du j) p (domainMeasure n E.target) := by
    intro j
    simpa [du, E, domainMeasure] using Lp.memLp (U.val (singleDerivIndex n j))
  have hweak : ∀ j, HasWeakDerivativeOn E.target [j] u (du j) := by
    intro j
    simpa [u, du, E, firstDerivIndex_one] using
      U.property.hasWeakDerivativeOn_first (by norm_num) j
  have hcv :=
    WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp
      (Approximation.standardMollifier n) hp hE hEsymm huLp hduLp hweak i
  have hsum : (fun x ↦ ∑ j, du j (E x) *
      ((fderiv ℝ (fun y ↦ E y) x) (EuclideanSpace.single i 1)).ofLp j) =
      fun x ↦ du i (x + a) := by
    funext x
    have hfderiv : fderiv ℝ (fun y ↦ E y) x =
        ContinuousLinearMap.id ℝ (ℝ^n) := by
      rw [show (fun y ↦ E y) = (fun y : ℝ^n ↦ y + a) by rfl, fderiv_add_const]
      exact (hasFDerivAt_id (𝕜 := ℝ) x).fderiv
    rw [hfderiv]
    simp [E, du]
  simpa [E, u, du, hsum] using hcv

/-- Translation of all coordinates of a first-order Sobolev function. -/
def translateW1p (hp : p ≠ ∞) (a : ℝ^n) :
    W^{1,p}(ℝ^n) →L[ℝ] W^{1,p}(ℝ^n) :=
  let ambient : WkpAmbientOn n 1 p Set.univ →L[ℝ] WkpAmbientOn n 1 p Set.univ :=
    let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
      (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Set.univ)
    e.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun q ↦
        (translateLp p a).toContinuousLinearMap.comp
          (PiLp.proj (𝕜 := ℝ) (p := p)
            (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Set.univ) q))
  ContinuousLinearMap.codRestrict
    (ambient.comp (Submodule.subtypeL (wkpSubmoduleOn n 1 p Set.univ)))
    (wkpSubmoduleOn n 1 p Set.univ) (by
    intro U q
    rcases q.eq_baseIndex_or_eq_singleDerivIndex with hq | ⟨i, hq⟩
    · subst q
      have hloc := memLp_locallyIntegrableOn_domain
        (Lp.memLp (translateLp p a (U.val (baseIndex n 1)))) Fact.out
      simpa [ambient, iteratedPartialDeriv] using hasWeakDerivativeOn_nil hloc
    · subst q
      have hpoint := hasWeakDerivativeOn_translate_add_W1p hp a U i
      have hbaseAE := translateLp_apply_ae p a (U.val (baseIndex n 1))
      have hderivAE := translateLp_apply_ae p a (U.val (singleDerivIndex n i))
      simpa using (hasWeakDerivativeOn_congr_ae (Ω := Set.univ) (α := [i])
        (by simpa [ambient] using hbaseAE) (by simpa [ambient] using hderivAE)).mpr hpoint)

/-- Each weak derivative coordinate is translated by the same displacement. -/
@[simp] theorem translateW1p_apply (hp : p ≠ ∞) (a : ℝ^n) (U : W^{1,p}(ℝ^n))
    (q : DerivIndex n 1) :
    (translateW1p hp a U).val q = translateLp p a (U.val q) := by
  let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Set.univ)
  change (e (e.symm (fun r ↦ translateLp p a (U.val r)))) q = _
  rw [e.apply_symm_apply]

/-- Vanishing translation vectors give convergence in the full Sobolev norm. -/
theorem tendsto_translateW1p_zero (hp : p ≠ ∞) (U : W^{1,p}(ℝ^n))
    {a : ℕ → ℝ^n} (ha : Filter.Tendsto a Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun m ↦ translateW1p hp (a m) U) Filter.atTop (𝓝 U) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_piLp_norm_of_forall hp
    (x := fun m ↦ (translateW1p hp (a m) U).val - U.val)
  intro q
  have h := ((continuous_translateLp p hp (U.val q)).tendsto 0).comp ha
  have h' : Filter.Tendsto (fun m ↦ translateLp p (a m) (U.val q))
      Filter.atTop (𝓝 (U.val q)) := by
    simpa only [translateLp_zero, Function.comp_def] using h
  simpa only [PiLp.sub_apply, translateW1p_apply] using
    tendsto_iff_norm_sub_tendsto_zero.mp h'

end SobolevSpace.GraphSpace
