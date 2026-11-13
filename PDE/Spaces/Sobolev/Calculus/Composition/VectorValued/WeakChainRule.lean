/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.VectorValued.SmoothApproximation
import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Locality

/-!
# The Banach-valued weak chain rule for all normed exponents

On each bounded open subdomain a Sobolev function belongs to `W^{1,1}`.
The finite-exponent chain rule therefore applies locally even at `p = ∞`.
Scalar open-cover locality and the continuous dual assemble the Bochner identity.
Subtracting and then restoring the constant value at zero removes any global
integrability requirement on the composed function.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Φ : E → F} {C : ℝ≥0}

private theorem hasWeakDerivativeOn_comp_zero
    (hΦ : ContDiff ℝ 1 Φ) (hzero : Φ 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (U : W^{1,p}(Ω; E)) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (fun x ↦ Φ (U.val (baseIndex n 1) x))
      (fun x ↦ fderiv ℝ Φ (U.val (baseIndex n 1) x)
        (U.val (singleDerivIndex n i) x)) := by
  have hf := memLp_comp_of_bounded_fderiv hΦ hzero hbound (Lp.memLp (U.val (baseIndex n 1)))
  have hg := memLp_fderiv_apply hΦ hbound (Lp.memLp (U.val (baseIndex n 1))).aestronglyMeasurable
    (Lp.memLp (U.val (singleDerivIndex n i)))
  apply (hasWeakDerivativeOn_iff_forall_dual
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable Fact.out))
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable Fact.out))).mpr
  intro L
  let D (x : ℝ^n) : Opens ℝ^n :=
    ⟨(Ω : Set ℝ^n) ∩ Metric.ball x 1, Ω.isOpen.inter Metric.isOpen_ball⟩
  have hD (x : ℝ^n) : D x ≤ Ω := inter_subset_left
  refine SobolevSpace.hasWeakDerivativeOn_single_of_open_cover
    (fun x ↦ (D x : Set ℝ^n)) (fun x ↦ (D x).isOpen) ?_ i ?_
  · intro x hx
    exact mem_iUnion.mpr ⟨x, hx, Metric.mem_ball_self zero_lt_one⟩
  · intro x
    let : IsFiniteMeasure (domainMeasure n (D x)) :=
      isFiniteMeasure_restrict.mpr
        ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
    have hmem (a : DerivIndex n 1) :
        MemLp (U.val a) 1 (domainMeasure n (D x)) :=
      ((Lp.memLp (U.val a)).mono_measure
        (Measure.restrict_mono (hD x) le_rfl)).mono_exponent Fact.out
    let V : W^{1,1}(D x; E) := ofWeakDerivatives (fun a ↦ U.val a) hmem
      (fun a ↦ (U.property a).restrict (hD x))
    have hV (a : DerivIndex n 1) :
        (V.val a : ℝ^n → E) =ᵐ[domainMeasure n (D x)] U.val a :=
      ofWeakDerivatives_apply_ae _ _ _ a
    have hc := hasWeakDerivativeOn_comp_of_ne_top (by simp) hΦ hzero hbound V i
    have hraw : HasWeakDerivativeOn (D x) [i]
        (fun y ↦ Φ (U.val (baseIndex n 1) y))
        (fun y ↦ fderiv ℝ Φ (U.val (baseIndex n 1) y)
          (U.val (singleDerivIndex n i) y)) := by
      apply hc.congr_ae ((hV (baseIndex n 1)).fun_comp Φ)
      filter_upwards [hV (baseIndex n 1), hV (singleDerivIndex n i)] with y hb hd
      exact congrArg₂ (fun z v ↦ fderiv ℝ Φ z v) hb hd
    exact hasWeakDerivativeOn_real_iff.mp (hraw.map L)

/-- A `C¹` map with bounded derivative satisfies the Banach-valued weak chain
rule on every open domain, for `1 ≤ p ≤ ∞`. The composed value only needs local
integrability, which follows here; neither finite volume nor `Φ 0 = 0` is assumed. -/
theorem hasWeakDerivativeOn_comp
    (hΦ : ContDiff ℝ 1 Φ) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C)
    (U : W^{1,p}(Ω; E)) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (fun x ↦ Φ (U.val (baseIndex n 1) x))
      (fun x ↦ fderiv ℝ Φ (U.val (baseIndex n 1) x)
        (U.val (singleDerivIndex n i) x)) := by
  have hcenter : ∀ z, ‖fderiv ℝ (fun y ↦ Φ y - Φ 0) z‖ ≤ C := by
    simpa only [fderiv_sub_const] using hbound
  have h := hasWeakDerivativeOn_comp_zero (hΦ.sub contDiff_const)
    (sub_self (Φ 0)) hcenter U i
  have hc : HasWeakDerivativeOn Ω [i] (fun _ ↦ Φ 0) (fun _ ↦ 0) := by
    have hd : ∂[i] (fun _ : ℝ^n ↦ Φ 0) = fun _ ↦ 0 :=
      funext fun _ ↦ PDE.partialDeriv_const (Φ 0)
    simpa only [hd] using
      hasWeakDerivativeOn_of_contDiffOn_one (Ω := Ω)
        (f := fun _ : ℝ^n ↦ Φ 0) contDiffOn_const i
  simpa only [Pi.add_def, sub_add_cancel, fderiv_sub_const, add_zero] using h.add hc

end SobolevSpace.VectorValued
