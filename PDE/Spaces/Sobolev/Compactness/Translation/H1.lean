/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.Rellich.Translation
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
public import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Translation on global `H¹`

The difference-quotient method for interior regularity (Evans, §6.3.1, Theorem 1) translates Sobolev
functions together with their weak derivatives: if `u ∈ H¹(ℝ^n)` then `u(· + a) ∈ H¹(ℝ^n)` with
`∂ᵢ(u(· + a)) = (∂ᵢu)(· + a)`. In the graph-space model this means translating every coordinate of
the derivative bundle, not only the base `L²` representative. We lift the `L²` translation
`translateLp` of `Rellich.Translation` to a continuous linear isometry `translateH1 a` of
`H1Space n = H¹(ℝ^n)`. Preservation of the weak derivative identities is obtained from the weak
change-of-variables theorem applied to the affine map `x ↦ x + a`, whose derivative is the identity.

## Main results

* `hasWeakDerivativeOn_translate_add`: translation commutes with coordinate
  weak derivatives on `ℝ^n`.
* `translateH1 a`: coordinatewise translation of the `H¹` bundle, with
  `translateH1_apply`.
* `norm_translateH1`: translation is an isometry of `H¹(ℝ^n)`.
* `translateH1_comp`, `translateH1_zero`: translations form an action of `ℝ^n`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 1, pp. 327-331, whose proof applies
  difference quotients to `u` and its weak derivatives.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open scoped Topology Sobolev
open SobolevSpace.GraphSpace.Rellich

variable {n : ℕ}


/-- Translation preserves a coordinate weak derivative on `ℝ^n`. -/
theorem hasWeakDerivativeOn_translate_add
    (a : ℝ^n) (U : W^{1,2}(ℝ^n)) (i : Fin n) :
    HasWeakDerivativeOn (n := n) Set.univ [i]
      (fun x ↦
        (((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
          DerivLp n 2 Set.univ) (x + a)))
      (fun x ↦
        (((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i) :
          DerivLp n 2 Set.univ) (x + a))) := by
  let E : OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
    (Homeomorph.addRight a).toOpenPartialHomeomorph
  let u : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
      DerivLp n 2 Set.univ)
  let du : Fin n → ℝ^n → ℝ := fun j ↦
    ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n j) :
      DerivLp n 2 Set.univ)
  have hE : ContDiff ℝ 1 (fun x ↦ E x) := by
    simpa [E] using
      ((contDiff_id : ContDiff ℝ 1 (fun x : ℝ^n ↦ x)).add
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ^n ↦ a)))
  have hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x) := by
    change ContDiff ℝ 1 (fun x : ℝ^n ↦ x + -a)
    exact
      (contDiff_id : ContDiff ℝ 1 (fun x : ℝ^n ↦ x)).add
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ^n ↦ -a))
  have huLp : MemLp u 2 (domainMeasure n E.target) := by
    simpa [u, E, domainMeasure] using
      Lp.memLp ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))
  have hduLp : ∀ j, MemLp (du j) 2 (domainMeasure n E.target) := by
    intro j
    simpa [du, E, domainMeasure] using
      Lp.memLp ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n j))
  have hweak : ∀ j, HasWeakDerivativeOn (n := n) E.target [j] u (du j) := by
    intro j
    simpa [u, du, E, firstDerivIndex_one] using
      U.property.hasWeakDerivativeOn_first (by norm_num) j
  have hcv :=
    SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp
      (Approximation.standardMollifier n) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hE hEsymm huLp hduLp hweak i
  have hsum : (fun x ↦
      ∑ j, du j (E x) *
        ((fderiv ℝ (fun y ↦ E y) x) (EuclideanSpace.single i 1)).ofLp j) =
      fun x ↦ du i (x + a) := by
    funext x
    have hfderiv : fderiv ℝ (fun y ↦ E y) x =
        ContinuousLinearMap.id ℝ (ℝ^n) := by
      rw [show (fun y ↦ E y) = (fun y : ℝ^n ↦ y + a) by rfl,
        fderiv_add_const]
      exact (hasFDerivAt_id (𝕜 := ℝ) x).fderiv
    rw [hfderiv]
    simp [E, du]
  simpa [E, u, du, hsum] using hcv

/-- Coordinatewise translation of the global `H¹` derivative bundle. -/
noncomputable def translateH1 (a : ℝ^n) :
    W^{1,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := by
  let ambient : WkpAmbientOn n 1 2 Set.univ →L[ℝ]
      WkpAmbientOn n 1 2 Set.univ := by
    let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 Set.univ)
    exact e.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun q ↦
        (translateLp 2 a).toContinuousLinearMap.comp
          (PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
            (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 Set.univ) q))
  refine ContinuousLinearMap.codRestrict
    (ambient.comp (Submodule.subtypeL (wkpSubmoduleOn n 1 2 Set.univ)))
    (wkpSubmoduleOn n 1 2 Set.univ) ?_
  intro U q
  rcases q.eq_baseIndex_or_eq_singleDerivIndex with hq | ⟨i, hq⟩
  · subst q
    have hloc := memLp_locallyIntegrableOn_domain
      (Lp.memLp (translateLp 2 a
        ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)))) (by norm_num)
    simpa [ambient, iteratedPartialDeriv] using
      (show HasWeakDerivativeOn (n := n) Set.univ []
        ((translateLp 2 a
          ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)) :
            DerivLp n 2 Set.univ) : ℝ^n → ℝ)
        ((translateLp 2 a
          ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)) :
            DerivLp n 2 Set.univ) : ℝ^n → ℝ) from
          hasWeakDerivativeOn_nil hloc)
  · subst q
    have hpoint := hasWeakDerivativeOn_translate_add a U i
    have hbaseAE := translateLp_apply_ae (n := n) 2 a
      ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))
    have hderivAE := translateLp_apply_ae (n := n) 2 a
      ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))
    simpa using (hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := Set.univ) (α := [i])
      (by simpa [ambient] using hbaseAE)
      (by simpa [ambient] using hderivAE)).2 hpoint

/-- Each coordinate of the translated bundle is the `L²` translate of the
corresponding coordinate of `U`. -/
@[simp]
theorem translateH1_apply (a : ℝ^n) (U : W^{1,2}(ℝ^n))
    (q : DerivIndex n 1) :
    ((translateH1 (n := n) a U : W^{1,2}(ℝ^n)) :
      WkpAmbientOn n 1 2 Set.univ) q =
      translateLp 2 a ((U : WkpAmbientOn n 1 2 Set.univ) q) := by
  let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 Set.univ)
  have hambient :
      ((translateH1 (n := n) a U : W^{1,2}(ℝ^n)) :
        WkpAmbientOn n 1 2 Set.univ) =
        e.symm (fun r ↦
          translateLp 2 a ((U : WkpAmbientOn n 1 2 Set.univ) r)) := by
    rfl
  rw [hambient]
  change
    (e (e.symm (fun r ↦
      translateLp 2 a ((U : WkpAmbientOn n 1 2 Set.univ) r)))) q =
      translateLp 2 a ((U : WkpAmbientOn n 1 2 Set.univ) q)
  rw [e.apply_symm_apply]

/-- Translation is an isometry on global `H¹`. -/
theorem norm_translateH1 (a : ℝ^n) (U : W^{1,2}(ℝ^n)) :
    ‖translateH1 (n := n) a U‖ = ‖U‖ := by
  change ‖((translateH1 (n := n) a U : W^{1,2}(ℝ^n)) :
    WkpAmbientOn n 1 2 Set.univ)‖ = ‖(U : WkpAmbientOn n 1 2 Set.univ)‖
  rw [PiLp.norm_eq_sum (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    PiLp.norm_eq_sum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [translateH1_apply, norm_translateLp]

/-- Successive `H¹` translations add their displacement vectors. -/
theorem translateH1_comp (a b : ℝ^n) (U : W^{1,2}(ℝ^n)) :
    translateH1 (n := n) a (translateH1 (n := n) b U) =
      translateH1 (n := n) (a + b) U := by
  apply Subtype.ext
  apply PiLp.ext
  intro q
  simp only [translateH1_apply]
  exact Rellich.translateLp_add 2 a b
    ((U : WkpAmbientOn n 1 2 Set.univ) q)

/-- Translation by zero is the identity on global `H¹`. -/
@[simp]
theorem translateH1_zero (U : W^{1,2}(ℝ^n)) :
    translateH1 (n := n) (0 : ℝ^n) U = U := by
  apply Subtype.ext
  apply PiLp.ext
  intro q
  simp

end SobolevSpace.GraphSpace
