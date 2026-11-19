/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Pointwise
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero
public import PDE.Spaces.Sobolev.Compactness.Translation.H1
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Boundary regularity: tangential translations

On the flattened upper half-space `Ω⁺ = {x ∈ ℝ^n : xₙ > 0}` the last coordinate
is normal to the boundary. A translation `x ↦ x + h eₖ` in a tangential
direction `k ≠ n` maps `Ω⁺` onto itself for every real step `h`, so it acts on
functions on `Ω⁺` with no extension or support-collar argument. This is what
allows the difference-quotient method to run up to the flat boundary. We
lift tangential translation to test functions, to `H¹₀(Ω⁺)`, and to
`Lᵖ(Ω⁺)`, where it is an isometry because it preserves the restricted
Lebesgue measure.

## Main results

* `coordinateStep_lastIndex_eq_zero`, `add_coordinateStep_mem_upper_iff`,
  `preimage_add_coordinateStep_upper`: a tangential step has no normal
  component and preserves the half-space exactly.
* `tangentialTranslateTestFunctionOnUpper`: translation of `C_c^∞(Ω⁺)` test
  functions.
* `tangentialTranslation_measurePreserving`: translation preserves Lebesgue
  measure restricted to `Ω⁺`.
* `tangentialTranslateH10`, `tangentialTranslateH10ToH1OnUpper_mem_H10`:
  translation as an endomorphism of `H¹₀(Ω⁺)`, with membership proved from
  the density of test functions rather than from a trace theorem.
* `tangentialTranslateLp`, `tangentialTranslateLp.apply_ae`,
  `tangentialTranslateH10_coordinate`: the `Lᵖ` isometry, its pointwise
  formula, and the identification of every Sobolev coordinate of the `H¹₀`
  translation with the corresponding `L²` translation.
* `tangentialTranslateL2_inv`, `inner_tangentialTranslateL2_left`: opposite
  steps are inverse, and translation by `h` is adjoint to translation by
  `-h` on `L²(Ω⁺)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 3 of the proof of Theorem 4 (tangential
  difference quotients), p. 335.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-!
## Tangential geometry of the flattened boundary

The final coordinate is normal to the flat boundary.  Every other coordinate
translation preserves the upper half-space exactly, for both signs and every
step size.  These facts replace the interior support-collar argument in the
boundary difference-quotient proof.
-/

/-- A tangential coordinate step `h eₖ` with `k ≠ n` has vanishing normal component.
This is the whole reason tangential translations preserve the half-space. -/
theorem coordinateStep_lastIndex_eq_zero
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ) :
    DifferenceQuotient.coordinateStep k h (PDE.Common.lastIndex (n := n)) = 0 := by
  simp [DifferenceQuotient.coordinateStep, Ne.symm hk]

/-- A coordinate difference-quotient step is tangential precisely in the
sense needed to preserve the flattened upper half-space. -/
theorem add_coordinateStep_mem_upper_iff
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (x : ℝ^n) :
    x + DifferenceQuotient.coordinateStep k h ∈ HalfSpace.upper n ↔
      x ∈ HalfSpace.upper n := by
  exact HalfSpace.add_mem_upper_iff_of_last_eq_zero n x
    (DifferenceQuotient.coordinateStep k h)
    (coordinateStep_lastIndex_eq_zero k hk h)

/-- Tangential translation has the upper half-space itself as its exact
preimage. -/
theorem preimage_add_coordinateStep_upper
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ) :
    (fun x : ℝ^n ↦ x + DifferenceQuotient.coordinateStep k h) ⁻¹'
        HalfSpace.upper n = HalfSpace.upper n := by
  exact HalfSpace.preimage_add_eq_upper_of_last_eq_zero n
    (DifferenceQuotient.coordinateStep k h)
    (coordinateStep_lastIndex_eq_zero k hk h)

/-- Tangential translation of a compactly supported smooth test function on
the upper half-space.  Exact preservation of the half-space ensures that no
support collar or extension convention enters this construction. -/
noncomputable def tangentialTranslateTestFunctionOnUpper
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (φ : TestFunctionOn n (HalfSpace.upper n)) :
    TestFunctionOn n (HalfSpace.upper n) := by
  let a := DifferenceQuotient.coordinateStep k h
  let f : ℝ^n → ℝ := fun x ↦ φ.1 (x + a)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    exact φ.1.contDiff.comp
      ((contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^n ↦ x)).add
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ^n ↦ a)))
  have hcompact : HasCompactSupport f := by
    simpa [f, a, Function.comp_def] using
      φ.1.hasCompactSupport.comp_homeomorph (Homeomorph.addRight a)
  let ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.mk f hf hcompact (Set.subset_univ _)
  refine ⟨ψ, ?_⟩
  have hsupport :
      tsupport f = (Homeomorph.addRight a) ⁻¹' tsupport φ.1.toFun := by
    simpa [f, Function.comp_def] using
      (tsupport_comp_eq_preimage φ.1.toFun (Homeomorph.addRight a))
  intro x hx
  have hψfun : ψ.toFun = f := by
    funext y
    rfl
  have hxf : x ∈ tsupport f := by
    rw [← hψfun]
    exact hx
  rw [hsupport] at hxf
  exact (add_coordinateStep_mem_upper_iff k hk h x).mp (φ.2 hxf)

/-- Pointwise formula for the translated test function: `x ↦ φ(x + h eₖ)`. -/
@[simp]
theorem tangentialTranslateTestFunctionOnUpper_apply
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (φ : TestFunctionOn n (HalfSpace.upper n)) (x : ℝ^n) :
    (tangentialTranslateTestFunctionOnUpper k hk h φ).1 x =
      φ.1 (x + DifferenceQuotient.coordinateStep k h) :=
  rfl

/-- Tangential translation preserves Lebesgue measure restricted to the
upper half-space.  Unlike a normal translation, its source and target
restricted measures are literally the same. -/
theorem tangentialTranslation_measurePreserving
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ) :
    MeasurePreserving
      (SobolevSpace.GraphSpace.Rellich.translationContinuousMap
        (DifferenceQuotient.coordinateStep k h))
      (domainMeasure n (HalfSpace.upper n))
      (domainMeasure n (HalfSpace.upper n)) := by
  have hpres :=
    (SobolevSpace.GraphSpace.Rellich.translationMeasurePreserving
      (n := n) (DifferenceQuotient.coordinateStep k h)).restrict_preimage
        (HalfSpace.measurableSet_upper (n := n))
  simpa [domainMeasure,
    SobolevSpace.GraphSpace.Rellich.translationContinuousMap,
    preimage_add_coordinateStep_upper (n := n) k hk h] using hpres

/-- Translate an `H¹₀` field tangentially after zero extension, then
restrict it back to the upper half-space.  The codomain is initially `H¹`;
the density argument below proves that the image still lies in `H¹₀`. -/
noncomputable def tangentialTranslateH10ToH1OnUpper
    [Fact (0 < n)] (k : Fin n) (h : ℝ) :
    H¹₀(HalfSpace.upper n) →L[ℝ]
      H¹(HalfSpace.upper n) :=
  (restrictCLM (n := n) (k := 1) (p := 2)
      (HalfSpace.measurableSet_upper (n := n))
      (subset_univ (HalfSpace.upper n))).comp
    ((translateH1 (n := n) (DifferenceQuotient.coordinateStep k h)).comp
      (ZeroTrace.zeroExtendH10 (n := n) (Ω := HalfSpace.upper n)
        (HalfSpace.measurableSet_upper (n := n))))

/-- On a compactly supported smooth input, tangential Sobolev translation
is exactly the classical translated test function. -/
theorem tangentialTranslateH10ToH1OnUpper_testFunction
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (φ : TestFunctionOn n (HalfSpace.upper n)) :
    tangentialTranslateH10ToH1OnUpper k h
        (testFunctionToH10 (n := n) (Ω := HalfSpace.upper n)
          φ) =
      testFunctionToH1 (n := n) (Ω := HalfSpace.upper n)
        (tangentialTranslateTestFunctionOnUpper k hk h φ) := by
  let Ωp := HalfSpace.upper n
  let hΩp : MeasurableSet Ωp := HalfSpace.measurableSet_upper (n := n)
  let a := DifferenceQuotient.coordinateStep k h
  let U : H¹((Set.univ : Set (ℝ^n))) :=
    testFunctionToH1 (n := n) (Ω := Set.univ) ⟨φ.1, subset_univ _⟩
  let ψ := tangentialTranslateTestFunctionOnUpper k hk h φ
  change restrictCLM (n := n) (k := 1) (p := 2) hΩp (subset_univ Ωp)
      (translateH1 (n := n) a (ZeroTrace.zeroExtendH10 (n := n) (Ω := Ωp) hΩp
        (testFunctionToH10 (n := n) (Ω := Ωp) φ))) =
    testFunctionToH1 (n := n) (Ω := Ωp) ψ
  rw [show ZeroTrace.zeroExtendH10 (n := n) (Ω := Ωp) hΩp
      (testFunctionToH10 (n := n) (Ω := Ωp) φ) = U by
    simpa [Ωp, hΩp, U] using ZeroTrace.zeroExtendH10_testFunction_eq (n := n) (Ω := Ωp) hΩp φ]
  apply WkpSpaceOn.ext_of_base_ae (HalfSpace.isOpen_upper (n := n))
  have hle := ae_mono (domainMeasure_le (n := n) (subset_univ Ωp))
  have hUbase : ((((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
      DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Set.univ] φ.1.toFun := by
    filter_upwards [mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := Set.univ)
      (f := φ.1.toFun) φ.1.contDiff φ.1.hasCompactSupport (baseIndex n 1)] with x hx
    simpa [U, testFunctionToH1, iteratedPartialDeriv] using hx
  have hψbase : ((((testFunctionToH1 (n := n) (Ω := Ωp) ψ : WkpAmbientOn n 1 2 Ωp)
      (baseIndex n 1) : DerivLp n 2 Ωp) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ωp]
        fun x ↦ φ.1 (x + a) := by
    filter_upwards [mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := Ωp)
      (f := ψ.1.toFun) ψ.1.contDiff ψ.1.hasCompactSupport (baseIndex n 1)] with x hx
    simpa [testFunctionToH1, ψ, a, iteratedPartialDeriv] using hx
  refine (restrictCLM_apply_ae hΩp (subset_univ Ωp) (translateH1 (n := n) a U)
    (baseIndex n 1)).trans ?_
  simpa only [translateH1_apply, Function.comp_def, Rellich.translationContinuousMap] using
    ((Rellich.translateLp_apply_ae (n := n) 2 a _).filter_mono hle).trans
      ((((Rellich.translationMeasurePreserving (n := n) a).quasiMeasurePreserving.ae_eq_comp
        hUbase).filter_mono hle).trans hψbase.symm)

/-- Tangential translation preserves `H¹₀` on the upper half-space in `ℝ^n`. The proof uses
the defining density of `C_c^∞` on that half-space and the exact translated-test theorem
above, so no trace characterization is assumed. -/
theorem tangentialTranslateH10ToH1OnUpper_mem_H10
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) :
    tangentialTranslateH10ToH1OnUpper k h u ∈
      (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule := by
  refine DenseRange.induction_on
    (denseRange_testFunctionToH10Linear
      (n := n) (Ω := HalfSpace.upper n)) u ?_ ?_
  · exact (instIsClosed_h10SubmoduleOn_toSubmodule
      (n := n) (Ω := HalfSpace.upper n)).preimage
        (tangentialTranslateH10ToH1OnUpper k h).continuous
  · intro φ
    change tangentialTranslateH10ToH1OnUpper k h
        (testFunctionToH10 (n := n) (Ω := HalfSpace.upper n)
          φ) ∈
      (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule
    rw [tangentialTranslateH10ToH1OnUpper_testFunction k hk h φ]
    exact testFunctionToH1_mem_H10
      (n := n) (Ω := HalfSpace.upper n)
      (tangentialTranslateTestFunctionOnUpper k hk h φ)

/-- Tangential translation as a continuous linear endomorphism of `H¹₀` on the upper half-space
in `ℝ^n`. -/
noncomputable def tangentialTranslateH10
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) :
    H¹₀(HalfSpace.upper n) →L[ℝ]
      H¹₀(HalfSpace.upper n) :=
  ContinuousLinearMap.codRestrict
    (tangentialTranslateH10ToH1OnUpper k h)
    (h10SubmoduleOn (n := n) (Ω := HalfSpace.upper n)).toSubmodule
    (tangentialTranslateH10ToH1OnUpper_mem_H10 k hk h)

/-- Forgetting the zero-trace witness, `tangentialTranslateH10` is the `H¹`-valued
translation `tangentialTranslateH10ToH1OnUpper`. -/
@[simp]
theorem tangentialTranslateH10.coe
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) :
    ((tangentialTranslateH10 k hk h u :
        H¹₀(HalfSpace.upper n)) :
      H¹(HalfSpace.upper n)) =
        tangentialTranslateH10ToH1OnUpper k h u :=
  rfl

/-- Tangential translation as a linear isometry of `Lᵖ` on the upper half-space in `ℝ^n`.
Its construction on the restricted measure avoids extending a field outside the half-space
and makes the boundary argument independent of representatives. -/
noncomputable def tangentialTranslateLp
    [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ) :
    DerivLp n p (HalfSpace.upper n) →ₗᵢ[ℝ]
      DerivLp n p (HalfSpace.upper n) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ
    (SobolevSpace.GraphSpace.Rellich.translationContinuousMap
      (DifferenceQuotient.coordinateStep k h))
    (tangentialTranslation_measurePreserving k hk h)

/-- Tangential translation preserves the `Lᵖ(Ω⁺)` norm: it is composition with a map that
preserves the restricted Lebesgue measure. -/
theorem tangentialTranslateLp.norm
    [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (u : DerivLp n p (HalfSpace.upper n)) :
    ‖tangentialTranslateLp p k hk h u‖ = ‖u‖ :=
  (tangentialTranslateLp (n := n) p k hk h).norm_map u

/-- The restricted-space translation has the expected representative almost
everywhere on the upper half-space. -/
theorem tangentialTranslateLp.apply_ae
    [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (u : DerivLp n p (HalfSpace.upper n)) :
    ((tangentialTranslateLp p k hk h u :
        DerivLp n p (HalfSpace.upper n)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (HalfSpace.upper n)]
        fun x ↦ u (x + DifferenceQuotient.coordinateStep k h) := by
  filter_upwards
    [MeasureTheory.Lp.coeFn_compMeasurePreserving u
      (tangentialTranslation_measurePreserving k hk h)] with x hx
  exact hx

/-- Every weak-derivative coordinate of tangential `H¹₀` translation is
the corresponding restricted `L²` translation.  This connects
admissibility in the Sobolev space with the coordinatewise energy algebra. -/
theorem tangentialTranslateH10_coordinate
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n))
    (q : DerivIndex n 1) :
    ((((tangentialTranslateH10 k hk h u :
        H¹₀(HalfSpace.upper n)) :
        H¹(HalfSpace.upper n)) :
      WkpAmbientOn n 1 2 (HalfSpace.upper n)) q) =
      tangentialTranslateLp 2 k hk h
        ((((u : H¹(HalfSpace.upper n)) :
          WkpAmbientOn n 1 2 (HalfSpace.upper n)) q)) := by
  let Ωp := HalfSpace.upper n
  let hΩp : MeasurableSet Ωp := HalfSpace.measurableSet_upper (n := n)
  let a := DifferenceQuotient.coordinateStep k h
  let U : H¹((Set.univ : Set (ℝ^n))) := ZeroTrace.zeroExtendH10 (n := n) (Ω := Ωp) hΩp u
  apply Lp.ext
  have hle := ae_mono (domainMeasure_le (n := n) (subset_univ Ωp))
  have hzero : ((((U : WkpAmbientOn n 1 2 Set.univ) q : DerivLp n 2 Set.univ) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Set.univ] Ωp.indicator fun x ↦
        ((((u : H¹(Ωp)) : WkpAmbientOn n 1 2 Ωp) q : DerivLp n 2 Ωp) : ℝ^n → ℝ) x := by
    simpa [U, domainMeasure] using
      ZeroTrace.zeroExtendH10_coordinate_apply_ae (n := n) (Ω := Ωp) hΩp u q
  have hzeroShift : (fun x ↦ ((((U : WkpAmbientOn n 1 2 Set.univ) q :
      DerivLp n 2 Set.univ) : ℝ^n → ℝ)) (x + a)) =ᵐ[domainMeasure n Ωp]
        fun x ↦ ((((u : H¹(Ωp)) : WkpAmbientOn n 1 2 Ωp) q : DerivLp n 2 Ωp) : ℝ^n → ℝ)
          (x + a) := by
    filter_upwards [((Rellich.translationMeasurePreserving (n := n) a).quasiMeasurePreserving
      |>.ae_eq_comp hzero).filter_mono hle, ae_restrict_mem hΩp] with x hx hxΩ
    exact hx.trans (indicator_of_mem ((add_coordinateStep_mem_upper_iff k hk h x).2 hxΩ) _)
  change (((((tangentialTranslateH10 k hk h u : H¹₀(Ωp)) : H¹(Ωp)) :
    WkpAmbientOn n 1 2 Ωp) q : DerivLp n 2 Ωp) : ℝ^n → ℝ) =ᵐ[_] _
  simpa only [tangentialTranslateH10.coe, tangentialTranslateH10ToH1OnUpper,
    ContinuousLinearMap.comp_apply, translateH1_apply, Function.comp_def,
    Rellich.translationContinuousMap, Ωp, hΩp, a, U] using
    (restrictCLM_apply_ae hΩp (subset_univ Ωp) (translateH1 (n := n) a U) q).trans
      (((Rellich.translateLp_apply_ae (n := n) 2 a _).filter_mono hle).trans
        (hzeroShift.trans (tangentialTranslateLp.apply_ae 2 k hk h _).symm))

/-- Tangential translations by opposite steps are inverse on the restricted
`L²` space. -/
theorem tangentialTranslateL2_inv
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (u : DerivLp n 2 (HalfSpace.upper n)) :
    tangentialTranslateLp 2 k hk h
        (tangentialTranslateLp 2 k hk (-h) u) = u := by
  apply Lp.ext
  filter_upwards [tangentialTranslateLp.apply_ae 2 k hk h (tangentialTranslateLp 2 k hk (-h) u),
    (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving.ae_eq_comp
      (tangentialTranslateLp.apply_ae 2 k hk (-h) u)] with x hout hin
  refine hout.trans (hin.trans (congrArg u ?_))
  simp [Rellich.translationContinuousMap, DifferenceQuotient.coordinateStep, add_assoc]

/-- Tangential translation is adjoint to translation by the opposite step on `L²` over the
upper half-space in `ℝ^n`. -/
theorem inner_tangentialTranslateL2_left
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (u v : DerivLp n 2 (HalfSpace.upper n)) :
    inner ℝ (tangentialTranslateLp 2 k hk h u) v =
      inner ℝ u (tangentialTranslateLp 2 k hk (-h) v) := by
  have hv : tangentialTranslateLp 2 k hk h
      (tangentialTranslateLp 2 k hk (-h) v) = v :=
    tangentialTranslateL2_inv k hk h v
  calc
    inner ℝ (tangentialTranslateLp 2 k hk h u) v =
        inner ℝ (tangentialTranslateLp 2 k hk h u)
          (tangentialTranslateLp 2 k hk h
            (tangentialTranslateLp 2 k hk (-h) v)) := by rw [hv]
    _ = inner ℝ u (tangentialTranslateLp 2 k hk (-h) v) :=
      (tangentialTranslateLp 2 k hk h).inner_map_map u
        (tangentialTranslateLp 2 k hk (-h) v)

end GraphSpace.BoundaryRegularity
end SobolevSpace
