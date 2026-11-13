/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
public import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.Operator
public import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback

/-!
# Flattened boundary fields for C¹ extension

We carry out, at the level of representatives, the boundary steps of
the extension theorem for `C¹` domains (Evans §5.4, Theorem 1). Fix a boundary
chart `Φᵢ` with partition function `ψᵢ` from the atlas and a Sobolev function
`u ∈ W^{1,p}(Ω)` with `L^p` weak derivatives.  Then:

1. `ψᵢ u` is a Sobolev function on `Ω` supported in the compact set
   `boundarySupport i = supp ψᵢ ⊆ Φᵢ.source`, with weak derivatives given by
   the product rule.
2. Its flattening `(ψᵢ u) ∘ Φᵢ⁻¹` is a Sobolev function on
   `Φᵢ.target ∩ ℝ^n₊ = Φᵢ(Ω ∩ source)`, with weak derivatives given by the chain
   rule `∑ⱼ (∂ⱼ(ψᵢu)) ∘ Φᵢ⁻¹ · ∂ₖ(Φᵢ⁻¹)ⱼ` (`flattenedBoundaryField`).  The
   change of variables preserves `L^p` because the pulled-back function is
   supported in the compact set `Φᵢ(supp ψᵢ)`, on which the Jacobian is
   bounded.
3. Extended by zero across the lateral boundary of the chart target, it is a
   Sobolev function on the whole upper half-space `ℝ^n₊`
   (`upperHalfSpaceBoundaryField`).  This uses that the support stays away
   from the lateral boundary, so a cutoff equal to one near the support
   transfers the weak-derivative identity.
4. The half-space reflection operator extends it to `W^{1,p}(ℝ^n)`
   (`reflectedBoundaryField`), agreeing with the unreflected field on `ℝ^n₊`.
5. Multiplying by the target cutoff `η`, equal to one on `Φᵢ(supp ψᵢ)` and
   compactly supported in `Φᵢ.target`, relocalizes the reflected function
   inside the chart target (`relocalizedReflectedBoundaryField`) so that it
   can be pulled back through `Φᵢ` in `BoundaryPiece.ClassicalRepresentative`.

## Main definitions and results

* `localizedBoundaryRepresentative`, `flattenedBoundaryRepresentative`: the
  functions `ψᵢ u` and `(ψᵢ u) ∘ Φᵢ⁻¹`.
* `pullback_memLp_of_support_subset_K`, `flattenedBoundaryRepresentative_memLp`:
  `L^p` membership of pullbacks of compactly supported functions.
* `flattenedBoundaryField`, `upperHalfSpaceBoundaryField`: the Sobolev
  structures on the flattened chart region and on `ℝ^n₊`.
* `reflectedBoundaryField`, `reflectedBoundaryField_agree_ae_upperHalfSpace`:
  the reflected extension to `ℝ^n` and its agreement on the upper half-space.
* `relocalizedReflectedBoundaryField` with its support bound and the product
  rule representative
  `relocalizedReflectedBoundaryDerivativeRepresentative` of its derivatives.

## Implementation notes

The half-space extension is used only through the existence statement
`HalfSpace.exists_representativeExtensionOperator`, chosen once via
`Classical.choose`; no formula for the reflection enters here. That statement is proved in
`HalfSpace.FirstOrder.Operator` by even reflection. The proof of Evans §5.4, Theorem 1 instead
reflects `C¹` functions by the higher-order reflection (3), p. 269, and reaches `W^{1,p}` by
density (step 7, p. 271).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; the proof flattens the boundary
  near each boundary point (step 5, p. 270), extends across the flat boundary, and glues the pieces
  with a partition of unity (step 6, (9), p. 270).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Set
open scoped ENNReal Topology

namespace Extension

namespace C1

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

open MeasureTheory
open CompactSupportLocalization
open SobolevSpace.Boundary.C1ExtensionAtlas.DerivedCutoffs

namespace BoundaryPiece

/-- An indicator-localized product is in `Lᵖ` when its first factor has compact support and its
second factor is continuous. -/
theorem memLp_indicator_mul_continuous_of_support_within
    {S K : Set (ℝ^n)} (hS : MeasurableSet S) (hK : IsCompact K)
    {f a : ℝ^n → ℝ} (hfLp : MeasureTheory.MemLp f p (domainMeasure n S))
    (hfsupp : ∀ x ∈ S, f x ≠ 0 → x ∈ K) (ha : Continuous a) :
    MeasureTheory.MemLp (S.indicator fun x ↦ f x * a x) p
      (domainMeasure n (Set.univ : Set (ℝ^n))) := by
  have hf0Lp : MemLp (S.indicator f) p (domainMeasure n (Set.univ : Set (ℝ^n))) := by
    rw [memLp_indicator_iff_restrict hS.nullMeasurableSet]
    simpa [domainMeasure] using hfLp
  have hsupp : Function.support (fun x ↦ S.indicator f x * a x) ⊆ K := fun x hx ↦ by
    have hfx := left_ne_zero_of_mul hx
    have hxS := mem_of_indicator_ne_zero hfx
    exact hfsupp x hxS (by rwa [indicator_of_mem hxS] at hfx)
  have hprodK : MemLp (fun x ↦ S.indicator f x * a x) p (domainMeasure n K) :=
    (by simpa [domainMeasure] using hf0Lp.restrict K : MemLp (S.indicator f) p _).fun_mul
      (r := p) (SobolevSpace.WeakChangeOfVariables.memLp_on_compact_of_continuous
        (p := (⊤ : ℝ≥0∞)) hK ha)
  have heq : S.indicator (fun x ↦ f x * a x) = fun x ↦ S.indicator f x * a x :=
    funext fun _ ↦ indicator_mul_left S f a
  exact heq ▸ memLp_of_support_subset_of_subset (n := n) (p := p) (U := K)
    (Ωbig := (Set.univ : Set (ℝ^n))) hK.measurableSet (subset_univ _) hsupp hprodK

/-- The partial derivative of a test function is essentially bounded. -/
private theorem memLp_top_iteratedPartialDeriv_testFunction (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (j : Fin n) (μ : Measure (ℝ^n)) :
    MemLp (iteratedPartialDeriv (n := n) [j] φ.toFun) (⊤ : ℝ≥0∞) μ := by
  let dφ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) φ
  have hdφ : dφ.toFun = iteratedPartialDeriv (n := n) [j] φ.toFun := by
    funext x
    change (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j (1 : ℝ)) φ :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x = iteratedPartialDeriv (n := n) [j] φ.toFun x
    rw [_root_.TestFunction.lineDerivCLM_eq_fderivCLM,
      _root_.TestFunction.fderivCLM_apply_of_le φ (by simp)]
    rfl
  exact hdφ ▸ dφ.contDiff.continuous.memLp_top_of_hasCompactSupport dφ.hasCompactSupport μ

/-- A product-rule expression `φ d + (∂ⱼφ) w` vanishes off the topological support of `φ`. -/
private theorem support_productRule_subset_tsupport (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (j : Fin n)
    (d w : ℝ^n → ℝ) :
    Function.support (fun x ↦ φ.toFun x * d x + iteratedPartialDeriv (n := n) [j] φ.toFun x * w x)
      ⊆ tsupport φ.toFun := by
  intro x hx
  by_contra hxK
  have hφ : φ.toFun x = 0 := image_eq_zero_of_notMem_tsupport hxK
  have hdφ : iteratedPartialDeriv (n := n) [j] φ.toFun x = 0 := image_eq_zero_of_notMem_tsupport
    fun h ↦ hxK (tsupport_iteratedPartialDeriv_subset_tsupport [j] φ.toFun h)
  exact hx (by simp only [hφ, hdφ, zero_mul, add_zero])

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The `i`-th localized Sobolev representative in the original coordinates. -/
noncomputable def localizedBoundaryRepresentative
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) : ℝ^n → ℝ :=
  fun x ↦ (hΩ.boundaryCutoff i).toFun x * u.toFun x

/-- The localized representative written in the flattened boundary coordinates. -/
noncomputable def flattenedBoundaryRepresentative
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) : ℝ^n → ℝ :=
  fun y ↦
    localizedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u ((hΩ.chart i).symm y)

omit [Fact (1 ≤ p)] in
private theorem support_localizedBoundaryRepresentative_subset_boundarySupport
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    Function.support
        (localizedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u) ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport (n := n) (Ω := Ω) i :=
  fun _ hx ↦ subset_tsupport _ (left_ne_zero_of_mul hx)

/-- Pullback through a boundary chart preserves `Lᵖ` for functions supported
in the compact localization set `K`.  The function is only assumed to belong
to `Lᵖ(Ω)`; zero extension is used internally for the chart estimate. -/
theorem pullback_memLp_of_support_subset_K
    (i : Fin hΩ.N) {f : ℝ^n → ℝ}
    (hfLp : MeasureTheory.MemLp f p (domainMeasure n Ω))
    (hsupp : Function.support f ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport (n := n) (Ω := Ω) i) :
    MeasureTheory.MemLp (fun y ↦ f ((hΩ.chart i).symm y)) p
      (domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n)) := by
  let f0 : ℝ^n → ℝ := Ω.indicator f
  have hf0supp : Function.support f0 ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport (n := n) (Ω := Ω) i :=
    fun _ hx ↦ hsupp (support_indicator.subset hx).2
  have hf0Lp : MeasureTheory.MemLp f0 p (domainMeasure n (hΩ.chart i).source) := by
    change MeasureTheory.MemLp (Ω.indicator f) p (domainMeasure n (hΩ.chart i).source)
    rw [MeasureTheory.memLp_indicator_iff_restrict hΩ.isOpen.measurableSet.nullMeasurableSet]
    have hmeasure :
        (domainMeasure n (hΩ.chart i).source).restrict Ω =
          (domainMeasure n Ω).restrict (hΩ.chart i).source := by
      rw [domainMeasure, Measure.restrict_restrict hΩ.isOpen.measurableSet,
        Measure.restrict_restrict (hΩ.chart i).open_source.measurableSet, inter_comm]
    rw [hmeasure]
    exact hfLp.restrict (hΩ.chart i).source
  let E := (hΩ.chart i).symm
  have hfull : MeasureTheory.MemLp (fun y ↦ f0 (E y)) p (domainMeasure n E.source) := by
    apply SobolevSpace.WeakChangeOfVariables.memLp_comp_partialHomeomorph_of_compact_support
      (n := n) (p := p) (E := E)
      (hE := hΩ.chart_symm_contDiff i)
      (hEsymm := by simpa [E] using hΩ.chart_contDiff i)
      (hK := Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_boundarySupport
        (n := n) (Ω := Ω) i)
      (hKsub := by
        simpa [E] using
          Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport_subset_source
            (n := n) (Ω := Ω) i)
      (hsupp := hf0supp)
      (hfLp := by simpa [E] using hf0Lp)
  have hrestricted := hfull.restrict
    ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n)
  have hmeasure :
      (domainMeasure n (hΩ.chart i).target).restrict
          ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n) =
        domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n) := by
    simpa [domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (MeasureTheory.volume : Measure (ℝ^n)))
        (inter_subset_left :
          (hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n ⊆ (hΩ.chart i).target))
  have hrestricted' : MeasureTheory.MemLp
      (fun y ↦ f0 ((hΩ.chart i).symm y)) p
      (domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n)) := by
    simpa [E, hmeasure] using hrestricted
  have heq : (fun y ↦ f0 ((hΩ.chart i).symm y))
      =ᵐ[domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n)]
        (fun y ↦ f ((hΩ.chart i).symm y)) := by
    refine MeasureTheory.ae_restrict_of_forall_mem
      ((hΩ.chart i).open_target.measurableSet.inter
        (SobolevSpace.HalfSpace.isOpen_upper (n := n)).measurableSet) ?_
    intro y hy
    have hysource : (hΩ.chart i).symm y ∈ (hΩ.chart i).source :=
      (hΩ.chart i).map_target hy.1
    have hyΩ : (hΩ.chart i).symm y ∈ Ω := by
      apply (hΩ.chart_mem_iff_upper i _ hysource).2
      simpa [(hΩ.chart i).right_inv hy.1] using hy.2
    simp [f0, hyΩ]
  exact (MeasureTheory.memLp_congr_ae heq).1 hrestricted'

/-- The flattened boundary representative belongs to `Lᵖ` on the chart portion of the upper
half-space.  The proof zero-extends only for the norm estimate; on the upper chart region the
zero-extended and original representatives agree pointwise. -/
theorem flattenedBoundaryRepresentative_memLp
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    MeasureTheory.MemLp
      (flattenedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u) p
      (domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n)) := by
  apply pullback_memLp_of_support_subset_K (n := n) (p := p) (Ω := Ω) i
  · exact (SobolevSpaceOn.mulTestFunction (n := n) (p := p) (hΩ.boundaryCutoff i) u).memLp
  · exact support_localizedBoundaryRepresentative_subset_boundarySupport
      (n := n) (p := p) (Ω := Ω) i u

/-- The product-rule candidate for the `j`th weak derivative of the `i`-th localized
representative in the original coordinates: `ψᵢ ∂ⱼu + (∂ⱼψᵢ) u`. -/
def localizedBoundaryDerivativeRepresentative
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω)
    (j : Fin n) (du : ℝ^n → ℝ) : ℝ^n → ℝ :=
  fun x ↦ (hΩ.boundaryCutoff i).toFun x * du x +
    iteratedPartialDeriv (n := n) [j] (hΩ.boundaryCutoff i).toFun x * u.toFun x

omit [Fact (1 ≤ p)] in
private theorem support_localizedBoundaryDerivativeRepresentative_subset_boundarySupport
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (j : Fin n) (du : ℝ^n → ℝ) :
    Function.support
        (localizedBoundaryDerivativeRepresentative
          (n := n) (p := p) (Ω := Ω) i u j du) ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport (n := n) (Ω := Ω) i :=
  support_productRule_subset_tsupport (hΩ.boundaryCutoff i) j du u.toFun

omit [Fact (1 ≤ p)] in
private theorem localizedBoundaryDerivativeRepresentative_memLp
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (j : Fin n)
    {du : ℝ^n → ℝ} (hduLp : MeasureTheory.MemLp du p (domainMeasure n Ω)) :
    MeasureTheory.MemLp
      (localizedBoundaryDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i u j du) p
      (domainMeasure n Ω) := by
  have hψTop : MemLp (hΩ.boundaryCutoff i).toFun (⊤ : ℝ≥0∞) (domainMeasure n Ω) :=
    (hΩ.boundaryCutoff i).contDiff.continuous.memLp_top_of_hasCompactSupport
      (hΩ.boundaryCutoff i).hasCompactSupport (domainMeasure n Ω)
  exact (hψTop.fun_mul (r := p) hduLp).add
    ((memLp_top_iteratedPartialDeriv_testFunction _ j _).fun_mul (r := p) u.memLp)

/-- The chain-rule candidate for the `k`th weak derivative of the flattened localized
representative, written in the flattened boundary coordinates. -/
def flattenedBoundaryDerivativeRepresentative
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω)
    (du : Fin n → ℝ^n → ℝ) (k : Fin n) : ℝ^n → ℝ :=
  fun y ↦ ∑ j : Fin n,
    localizedBoundaryDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i u j (du j) ((hΩ.chart i).symm y) *
      ((fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) y)
        (EuclideanSpace.single k (1 : ℝ))) j

/-- The flattened derivative candidate lies in `Lp` on the flattened chart image. -/
theorem flattenedBoundaryDerivativeRepresentative_memLp
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (du : Fin n → ℝ^n → ℝ)
    (hduLp : ∀ j, MeasureTheory.MemLp (du j) p (domainMeasure n Ω)) (k : Fin n) :
    MeasureTheory.MemLp
      (flattenedBoundaryDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i u du k) p
      (domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n)) := by
  let U := (hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n
  let a : Fin n → ℝ^n → ℝ := fun j y ↦
    ((fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) y)
      (EuclideanSpace.single k (1 : ℝ))) j
  have haCont (j : Fin n) : Continuous (a j) :=
    (PiLp.continuous_apply 2 _ j).comp
      (((hΩ.chart_symm_contDiff i).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hUbounded : Bornology.IsBounded U :=
    (hΩ.chart_target_bounded i).subset inter_subset_left
  have hterm : ∀ j : Fin n, MeasureTheory.MemLp
      (fun y ↦
        localizedBoundaryDerivativeRepresentative
            (n := n) (p := p) (Ω := Ω) i u j (du j) ((hΩ.chart i).symm y) *
          a j y) p (domainMeasure n U) := by
    intro j
    have hcomp := pullback_memLp_of_support_subset_K (n := n) (p := p) (Ω := Ω) i
      (localizedBoundaryDerivativeRepresentative_memLp
        (n := n) (p := p) (Ω := Ω) i u j (hduLp j))
      (support_localizedBoundaryDerivativeRepresentative_subset_boundarySupport
        (n := n) (p := p) (Ω := Ω) i u j (du j))
    have haTop : MeasureTheory.MemLp (a j) (⊤ : ℝ≥0∞) (domainMeasure n U) :=
      SobolevSpace.WeakChangeOfVariables.memLp_top_on_bounded_of_continuous
        (n := n) hUbounded (haCont j)
    exact hcomp.fun_mul (r := p) haTop
  have hsum := MeasureTheory.memLp_finsetSum'
    (Finset.univ : Finset (Fin n)) (fun j _ ↦ hterm j)
  convert hsum using 1
  ext y
  simp [flattenedBoundaryDerivativeRepresentative, a]

/-- The flattened derivative candidate is the weak derivative of the flattened
representative on the flattened chart image. -/
theorem flattenedBoundaryRepresentative_hasWeakDerivative
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (du : Fin n → ℝ^n → ℝ)
    (hduLp : ∀ j, MeasureTheory.MemLp (du j) p (domainMeasure n Ω))
    (hduWeak : ∀ j, HasWeakDerivativeOn (n := n) Ω [j] u.toFun (du j))
    (k : Fin n) :
    HasWeakDerivativeOn (n := n)
      ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n) [k]
      (flattenedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u)
      (flattenedBoundaryDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i u du k) := by
  let chartΩ := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i
  let E := chartΩ.symm
  have htarget : E.target ⊆ Ω := by
    intro x hx
    have hx' : x ∈ chartΩ.source := by simpa [E] using hx
    simpa [chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] using hx'.2
  have hvolTarget : (MeasureTheory.volume : Measure (ℝ^n)) E.target ≠ ∞ :=
    ((hΩ.bounded.subset htarget).measure_lt_top
      (μ := (MeasureTheory.volume : Measure (ℝ^n)))).ne
  have hmeasure : (domainMeasure n Ω).restrict E.target = domainMeasure n E.target := by
    simpa [domainMeasure] using
      Measure.restrict_restrict_of_subset (μ := (volume : Measure (ℝ^n))) htarget
  have hlocalizedLp : MemLp
      (localizedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u) p
      (domainMeasure n E.target) := hmeasure ▸
    (SobolevSpaceOn.mulTestFunction (n := n) (p := p) (hΩ.boundaryCutoff i) u).memLp.restrict
      E.target
  let dg : Fin n → ℝ^n → ℝ := fun j ↦
    localizedBoundaryDerivativeRepresentative (n := n) (p := p) (Ω := Ω) i u j (du j)
  have hdgLp (j : Fin n) : MemLp (dg j) p (domainMeasure n E.target) := hmeasure ▸
    (localizedBoundaryDerivativeRepresentative_memLp (n := n) (p := p) (Ω := Ω) i u j
      (hduLp j)).restrict E.target
  have hdgWeak (j : Fin n) : HasWeakDerivativeOn (n := n) E.target [j]
      (localizedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u) (dg j) :=
    HasWeakDerivativeOn.mono (n := n) E.open_target.measurableSet htarget
      (hasWeakDerivativeOn_mul_testFunction_first (n := n) (p := p) (Ω := Ω) (i := j)
        u.memLp (hduLp j) (hduWeak j) (hΩ.boundaryCutoff i))
  have hchain :=
    SobolevSpace.WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp
      (n := n) (p := p) (SobolevSpace.Approximation.standardMollifier n)
      (E := E)
      (hE := by
        simpa [E, chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using
          hΩ.chart_symm_contDiff i)
      (hEsymm := by
        simpa [E, chartΩ, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using
          hΩ.chart_contDiff i)
      hvolTarget hlocalizedLp hdgLp hdgWeak k
  have hsource : E.source =
      (hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n := by
    change chartΩ.target = (hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n
    exact Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper (n := n) (Ω := Ω) i
  rw [hsource] at hchain
  exact hchain

/-- The localized boundary term is a `W^{1,p}` function in flattened coordinates. -/
noncomputable def flattenedBoundaryField
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    SobolevSpaceOn n 1 p
      ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n) := by
  classical
  choose du hduLp hduWeak using fun j : Fin n ↦ u.weak_derivs_inLp [j] (by simp)
  refine
    { toFun := flattenedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u
      memLp := flattenedBoundaryRepresentative_memLp (n := n) (p := p) (Ω := Ω) i u
      weak_derivs_inLp := ?_ }
  intro α hα
  have hshape : α = [] ∨ ∃ k : Fin n, α = [k] := by
    cases α with
    | nil => exact Or.inl rfl
    | cons k rest =>
        cases rest with
        | nil => exact Or.inr ⟨k, rfl⟩
        | cons l tail => simp at hα
  rcases hshape with rfl | ⟨k, rfl⟩
  · have hLp := flattenedBoundaryRepresentative_memLp (n := n) (p := p) (Ω := Ω) i u
    refine ⟨flattenedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u, hLp, ?_⟩
    have hloc := memLp_locallyIntegrableOn_domain hLp (Fact.out : (1 : ℝ≥0∞) ≤ p)
    exact hasWeakDerivativeOn_nil hloc
  · refine
      ⟨flattenedBoundaryDerivativeRepresentative
          (n := n) (p := p) (Ω := Ω) i u du k,
        ?_, ?_⟩
    · exact flattenedBoundaryDerivativeRepresentative_memLp
        (n := n) (p := p) (Ω := Ω) i u du hduLp k
    · exact flattenedBoundaryRepresentative_hasWeakDerivative
        (n := n) (p := p) (Ω := Ω) i u du hduLp hduWeak k

/-- The flattened local field, extended by zero outside the chart target. -/
def upperHalfSpaceBoundaryRepresentative
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) : ℝ^n → ℝ :=
  (hΩ.chart i).target.indicator
    (flattenedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u)

omit [Fact (1 ≤ p)] in
/-- The zero-extended flattened field is supported in the compact target support set. -/
theorem support_upperHalfSpaceBoundaryRepresentative_subset_targetSupport
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    Function.support
        (upperHalfSpaceBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u) ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget (n := n) (Ω := Ω) i := by
  intro y hy
  obtain ⟨hyT, hflat⟩ := support_indicator.subset hy
  exact ⟨(hΩ.chart i).symm y, support_localizedBoundaryRepresentative_subset_boundarySupport
    (n := n) (p := p) (Ω := Ω) i u hflat, (hΩ.chart i).right_inv hyT⟩

/-- The zero-extended flattened field lies in `Lp` on the upper half-space. -/
theorem upperHalfSpaceBoundaryRepresentative_memLp
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    MeasureTheory.MemLp
      (upperHalfSpaceBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u) p
      (domainMeasure n (SobolevSpace.HalfSpace.upper n)) := by
  rw [upperHalfSpaceBoundaryRepresentative, MeasureTheory.memLp_indicator_iff_restrict
    (hΩ.chart i).open_target.measurableSet.nullMeasurableSet]
  have hmeasure : (domainMeasure n (SobolevSpace.HalfSpace.upper n)).restrict
      (hΩ.chart i).target =
      domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n) := by
    rw [domainMeasure,
      Measure.restrict_restrict (hΩ.chart i).open_target.measurableSet]
  rw [hmeasure]
  exact flattenedBoundaryRepresentative_memLp (n := n) (p := p) (Ω := Ω) i u

/-- The flattened derivative candidate, extended by zero outside the chart target. -/
def upperHalfSpaceBoundaryDerivativeRepresentative
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω)
    (du : Fin n → ℝ^n → ℝ) (k : Fin n) : ℝ^n → ℝ :=
  (hΩ.chart i).target.indicator
    (flattenedBoundaryDerivativeRepresentative (n := n) (p := p) (Ω := Ω) i u du k)

omit [Fact (1 ≤ p)] in
/-- The zero-extended derivative candidate is supported in the compact target support set. -/
theorem support_upperHalfSpaceBoundaryDerivativeRepresentative_subset_targetSupport
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (du : Fin n → ℝ^n → ℝ) (k : Fin n) :
    Function.support
        (upperHalfSpaceBoundaryDerivativeRepresentative
          (n := n) (p := p) (Ω := Ω) i u du k) ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget (n := n) (Ω := Ω) i := by
  intro y hy
  obtain ⟨hyT, hflat⟩ := support_indicator.subset hy
  by_contra hyK
  have hzero (j : Fin n) : localizedBoundaryDerivativeRepresentative
      (n := n) (p := p) (Ω := Ω) i u j (du j) ((hΩ.chart i).symm y) = 0 := by
    by_contra hne
    exact hyK ⟨_, support_localizedBoundaryDerivativeRepresentative_subset_boundarySupport
      (n := n) (p := p) (Ω := Ω) i u j (du j) hne, (hΩ.chart i).right_inv hyT⟩
  exact hflat (by simp [flattenedBoundaryDerivativeRepresentative, hzero])

/-- The zero-extended derivative candidate lies in `Lp` on the upper half-space. -/
theorem upperHalfSpaceBoundaryDerivativeRepresentative_memLp
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (du : Fin n → ℝ^n → ℝ)
    (hduLp : ∀ j, MeasureTheory.MemLp (du j) p (domainMeasure n Ω)) (k : Fin n) :
    MeasureTheory.MemLp
      (upperHalfSpaceBoundaryDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i u du k) p
      (domainMeasure n (SobolevSpace.HalfSpace.upper n)) := by
  rw [upperHalfSpaceBoundaryDerivativeRepresentative,
    MeasureTheory.memLp_indicator_iff_restrict
    (hΩ.chart i).open_target.measurableSet.nullMeasurableSet]
  have hmeasure : (domainMeasure n (SobolevSpace.HalfSpace.upper n)).restrict
      (hΩ.chart i).target =
      domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n) := by
    rw [domainMeasure,
      Measure.restrict_restrict (hΩ.chart i).open_target.measurableSet]
  rw [hmeasure]
  exact flattenedBoundaryDerivativeRepresentative_memLp
    (n := n) (p := p) (Ω := Ω) i u du hduLp k

/-- The flattened boundary term, zeroed across the lateral chart boundary, is a
`W^{1,p}` function on the upper half-space in `ℝ^n` to which the reflection extension
applies. -/
noncomputable def upperHalfSpaceBoundaryField
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    SobolevSpaceOn n 1 p (SobolevSpace.HalfSpace.upper n) := by
  classical
  choose du hduLp hduWeak using fun j : Fin n ↦ u.weak_derivs_inLp [j] (by simp)
  refine
    { toFun := upperHalfSpaceBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u
      memLp := upperHalfSpaceBoundaryRepresentative_memLp
        (n := n) (p := p) (Ω := Ω) i u
      weak_derivs_inLp := ?_ }
  intro α hα
  have hshape : α = [] ∨ ∃ k : Fin n, α = [k] := by
    cases α with
    | nil => exact Or.inl rfl
    | cons k rest =>
        cases rest with
        | nil => exact Or.inr ⟨k, rfl⟩
        | cons l tail => simp at hα
  rcases hshape with rfl | ⟨k, rfl⟩
  · have hLp :=
      upperHalfSpaceBoundaryRepresentative_memLp (n := n) (p := p) (Ω := Ω) i u
    refine
      ⟨upperHalfSpaceBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u,
        hLp, ?_⟩
    have hloc := memLp_locallyIntegrableOn_domain hLp (Fact.out : (1 : ℝ≥0∞) ≤ p)
    exact hasWeakDerivativeOn_nil hloc
  · let g :=
      upperHalfSpaceBoundaryDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i u du k
    have hgLp := upperHalfSpaceBoundaryDerivativeRepresentative_memLp
      (n := n) (p := p) (Ω := Ω) i u du hduLp k
    refine ⟨g, hgLp, ?_⟩
    have hflatWeak := flattenedBoundaryRepresentative_hasWeakDerivative
      (n := n) (p := p) (Ω := Ω) i u du hduLp hduWeak k
    have hbaseEq :
        upperHalfSpaceBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u
        =ᵐ[domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n)]
          flattenedBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u := by
      refine MeasureTheory.ae_restrict_of_forall_mem
        ((hΩ.chart i).open_target.measurableSet.inter
          (SobolevSpace.HalfSpace.isOpen_upper (n := n)).measurableSet) ?_
      intro y hy
      simp [upperHalfSpaceBoundaryRepresentative, hy.1]
    have hderivEq : g
        =ᵐ[domainMeasure n ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n)]
          flattenedBoundaryDerivativeRepresentative
            (n := n) (p := p) (Ω := Ω) i u du k := by
      refine MeasureTheory.ae_restrict_of_forall_mem
        ((hΩ.chart i).open_target.measurableSet.inter
          (SobolevSpace.HalfSpace.isOpen_upper (n := n)).measurableSet) ?_
      intro y hy
      simp [g, upperHalfSpaceBoundaryDerivativeRepresentative, hy.1]
    have hweakInter : HasWeakDerivativeOn (n := n)
        ((hΩ.chart i).target ∩ SobolevSpace.HalfSpace.upper n) [k]
        (upperHalfSpaceBoundaryRepresentative (n := n) (p := p) (Ω := Ω) i u) g :=
      ((SobolevSpace.hasWeakDerivativeOn_congr_ae
        (n := n) (hfg := hbaseEq) (hf'g' := hderivEq)).2 hflatWeak)
    exact hasWeakDerivativeOn_of_inter_of_cutoff_one_nhds
      (n := n) (p := p)
      (hV := (hΩ.chart i).open_target)
      (hΩbig := SobolevSpace.HalfSpace.isOpen_upper (n := n))
      (K := Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget (n := n) (Ω := Ω) i)
      (support_upperHalfSpaceBoundaryRepresentative_subset_targetSupport
        (n := n) (p := p) (Ω := Ω) i u)
      (support_upperHalfSpaceBoundaryDerivativeRepresentative_subset_targetSupport
        (n := n) (p := p) (Ω := Ω) i u du k)
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff (n := n) (Ω := Ω) i)
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.tsupport_targetSupportCutoff_subset_target
        (n := n) (Ω := Ω) i)
      (targetSupportCutoff_eq_one_nhds_on_boundarySupportInTarget
        (n := n) (Ω := Ω) i)
      (upperHalfSpaceBoundaryRepresentative_memLp
        (n := n) (p := p) (Ω := Ω) i u) hgLp hweakInter

/-- A representative-level extension map from `ℝ^n₊` to `ℝ^n`, chosen with `Classical.choose`
from `HalfSpace.exists_representativeExtensionOperator`. -/
noncomputable def halfSpaceExtension :
    SobolevSpaceOn n 1 p (SobolevSpace.HalfSpace.upper n) →
      _root_.SobolevSpace.GlobalSobolevSpace n 1 p :=
  Classical.choose
    (SobolevSpace.Extension.GraphSpace.HalfSpace.exists_representativeExtensionOperator
      (n := n) (p := p))

/-- Reflect the flattened boundary term across the flat boundary. -/
noncomputable def reflectedBoundaryField
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    _root_.SobolevSpace.GlobalSobolevSpace n 1 p :=
  halfSpaceExtension (n := n) (p := p)
    (upperHalfSpaceBoundaryField (n := n) (p := p) (Ω := Ω) i u)

/-- The reflected term agrees almost everywhere with the unreflected flattened term on the
upper half-space. -/
theorem reflectedBoundaryField_agree_ae_upperHalfSpace
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    ∀ᵐ y ∂ domainMeasure n (SobolevSpace.HalfSpace.upper n),
      (reflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun y =
        (upperHalfSpaceBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun y :=
  Classical.choose_spec
    (SobolevSpace.Extension.GraphSpace.HalfSpace.exists_representativeExtensionOperator
      (n := n) (p := p))
    (upperHalfSpaceBoundaryField (n := n) (p := p) (Ω := Ω) i u)

/-- Localize the reflected function back inside the chart target before pulling it to the
original coordinates. -/
noncomputable def relocalizedReflectedBoundaryField
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    _root_.SobolevSpace.GlobalSobolevSpace n 1 p :=
  SobolevSpaceOn.mulTestFunction
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff (n := n) (Ω := Ω) i)
    (reflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u)

/-- Pointwise, the relocalized field is the target cutoff `η` times the
reflected field. -/
@[simp] theorem relocalizedReflectedBoundaryField_apply
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (y : ℝ^n) :
    (relocalizedReflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun y =
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff (n := n) (Ω := Ω) i).toFun y *
        (reflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun y :=
  rfl

/-- The reflected and relocalized chart field is supported in the reflected target compact set. -/
theorem support_relocalizedReflectedBoundaryField_subset_targetCutoffSupport
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) :
    Function.support
        (relocalizedReflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport (n := n) (Ω := Ω) i :=
  fun _ hy ↦ subset_tsupport _ (left_ne_zero_of_mul hy)

/-- Product-rule representative for a derivative of the relocalized reflected chart field. -/
def relocalizedReflectedBoundaryDerivativeRepresentative
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (j : Fin n) (dR : ℝ^n → ℝ) :
    ℝ^n → ℝ :=
  fun y ↦
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := n) (Ω := Ω) i).toFun y * dR y +
      iteratedPartialDeriv (n := n) [j]
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
          (n := n) (Ω := Ω) i).toFun y *
        (reflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).toFun y

/-- Each derivative representative is supported in the reflected target compact set. -/
theorem support_relocalizedReflectedBoundaryDerivativeRepresentative_subset
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (j : Fin n) (dR : ℝ^n → ℝ) :
    Function.support
      (relocalizedReflectedBoundaryDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i u j dR) ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport (n := n) (Ω := Ω) i :=
  support_productRule_subset_tsupport _ j dR _

/-- The relocalized reflected derivative representative belongs to global `Lᵖ`. -/
theorem relocalizedReflectedBoundaryDerivativeRepresentative_memLp
    (i : Fin hΩ.N) (u : SobolevSpaceOn n 1 p Ω) (j : Fin n) {dR : ℝ^n → ℝ}
    (hdRLp : MeasureTheory.MemLp dR p
      (domainMeasure n (Set.univ : Set (ℝ^n)))) :
    MeasureTheory.MemLp
      (relocalizedReflectedBoundaryDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) i u j dR) p
      (domainMeasure n (Set.univ : Set (ℝ^n))) := by
  let η := Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff (n := n) (Ω := Ω) i
  have hηTop : MemLp η.toFun (⊤ : ℝ≥0∞) (domainMeasure n (Set.univ : Set (ℝ^n))) :=
    η.contDiff.continuous.memLp_top_of_hasCompactSupport η.hasCompactSupport _
  exact (hηTop.fun_mul (r := p) hdRLp).add
    ((memLp_top_iteratedPartialDeriv_testFunction η j _).fun_mul (r := p)
      (reflectedBoundaryField (n := n) (p := p) (Ω := Ω) i u).memLp)

end BoundaryPiece

end C1

end Extension

end SobolevSpace
