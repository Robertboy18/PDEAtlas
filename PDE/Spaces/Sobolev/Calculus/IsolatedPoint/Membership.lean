/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import PDE.FDeriv.Operators
public import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder
public import PDE.Spaces.Sobolev.Calculus.IsolatedPoint
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
public import PDE.Spaces.Sobolev.GraphSpace.Local.Definitions
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder

/-!
# Sobolev membership of functions that are smooth away from a point

A function that is smooth except at one point is often known to be in `W^{1,p}_loc`, and one
wants to compute with its classical derivatives. Both directions hold. On `ℝⁿ⁺¹`, `n ≥ 1`, a
function that is `C¹` off the origin, with the function and its classical partial derivatives
in `Lᵖ`, is an element of `W^{1,p}` whose weak partial derivatives are the classical ones.
Conversely, a function of `W^{1,p}_loc(ℝⁿ)` that is `C¹` off a point has its classical partial
derivatives in `Lᵖ` on every bounded open set, when points are null sets. The same for higher
order, `W^{k,p}_loc` and `Cᵏ` off a point with `k ≥ 2`, is not stated here.
`NavierStokes.Stationary.exists_solenoidal_H1_of_contDiffOn` is the version for divergence-free
vector fields. Hou, Wang and Yang ask their approximate profile to be smooth off the origin and
locally in `H¹` and then compute with its classical derivatives.

## Main results

* `SobolevSpace.GraphSpace.IsLocallyWkpOn.memLp`: a function of `W^{k,p}_loc(Ω)` is in `Lᵖ` on
  every open set whose closure is a compact subset of `Ω`.
* `SobolevSpace.GraphSpace.IsLocallyWkpOn.memLp_partialDeriv_of_contDiffOn`: its classical
  partial derivatives are in `Lᵖ` on bounded open sets when it is `C¹` off one point.
* `SobolevSpace.exists_wkpSpace_of_contDiffAt_off_zero`: a point is removable for `W^{1,p}`.

## How it works

In dimension at least two a point is too small to carry a derivative: if a function and its
classical partial derivatives are locally integrable, the classical derivatives are the weak
ones on the whole space (`hasWeakDerivativeOn_partialDeriv_of_contDiffAt_off_zero`), and
`exists_of_weakGradient` builds the Sobolev element. Conversely, on a bounded open set `V` a
function of `W^{1,p}_loc` has a weak gradient in `Lᵖ(V)`. On `V` minus the point the classical
gradient is also a weak gradient (`hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn`), and
weak derivatives are unique (`HasWeakDerivativeOn.unique_ae`), so the two agree almost everywhere
on `V`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Assumption 1 and Section 2.1.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal Sobolev

namespace SobolevSpace

variable {n : ℕ} {p : ℝ≥0∞}

namespace GraphSpace

/-- A function of `W^{k,p}_loc(Ω)` is in `Lᵖ` on every open set whose closure is a compact
subset of `Ω`. -/
theorem IsLocallyWkpOn.memLp {k : ℕ} {Ω V : Set (ℝ^n)} {u : ℝ^n → ℝ}
    (hu : IsLocallyWkpOn k p Ω u) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) : MemLp u p (domainMeasure n V) := by
  obtain ⟨U, hU⟩ := hu V hV hVc hVΩ
  exact (Lp.memLp _).ae_eq hU

/-- A function of `W^{1,p}_loc(ℝⁿ)` that is `C¹` away from a point `z` has its classical partial
derivatives in `Lᵖ` on every bounded open set: there they agree almost everywhere with the weak
derivatives, because both are weak derivatives on the set with `z` removed. -/
theorem IsLocallyWkpOn.memLp_partialDeriv_of_contDiffOn [Fact (1 ≤ p)]
    [NullSingletonClass (volume : Measure (ℝ^n))] {u : ℝ^n → ℝ} (hu : IsLocallyWkpOn 1 p univ u)
    {z : ℝ^n} (hs : ContDiffOn ℝ 1 u {z}ᶜ) (i : Fin n) {V : Set (ℝ^n)} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) : MemLp (PDE.partialDeriv i u) p (domainMeasure n V) := by
  obtain ⟨U, hU⟩ := hu V hV hVc (subset_univ _)
  have hweak : HasWeakDerivativeOn V [i] u (fun x ↦ wkpGradientCLM U x i) :=
    (hasWeakDerivativeOn_wkpGradientCLM U i).congr_ae hU Filter.EventuallyEq.rfl
  have hV' : IsOpen (V ∩ {z}ᶜ) := hV.inter isOpen_compl_singleton
  have h₁ := hweak.mono hV'.measurableSet inter_subset_left
  have h₂ : HasWeakDerivativeOn (V ∩ {z}ᶜ) [i] u (PDE.partialDeriv i u) := by
    simpa only [PDE.iteratedPartialDeriv] using
      hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn (k := 1) hV'
        (hs.mono inter_subset_right) [i] (by simp)
  have hae' := h₁.unique_ae hV' h₂
  -- The point `z` is a null set, so the identification holds almost everywhere on `V`.
  have hae : (fun x ↦ wkpGradientCLM U x i) =ᵐ[domainMeasure n V] PDE.partialDeriv i u := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hV.measurableSet]
    rw [Filter.EventuallyEq, ae_restrict_iff' hV'.measurableSet] at hae'
    filter_upwards [hae', (volume : Measure (ℝ^n)).ae_ne z] with x hx hxz hxV
    exact hx ⟨hxV, hxz⟩
  have hg : MemLp (fun x ↦ wkpGradientCLM U x i) p (domainMeasure n V) := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (Lp.memLp (wkpGradientCLM U))
  exact hg.ae_eq hae

end GraphSpace

open GraphSpace

/-- **A point is removable for `W^{1,p}`.** A function on `ℝⁿ⁺¹`, `n ≥ 1`, that is `C¹` away
from the origin, with the function and its classical partial derivatives in `Lᵖ`, is an element
of `W^{1,p}(ℝⁿ⁺¹)`, and its weak partial derivatives are the classical ones. -/
theorem exists_wkpSpace_of_contDiffAt_off_zero [Fact (1 ≤ p)] [NeZero n]
    {f : ℝ^(n + 1) → ℝ} (hf : ∀ x : ℝ^(n + 1), x ≠ 0 → ContDiffAt ℝ 1 f x)
    (hfp : MemLp f p volume) (hgp : ∀ i, MemLp (PDE.partialDeriv i f) p volume) :
    ∃ U : W^{1,p}(ℝ^(n + 1)), baseRepresentative U =ᵐ[volume] f ∧
      ∀ i, (wkpCoordinateCLM (singleDerivIndex (n + 1) i) U : ℝ^(n + 1) → ℝ) =ᵐ[volume]
        PDE.partialDeriv i f := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hfp' : MemLp f p (domainMeasure (n + 1) univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using hfp
  have hgp' : MemLp (gradient f) p (domainMeasure (n + 1) univ) := by
    apply memLp_piLp_iff.mpr
    intro j
    simpa only [PDE.gradient_apply_eq_partialDeriv, domainMeasure, Measure.restrict_univ] using
      hgp j
  obtain ⟨U, hbase, hgrad⟩ := exists_of_weakGradient hfp' hgp' fun j ↦ by
    simpa only [PDE.gradient_apply_eq_partialDeriv] using
      hasWeakDerivativeOn_partialDeriv_of_contDiffAt_off_zero hf
        (memLp_locallyIntegrableOn_domain hfp' hp) j
        (memLp_locallyIntegrableOn_domain (by
          simpa only [domainMeasure, Measure.restrict_univ] using hgp j) hp)
  simp only [domainMeasure, Measure.restrict_univ] at hbase hgrad
  refine ⟨U, hbase, fun j ↦ ?_⟩
  have hcoord := wkpGradientCLM_apply_ae U
  simp only [domainMeasure, Measure.restrict_univ] at hcoord
  filter_upwards [hcoord, hgrad] with x hx hy
  calc (wkpCoordinateCLM (singleDerivIndex (n + 1) j) U : ℝ^(n + 1) → ℝ) x
      = wkpGradientCLM U x j := (hx j).symm
    _ = gradient f x j := congrArg (fun z : ℝ^(n + 1) ↦ z j) hy
    _ = PDE.partialDeriv j f x := PDE.gradient_apply_eq_partialDeriv _ _ _

end SobolevSpace
