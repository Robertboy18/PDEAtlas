/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
public import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra -- shake: keep
public import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep

/-!
# Interior localization for the `C¹` extension operator

The extension theorem for a bounded `C¹` domain `Ω` (Evans, PDE, §5.4) splits a Sobolev function
`u ∈ W^{1,p}(Ω)` with a partition of unity `ψ₀ + ∑ ψᵢ = 1` on `Ω`, where `ψ₀` is supported inside
`Ω` and each `ψᵢ` lives in a boundary chart. The boundary pieces are flattened to the half-space
and extended by reflection; the interior piece `ψ₀ u` needs no reflection at all, since it
vanishes near `∂Ω` and its zero extension is already a global `W^{1,p}(ℝ^n)` function. We
handle that interior piece.

The partition data comes from the `Boundary.C1ExtensionAtlas` instance: `ψ₀` is
`hΩ.interiorCutoff`, a test function with `tsupport ψ₀ ⊆ Ω`.

## Main results

* `InteriorPiece.interiorCutoffRepresentative`: the pointwise product `ψ₀ · u`, read as a
  function on all of `ℝ^n` (the representative `u.toFun` is already a total function).
* `InteriorPiece.extension`: the product as an element of the global space
  `GlobalSobolevSpace n 1 p`. The order-one weak derivatives are `ψ₀ ∂ᵢu + (∂ᵢψ₀) u`, obtained
  from the product rule on `Ω` and transferred to `ℝ^n` because both the function and its
  candidate derivatives are supported in the compact set `tsupport ψ₀ ⊆ Ω`, on a neighbourhood of
  which a further cutoff equals one.
* `InteriorPiece.extension_apply`: the global function agrees with `ψ₀ u` pointwise.

## Implementation notes

Only orders `0` and `1` need to be checked for membership in `W^{1,p}`; the multi-index case
split in `extension` reflects that. `L^p` membership on `ℝ^n` is reduced to `L^p` membership on
`Ω` through `memLp_of_support_subset_of_subset`, using that the support lies in `Ω`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, step 6 of the proof, p. 270:
  with a partition of unity `{ζᵢ}` for an open set `W₀ ⊂⊂ U` and boundary sets `Wᵢ`, the extension
  is `Σ ζᵢ ūᵢ` with `ū₀ = u`, so the interior piece is `ζ₀ u`.
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
open Boundary.C1ExtensionAtlas.DerivedCutoffs

namespace InteriorPiece

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The representative of the interior partition component `ψ₀u`, regarded as a function on all
of `ℝ^n`.  Compact support inside `Ω` makes zero extension across the boundary harmless. -/
noncomputable def interiorCutoffRepresentative
    (u : SobolevSpaceOn n 1 p Ω) : ℝ^n → ℝ :=
  fun x ↦ hΩ.interiorCutoff.toFun x * u.toFun x

omit [Fact (1 ≤ p)] in
/-- The interior partition component is supported in the interior support set. -/
theorem support_interiorCutoffRepresentative_subset
    (u : SobolevSpaceOn n 1 p Ω) :
    Function.support
        (interiorCutoffRepresentative (n := n) (p := p) (Ω := Ω) u) ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupport (n := n) (Ω := Ω) := by
  intro x hx
  apply subset_tsupport hΩ.interiorCutoff.toFun
  intro hψ
  exact hx (by simp [interiorCutoffRepresentative, hψ])

omit [Fact (1 ≤ p)] in
/-- The interior partition component lies in `Lp` on all of `ℝ^n`. -/
theorem memLp_interiorCutoffRepresentative
    (u : SobolevSpaceOn n 1 p Ω) :
    MeasureTheory.MemLp
      (interiorCutoffRepresentative (n := n) (p := p) (Ω := Ω) u) p
      (domainMeasure n (Set.univ : Set (ℝ^n))) := by
  have hlocal : MeasureTheory.MemLp
      (interiorCutoffRepresentative (n := n) (p := p) (Ω := Ω) u) p
      (domainMeasure n Ω) := by
    have hψTop : MeasureTheory.MemLp hΩ.interiorCutoff.toFun (⊤ : ℝ≥0∞) (domainMeasure n Ω) :=
      hΩ.interiorCutoff.contDiff.continuous.memLp_top_of_hasCompactSupport
        hΩ.interiorCutoff.hasCompactSupport (domainMeasure n Ω)
    change MeasureTheory.MemLp (fun x ↦ hΩ.interiorCutoff.toFun x * u.toFun x) p
      (domainMeasure n Ω)
    exact hψTop.fun_mul u.memLp
  exact
    memLp_of_support_subset_of_subset (n := n) (p := p) (U := Ω)
      (Ωbig := (Set.univ : Set (ℝ^n))) hΩ.isOpen.measurableSet (subset_univ _)
      ((support_interiorCutoffRepresentative_subset
          (n := n) (p := p) (Ω := Ω) u).trans
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupport_subset_domain
          (n := n) (Ω := Ω))) hlocal

/-- The product-rule candidate for the `i`th weak derivative of the interior partition
component: `ψ₀ ∂ᵢu + (∂ᵢψ₀) u`. -/
def interiorCutoffDerivativeRepresentative
    (u : SobolevSpaceOn n 1 p Ω) (i : Fin n)
    (du : ℝ^n → ℝ) : ℝ^n → ℝ :=
  fun x ↦ hΩ.interiorCutoff.toFun x * du x +
    iteratedPartialDeriv (n := n) [i] hΩ.interiorCutoff.toFun x * u.toFun x

omit [Fact (1 ≤ p)] in
/-- The derivative candidate is supported in the interior support set. -/
theorem support_interiorCutoffDerivativeRepresentative_subset
    (u : SobolevSpaceOn n 1 p Ω)
    (i : Fin n) (du : ℝ^n → ℝ) :
    Function.support
        (interiorCutoffDerivativeRepresentative
          (n := n) (p := p) (Ω := Ω) u i du) ⊆
      Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupport (n := n) (Ω := Ω) := by
  intro x hx
  by_contra hxK
  have hψ : hΩ.interiorCutoff.toFun x = 0 := by
    by_contra hne
    exact hxK (subset_tsupport hΩ.interiorCutoff.toFun hne)
  have hdψ : iteratedPartialDeriv (n := n) [i] hΩ.interiorCutoff.toFun x = 0 := by
    by_contra hne
    have hxTs : x ∈ tsupport (iteratedPartialDeriv (n := n) [i] hΩ.interiorCutoff.toFun) :=
      subset_tsupport _ hne
    exact hxK
      (tsupport_iteratedPartialDeriv_subset_tsupport
        (n := n) ([i] : List (Fin n)) hΩ.interiorCutoff.toFun hxTs)
  apply hx
  change hΩ.interiorCutoff.toFun x * du x +
    iteratedPartialDeriv (n := n) [i] hΩ.interiorCutoff.toFun x * u.toFun x = 0
  rw [hψ, hdψ]
  simp

omit [Fact (1 ≤ p)] in
/-- The derivative candidate lies in `Lp` on `Ω` whenever the weak derivative of `u` does. -/
theorem memLp_interiorCutoffDerivativeRepresentative
    (u : SobolevSpaceOn n 1 p Ω) (i : Fin n)
    {du : ℝ^n → ℝ} (hduLp : MeasureTheory.MemLp du p (domainMeasure n Ω)) :
    MeasureTheory.MemLp
      (interiorCutoffDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) u i du) p
      (domainMeasure n Ω) := by
  have hψTop : MeasureTheory.MemLp hΩ.interiorCutoff.toFun (⊤ : ℝ≥0∞) (domainMeasure n Ω) :=
    hΩ.interiorCutoff.contDiff.continuous.memLp_top_of_hasCompactSupport
      hΩ.interiorCutoff.hasCompactSupport (domainMeasure n Ω)
  let dψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) hΩ.interiorCutoff
  have hdψTop : MeasureTheory.MemLp dψ.toFun (⊤ : ℝ≥0∞) (domainMeasure n Ω) :=
    dψ.contDiff.continuous.memLp_top_of_hasCompactSupport dψ.hasCompactSupport
      (domainMeasure n Ω)
  have hdψEq : dψ.toFun = fun x ↦ iteratedPartialDeriv (n := n) [i] hΩ.interiorCutoff.toFun x := by
    funext x
    change (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) hΩ.interiorCutoff :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
      iteratedPartialDeriv (n := n) [i] hΩ.interiorCutoff.toFun x
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [(hΩ.interiorCutoff.contDiff.differentiable
      (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  have hfirst : MeasureTheory.MemLp (fun x ↦ hΩ.interiorCutoff.toFun x * du x) p
      (domainMeasure n Ω) := by
    exact hψTop.fun_mul hduLp
  have hsecond : MeasureTheory.MemLp
      (fun x ↦ iteratedPartialDeriv (n := n) [i] hΩ.interiorCutoff.toFun x * u.toFun x) p
      (domainMeasure n Ω) := by
    have hdψTop' : MeasureTheory.MemLp
        (fun x ↦ iteratedPartialDeriv (n := n) [i] hΩ.interiorCutoff.toFun x)
        (⊤ : ℝ≥0∞) (domainMeasure n Ω) := by
      simpa only [← hdψEq] using hdψTop
    exact hdψTop'.fun_mul u.memLp
  exact hfirst.add hsecond

/-- The interior partition component is a global `W^{1,p}(ℝ^n)` function. -/
noncomputable def extension (u : SobolevSpaceOn n 1 p Ω) :
    _root_.SobolevSpace.GlobalSobolevSpace n 1 p := by
  classical
  refine
    { toFun := interiorCutoffRepresentative (n := n) (p := p) (Ω := Ω) u
      memLp := memLp_interiorCutoffRepresentative
        (n := n) (p := p) (Ω := Ω) u
      weak_derivs_inLp := ?_ }
  intro α hα
  have hshape : α = [] ∨ ∃ i : Fin n, α = [i] := by
    cases α with
    | nil => exact Or.inl rfl
    | cons i rest =>
        cases rest with
        | nil => exact Or.inr ⟨i, rfl⟩
        | cons j tail => simp at hα
  rcases hshape with rfl | ⟨i, rfl⟩
  · -- Zeroth weak derivative: the function is its own order-zero derivative.
    refine ⟨interiorCutoffRepresentative (n := n) (p := p) (Ω := Ω) u,
      memLp_interiorCutoffRepresentative
        (n := n) (p := p) (Ω := Ω) u, ?_⟩
    have hloc : MeasureTheory.LocallyIntegrableOn
        (interiorCutoffRepresentative (n := n) (p := p) (Ω := Ω) u) Set.univ
        (MeasureTheory.volume : Measure (ℝ^n)) :=
      memLp_locallyIntegrableOn_domain
        (n := n) (Ω := (Set.univ : Set (ℝ^n)))
        (memLp_interiorCutoffRepresentative
          (n := n) (p := p) (Ω := Ω) u)
        (Fact.out : (1 : ℝ≥0∞) ≤ p)
    exact hasWeakDerivativeOn_nil hloc
  · -- First derivatives use the product rule on `Ω`, followed by compact-support localization.
    rcases u.weak_derivs_inLp [i] (by simp) with ⟨du, hduLp, hduWeak⟩
    let g := interiorCutoffDerivativeRepresentative
      (n := n) (p := p) (Ω := Ω) u i du
    have hgLpOn : MeasureTheory.MemLp g p (domainMeasure n Ω) :=
      memLp_interiorCutoffDerivativeRepresentative
        (n := n) (p := p) (Ω := Ω) u i hduLp
    have hweakOn : HasWeakDerivativeOn (n := n) Ω [i]
        (interiorCutoffRepresentative (n := n) (p := p) (Ω := Ω) u) g := by
      change HasWeakDerivativeOn (n := n) Ω [i]
        (fun x ↦ hΩ.interiorCutoff.toFun x * u.toFun x)
        (fun x ↦ hΩ.interiorCutoff.toFun x * du x +
          iteratedPartialDeriv (n := n) [i] hΩ.interiorCutoff.toFun x * u.toFun x)
      exact hasWeakDerivativeOn_mul_testFunction_first
        (n := n) (p := p) (Ω := Ω) (i := i)
        u.memLp hduLp hduWeak hΩ.interiorCutoff
    have hgLpUniv : MeasureTheory.MemLp g p
        (domainMeasure n (Set.univ : Set (ℝ^n))) :=
      memLp_of_support_subset_of_subset (n := n) (p := p) (U := Ω)
        (Ωbig := (Set.univ : Set (ℝ^n))) hΩ.isOpen.measurableSet (subset_univ _)
        ((support_interiorCutoffDerivativeRepresentative_subset
            (n := n) (p := p) (Ω := Ω) u i du).trans
          (Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupport_subset_domain
            (n := n) (Ω := Ω))) hgLpOn
    refine ⟨g, hgLpUniv, ?_⟩
    exact
      hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds
        (n := n) (U := Ω)
        (K := Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupport (n := n) (Ω := Ω)) hΩ.isOpen
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupport_subset_domain (n := n) (Ω := Ω))
        (support_interiorCutoffRepresentative_subset
          (n := n) (p := p) (Ω := Ω) u)
        (support_interiorCutoffDerivativeRepresentative_subset
          (n := n) (p := p) (Ω := Ω) u i du)
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupportCutoff (n := n) (Ω := Ω))
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.tsupport_interiorSupportCutoff_subset_domain
          (n := n) (Ω := Ω))
        (interiorSupportCutoff_eq_one_nhds_on_interiorSupport
          (n := n) (Ω := Ω)) hweakOn

/-- On `Ω`, the global interior component evaluates to the expected partition term `ψ₀u`. -/
@[simp] theorem extension_apply (u : SobolevSpaceOn n 1 p Ω) (x : ℝ^n) :
    (extension (n := n) (p := p) (Ω := Ω) u).toFun x = hΩ.interiorCutoff.toFun x * u.toFun x :=
  rfl

end InteriorPiece

end C1

end Extension

end SobolevSpace
