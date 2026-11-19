/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TestFunctions
public import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Odd reflection of `H¹₀` from the upper half-space

An odd reflection of an arbitrary `H¹` function can acquire a boundary
measure. The construction below is therefore for `H¹₀(ℝ^n₊)`. At
first order the parity forced by the chain rule is:

* the function itself and every tangential derivative are reflected oddly;
* the normal derivative is reflected evenly.

The density argument in `oddExtendAmbient_mem_globalH1` proves that this
coordinate bundle is a global `H¹` element for zero-trace data.

The argument is the usual one for reflection across a flat boundary: on a
smooth function compactly supported in the open half-space, the odd
reflection is again smooth with compact support and the weak derivative
identities hold literally, with the stated parities; the identities then
pass to `H¹₀(ℝ^n₊)` because the reflection is bounded and the smooth
functions are dense. Even reflection (Brezis, Functional Analysis, Sobolev
Spaces and PDE, Chapter 9) and the higher-order reflection of the extension
theorem (Evans, PDE, §5.4) extend all of `W^{1,p}` from a half-space; odd
reflection needs zero trace because the reflected function must not jump
across the hyperplane.

## Main results

* `oddExtendLpAt`, `oddExtendAmbient`: the parity-selected reflections on each coordinate of
  the first-order derivative bundle and the resulting map on ambient bundles.
* `oddExtendAmbient_mem_globalH1`: for `u ∈ H¹₀(ℝ^n₊)` the reflected bundle satisfies all
  weak derivative identities on `ℝ^n`.
* `oddExtendH10`: the odd reflection `H¹₀(ℝ^n₊) → H¹(ℝ^n)` as a bounded operator, with
  `oddExtendH10_coordinate` and `oddExtendH10_base_apply_ae` describing its coordinates.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, and the higher-order reflection
  (3) of its proof, p. 269.
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for extension by reflection across a flat boundary.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

open PDE (partialDeriv iteratedPartialDeriv)

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace
namespace GraphSpace
namespace ZeroTraceOdd

open Set MeasureTheory Function
open scoped ENNReal Topology Sobolev

variable (n : ℕ) [Fact (0 < n)]


/-- The reflection chosen for one coordinate of the first-order derivative
bundle of an oddly reflected function. -/
noncomputable def oddExtendLpAt (a : DerivIndex n 1) :
    DerivLp n 2 ℝ^n₊ →L[ℝ] DerivLp n 2 Set.univ :=
  firstOrderRows
    (_root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := 2))
    (fun i ↦
      if i = PDE.Common.lastIndex (n := n) then
        _root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := 2)
      else
        _root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := 2))
    a

/-- The parity-correct odd-reflection map on ambient first-order Sobolev
bundles.  Its restriction to `H¹₀(ℝ^n₊)` will land in global `H¹`. -/
noncomputable def oddExtendAmbient :
    WkpAmbientOn n 1 2 ℝ^n₊ →L[ℝ] WkpAmbientOn n 1 2 Set.univ := by
  classical
  let eUpper := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 ℝ^n₊)
  let eUniv := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n 1 ↦ DerivLp n 2 Set.univ)
  exact eUniv.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a ↦
        (oddExtendLpAt (n := n) a).comp
          (ContinuousLinearMap.proj a)).comp
      eUpper.toContinuousLinearMap)

/-- Ambient odd extension acts coordinatewise with the parity selected by the derivative index. -/
@[simp] theorem oddExtendAmbient_apply
    (U : WkpAmbientOn n 1 2 ℝ^n₊) (a : DerivIndex n 1) :
    oddExtendAmbient (n := n) U a = oddExtendLpAt (n := n) a (U a) := by
  classical
  simp [oddExtendAmbient, oddExtendLpAt]

/-- A test function supported in the upper half-space is its own indicator there, and its
reflection is its own indicator on the lower half-space. -/
private theorem indicator_upper_and_lower_reflect
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ ℝ^n₊) :
    ℝ^n₊.indicator φ.toFun = φ.toFun ∧
      (_root_.SobolevSpace.HalfSpace.lower n).indicator
          (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) =
        fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y) :=
  ⟨Set.indicator_eq_self.2 ((subset_tsupport _).trans hφ), Set.indicator_eq_self.2 fun y hy ↦
    (_root_.SobolevSpace.HalfSpace.mem_upper_reflect_iff n y).1 (hφ (subset_tsupport _ hy))⟩

private theorem indicator_odd_eq_oddPartTestFunction
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ ℝ^n₊) (x : ℝ^n) :
    ℝ^n₊.indicator φ.toFun x -
        (_root_.SobolevSpace.HalfSpace.lower n).indicator
          (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) x =
      (Extension.GraphSpace.HalfSpace.oddPartTestFunction (n := n) φ).toFun x := by
  rw [Extension.GraphSpace.HalfSpace.oddPartTestFunction_toFun,
    (indicator_upper_and_lower_reflect (n := n) φ hφ).1,
    (indicator_upper_and_lower_reflect (n := n) φ hφ).2]

private theorem indicator_even_eq_evenPartTestFunction
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ ℝ^n₊) (x : ℝ^n) :
    ℝ^n₊.indicator φ.toFun x +
        (_root_.SobolevSpace.HalfSpace.lower n).indicator
          (fun y ↦ φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)) x =
      (Extension.GraphSpace.HalfSpace.evenPartTestFunction (n := n) φ).toFun x := by
  rw [Extension.GraphSpace.HalfSpace.evenPartTestFunction_toFun,
    (indicator_upper_and_lower_reflect (n := n) φ hφ).1,
    (indicator_upper_and_lower_reflect (n := n) φ hφ).2]

/-- An a.e. identity on the upper half-space holds a.e. at its points and, after reflection,
a.e. at the points of the lower half-space. -/
private theorem ae_eq_on_upper_and_reflect
    (u : DerivLp n 2 ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hu : (u : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₊] φ.toFun) :
    ∀ᵐ x ∂(MeasureTheory.volume : Measure (ℝ^n)),
      (x ∈ ℝ^n₊ → (u : ℝ^n → ℝ) x = φ.toFun x) ∧
        (x ∈ _root_.SobolevSpace.HalfSpace.lower n →
          (u : ℝ^n → ℝ) (_root_.SobolevSpace.HalfSpace.reflect n x) =
            φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n x)) := by
  have hreflect :=
    (_root_.SobolevSpace.HalfSpace.measurePreserving_reflect_restrict_lower
      (n := n)).quasiMeasurePreserving.ae_eq_comp hu
  filter_upwards [(MeasureTheory.ae_restrict_iff'
      (_root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n))).1 hu,
    (MeasureTheory.ae_restrict_iff'
      (_root_.SobolevSpace.HalfSpace.isOpen_lower (n := n)).measurableSet).1 hreflect]
    with x h₁ h₂ using ⟨h₁, h₂⟩

/-- Odd `L²` reflection agrees a.e. with smooth odd reflection whenever the
input representative agrees with a test function on the upper half-space. -/
theorem oddExtendLp_apply_ae_of_test_representative
    (u : DerivLp n 2 ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hφ : tsupport φ.toFun ⊆ ℝ^n₊)
    (hu : (u : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₊] φ.toFun) :
    (((_root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := 2) u :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
      (Extension.GraphSpace.HalfSpace.oddPartTestFunction (n := n) φ).toFun := by
  filter_upwards [_root_.SobolevSpace.HalfSpace.oddExtendLp_apply_ae (n := n) (p := 2) u,
    ae_eq_on_upper_and_reflect (n := n) u φ hu] with x hextx ⟨hux, hrefx⟩
  rw [hextx, ← indicator_odd_eq_oddPartTestFunction (n := n) φ hφ x]
  by_cases hxU : x ∈ ℝ^n₊ <;> by_cases hxL : x ∈ _root_.SobolevSpace.HalfSpace.lower n <;>
    simp [hxU, hxL, hux, hrefx]

/-- Even `L²` reflection agrees a.e. with smooth even reflection under the
same representative and support hypotheses. -/
theorem evenExtendLp_apply_ae_of_test_representative
    (u : DerivLp n 2 ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hφ : tsupport φ.toFun ⊆ ℝ^n₊)
    (hu : (u : ℝ^n → ℝ) =ᵐ[domainMeasure n ℝ^n₊] φ.toFun) :
    (((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := 2) u :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
      (Extension.GraphSpace.HalfSpace.evenPartTestFunction (n := n) φ).toFun := by
  filter_upwards [_root_.SobolevSpace.HalfSpace.evenExtendLp_apply_ae (n := n) (p := 2) u,
    ae_eq_on_upper_and_reflect (n := n) u φ hu] with x hextx ⟨hux, hrefx⟩
  rw [hextx, ← indicator_even_eq_evenPartTestFunction (n := n) φ hφ x]
  by_cases hxU : x ∈ ℝ^n₊ <;> by_cases hxL : x ∈ _root_.SobolevSpace.HalfSpace.lower n <;>
    simp [hxU, hxL, hux, hrefx]

omit [Fact (0 < n)] in
/-- The line derivative of a test function along `e_i` is its `i`-th partial derivative. -/
private theorem lineDerivCLM_single_apply (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) (x : ℝ^n) :
    (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x = (∂[i] φ.toFun) x := by
  rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp),
    (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  rfl

/-- On the smooth core of `H¹₀(ℝ^n₊)`, the coordinatewise parity bundle is
exactly the global smooth odd reflection. -/
private theorem oddExtendAmbient_testFunction_eq
    (φΩ : TestFunctionOn n ℝ^n₊) :
    oddExtendAmbient (n := n)
        (testFunctionToH1 (n := n) (Ω := ℝ^n₊) φΩ :
            WkpAmbientOn n 1 2 ℝ^n₊) =
      (testFunctionToH1 (n := n) (Ω := Set.univ)
        (⟨Extension.GraphSpace.HalfSpace.oddPartTestFunction (n := n) φΩ.1, subset_univ _⟩ :
          TestFunctionOn n Set.univ) : WkpAmbientOn n 1 2 Set.univ) := by
  classical
  apply PiLp.ext
  intro a
  apply MeasureTheory.Lp.ext
  let hUpper := _root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n)
  let ψodd := Extension.GraphSpace.HalfSpace.oddPartTestFunction (n := n) φΩ.1
  have hlocal :=
    mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := ℝ^n₊)
      φΩ.1.toFun φΩ.1.contDiff φΩ.1.hasCompactSupport (a := a)
  have hglobal :=
    mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2)
      (Ω := (Set.univ : Set (ℝ^n)))
      ψodd.toFun ψodd.contDiff ψodd.hasCompactSupport (a := a)
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hlocalBase :
        (((testFunctionToH1 (n := n) (Ω := ℝ^n₊) φΩ :
            WkpAmbientOn n 1 2 ℝ^n₊) (baseIndex n 1) :
              DerivLp n 2 ℝ^n₊) : ℝ^n → ℝ)
          =ᵐ[domainMeasure n ℝ^n₊] φΩ.1.toFun := by
      simpa [testFunctionToH1, iteratedPartialDeriv] using hlocal
    have hreflected := oddExtendLp_apply_ae_of_test_representative
      (n := n)
      (((testFunctionToH1 (n := n) (Ω := ℝ^n₊) φΩ :
        WkpAmbientOn n 1 2 ℝ^n₊) (baseIndex n 1))) φΩ.1 φΩ.2 hlocalBase
    have hglobalBase :
        ((((testFunctionToH1 (n := n) (Ω := Set.univ)
            (⟨ψodd, subset_univ _⟩ : TestFunctionOn n Set.univ) :
              WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
                DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
                  ψodd.toFun := by
      simpa [testFunctionToH1, iteratedPartialDeriv, domainMeasure] using hglobal
    simpa [oddExtendAmbient_apply, oddExtendLpAt, ψodd, domainMeasure] using
      hreflected.trans hglobalBase.symm
  · subst a
    let ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
      _root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φΩ.1
    have hψ : ψ.toFun = fun x ↦ (∂[i] φΩ.1.toFun) x :=
      funext (lineDerivCLM_single_apply (n := n) φΩ.1 i)
    have hψsupport : tsupport ψ.toFun ⊆ ℝ^n₊ := by
      rw [hψ]
      simpa [partialDeriv] using (tsupport_fderiv_apply_subset ℝ
        (EuclideanSpace.single i (1 : ℝ)) (f := φΩ.1.toFun)).trans φΩ.2
    have hlocalDeriv :
        (((testFunctionToH1 (n := n) (Ω := ℝ^n₊) φΩ :
            WkpAmbientOn n 1 2 ℝ^n₊) (singleDerivIndex n i) :
              DerivLp n 2 ℝ^n₊) : ℝ^n → ℝ)
          =ᵐ[domainMeasure n ℝ^n₊] ψ.toFun := by
      rw [hψ]
      simpa [testFunctionToH1, iteratedPartialDeriv] using hlocal
    have hglobalDeriv :
        ((((testFunctionToH1 (n := n) (Ω := Set.univ)
            (⟨ψodd, subset_univ _⟩ : TestFunctionOn n Set.univ) :
              WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i) :
                DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
          fun x ↦ (∂[i] ψodd.toFun) x := by
      simpa [testFunctionToH1, iteratedPartialDeriv, domainMeasure] using hglobal
    by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst hi
      -- the normal derivative of the odd part is the even part of the normal derivative
      have hparity (x : ℝ^n) : (∂[PDE.Common.lastIndex (n := n)] ψodd.toFun) x =
          (Extension.GraphSpace.HalfSpace.evenPartTestFunction (n := n) ψ).toFun x :=
        (lineDerivCLM_single_apply (n := n) ψodd _ x).symm.trans
          (Extension.GraphSpace.HalfSpace.lineDerivCLM_oddPartTestFunction_last (n := n) φΩ.1 x)
      simpa [oddExtendAmbient_apply, oddExtendLpAt, domainMeasure] using
        (evenExtendLp_apply_ae_of_test_representative (n := n) _ ψ hψsupport hlocalDeriv).trans
          (hglobalDeriv.trans (.of_forall hparity)).symm
    · -- a tangential derivative of the odd part is the odd part of the derivative
      have hparity (x : ℝ^n) : (∂[i] ψodd.toFun) x =
          (Extension.GraphSpace.HalfSpace.oddPartTestFunction (n := n) ψ).toFun x :=
        (lineDerivCLM_single_apply (n := n) ψodd i x).symm.trans
          (Extension.GraphSpace.HalfSpace.lineDerivCLM_oddPartTestFunction_of_ne_last
            (n := n) i hi φΩ.1 x)
      simpa [oddExtendAmbient_apply, oddExtendLpAt, hi, domainMeasure] using
        (oddExtendLp_apply_ae_of_test_representative (n := n) _ ψ hψsupport hlocalDeriv).trans
          (hglobalDeriv.trans (.of_forall hparity)).symm

/-- The parity-correct odd-reflection bundle of every upper-half-space
`H¹₀` function satisfies all global weak first-derivative identities. -/
theorem oddExtendAmbient_mem_globalH1
    (u : H¹₀(ℝ^n₊)) :
    oddExtendAmbient (n := n)
        ((u : H¹(ℝ^n₊)) : WkpAmbientOn n 1 2 ℝ^n₊) ∈
      (wkpSubmoduleOn n 1 2 (Set.univ : Set (ℝ^n)) :
        Submodule ℝ (WkpAmbientOn n 1 2 Set.univ)) := by
  let hUpper := _root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n)
  let A : H¹(ℝ^n₊) →L[ℝ] WkpAmbientOn n 1 2 Set.univ :=
    (oddExtendAmbient (n := n)).comp
      (Submodule.subtypeL (wkpSubmoduleOn n 1 2 ℝ^n₊))
  let S : Set (H¹(ℝ^n₊)) :=
    A ⁻¹' (wkpSubmoduleOn n 1 2 (Set.univ : Set (ℝ^n)) :
      Set (WkpAmbientOn n 1 2 Set.univ))
  have hSclosed : IsClosed S :=
    (isClosed_WkpSubmoduleOn n 1 2 (Set.univ : Set (ℝ^n))).preimage A.continuous
  have hCc :
      ((ccSmoothSubmoduleOn (n := n) (Ω := ℝ^n₊) :
        Submodule ℝ (H¹(ℝ^n₊))) : Set (H¹(ℝ^n₊))) ⊆ S := by
    intro v hv
    rcases hv with ⟨φΩ, rfl⟩
    change oddExtendAmbient (n := n)
        (testFunctionToH1 (n := n) (Ω := ℝ^n₊) φΩ :
          WkpAmbientOn n 1 2 ℝ^n₊) ∈
      (wkpSubmoduleOn n 1 2 (Set.univ : Set (ℝ^n)) :
        Submodule ℝ (WkpAmbientOn n 1 2 Set.univ))
    rw [oddExtendAmbient_testFunction_eq (n := n) φΩ]
    exact (testFunctionToH1 (n := n) (Ω := Set.univ)
      (⟨Extension.GraphSpace.HalfSpace.oddPartTestFunction (n := n) φΩ.1, subset_univ _⟩ :
        TestFunctionOn n Set.univ)).property
  exact H10SpaceOn.closed_property_of_CcSmooth
    (n := n) (Ω := ℝ^n₊) hSclosed hCc u

/-- Continuous odd reflection from upper-half-space `H¹₀` into global
`H¹(ℝ^n)`.  The codomain is the global Sobolev subspace, not a
certificate type. -/
noncomputable def oddExtendH10 :
    H¹₀(ℝ^n₊) →L[ℝ]
      H¹(ℝ^n) :=
  ContinuousLinearMap.codRestrict
    ((oddExtendAmbient (n := n)).comp
      ((Submodule.subtypeL (wkpSubmoduleOn n 1 2 ℝ^n₊)).comp
        (Submodule.subtypeL
          ((h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule))))
    (wkpSubmoduleOn n 1 2 (Set.univ : Set (ℝ^n)))
    (fun u ↦ oddExtendAmbient_mem_globalH1 (n := n) u)

/-- The ambient bundle of the odd `H¹₀` extension uses the chosen parity in each coordinate. -/
@[simp] theorem oddExtendH10_apply_coe
    (u : H¹₀(ℝ^n₊)) :
    ((oddExtendH10 (n := n) u : H¹(ℝ^n)) :
        WkpAmbientOn n 1 2 Set.univ) =
      oddExtendAmbient (n := n)
        ((u : H¹(ℝ^n₊)) : WkpAmbientOn n 1 2 ℝ^n₊) :=
  rfl

/-- Every coordinate of `oddExtendH10` is the parity-selected scalar
reflection of the corresponding upper-half-space coordinate. -/
theorem oddExtendH10_coordinate
    (u : H¹₀(ℝ^n₊))
    (a : DerivIndex n 1) :
    (((oddExtendH10 (n := n) u : H¹(ℝ^n)) :
        WkpAmbientOn n 1 2 Set.univ) a) =
      oddExtendLpAt (n := n) a
        (((u : H¹(ℝ^n₊)) : WkpAmbientOn n 1 2 ℝ^n₊) a) := by
  rw [oddExtendH10_apply_coe, oddExtendAmbient_apply]

/-- The base coordinate is represented by the literal odd reflection: the
upper representative on `ℝ^n₊`, minus its reflected representative on the
lower half-space. -/
theorem oddExtendH10_base_apply_ae
    (u : H¹₀(ℝ^n₊)) :
    (((((oddExtendH10 (n := n) u : H¹(ℝ^n)) :
        WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
          DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
      fun x ↦ ℝ^n₊.indicator
          (fun y ↦ ((((u : H¹(ℝ^n₊)) :
            WkpAmbientOn n 1 2 ℝ^n₊) (baseIndex n 1) :
              DerivLp n 2 ℝ^n₊) : ℝ^n → ℝ) y) x -
        (_root_.SobolevSpace.HalfSpace.lower n).indicator
          (fun y ↦ ((((u : H¹(ℝ^n₊)) :
            WkpAmbientOn n 1 2 ℝ^n₊) (baseIndex n 1) :
              DerivLp n 2 ℝ^n₊) : ℝ^n → ℝ)
                (_root_.SobolevSpace.HalfSpace.reflect n y)) x := by
  rw [oddExtendH10_coordinate]
  simpa [oddExtendLpAt] using
    (_root_.SobolevSpace.HalfSpace.oddExtendLp_apply_ae
      (n := n) (p := (2 : ℝ≥0∞))
      ((((u : H¹(ℝ^n₊)) : WkpAmbientOn n 1 2 ℝ^n₊)
        (baseIndex n 1))))

end ZeroTraceOdd
end GraphSpace
end SobolevSpace
