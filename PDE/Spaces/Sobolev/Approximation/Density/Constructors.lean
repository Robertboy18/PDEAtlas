/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability
public import PDE.Spaces.Sobolev.Approximation.Density.ClassicalDerivatives -- shake: keep

/-!
# Sobolev graph-space constructors

The Sobolev space `WkpSpaceOn n k p Ω` is modelled as a graph space: an element is a family of
`Lᵖ(Ω)` functions indexed by multi-indices `a : DerivIndex n k` of order at most `k`, in
which the row indexed by `a` is the weak derivative `D^a` of the base row (Evans, PDE, §5.2.2).
For finite `p` the norm is the `ℓᵖ` sum of the row norms, `(∑ₐ ‖D^a u‖ₚᵖ)^(1/p)`, which is
Evans's norm on `W^{k,p}(Ω)`. Each constructor builds such an element from ordinary
functions, together with lemmas describing each of its rows almost everywhere.

The smooth constructors fill every row with a classical iterated partial derivative and use
`hasWeakDerivativeOn_iteratedPartialDeriv` (or its finite-regularity version) to verify the
weak derivative identities. The general constructor `mkWkpSpaceOnOfWeakDerivatives` instead
takes an arbitrary family of `Lᵖ` representatives together with proofs that they are weak
derivatives; it imposes no continuity, which is what gluing arguments and extension domains
need. Global test functions embed linearly.

## Main declarations

* `mkWkpSpaceOnOfContDiff`: a `C^∞` compactly supported function on `ℝ^n` as an element of
  `W^{k,p}(Ω)`.
* `mkWkpSpaceOnOfContDiffMemLp`, `mkWkpSpaceOnOfContDiffMemLpFinite`: the same for a `C^∞`
  (respectively `C^k`) function without compact support, given `Lᵖ` membership of the
  classical derivatives through order `k`.
* `mkWkpSpaceOnOfWeakDerivatives`: an element from explicit `Lᵖ` rows and weak-derivative
  identities; `norm_sq_mkWkpSpaceOnOfWeakDerivatives` computes its squared `W^{k,2}` norm as
  the sum of the squared `L²` row norms.
* `*_apply_ae`: each constructor's rows agree almost everywhere on `Ω` with the supplied or
  classical derivatives.
* `norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal`: a row norm is the `Lᵖ` norm of
  the corresponding classical derivative.
* `wkpConstant`: a constant function as an element of `W^{1,p}(Ω)` on a finite-measure domain,
  with base row `c` (`wkpConstant_base_ae`) and zero derivative rows
  (`wkpConstant_deriv_eq_zero`, `wkpConstant_deriv_ae`).
* `globalTestFunctionToWkpOn`, `globalTestFunctionToWkpOnLinear`: the linear embedding of
  `C_c^∞(ℝ^n)` into `W^{k,p}(Ω)`; `mkWkpSpaceOnOfContDiff_sub` is the corresponding
  compatibility with subtraction.

## Implementation notes

`Ω` is an arbitrary set and `domainMeasure n Ω` is Lebesgue measure restricted to it; no
regularity of `Ω` is needed to build elements, only to prove density statements about them.
Rows are `Lᵖ` classes, so all identifications are almost-everywhere statements, and the
constructors are compared through `MeasureTheory.Lp.ext` after `filter_upwards` over the
`_apply_ae` lemmas.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, pp. 258-259, for the definition of `W^{k,p}(U)` and
  its norm.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace GraphSpace

section Constructors

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- The `Lᵖ` class, for the domain measure, of a continuous compactly supported function. -/
noncomputable def toLpOfContCompact
    (f : ℝ^n → ℝ) (hf : Continuous f) (hcs : HasCompactSupport f) :
    MeasureTheory.Lp ℝ p (domainMeasure n Ω) :=
  (hf.memLp_of_hasCompactSupport (μ := domainMeasure n Ω) (p := p) hcs).toLp f

/-- The `Lᵖ` class of a continuous compactly supported function is represented almost
everywhere by that function. -/
theorem toLpOfContCompact_coeFn
    {f : ℝ^n → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    (toLpOfContCompact (n := n) (p := p) (Ω := Ω) f hf hcs : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f :=
  (hf.memLp_of_hasCompactSupport (μ := domainMeasure n Ω) (p := p) hcs).coeFn_toLp

/-- Build an element of the Sobolev graph space `W^{k,p}(Ω)` from a smooth, compactly
supported function on `ℝ^n`, using classical (iterated) partial derivatives as the chosen weak
derivatives. -/
noncomputable def mkWkpSpaceOnOfContDiff
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) : W^{k,p}(Ω) :=
  let U : WkpAmbientOn n k p Ω :=
    WithLp.toLp p (fun a ↦
      toLpOfContCompact (n := n) (p := p) (Ω := Ω)
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
        (PDE.contDiff_top_iteratedPartialDeriv (n := n) (f := f) hf a.toList).continuous
        (hasCompactSupport_iteratedPartialDeriv (n := n) (f := f) hcs a.toList))
  ⟨U, by
    intro a
    -- Use AE equivalence between `U` components and the classical derivatives.
    have hbase_ae :
        (U (baseIndex n k) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f := by
      simpa [U, baseIndex_toList, iteratedPartialDeriv] using
        toLpOfContCompact_coeFn (n := n) (p := p) (Ω := Ω) (f := f) hf.continuous hcs
    have ha_ae :
        (U a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
          fun x ↦ iteratedPartialDeriv (n := n) a.toList f x := by
      simpa [U] using
        toLpOfContCompact_coeFn (n := n) (p := p) (Ω := Ω)
          (f := fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
          (PDE.contDiff_top_iteratedPartialDeriv (n := n) (f := f) hf a.toList).continuous
          (hasCompactSupport_iteratedPartialDeriv (n := n) (f := f) hcs a.toList)
    have hweak :
        HasWeakDerivativeOn (n := n) Ω a.toList f
          (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x) :=
      hasWeakDerivativeOn_iteratedPartialDeriv (n := n) (Ω := Ω) (f := f) hf a.toList
    exact ((hasWeakDerivativeOn_congr_ae (n := n) (Ω := Ω) (α := a.toList)
      (f := (U (baseIndex n k) : ℝ^n → ℝ)) (g := f)
      (f' := (U a : ℝ^n → ℝ))
      (g' := fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
      hbase_ae ha_ae).2 hweak)⟩

/-- Build a Sobolev graph-space `W^{k,p}(Ω)` element from a globally smooth
function when `Lᵖ` membership is supplied for every classical derivative up to
order `k`.  Compact support is not required. -/
noncomputable def mkWkpSpaceOnOfContDiffMemLp
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ a : DerivIndex n k,
      MeasureTheory.MemLp
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
        p (domainMeasure n Ω)) : W^{k,p}(Ω) :=
  let U : WkpAmbientOn n k p Ω :=
    WithLp.toLp p (fun a ↦ (hmem a).toLp
      (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x))
  ⟨U, by
    intro a
    have hbase_ae :
        (U (baseIndex n k) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f := by
      simpa [U, baseIndex_toList, iteratedPartialDeriv] using
        (hmem (baseIndex n k)).coeFn_toLp
    have ha_ae :
        (U a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
          fun x ↦ iteratedPartialDeriv (n := n) a.toList f x := by
      simpa [U] using (hmem a).coeFn_toLp
    have hweak :
        HasWeakDerivativeOn (n := n) Ω a.toList f
          (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x) :=
      hasWeakDerivativeOn_iteratedPartialDeriv
        (n := n) (Ω := Ω) (f := f) hf a.toList
    exact ((hasWeakDerivativeOn_congr_ae (n := n) (Ω := Ω) (α := a.toList)
      (f := (U (baseIndex n k) : ℝ^n → ℝ)) (g := f)
      (f' := (U a : ℝ^n → ℝ))
      (g' := fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
      hbase_ae ha_ae).2 hweak)⟩

/-- Every coordinate of `mkWkpSpaceOnOfContDiffMemLp` agrees almost
everywhere with its classical iterated partial derivative. -/
theorem mkWkpSpaceOnOfContDiffMemLp_apply_ae
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ a : DerivIndex n k,
      MeasureTheory.MemLp
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
        p (domainMeasure n Ω)) (a : DerivIndex n k) :
    (((mkWkpSpaceOnOfContDiffMemLp
      (n := n) (k := k) (p := p) (Ω := Ω) f hf hmem :
        WkpAmbientOn n k p Ω) a : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
      fun x ↦ iteratedPartialDeriv (n := n) a.toList f x := by
  classical
  simpa [mkWkpSpaceOnOfContDiffMemLp] using (hmem a).coeFn_toLp

/-- Finite-regularity variant of `mkWkpSpaceOnOfContDiffMemLp`: constructing
`W^{k,p}` requires only `C^k` regularity together with `Lᵖ` membership of the
classical derivatives through order `k`. -/
noncomputable def mkWkpSpaceOnOfContDiffMemLpFinite
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ k f)
    (hmem : ∀ a : DerivIndex n k,
      MeasureTheory.MemLp
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
        p (domainMeasure n Ω)) : W^{k,p}(Ω) :=
  let U : WkpAmbientOn n k p Ω :=
    WithLp.toLp p (fun a ↦ (hmem a).toLp
      (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x))
  ⟨U, by
    intro a
    have hbase_ae :
        (U (baseIndex n k) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f := by
      simpa [U, baseIndex_toList, iteratedPartialDeriv] using
        (hmem (baseIndex n k)).coeFn_toLp
    have ha_ae :
        (U a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
          fun x ↦ iteratedPartialDeriv (n := n) a.toList f x := by
      simpa [U] using (hmem a).coeFn_toLp
    have hfa : ContDiff ℝ (a.toList.length : ℕ∞) f := by
      apply hf.of_le
      exact_mod_cast a.toList_length_le
    have hweak :
        HasWeakDerivativeOn (n := n) Ω a.toList f
          (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x) :=
      hasWeakDerivativeOn_iteratedPartialDeriv_finite
        (n := n) (Ω := Ω) a.toList hfa
    exact ((hasWeakDerivativeOn_congr_ae (n := n) (Ω := Ω) (α := a.toList)
      (f := (U (baseIndex n k) : ℝ^n → ℝ)) (g := f)
      (f' := (U a : ℝ^n → ℝ))
      (g' := fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
      hbase_ae ha_ae).2 hweak)⟩

/-- Coordinates of the finite-regularity constructor agree almost everywhere
with the supplied classical derivatives. -/
theorem mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ k f)
    (hmem : ∀ a : DerivIndex n k,
      MeasureTheory.MemLp
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
        p (domainMeasure n Ω)) (a : DerivIndex n k) :
    (((mkWkpSpaceOnOfContDiffMemLpFinite
      (n := n) (k := k) (p := p) (Ω := Ω) f hf hmem :
        WkpAmbientOn n k p Ω) a : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
      fun x ↦ iteratedPartialDeriv (n := n) a.toList f x := by
  classical
  simpa [mkWkpSpaceOnOfContDiffMemLpFinite] using (hmem a).coeFn_toLp

/-- An element of `W^{k,p}(Ω)` built from an explicit finite family of `L^p` rows and their
weak-derivative identities. Unlike the classical constructors, this one imposes no continuity
on the rows, as needed for weak derivatives obtained by gluing along an interface. -/
noncomputable def mkWkpSpaceOnOfWeakDerivatives
    (f : ℝ^n → ℝ) (d : DerivIndex n k → ℝ^n → ℝ)
    (hbase : d (baseIndex n k) = f)
    (hmem : ∀ a : DerivIndex n k,
      MeasureTheory.MemLp (d a) p (domainMeasure n Ω))
    (hweak : ∀ a : DerivIndex n k,
      HasWeakDerivativeOn (n := n) Ω a.toList f (d a)) :
    W^{k,p}(Ω) :=
  let U : WkpAmbientOn n k p Ω :=
    WithLp.toLp p (fun a ↦ (hmem a).toLp (d a))
  ⟨U, by
    intro a
    have hbaseAe :
        (U (baseIndex n k) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f := by
      simpa [U, hbase] using (hmem (baseIndex n k)).coeFn_toLp
    have haAe :
        (U a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] d a := by
      simpa [U] using (hmem a).coeFn_toLp
    exact ((hasWeakDerivativeOn_congr_ae (n := n) (Ω := Ω)
      (α := a.toList) (f := (U (baseIndex n k) : ℝ^n → ℝ)) (g := f)
      (f' := (U a : ℝ^n → ℝ)) (g' := d a) hbaseAe haAe).2 (hweak a))⟩

/-- Every coordinate of `mkWkpSpaceOnOfWeakDerivatives` agrees almost
everywhere with the supplied weak-derivative representative. -/
theorem mkWkpSpaceOnOfWeakDerivatives_apply_ae
    (f : ℝ^n → ℝ) (d : DerivIndex n k → ℝ^n → ℝ)
    (hbase : d (baseIndex n k) = f)
    (hmem : ∀ a : DerivIndex n k,
      MeasureTheory.MemLp (d a) p (domainMeasure n Ω))
    (hweak : ∀ a : DerivIndex n k,
      HasWeakDerivativeOn (n := n) Ω a.toList f (d a))
    (a : DerivIndex n k) :
    ((((mkWkpSpaceOnOfWeakDerivatives
      (n := n) (k := k) (p := p) (Ω := Ω) f d hbase hmem hweak :
        WkpAmbientOn n k p Ω) a : DerivLp n p Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω] d a := by
  classical
  simpa [mkWkpSpaceOnOfWeakDerivatives] using (hmem a).coeFn_toLp

/-- For `p = 2`, the squared norm of the explicit weak-row constructor is
exactly the finite sum of the squared `L²` row integrals. -/
theorem norm_sq_mkWkpSpaceOnOfWeakDerivatives
    (f : ℝ^n → ℝ) (d : DerivIndex n k → ℝ^n → ℝ)
    (hbase : d (baseIndex n k) = f)
    (hmem : ∀ a : DerivIndex n k,
      MeasureTheory.MemLp (d a) 2 (domainMeasure n Ω))
    (hweak : ∀ a : DerivIndex n k,
      HasWeakDerivativeOn (n := n) Ω a.toList f (d a)) :
    ‖mkWkpSpaceOnOfWeakDerivatives
        (n := n) (k := k) (p := (2 : ℝ≥0∞)) (Ω := Ω)
        f d hbase hmem hweak‖ ^ 2 =
      ∑ a : DerivIndex n k, ∫ x, (d a x) ^ 2 ∂domainMeasure n Ω := by
  let U := mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := k) (p := (2 : ℝ≥0∞)) (Ω := Ω)
    f d hbase hmem hweak
  have hcoord (a : DerivIndex n k) :
      ‖((U : WkpAmbientOn n k 2 Ω) a)‖ ^ 2 =
        ∫ x, (d a x) ^ 2 ∂domainMeasure n Ω := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    have hae := mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := k) (p := (2 : ℝ≥0∞)) (Ω := Ω)
      f d hbase hmem hweak a
    filter_upwards [hae] with x hx
    rw [hx]
    simp [pow_two]
  change ‖(U : WkpAmbientOn n k 2 Ω)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun a _ ↦ hcoord a

/-- Every coordinate of the compactly supported smooth constructor is represented almost
everywhere by the corresponding classical iterated partial derivative. -/
theorem mkWkpSpaceOnOfContDiff_apply_ae
    {Ω : Set (ℝ^n)} (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) (a : DerivIndex n k) :
    ((mkWkpSpaceOnOfContDiff
        (n := n) (k := k) (p := p) (Ω := Ω) (f := f) hf hcs :
        WkpAmbientOn n k p Ω) a : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ iteratedPartialDeriv (n := n) a.toList f x := by
  classical
  simpa [mkWkpSpaceOnOfContDiff] using
    (toLpOfContCompact_coeFn (n := n) (p := p) (Ω := Ω)
      (f := fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
      (hf := (PDE.contDiff_top_iteratedPartialDeriv (n := n) (f := f) hf a.toList).continuous)
      (hcs := hasCompactSupport_iteratedPartialDeriv (n := n) (f := f) hcs a.toList))

/-- The norm of a coordinate in the smooth Sobolev constructor is the
`Lᵖ` seminorm of the corresponding classical derivative. -/
theorem norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (a : DerivIndex n k) :
    ‖((mkWkpSpaceOnOfContDiff
        (n := n) (k := k) (p := p) (Ω := Ω) f hf hcs :
        WkpAmbientOn n k p Ω) a)‖ =
      (eLpNorm
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList f x)
        p (domainMeasure n Ω)).toReal := by
  rw [MeasureTheory.Lp.norm_def]
  congr 1
  exact eLpNorm_congr_ae
    (mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := k) (p := p) (Ω := Ω)
      f hf hcs a)

/-- A global smooth compactly supported test function, viewed canonically as
an element of `W^{k,p}(Ω)`. -/
noncomputable abbrev globalTestFunctionToWkpOn
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : W^{k,p}(Ω) :=
  mkWkpSpaceOnOfContDiff
    (n := n) (k := k) (p := p) (Ω := Ω)
    φ.toFun φ.contDiff φ.hasCompactSupport

/-- Each coordinate of the canonical global test-function embedding is the
corresponding classical derivative almost everywhere on `Ω`. -/
theorem globalTestFunctionToWkpOn_coordinate_ae
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (a : DerivIndex n k) :
    (((globalTestFunctionToWkpOn
        (n := n) (k := k) (p := p) (Ω := Ω) φ :
        WkpAmbientOn n k p Ω) a : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
      fun x ↦ iteratedPartialDeriv (n := n) a.toList φ.toFun x := by
  simpa [globalTestFunctionToWkpOn] using
    (mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := k) (p := p) (Ω := Ω)
      φ.toFun φ.contDiff φ.hasCompactSupport a)

/-- The embedding of global test functions into `W^{k,p}(Ω)` is additive. -/
theorem globalTestFunctionToWkpOn_add
    (φ ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    globalTestFunctionToWkpOn
        (n := n) (k := k) (p := p) (Ω := Ω) (φ + ψ) =
      globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) φ +
        globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) ψ := by
  classical
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  have hcoord :
      (((globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) φ +
        globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) ψ :
          W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) a) =
        (globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) φ :
          WkpAmbientOn n k p Ω) a +
        (globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) ψ :
          WkpAmbientOn n k p Ω) a := by
    rfl
  rw [hcoord]
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalTestFunctionToWkpOn_coordinate_ae
        (n := n) (k := k) (p := p) (Ω := Ω) (φ + ψ) a,
      globalTestFunctionToWkpOn_coordinate_ae
        (n := n) (k := k) (p := p) (Ω := Ω) φ a,
      globalTestFunctionToWkpOn_coordinate_ae
        (n := n) (k := k) (p := p) (Ω := Ω) ψ a,
      MeasureTheory.Lp.coeFn_add
        ((globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) φ :
          WkpAmbientOn n k p Ω) a)
        ((globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) ψ :
          WkpAmbientOn n k p Ω) a)] with x hadd hφ hψ hsum
  rw [hadd, hsum]
  simp only [Pi.add_apply]
  rw [hφ, hψ]
  exact congrFun
    (PDE.iteratedPartialDeriv_add_of_contDiff a.toList
      (φ.contDiff.of_le (by exact_mod_cast le_top))
      (ψ.contDiff.of_le (by exact_mod_cast le_top))) x

/-- The embedding of global test functions into `W^{k,p}(Ω)` commutes with real scalars. -/
theorem globalTestFunctionToWkpOn_smul
    (c : ℝ) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    globalTestFunctionToWkpOn
        (n := n) (k := k) (p := p) (Ω := Ω) (c • φ) =
      c • globalTestFunctionToWkpOn
        (n := n) (k := k) (p := p) (Ω := Ω) φ := by
  classical
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  have hcoord :
      (((c • globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) φ :
          W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) a) =
        c • (globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) φ :
          WkpAmbientOn n k p Ω) a := by
    rfl
  rw [hcoord]
  apply MeasureTheory.Lp.ext
  filter_upwards
    [globalTestFunctionToWkpOn_coordinate_ae
        (n := n) (k := k) (p := p) (Ω := Ω) (c • φ) a,
      globalTestFunctionToWkpOn_coordinate_ae
        (n := n) (k := k) (p := p) (Ω := Ω) φ a,
      MeasureTheory.Lp.coeFn_smul (p := p) (c := c)
        ((globalTestFunctionToWkpOn
          (n := n) (k := k) (p := p) (Ω := Ω) φ :
          WkpAmbientOn n k p Ω) a)] with x hsmul hφ hcoord
  rw [hsmul, hcoord]
  simp only [Pi.smul_apply]
  rw [hφ]
  exact congrFun
    (PDE.iteratedPartialDeriv_const_smul (n := n) c a.toList φ.toFun) x

/-- The canonical embedding of global test functions into `W^{k,p}(Ω)` is
linear. -/
noncomputable def globalTestFunctionToWkpOnLinear :
    𝓓((⊤ : Opens (ℝ^n)), ℝ) →ₗ[ℝ] W^{k,p}(Ω) where
  toFun := globalTestFunctionToWkpOn
    (n := n) (k := k) (p := p) (Ω := Ω)
  map_add' := globalTestFunctionToWkpOn_add
    (n := n) (k := k) (p := p) (Ω := Ω)
  map_smul' := globalTestFunctionToWkpOn_smul
    (n := n) (k := k) (p := p) (Ω := Ω)

/-- Packaging smooth compactly supported functions into a Sobolev graph
space commutes with subtraction. -/
theorem mkWkpSpaceOnOfContDiff_sub
    (f g : ℝ^n → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfcs : HasCompactSupport f)
    (hgcs : HasCompactSupport g) :
    mkWkpSpaceOnOfContDiff
        (n := n) (k := k) (p := p) (Ω := Ω)
        (f - g) (hf.sub hg) (hfcs.sub hgcs) =
      mkWkpSpaceOnOfContDiff
          (n := n) (k := k) (p := p) (Ω := Ω)
          f hf hfcs -
        mkWkpSpaceOnOfContDiff
          (n := n) (k := k) (p := p) (Ω := Ω)
          g hg hgcs := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  apply MeasureTheory.Lp.ext
  have hsub :=
    MeasureTheory.Lp.coeFn_sub
      ((mkWkpSpaceOnOfContDiff
          (n := n) (k := k) (p := p) (Ω := Ω)
          f hf hfcs : WkpAmbientOn n k p Ω) a)
      ((mkWkpSpaceOnOfContDiff
          (n := n) (k := k) (p := p) (Ω := Ω)
          g hg hgcs : WkpAmbientOn n k p Ω) a)
  filter_upwards
    [mkWkpSpaceOnOfContDiff_apply_ae
        (n := n) (k := k) (p := p) (Ω := Ω)
        (f - g) (hf.sub hg) (hfcs.sub hgcs) a,
      mkWkpSpaceOnOfContDiff_apply_ae
        (n := n) (k := k) (p := p) (Ω := Ω)
        f hf hfcs a,
      mkWkpSpaceOnOfContDiff_apply_ae
        (n := n) (k := k) (p := p) (Ω := Ω)
        g hg hgcs a,
      hsub] with x hfgx hfx hgx hsx
  calc
    ((mkWkpSpaceOnOfContDiff
        (n := n) (k := k) (p := p) (Ω := Ω)
        (f - g) (hf.sub hg) (hfcs.sub hgcs) :
        WkpAmbientOn n k p Ω) a : ℝ^n → ℝ) x =
        iteratedPartialDeriv (n := n) a.toList (f - g) x := hfgx
    _ = iteratedPartialDeriv (n := n) a.toList f x -
        iteratedPartialDeriv (n := n) a.toList g x := by
      exact congrFun
        (PDE.iteratedPartialDeriv_sub_of_contDiff a.toList
          (hf.of_le (by exact_mod_cast le_top))
          (hg.of_le (by exact_mod_cast le_top))) x
    _ = ((mkWkpSpaceOnOfContDiff
          (n := n) (k := k) (p := p) (Ω := Ω)
          f hf hfcs : WkpAmbientOn n k p Ω) a : ℝ^n → ℝ) x -
        ((mkWkpSpaceOnOfContDiff
          (n := n) (k := k) (p := p) (Ω := Ω)
          g hg hgcs : WkpAmbientOn n k p Ω) a : ℝ^n → ℝ) x := by
      rw [hfx, hgx]
    _ = (((mkWkpSpaceOnOfContDiff
          (n := n) (k := k) (p := p) (Ω := Ω)
          f hf hfcs : WkpAmbientOn n k p Ω) a -
        (mkWkpSpaceOnOfContDiff
          (n := n) (k := k) (p := p) (Ω := Ω)
          g hg hgcs : WkpAmbientOn n k p Ω) a :
        DerivLp n p Ω) : ℝ^n → ℝ) x := hsx.symm

end Constructors

section Constant

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)} [IsFiniteMeasure (domainMeasure n Ω)]

/-- On a finite-measure domain, the first-order classical derivative rows of a constant
belong to every `Lᵖ`. -/
theorem memLp_iteratedPartialDeriv_const (c : ℝ) (a : DerivIndex n 1) :
    MemLp (fun x : ℝ^n ↦ iteratedPartialDeriv a.toList (fun _ ↦ c) x)
      p (domainMeasure n Ω) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa [iteratedPartialDeriv] using
      (memLp_const c : MemLp (fun _ : ℝ^n ↦ c) p (domainMeasure n Ω))
  · simp [iteratedPartialDeriv, PDE.partialDeriv_const]

/-- The constant function, as an element of `W¹ᵖ` on a finite-measure domain. -/
noncomputable def wkpConstant (c : ℝ) : W^{1,p}(Ω) :=
  mkWkpSpaceOnOfContDiffMemLp (fun _ ↦ c) contDiff_const
    (memLp_iteratedPartialDeriv_const c)

/-- The base coordinate of the constant Sobolev element is the specified constant. -/
theorem wkpConstant_base_ae [Fact (1 ≤ p)] (c : ℝ) :
    (wkpBaseCoordinateCLM (wkpConstant (n := n) (p := p) (Ω := Ω) c) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun _ ↦ c := by
  simpa [wkpConstant, iteratedPartialDeriv] using
    mkWkpSpaceOnOfContDiffMemLp_apply_ae (fun _ : ℝ^n ↦ c) contDiff_const
      (memLp_iteratedPartialDeriv_const (p := p) (Ω := Ω) c) (baseIndex n 1)

/-- Every weak derivative coordinate of a constant Sobolev element vanishes. -/
theorem wkpConstant_deriv_eq_zero (c : ℝ) (i : Fin n) :
    (wkpConstant (n := n) (p := p) (Ω := Ω) c : WkpAmbientOn n 1 p Ω)
      (singleDerivIndex n i) = 0 := by
  apply Lp.ext
  have h := mkWkpSpaceOnOfContDiffMemLp_apply_ae (fun _ : ℝ^n ↦ c) contDiff_const
    (memLp_iteratedPartialDeriv_const (p := p) (Ω := Ω) c) (singleDerivIndex n i)
  have hzero :
      ((wkpConstant (n := n) (p := p) (Ω := Ω) c : WkpAmbientOn n 1 p Ω)
        (singleDerivIndex n i) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] 0 := by
    simpa [wkpConstant, iteratedPartialDeriv, PDE.partialDeriv_const, Pi.zero_def] using h
  exact hzero.trans (Lp.coeFn_zero ℝ p (domainMeasure n Ω)).symm

/-- Every weak derivative coordinate of a constant Sobolev element vanishes almost
everywhere. -/
theorem wkpConstant_deriv_ae (c : ℝ) (i : Fin n) :
    ((wkpConstant (n := n) (p := p) (Ω := Ω) c : WkpAmbientOn n 1 p Ω)
        (singleDerivIndex n i) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun _ ↦ 0 := by
  rw [wkpConstant_deriv_eq_zero]
  exact Lp.coeFn_zero ℝ p (domainMeasure n Ω)

end Constant

/-- A globally `C^k` scalar function has an `H^k` representative on every bounded domain.
Boundedness makes its continuous derivatives square integrable; no regularity of the
boundary is required. -/
theorem exists_HkSpaceOn_of_contDiff_of_isBounded {n k : ℕ} {Ω : Set (ℝ^n)}
    (hΩ : Bornology.IsBounded Ω) (f : ℝ^n → ℝ) (hf : ContDiff ℝ k f) :
    ∃ U : W^{k,2}(Ω), baseRepresentative U =ᵐ[domainMeasure n Ω] f := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hΩ
  have hmem (a : DerivIndex n k) :
      MemLp (iteratedPartialDeriv a.toList f) 2 (domainMeasure n Ω) :=
    (WeakChangeOfVariables.memLp_top_on_bounded_of_continuous hΩ
      (PDE.contDiff_iteratedPartialDeriv_of_le hf a.toList
        a.toList_length_le).continuous).mono_exponent
        (by simp)
  refine ⟨mkWkpSpaceOnOfContDiffMemLpFinite f hf hmem, ?_⟩
  simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
    mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae f hf hmem (baseIndex n k)

end GraphSpace

end SobolevSpace
