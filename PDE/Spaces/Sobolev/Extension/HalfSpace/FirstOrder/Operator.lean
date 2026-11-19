/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global
public import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.Basic
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.Ambient
import PDE.Spaces.Sobolev.Approximation.Density.ExtensionDomain
import PDE.Spaces.Sobolev.Extension.GraphSpace.Operator.RepresentativeBridge
import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.NormalDerivative
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TangentialDerivative

/-!
# The bounded half-space extension operator

Even reflection of the base and tangential derivative coordinates, together
with odd reflection of the normal derivative, defines a bounded map from
`W^{1,p}` on the upper half-space to global `W^{1,p}`.  The extension agrees
almost everywhere with the original function on the upper half-space.

The graph-space operator is also transported to representative-level
Sobolev data.  Its consequences include smooth approximation on the
half-space and the first-order Sobolev embedding obtained by extension to
the whole space.

This is the half-space model case of the extension theorem (Evans, PDE, §5.4). Evans extends
`C¹` functions across a flat boundary by the higher-order reflection
`-3u(x', -xₙ) + 4u(x', -xₙ/2)`, which is again `C¹`, and passes to `W^{1,p}` by density. At
order one we reflect evenly instead: `ū(x', xₙ) = u(x', -xₙ)` for `xₙ < 0` preserves `L^p`
norms and produces the correct weak derivatives, even for the tangential ones and odd for the
normal one. The weak-derivative
identities are proved in `HalfSpace.FirstOrder.NormalDerivative` and the tangential files; here
they are assembled into a single bounded operator.

## Main results

* `operator`: the extension operator `WkpSpaceOn n 1 p ℝ^n₊ → WkpSpace n 1 p` as a graph-space
  `Operator`, agreeing a.e. with the input on `ℝ^n₊`.
* `exists_extensionOperator`, `exists_representativeExtensionOperator`: the corresponding
  existence statements at graph-space and representative level.
* `approximation_W1p_upper`: density of `C_c^∞(ℝ^n)` in `W^{1,p}(ℝ^n₊)`, `p < ∞`, including the
  weak first derivatives.
* `memLp_pStar_of_sobolevSpaceOn_upper`: the Gagliardo–Nirenberg–Sobolev embedding
  `W^{1,p}(ℝ^n₊) ⊆ L^{p*}(ℝ^n₊)` for `1 ≤ p < n`, via extension and the global inequality.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, whose proof extends `C¹`
  functions across a flat boundary by the higher-order reflection (3), p. 269, where we reflect
  evenly; §5.3.3, Theorem 3, pp. 266-268, the corresponding approximation theorem on bounded `C¹`
  domains; and §5.6.1, Theorem 2, p. 279, whose proof deduces the embedding on a domain from an
  extension operator and Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

namespace SobolevSpace

open Set MeasureTheory Function
open scoped ENNReal Topology

section

namespace Extension

namespace GraphSpace

open SobolevSpace.GraphSpace


namespace HalfSpace

open _root_.SobolevSpace.HalfSpace

variable (n : ℕ)
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]


section Proofs

open scoped RealInnerProductSpace
open Filter


local notation "μ" => (domainMeasure n (Set.univ : Set (ℝ^n)))
local notation "μ₊" => (domainMeasure n ℝ^n₊)
local notation "μ₋" => (domainMeasure n ℝ^n₋)

section PositiveDimension

variable [Fact (0 < n)]

private theorem extendAmbient_mapsIsWkpOn (U : WkpAmbientOn n 1 p ℝ^n₊)
    (hU : IsWkpOn (n := n) (k := 1) (p := p) (Ω := ℝ^n₊) U) :
    IsWkpOn (n := n) (k := 1) (p := p) (Ω := (Set.univ : Set (ℝ^n)))
      (extendAmbient (n := n) (p := p) U) := by
  classical
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hloc := memLp_locallyIntegrableOn_domain
      (MeasureTheory.Lp.memLp ((extendAmbient (n := n) (p := p) U) (baseIndex n 1)))
      (Fact.out : (1 : ℝ≥0∞) ≤ p)
    simpa only [SobolevSpace.GraphSpace.baseIndex_toList] using hasWeakDerivativeOn_nil hloc
  · subst a
    by_cases hi : i = PDE.Common.lastIndex (n := n)
    · simpa [extendAmbient_apply, extendLpAt, hi] using
        hasWeakDerivativeOn_univ_evenExtend_of_upper_last (n := n) (p := p)
          (u := U (baseIndex n 1)) (du := U (singleDerivIndex n i))
          (by simpa [firstDerivIndex_one, hi] using hU.hasWeakDerivativeOn_first (by norm_num) i)
    · simpa [extendAmbient_apply, extendLpAt, hi] using
        hasWeakDerivativeOn_univ_evenExtend_of_upper_ne_last (n := n) (p := p) (i := i) hi
          (u := U (baseIndex n 1)) (du := U (singleDerivIndex n i))
          (by simpa only [firstDerivIndex_one] using hU.hasWeakDerivativeOn_first (by norm_num) i)

/-- The reflection extension `W^{1,p}(ℝ^n₊) → W^{1,p}(ℝ^n)` as a continuous linear map into
the whole-space graph space. -/
noncomputable def extendCLM :
    W^{1,p}(ℝ^n₊) →L[ℝ] W^{1,p}(ℝ^n) :=
  ContinuousLinearMap.codRestrict
    ((extendAmbient (n := n) (p := p)).comp (Submodule.subtypeL (wkpSubmoduleOn n 1 p ℝ^n₊)))
    (wkpSubmoduleOn n 1 p (Set.univ : Set (ℝ^n)))
    (by
      intro u
      exact
        extendAmbient_mapsIsWkpOn (n := n) (p := p)
          (U := (u : WkpAmbientOn n 1 p ℝ^n₊)) u.property)

/-- The base coordinate of the extension is the even reflection of the original base
coordinate. -/
private theorem extendCLM_apply_base (u : W^{1,p}(ℝ^n₊)) :
    ((extendCLM (n := n) (p := p) u : WkpAmbientOn n 1 p Set.univ)
        (baseIndex n 1) : DerivLp n p Set.univ) =
      _root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p)
        ((u : WkpAmbientOn n 1 p ℝ^n₊) (baseIndex n 1)) := by
  change
    extendAmbient (n := n) (p := p) (u : WkpAmbientOn n 1 p ℝ^n₊) (baseIndex n 1) = _
  simp [extendAmbient_apply, extendLpAt]

private theorem evenExtendLp_agree_ae_upper (u : DerivLp n p ℝ^n₊) :
    ((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p) u :
        DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[μ₊] (u : ℝ^n → ℝ) := by
  filter_upwards [ae_restrict_of_ae (_root_.SobolevSpace.HalfSpace.evenExtendLp_apply_ae
    (n := n) (p := p) u), ae_restrict_mem (measurableSet_upper (n := n))] with x hx hxU
  have hxL : x ∉ ℝ^n₋ := by
    simpa [_root_.SobolevSpace.HalfSpace.lower] using
      (not_lt_of_ge (le_of_lt (by simpa [_root_.SobolevSpace.HalfSpace.upper] using hxU)) :
        ¬ x (PDE.Common.lastIndex (n := n)) < 0)
  rw [hx, indicator_of_mem hxU, indicator_of_notMem hxL, add_zero]

/-- The bounded `W^{1,p}` half-space extension obtained by even reflection of the function and
tangential derivatives and odd reflection of the normal derivative. -/
noncomputable def operator :
    SobolevSpace.Extension.GraphSpace.Operator n 1 p ℝ^n₊ where
  toContinuousLinearMap := extendCLM (n := n) (p := p)
  agree_ae := by
    intro u
    -- base coordinate is the even extension of the base coordinate.
    have hbase :
        ((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p)
            ((u : WkpAmbientOn n 1 p ℝ^n₊) (baseIndex n 1)) : DerivLp n p Set.univ) : ℝ^n → ℝ)
          =ᵐ[μ₊] (((u : WkpAmbientOn n 1 p ℝ^n₊) (baseIndex n 1)) : ℝ^n → ℝ) :=
      evenExtendLp_agree_ae_upper (n := n) (p := p) ((u : WkpAmbientOn n 1 p ℝ^n₊) (baseIndex n 1))
    filter_upwards [hbase] with x hx
    calc
      (((extendCLM (n := n) (p := p) u : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1)) x) =
          ((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p)
            ((u : WkpAmbientOn n 1 p ℝ^n₊) (baseIndex n 1)) :
              DerivLp n p Set.univ) x) := by
        rw [extendCLM_apply_base]
      _ = (((u : WkpAmbientOn n 1 p ℝ^n₊) (baseIndex n 1)) x) := hx

/-- The upper half-space admits a bounded `W^{1,p}` extension operator, namely the reflection
operator `operator`. -/
theorem exists_extensionOperator :
    SobolevSpace.Extension.GraphSpace.HasExtensionOperator n 1 p ℝ^n₊ :=
  ⟨operator (n := n) (p := p)⟩

/-- Representative-level extension obtained by forgetting the graph-space structure. -/
theorem exists_representativeExtensionOperator :
    SobolevSpace.Extension.Representative.HasExtension n 1 p ℝ^n₊ := by
  exact
    SobolevSpace.Extension.GraphSpace.exists_representativeExtensionOperator
      (n := n) (k := 1) (p := p) (Ω := ℝ^n₊)
      (SobolevSpace.Extension.GraphSpace.HalfSpace.exists_extensionOperator (n := n) (p := p))

/-- For finite `p`, every `W^{1,p}` representative `u` on the upper half-space in `ℝ^n` is
approximated by smooth compactly supported functions on `ℝ^n`, coordinatewise in `eLpNorm` on
`ℝ^n₊`: the functions converge to `u` and their partial derivatives of order at most one
converge to weak derivatives of `u`.

The proof applies the extension-based approximation theorem
`SobolevSpace.Approximation.approximation_Wkp` to the reflection operator; compare Evans §5.3.3,
Theorem 3, on bounded `C¹` domains. -/
theorem approximation_W1p_upper
    (moll : SobolevSpace.Approximation.Mollifier n) (hp : p ≠ ∞) :
    ∀ u : SobolevSpaceOn n 1 p ℝ^n₊,
      ∃ u_m : ℕ → (ℝ^n → ℝ),
        (∀ m, ContDiff ℝ (⊤ : ℕ∞) (u_m m)) ∧
        (∀ m, HasCompactSupport (u_m m)) ∧
        Filter.Tendsto
          (fun m ↦
            MeasureTheory.eLpNorm (fun x ↦ u_m m x - u.toFun x) p (domainMeasure n ℝ^n₊))
          Filter.atTop (𝓝 0) ∧
        (∀ α : List (Fin n), α.length ≤ 1 →
          ∃ g : ℝ^n → ℝ,
            MeasureTheory.MemLp g p (domainMeasure n ℝ^n₊) ∧
            HasWeakDerivativeOn (n := n) ℝ^n₊ α u.toFun g ∧
            Filter.Tendsto
              (fun m ↦
                MeasureTheory.eLpNorm (fun x ↦ iteratedPartialDeriv (n := n) α (u_m m) x - g x) p
                  (domainMeasure n ℝ^n₊))
              Filter.atTop (𝓝 0)) := by
  intro u
  exact
    SobolevSpace.Approximation.approximation_Wkp (n := n)
      moll p hp 1 ℝ^n₊ u (_root_.SobolevSpace.HalfSpace.isOpen_upper (n := n))
      (exists_representativeExtensionOperator (n := n) (p := p))

/-- Sobolev embedding on the upper half-space: for `1 ≤ p < n`, every `W^{1,p}`
representative on `ℝ^n₊` lies in `L^{p*}(ℝ^n₊)`. It is deduced from:

1. the even reflection extension, `exists_representativeExtensionOperator`, and
2. the global Sobolev embedding on `ℝ^n`
   (Evans §5.6.1, `Inequalities.Sobolev.FirstOrder.Global`),

as in the proof of Evans §5.6.1, Theorem 2. -/
theorem memLp_pStar_of_sobolevSpaceOn_upper
    {p : NNReal} (hp : (1 : NNReal) ≤ p) (hn : 0 < n) (hp_lt : (p : ℝ) < (n : ℝ)) :
    ∀ u : SobolevSpaceOn n 1 (p : ℝ≥0∞) ℝ^n₊,
      MeasureTheory.MemLp u.toFun (SobolevSpace.Inequalities.pStar n p : ℝ≥0∞)
        (domainMeasure n ℝ^n₊) := by
  classical
  intro u
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  have hE :
      SobolevSpace.Extension.Representative.HasExtension n 1 (p : ℝ≥0∞) ℝ^n₊ :=
    exists_representativeExtensionOperator (n := n) (p := (p : ℝ≥0∞))
  exact
    SobolevSpace.Inequalities.memLp_pStar_of_sobolevSpaceOn_of_extension (n := n) (p := p)
      hp hn hp_lt (Ω := ℝ^n₊) hE u

end PositiveDimension

end Proofs

end HalfSpace

end GraphSpace

end Extension

end

end SobolevSpace
