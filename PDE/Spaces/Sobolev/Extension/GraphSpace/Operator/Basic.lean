/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.CompactCutoff
public import PDE.Spaces.Sobolev.Extension.HigherOrder.Cutoff

/-!
# Sobolev graph-space extension operators

We define extension operators directly on the completed Sobolev
graph-space model. An extension operator is a continuous linear map to
the global graph space whose base coordinate agrees almost everywhere on the
original domain.

Support localization is recorded by a separate structure because it is
additional data, not part of the abstract extension property. The
representative-level extensions are obtained from these operators in
`RepresentativeBridge`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; the support condition (ii) is
  arranged in step 6, p. 270.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

set_option linter.missingDocs true

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function ENNReal

namespace Extension

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {Ω : Set (ℝ^n)}

namespace GraphSpace

open SobolevSpace.GraphSpace

/-- An extension operator in the Sobolev graph-space model (Evans §5.4, Theorem 1): a bounded linear
map `W^{k,p}(Ω) → W^{k,p}(ℝ^n)` whose base coordinate agrees almost everywhere on `Ω` with the
input. Prescribed support is recorded separately by `SupportedOperator`. -/
structure Operator (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Set (ℝ^n)) where
  /-- The bounded linear map from the domain graph space to the global graph space. -/
  toContinuousLinearMap : W^{k,p}(Ω) →L[ℝ] W^{k,p}(ℝ^n)
  /-- The base coordinate of the extension agrees almost everywhere with the
  original Sobolev function on `Ω`. -/
  agree_ae :
    ∀ u : W^{k,p}(Ω),
      (∀ᵐ x ∂ domainMeasure n Ω,
        ((toContinuousLinearMap u : WkpAmbientOn n k p Set.univ) (baseIndex n k)) x =
          ((u : WkpAmbientOn n k p Ω) (baseIndex n k)) x)

/-- There is an extension operator `W^{k,p}(Ω) → W^{k,p}(ℝ^n)` in the sense of `Operator`
(Evans §5.4, Theorem 1). The definition places no hypothesis on `Ω`. -/
def HasExtensionOperator (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Set (ℝ^n)) : Prop :=
  Nonempty (Operator n k p Ω)

/-- A bounded extension operator whose base representative is supported
almost everywhere in a prescribed set `V`.

Sobolev functions are equivalence classes modulo null sets, so the correct
representative-independent support statement is the displayed indicator
identity rather than pointwise `Function.support` for an arbitrary chosen
representative. -/
structure SupportedOperator
    (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω V : Set (ℝ^n)) where
  /-- The underlying extension operator before recording its prescribed support. -/
  toOperator : Operator n k p Ω
  /-- The base coordinate of every extension vanishes almost everywhere
  outside `V`, expressed by invariance under the indicator of `V`. -/
  supported_ae :
    ∀ u : W^{k,p}(Ω),
      V.indicator
          (fun x ↦
            (((toOperator.toContinuousLinearMap u : WkpAmbientOn n k p Set.univ)
              (baseIndex n k) : DerivLp n p Set.univ) : ℝ^n → ℝ) x)
        =ᵐ[domainMeasure n Set.univ]
          fun x ↦
            (((toOperator.toContinuousLinearMap u : WkpAmbientOn n k p Set.univ)
              (baseIndex n k) : DerivLp n p Set.univ) : ℝ^n → ℝ) x

/-- Existence of a bounded extension supported almost everywhere in `V`. -/
def HasSupportedExtensionOperator
    (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Ω V : Set (ℝ^n)) : Prop :=
  Nonempty (SupportedOperator n k p Ω V)

/-- Localize a bounded extension of any finite Sobolev order to an arbitrary open
neighborhood of `closure Ω`.

This gives condition (ii) of Evans §5.4, Theorem 1, "`Eu` has support within `V`", which Evans
arranges in step 6 of the proof. We choose a smooth cutoff with support in `V` and equal to one
on `closure Ω`, multiply the original extension by it, and retain both a.e. agreement on `Ω` and
bounded linearity. The domain need only be measurable; the cutoff acts on the whole-space
extension. This includes order zero and `p = ∞`. -/
noncomputable def Operator.withSupportIn
    (E : Operator n k p Ω)
    (V : Set (ℝ^n))
    (hΩmeas : MeasurableSet Ω)
    (hVopen : IsOpen V)
    (hΩcompact : IsCompact (closure Ω))
    (hΩV : closure Ω ⊆ V) :
    SupportedOperator n k p Ω V :=
  let hcutoff :=
    TestFunction.exists_eq_one_on_compact
      hVopen hΩcompact hΩV
  let ψ := Classical.choose hcutoff
  have hψspec := Classical.choose_spec hcutoff
  have hψV := hψspec.1
  have hψone := hψspec.2.1
  let localized :
      W^{k,p}(Ω) →L[ℝ] W^{k,p}(ℝ^n) :=
    (HigherOrder.cutoffExtensionCLM isOpen_univ isOpen_univ
      (Subset.rfl) ψ (subset_univ _)).comp E.toContinuousLinearMap
  have hbase (u : W^{k,p}(Ω)) :
      baseRepresentative (localized u) =ᵐ[domainMeasure n Set.univ]
        fun x ↦ ψ.toFun x * baseRepresentative (E.toContinuousLinearMap u) x :=
    CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff_base_ae
      isOpen_univ (Subset.rfl) ψ (subset_univ _) (E.toContinuousLinearMap u)
  { toOperator :=
      { toContinuousLinearMap := localized
        agree_ae := by
          intro u
          change baseRepresentative (localized u) =ᵐ[domainMeasure n Ω]
            baseRepresentative u
          have hcutΩ :
              baseRepresentative (localized u) =ᵐ[domainMeasure n Ω]
                fun x ↦ ψ.toFun x * baseRepresentative (E.toContinuousLinearMap u) x := by
            simpa only [Filter.EventuallyEq, domainMeasure, Measure.restrict_univ] using
              MeasureTheory.ae_restrict_of_ae (s := Ω) (hbase u)
          have hmem : ∀ᵐ x ∂domainMeasure n Ω, x ∈ Ω := by
            simpa [domainMeasure] using
              (MeasureTheory.ae_restrict_mem hΩmeas :
                ∀ᵐ x ∂(MeasureTheory.volume : Measure (ℝ^n)).restrict Ω, x ∈ Ω)
          filter_upwards [hcutΩ, E.agree_ae u, hmem] with x hxcut hxagree hxΩ
          rw [hxcut, hψone x (subset_closure hxΩ), one_mul]
          exact hxagree }
    supported_ae := by
      intro u
      change V.indicator (baseRepresentative (localized u)) =ᵐ[domainMeasure n Set.univ]
        baseRepresentative (localized u)
      filter_upwards [hbase u] with x hx
      by_cases hxV : x ∈ V
      · rw [Set.indicator_of_mem hxV]
      · have hxSupport : x ∉ tsupport ψ.toFun := fun hxK ↦ hxV (hψV hxK)
        rw [Set.indicator_of_notMem hxV, hx,
          image_eq_zero_of_notMem_tsupport hxSupport, zero_mul] }

end GraphSpace

end Extension

end SobolevSpace

end
