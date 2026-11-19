/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.DomainTruncation
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator

/-!
# Interval truncation on operational C¹ domains

We specialize finite-measure domain truncation to bounded domains
carrying an operational `Boundary.C1ExtensionAtlas`. Every ordered
interval defines a first-order Sobolev truncation; unlike the whole-space
construction, the interval need not contain zero.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.GraphSpace

open MeasureTheory Set ENNReal
open scoped Sobolev

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Set (ℝ^n)} [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Interval truncation of a first-order Sobolev element on an operational
`C¹` domain. The ordered interval need not contain zero. -/
noncomputable def intervalTruncationOn
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(Ω)) :
    W^{1,p}(Ω) :=
  intervalTruncationOnOfExtension hΩ.isOpen
    (Extension.C1.operator (n := n) (p := p) (Ω := Ω))
    hp_top hab U

/-- The base coordinate of `intervalTruncationOn` is the pointwise clamp
almost everywhere. -/
theorem intervalTruncationOn_base_ae
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(Ω)) :
    ((((intervalTruncationOn hp_top hab U :
        WkpAmbientOn n 1 p Ω)
      (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Calculus.intervalTruncation a b
            ((((U : WkpAmbientOn n 1 p Ω)
              (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x) := by
  exact intervalTruncationOnOfExtension_base_ae hΩ.isOpen
    (Extension.C1.operator (n := n) (p := p) (Ω := Ω))
    hp_top hab U

/-- The derivative coordinate of `intervalTruncationOn` is the
sign-difference multiplier times the original derivative. -/
theorem intervalTruncationOn_derivative_ae
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(Ω)) (i : Fin n) :
    ((((intervalTruncationOn hp_top hab U :
        WkpAmbientOn n 1 p Ω)
      (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          (((SignType.sign
            (((((U : WkpAmbientOn n 1 p Ω)
              (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x) - a) : ℝ) -
            (SignType.sign
              (((((U : WkpAmbientOn n 1 p Ω)
                (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x) - b) : ℝ)) /
              2) *
            ((((U : WkpAmbientOn n 1 p Ω)
              (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ) x) := by
  exact intervalTruncationOnOfExtension_derivative_ae hΩ.isOpen
    (Extension.C1.operator (n := n) (p := p) (Ω := Ω))
    hp_top hab U i

/-- The derivative of `intervalTruncationOn` is the original derivative on
the open interval and zero outside it, almost everywhere. -/
theorem intervalTruncationOn_derivative_indicator_ae
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(Ω)) (i : Fin n) :
    ((((intervalTruncationOn hp_top hab U :
        WkpAmbientOn n 1 p Ω)
      (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          if a <
              ((((U : WkpAmbientOn n 1 p Ω)
                (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x) ∧
              ((((U : WkpAmbientOn n 1 p Ω)
                (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x) < b then
            ((((U : WkpAmbientOn n 1 p Ω)
              (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ) x)
          else 0 := by
  exact intervalTruncationOnOfExtension_derivative_indicator_ae hΩ.isOpen
    (Extension.C1.operator (n := n) (p := p) (Ω := Ω))
    hp_top hab U i

/-- Every ordered interval truncation obeys the weak Sobolev chain rule on
an operational `C¹` domain. -/
theorem hasWeakDerivativeOn_intervalTruncation_on
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(Ω)) (i : Fin n) :
    let u : ℝ^n → ℝ :=
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := p) (Ω := Ω) U : ℝ^n → ℝ)
    let du : ℝ^n → ℝ :=
      (wkpCoordinateCLM
        (n := n) (p := p) (Ω := Ω)
        (singleDerivIndex n i) U : ℝ^n → ℝ)
    HasWeakDerivativeOn (n := n) Ω [i]
      (fun x ↦ PDE.Analysis.Calculus.intervalTruncation a b (u x))
      (fun x ↦
        (((SignType.sign (u x - a) : ℝ) -
          (SignType.sign (u x - b) : ℝ)) / 2) * du x) := by
  exact hasWeakDerivativeOn_intervalTruncation_on_of_extension hΩ.isOpen
    (Extension.C1.operator (n := n) (p := p) (Ω := Ω))
    hp_top hab U i

end SobolevSpace.GraphSpace
