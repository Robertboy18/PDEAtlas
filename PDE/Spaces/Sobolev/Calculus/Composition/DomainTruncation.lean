/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.DomainCore
public import PDE.Spaces.Sobolev.Calculus.Composition.Truncation

/-!
# Interval truncation on finite-measure extension domains

We remove the whole-space requirement that a truncation interval
contain zero. The global Sobolev operation is applied to the centered clamp
`T_[a,b] - T_[a,b](0)`, then the missing constant is restored after
restriction to a finite-measure domain.

For every ordered interval, the resulting element has pointwise base
coordinate `T_[a,b](u)` and derivative

`∂ᵢ T_[a,b](u) = 1_{a < u < b} ∂ᵢu`

almost everywhere.

The clamp `T_[a,b](u) = min (max u a) b` is a composition of the lattice operations `u ↦ u⁺` shifted
by constants, so this is the truncation lemma for `W^{1,p}` (Gilbarg and Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Chapter 7), together with the fact that
the weak gradient vanishes a.e. on the level sets `{u = a}` and `{u = b}`, which is what allows the
derivative to be written with the open-interval indicator.

## Main results

* `intervalTruncationOnOfExtension`: `T_[a,b](U)` in `W^{1,p}(Ω)`, for any `a ≤ b`, given an
  extension operator on the finite-measure open set `Ω`.
* `intervalTruncationOnOfExtension_base_ae`: its base coordinate is the pointwise clamp.
* `intervalTruncationOnOfExtension_derivative_ae`,
  `intervalTruncationOnOfExtension_derivative_indicator_ae`: its `i`th derivative coordinate
  is `∂ᵢu` on `{a < u < b}` and zero elsewhere, almost everywhere.
* `hasWeakDerivativeOn_intervalTruncation_on_of_extension`: the same statement as a weak
  derivative identity on `Ω`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 7, Sobolev Spaces, pp. 144-176, for the
  truncation lemma in `W^{1,p}` and the vanishing of `Du` a.e. on level sets.
  <https://doi.org/10.1007/978-3-642-61798-0>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.10, Problem 18, p. 308, the exercise, for bounded `U`,
  that `u⁺, u⁻ ∈ W^{1,p}(U)` with the expected derivatives and that `Du = 0` a.e. on `{u = 0}`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set Function ENNReal
open scoped Sobolev
open DomainComposition

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Set (ℝ^n)} [IsFiniteMeasure (domainMeasure n Ω)]

/-- Interval truncation on a finite-measure open domain admitting a
first-order Sobolev extension operator. -/
noncomputable def intervalTruncationOnOfExtension
    (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(Ω)) :
    W^{1,p}(Ω) :=
  restrictAndRestoreConstant hΩ
    (centeredIntervalTruncation hp_top hab
      (E.toContinuousLinearMap U))
    (PDE.Analysis.Calculus.intervalTruncation a b 0)

/-- The base coordinate of `intervalTruncationOnOfExtension` is the
pointwise clamp almost everywhere. -/
theorem intervalTruncationOnOfExtension_base_ae
    (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(Ω)) :
    ((((intervalTruncationOnOfExtension hΩ E hp_top hab U :
        WkpAmbientOn n 1 p Ω)
      (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        fun x ↦
          PDE.Analysis.Calculus.intervalTruncation a b
            ((((U : WkpAmbientOn n 1 p Ω)
              (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x) := by
  let EU := E.toContinuousLinearMap U
  let V : W^{1,p}(ℝ^n) :=
    centeredIntervalTruncation hp_top hab EU
  have hlocal :=
    restrictAndRestoreConstant_base_ae
      (n := n) (p := p) (Ω := Ω) hΩ V
      (PDE.Analysis.Calculus.intervalTruncation a b 0)
  have hcentered :=
    centeredIntervalTruncation_base_ae hp_top hab EU
  have hmeasure :
      domainMeasure n Ω ≤ domainMeasure n Set.univ := by
    simpa [domainMeasure] using
      (Measure.restrict_le_self :
        (volume : Measure (ℝ^n)).restrict Ω ≤ volume)
  have hcenteredΩ := hcentered.filter_mono (ae_mono hmeasure)
  have hagree := E.agree_ae U
  filter_upwards [hlocal, hcenteredΩ, hagree] with
      x hxlocal hxcentered hxagree
  change
    ((((intervalTruncationOnOfExtension hΩ E hp_top hab U :
      WkpAmbientOn n 1 p Ω)
      (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ)) x =
      PDE.Analysis.Calculus.intervalTruncation a b
        ((((U : WkpAmbientOn n 1 p Ω)
          (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ) x)
  change
    ((((restrictAndRestoreConstant hΩ V
      (PDE.Analysis.Calculus.intervalTruncation a b 0) :
        WkpAmbientOn n 1 p Ω) (baseIndex n 1) :
          DerivLp n p Ω) : ℝ^n → ℝ) x) = _
  rw [hxlocal, hxcentered, hxagree]
  simp [PDE.Analysis.Calculus.centeredIntervalTruncation]

/-- The derivative coordinate of `intervalTruncationOnOfExtension` is the
sign-difference multiplier times the original derivative. -/
theorem intervalTruncationOnOfExtension_derivative_ae
    (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(Ω)) (i : Fin n) :
    ((((intervalTruncationOnOfExtension hΩ E hp_top hab U :
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
  let EU := E.toContinuousLinearMap U
  let V : W^{1,p}(ℝ^n) :=
    centeredIntervalTruncation hp_top hab EU
  have hlocal :=
    restrictAndRestoreConstant_derivative_ae
      (n := n) (p := p) (Ω := Ω) hΩ V
      (PDE.Analysis.Calculus.intervalTruncation a b 0) i
  have hcentered :=
    centeredIntervalTruncation_derivative_ae hp_top hab EU i
  have hmeasure :
      domainMeasure n Ω ≤ domainMeasure n Set.univ := by
    simpa [domainMeasure] using
      (Measure.restrict_le_self :
        (volume : Measure (ℝ^n)).restrict Ω ≤ volume)
  have hcenteredΩ := hcentered.filter_mono (ae_mono hmeasure)
  have hagree := E.agree_ae U
  have hEcoord :=
    extension_coordinate_ae hΩ E U (singleDerivIndex n i)
  filter_upwards [hlocal, hcenteredΩ, hagree, hEcoord] with
      x hxlocal hxcentered hxagree hxEcoord
  change
    ((((intervalTruncationOnOfExtension hΩ E hp_top hab U :
      WkpAmbientOn n 1 p Ω)
      (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ)) x = _
  change
    ((((restrictAndRestoreConstant hΩ V
      (PDE.Analysis.Calculus.intervalTruncation a b 0) :
        WkpAmbientOn n 1 p Ω) (singleDerivIndex n i) :
          DerivLp n p Ω) : ℝ^n → ℝ) x) = _
  rw [hxlocal, hxcentered, hxagree, hxEcoord]

/-- The derivative of domain interval truncation is the original derivative
on the open interval and zero outside it, almost everywhere. -/
theorem intervalTruncationOnOfExtension_derivative_indicator_ae
    (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
    (hp_top : p ≠ ∞) {a b : ℝ} (hab : a ≤ b)
    (U : W^{1,p}(Ω)) (i : Fin n) :
    ((((intervalTruncationOnOfExtension hΩ E hp_top hab U :
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
  let EU := E.toContinuousLinearMap U
  let V : W^{1,p}(ℝ^n) :=
    centeredIntervalTruncation hp_top hab EU
  have hlocal :=
    restrictAndRestoreConstant_derivative_ae
      (n := n) (p := p) (Ω := Ω) hΩ V
      (PDE.Analysis.Calculus.intervalTruncation a b 0) i
  have hcentered :=
    centeredIntervalTruncation_derivative_indicator_ae hp_top hab EU i
  have hmeasure :
      domainMeasure n Ω ≤ domainMeasure n Set.univ := by
    simpa [domainMeasure] using
      (Measure.restrict_le_self :
        (volume : Measure (ℝ^n)).restrict Ω ≤ volume)
  have hcenteredΩ := hcentered.filter_mono (ae_mono hmeasure)
  have hagree := E.agree_ae U
  have hEcoord :=
    extension_coordinate_ae hΩ E U (singleDerivIndex n i)
  filter_upwards [hlocal, hcenteredΩ, hagree, hEcoord] with
      x hxlocal hxcentered hxagree hxEcoord
  change
    ((((intervalTruncationOnOfExtension hΩ E hp_top hab U :
      WkpAmbientOn n 1 p Ω)
      (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ)) x = _
  change
    ((((restrictAndRestoreConstant hΩ V
      (PDE.Analysis.Calculus.intervalTruncation a b 0) :
        WkpAmbientOn n 1 p Ω) (singleDerivIndex n i) :
          DerivLp n p Ω) : ℝ^n → ℝ) x) = _
  rw [hxlocal, hxcentered, hxagree, hxEcoord]

/-- Interval truncation obeys the weak Sobolev chain rule on every
finite-measure open domain admitting a first-order extension operator, for
every ordered interval. -/
theorem hasWeakDerivativeOn_intervalTruncation_on_of_extension
    (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
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
  let V := intervalTruncationOnOfExtension hΩ E hp_top hab U
  have hV :
      HasWeakDerivativeOn (n := n) Ω [i]
        (((V : WkpAmbientOn n 1 p Ω)
          (baseIndex n 1) : DerivLp n p Ω) : ℝ^n → ℝ)
        (((V : WkpAmbientOn n 1 p Ω)
          (singleDerivIndex n i) : DerivLp n p Ω) : ℝ^n → ℝ) := by
    simpa [firstDerivIndex_one] using
      V.property.hasWeakDerivativeOn_first (by norm_num) i
  exact
    (hasWeakDerivativeOn_congr_ae
      (intervalTruncationOnOfExtension_base_ae
        hΩ E hp_top hab U)
      (intervalTruncationOnOfExtension_derivative_ae
        hΩ E hp_top hab U i)).mp hV

end SobolevSpace.GraphSpace
