/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SmoothAbsoluteValue
public import PDE.Spaces.Sobolev.Calculus.Composition.Smooth
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Analysis.Calculus.AbsoluteValue
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Absolute value in first-order Sobolev spaces

We prove the nonsmooth weak chain rule

`∂ᵢ |u| = sign(u) ∂ᵢ u`

for global real-valued `W^{1,p}` functions, `1 ≤ p ≤ ∞`. Absolute value is then an operation on
the completed Sobolev graph space, with explicit base and derivative coordinates.

These are the classical facts about the lattice operations on `W^{1,p}`: `u⁺`, `u⁻` and `|u|` lie in
`W^{1,p}` with `∇u⁺ = ∇u` on `{u > 0}` and `0` on `{u ≤ 0}`, and `∇u = 0` a.e. on every level set
`{u = c}` (Gilbarg and Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Chapter 7). The level-set statement is what turns the sign formula, which is ambiguous where
`u = 0`, into the indicator formulas for `u⁺` and `u⁻`.

## Main results

* `hasWeakDerivativeOn_abs`: `∂ᵢ|u| = sign(u) ∂ᵢu` weakly, for `u ∈ W^{1,p}(ℝ^n)`.
* `absoluteValue`, `positivePart`, `negativePart`: `|u|`, `u⁺ = max u 0`, `u⁻ = max (-u) 0` as
  operations on `W^{1,p}(ℝ^n)`, with `_base_ae` and `_derivative_ae` lemmas describing their
  coordinates almost everywhere.
* `derivative_eq_zero_ae_of_base_eq_zero`, `derivative_eq_zero_ae_of_base_eq`: the weak
  gradient vanishes a.e. on `{u = 0}`, hence on every level set `{u = c}`.
* `positivePart_derivative_indicator_ae`, `negativePart_derivative_indicator_ae`:
  `∂ᵢu⁺ = 𝟙_{u > 0} ∂ᵢu` and `∂ᵢu⁻ = -𝟙_{u < 0} ∂ᵢu` almost everywhere.

## How it works

We obtain `∂ᵢ|u| = sign(u) ∂ᵢu` as the case `F = |·|` of the Lipschitz chain rule
`hasWeakDerivativeOn_comp_lipschitz`, and define `positivePart U = (U + |U|) / 2` and
`negativePart U = (|U| - U) / 2`. Evans, PDE, §5.10, Problem 18, p. 308, sets these facts as an
exercise on a bounded domain, with the hint `u⁺ = lim_{ε → 0} F_ε(u)` for
`F_ε(z) = (z² + ε²)^{1/2} - ε` on `z ≥ 0`. The level-set theorem at level zero,
`derivative_eq_zero_ae_of_base_eq_zero`, comes from comparing two formulas for the derivative of
`u⁺`: since `u⁺ = |u⁺|`, the chain rule gives `∂ᵢu⁺ = sign(u⁺) ∂ᵢu⁺`, which is zero on `{u = 0}`,
while the sign formula gives `∂ᵢu⁺ = ∂ᵢu / 2` there. For a level `c ≠ 0` we cannot subtract the
constant `c`, which is not in `L^p(ℝ^n)`; instead `derivative_eq_zero_ae_of_base_eq` composes `u`
with `PDE.Analysis.Calculus.smoothLevelProbe c`, a smooth one-Lipschitz function that vanishes at
`0` and at `c` and has nonzero slope at `c`, and applies the level-zero case.

## Implementation notes

Everything is on the whole space `Ω = Set.univ`; the domain versions live in the `Domain*`
files of this directory.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 7, Sobolev Spaces, pp. 144-176, for the lattice
  operations on `W^{1,p}` and the vanishing of `Du` a.e. on level sets.
  <https://doi.org/10.1007/978-3-642-61798-0>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.10, Problem 18, p. 308, which asks to prove, for bounded
  `U` and `1 ≤ p ≤ ∞`, that `|u|, u⁺, u⁻ ∈ W^{1,p}(U)`, with `Du⁺ = Du` a.e. on `{u > 0}` and `0`
  a.e. on `{u ≤ 0}`, and that `Du = 0` a.e. on `{u = 0}`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set Function ENNReal
open scoped Topology Sobolev

/-- Absolute value obeys the weak Sobolev chain rule for every `1 ≤ p ≤ ∞`: each weak partial
derivative is multiplied by the pointwise sign of the base coordinate. This is the Lipschitz
chain rule `hasWeakDerivativeOn_comp_lipschitz` with `deriv |·| = sign`. -/
theorem hasWeakDerivativeOn_abs
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    let u : ℝ^n → ℝ :=
      (wkpBaseCoordinateCLM
        (n := n) (m := 1) (p := p) (Ω := Set.univ) U :
          ℝ^n → ℝ)
    let du : ℝ^n → ℝ :=
      (wkpCoordinateCLM
        (n := n) (p := p) (Ω := Set.univ)
        (singleDerivIndex n i) U : ℝ^n → ℝ)
    HasWeakDerivativeOn (n := n) Set.univ [i]
      (fun x ↦ |u x|)
      (fun x ↦ (SignType.sign (u x) : ℝ) * du x) := by
  have hlip : LipschitzWith 1 (fun x : ℝ ↦ |x|) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y
  have hderiv : deriv (fun x : ℝ ↦ |x|) = fun x ↦ (SignType.sign x : ℝ) :=
    funext deriv_abs
  simpa only [Function.comp_def, hderiv] using
    hasWeakDerivativeOn_comp_lipschitz hlip abs_zero U i

private theorem aestronglyMeasurable_sign_comp
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {u : α → ℝ} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable
      (fun x ↦ (SignType.sign (u x) : ℝ)) μ := by
  let ε : ℕ → ℝ := fun k ↦ (1 : ℝ) / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by
    dsimp [ε]
    positivity
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1))
          atTop (𝓝 (0 : ℝ)))
  have hslopeContinuous (k : ℕ) :
      Continuous (PDE.Analysis.Calculus.smoothAbsSlope (ε k)) := by
    unfold PDE.Analysis.Calculus.smoothAbsSlope
    apply continuous_id.div
      (Real.continuous_sqrt.comp
        ((continuous_id.pow 2).add (continuous_const.pow 2)))
    intro x
    exact ne_of_gt
      (Real.sqrt_pos.2
        (PDE.Analysis.Calculus.smoothAbs_sq_add_pos (hεpos k) x))
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun k ↦ (hslopeContinuous k).comp_aestronglyMeasurable hu)
  filter_upwards [] with x
  exact
    PDE.Analysis.Calculus.tendsto_smoothAbsSlope_of_tendsto_zero
      hεzero (u x)

/-- The base function of the absolute value: `|u|` for the base coordinate
representative `u` of `U`. -/
abbrev absoluteValueBase
    {n : ℕ} {p : ℝ≥0∞}
    (U : W^{1,p}(ℝ^n)) :
    ℝ^n → ℝ :=
  fun x ↦
    |((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ) x|

/-- The coordinate rows of the absolute value: the base row is `|u|` and the
`i`th derivative row is `sign(u) ∂ᵢu`. -/
def absoluteValueRows
    {n : ℕ} {p : ℝ≥0∞}
    (U : W^{1,p}(ℝ^n)) (a : DerivIndex n 1) :
    ℝ^n → ℝ :=
  firstOrderRows (absoluteValueBase U)
    (fun i x ↦
        (SignType.sign
          (((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : ℝ^n → ℝ) x) : ℝ) *
          ((U : WkpAmbientOn n 1 p Set.univ)
            (singleDerivIndex n i) : ℝ^n → ℝ) x)
    a

/-- The base row of `absoluteValueRows` is `absoluteValueBase`. -/
theorem absoluteValueRows_base
    {n : ℕ} {p : ℝ≥0∞}
    (U : W^{1,p}(ℝ^n)) :
    absoluteValueRows U (baseIndex n 1) =
      absoluteValueBase U := by
  simp [absoluteValueRows]

/-- Every row of `absoluteValueRows` lies in `Lp`. -/
theorem absoluteValueRows_memLp
    {n : ℕ} {p : ℝ≥0∞}
    (U : W^{1,p}(ℝ^n)) (a : DerivIndex n 1) :
    MemLp (absoluteValueRows U a) p (domainMeasure n Set.univ) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hbase :
        MemLp
          (((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
          p (domainMeasure n Set.univ) :=
      Lp.memLp _
    simpa [absoluteValueRows, Real.norm_eq_abs] using hbase.norm
  · subst a
    have hbaseMeas :
        AEStronglyMeasurable
          (((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
          (domainMeasure n Set.univ) :=
      (Lp.memLp _).aestronglyMeasurable
    have hcoord :
        MemLp
          (((U : WkpAmbientOn n 1 p Set.univ) (singleDerivIndex n i) :
            DerivLp n p Set.univ) : ℝ^n → ℝ)
          p (domainMeasure n Set.univ) :=
      Lp.memLp _
    apply MemLp.of_le_mul hcoord
    · rw [absoluteValueRows, firstOrderRows_singleDerivIndex]
      exact
        (aestronglyMeasurable_sign_comp hbaseMeas).mul
          hcoord.aestronglyMeasurable
    · filter_upwards [] with x
      rw [absoluteValueRows, firstOrderRows_singleDerivIndex, Real.norm_eq_abs,
        abs_mul, one_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (PDE.Analysis.Calculus.abs_coe_sign_le_one
          (((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : ℝ^n → ℝ) x))

/-- Each row of `absoluteValueRows` is the corresponding weak derivative of
`absoluteValueBase` on the whole space. -/
theorem absoluteValueRows_weak
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n))
    (a : DerivIndex n 1) :
    HasWeakDerivativeOn (n := n) Set.univ a.toList
      (absoluteValueBase U)
      (absoluteValueRows U a) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hloc :=
      memLp_locallyIntegrableOn_domain
        (absoluteValueRows_memLp U (baseIndex n 1))
        (Fact.out : (1 : ℝ≥0∞) ≤ p)
    have hloc' :
        LocallyIntegrableOn (absoluteValueBase U) Set.univ
          (volume : Measure (ℝ^n)) := by
      simpa [absoluteValueRows] using hloc
    simpa [absoluteValueRows, iteratedPartialDeriv] using
      (show HasWeakDerivativeOn (n := n) Set.univ []
          (absoluteValueBase U)
          (absoluteValueBase U) from
        hasWeakDerivativeOn_nil hloc')
  · subst a
    simpa [absoluteValueRows] using hasWeakDerivativeOn_abs U i

/-- Absolute value as an operation on global `W^{1,p}`. -/
noncomputable def absoluteValue
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) :
    W^{1,p}(ℝ^n) :=
  mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 1) (p := p) (Ω := Set.univ)
    (absoluteValueBase U)
    (absoluteValueRows U)
    (absoluteValueRows_base U)
    (absoluteValueRows_memLp U)
    (absoluteValueRows_weak U)

/-- The base coordinate of `absoluteValue U` is `|u|` almost
everywhere. -/
theorem absoluteValue_base_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) :
    (((absoluteValue U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          |((U : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : ℝ^n → ℝ) x| := by
  simpa [absoluteValue, absoluteValueRows_base] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := p) (Ω := Set.univ)
      (absoluteValueBase U)
      (absoluteValueRows U)
      (absoluteValueRows_base U)
      (absoluteValueRows_memLp U)
      (absoluteValueRows_weak U)
      (baseIndex n 1)

/-- The `i`th weak derivative of `absoluteValue U` is
`sign(u) ∂ᵢu` almost everywhere. -/
theorem absoluteValue_derivative_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((absoluteValue U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          (SignType.sign
            (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) : ℝ) *
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x := by
  simpa [absoluteValue, absoluteValueRows] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := p) (Ω := Set.univ)
      (absoluteValueBase U)
      (absoluteValueRows U)
      (absoluteValueRows_base U)
      (absoluteValueRows_memLp U)
      (absoluteValueRows_weak U)
      (singleDerivIndex n i)

/-- Positive part as an operation on global `W^{1,p}`. -/
noncomputable def positivePart
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) :
    W^{1,p}(ℝ^n) :=
  (1 / 2 : ℝ) • (U + absoluteValue U)

/-- The base coordinate of `positivePart U` is `max u 0` almost
everywhere. -/
theorem positivePart_base_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) :
    (((positivePart U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          posPart
            (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul (1 / 2 : ℝ)
      (((U + absoluteValue U :
        W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
        (baseIndex n 1)),
    MeasureTheory.Lp.coeFn_add
      ((U : WkpAmbientOn n 1 p Set.univ) (baseIndex n 1))
      ((absoluteValue U : WkpAmbientOn n 1 p Set.univ)
        (baseIndex n 1)),
    absoluteValue_base_ae U] with x hsmul hadd habs
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  simp only [Pi.add_apply] at hadd
  rw [habs] at hadd
  change
    ((((U + absoluteValue U :
      W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        _ at hadd
  change
    (((positivePart U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
      _
  rw [show
    (((positivePart U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        (1 / 2 : ℝ) *
          (((U + absoluteValue U :
            W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : ℝ^n → ℝ) x by
      simpa [positivePart] using hsmul]
  rw [hadd]
  have hpos := add_abs_eq_two_nsmul_posPart
    (((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ) x)
  rw [two_nsmul] at hpos
  linarith

/-- The `i`th weak derivative of `positivePart U` is
`((1 + sign u) / 2) ∂ᵢu` almost everywhere. -/
theorem positivePart_derivative_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((positivePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          ((1 + (SignType.sign
            (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) : ℝ)) / 2) *
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul (1 / 2 : ℝ)
      (((U + absoluteValue U :
        W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i)),
    MeasureTheory.Lp.coeFn_add
      ((U : WkpAmbientOn n 1 p Set.univ) (singleDerivIndex n i))
      ((absoluteValue U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i)),
    absoluteValue_derivative_ae U i] with x hsmul hadd habs
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  simp only [Pi.add_apply] at hadd
  rw [habs] at hadd
  change
    ((((U + absoluteValue U :
      W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        _ at hadd
  change
    (((positivePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
      _
  rw [show
    (((positivePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        (1 / 2 : ℝ) *
          (((U + absoluteValue U :
            W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
            (singleDerivIndex n i) : ℝ^n → ℝ) x by
      simpa [positivePart] using hsmul]
  rw [hadd]
  ring

/-- Negative part as an operation on global `W^{1,p}`. -/
noncomputable def negativePart
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) :
    W^{1,p}(ℝ^n) :=
  (1 / 2 : ℝ) • (absoluteValue U - U)

/-- The base coordinate of `negativePart U` is `max (-u) 0` almost
everywhere. -/
theorem negativePart_base_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) :
    (((negativePart U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          negPart
            (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul (1 / 2 : ℝ)
      (((absoluteValue U - U :
        W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
        (baseIndex n 1)),
    MeasureTheory.Lp.coeFn_sub
      ((absoluteValue U : WkpAmbientOn n 1 p Set.univ)
        (baseIndex n 1))
      ((U : WkpAmbientOn n 1 p Set.univ) (baseIndex n 1)),
    absoluteValue_base_ae U] with x hsmul hsub habs
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  simp only [Pi.sub_apply] at hsub
  rw [habs] at hsub
  change
    ((((absoluteValue U - U :
      W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        _ at hsub
  change
    (((negativePart U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
      _
  rw [show
    (((negativePart U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        (1 / 2 : ℝ) *
          (((absoluteValue U - U :
            W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
            (baseIndex n 1) : ℝ^n → ℝ) x by
      simpa [negativePart] using hsmul]
  rw [hsub]
  have hneg := abs_sub_eq_two_nsmul_negPart
    (((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ) x)
  rw [two_nsmul] at hneg
  linarith

/-- The `i`th weak derivative of `negativePart U` is
`((sign u - 1) / 2) ∂ᵢu` almost everywhere. -/
theorem negativePart_derivative_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((negativePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          (((SignType.sign
            (((U : WkpAmbientOn n 1 p Set.univ)
              (baseIndex n 1) : ℝ^n → ℝ) x) : ℝ) - 1) / 2) *
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul (1 / 2 : ℝ)
      (((absoluteValue U - U :
        W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i)),
    MeasureTheory.Lp.coeFn_sub
      ((absoluteValue U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i))
      ((U : WkpAmbientOn n 1 p Set.univ) (singleDerivIndex n i)),
    absoluteValue_derivative_ae U i] with x hsmul hsub habs
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  simp only [Pi.sub_apply] at hsub
  rw [habs] at hsub
  change
    ((((absoluteValue U - U :
      W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        _ at hsub
  change
    (((negativePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
      _
  rw [show
    (((negativePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        (1 / 2 : ℝ) *
          (((absoluteValue U - U :
            W^{1,p}(ℝ^n)) : WkpAmbientOn n 1 p Set.univ)
            (singleDerivIndex n i) : ℝ^n → ℝ) x by
      simpa [negativePart] using hsmul]
  rw [hsub]
  ring

/-- Every first weak derivative of `U` vanishes almost everywhere on the
zero set of its base coordinate. This is the multidimensional Stampacchia
level-set theorem at level zero. -/
theorem derivative_eq_zero_ae_of_base_eq_zero
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    let u : ℝ^n → ℝ :=
      ((U : WkpAmbientOn n 1 p Set.univ)
        (baseIndex n 1) : ℝ^n → ℝ)
    let du : ℝ^n → ℝ :=
      ((U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i) : ℝ^n → ℝ)
    ∀ᵐ x ∂domainMeasure n Set.univ, u x = 0 → du x = 0 := by
  let u : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ)
  let du : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : ℝ^n → ℝ)
  let V : W^{1,p}(ℝ^n) := positivePart U
  let v : ℝ^n → ℝ :=
    ((V : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ)
  let dv : ℝ^n → ℝ :=
    ((V : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : ℝ^n → ℝ)
  have hVweak :
      HasWeakDerivativeOn (n := n) Set.univ [i] v dv := by
    simpa [v, dv, firstDerivIndex_one] using
      V.property.hasWeakDerivativeOn_first (by norm_num) i
  have hvNonneg :
      ∀ᵐ x ∂domainMeasure n Set.univ, 0 ≤ v x := by
    filter_upwards [positivePart_base_ae U] with x hx
    rw [show v x =
      posPart (u x) by
        simpa [v, V, u] using hx]
    exact posPart_nonneg _
  have hvAbs :
      (fun x ↦ |v x|) =ᵐ[domainMeasure n Set.univ] v := by
    filter_upwards [hvNonneg] with x hx
    exact abs_of_nonneg hx
  have habsWeak :
      HasWeakDerivativeOn (n := n) Set.univ [i] v
        (fun x ↦ (SignType.sign (v x) : ℝ) * dv x) := by
    apply
      (hasWeakDerivativeOn_congr_ae
        (n := n) hvAbs (Filter.EventuallyEq.rfl)).mp
    simpa [v, dv] using hasWeakDerivativeOn_abs V i
  have hdv := hVweak.unique_ae isOpen_univ habsWeak
  filter_upwards [
    hdv,
    positivePart_base_ae U,
    positivePart_derivative_ae U i] with x hdv hbase hderiv
  intro hu
  have hu' : u x = 0 := by
    simpa [u] using hu
  have hv0 : v x = 0 := by
    rw [show v x =
      posPart (u x) by
        simpa [v, V, u] using hbase,
      hu']
    simp
  have hdv0 : dv x = 0 := by
    simpa [hv0] using hdv
  have hhalf : dv x = (1 / 2 : ℝ) * du x := by
    rw [show dv x =
      ((1 + (SignType.sign (u x) : ℝ)) / 2) * du x by
        simpa [dv, V, u, du] using hderiv,
      hu']
    norm_num
  linarith

/-- Every first weak derivative of `U` vanishes almost everywhere on each
level set of its base coordinate. -/
theorem derivative_eq_zero_ae_of_base_eq
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) (i : Fin n) (c : ℝ) :
    let u : ℝ^n → ℝ :=
      ((U : WkpAmbientOn n 1 p Set.univ)
        (baseIndex n 1) : ℝ^n → ℝ)
    let du : ℝ^n → ℝ :=
      ((U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i) : ℝ^n → ℝ)
    ∀ᵐ x ∂domainMeasure n Set.univ, u x = c → du x = 0 := by
  by_cases hc : c = 0
  · subst c
    exact derivative_eq_zero_ae_of_base_eq_zero U i
  let u : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ)
  let du : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : ℝ^n → ℝ)
  let V : W^{1,p}(ℝ^n) :=
    smoothComposition
      ((PDE.Analysis.Calculus.contDiff_smoothLevelProbe c).of_le
        (by simp))
      (PDE.Analysis.Calculus.hasDerivAt_smoothLevelProbe c)
      (PDE.Analysis.Calculus.smoothLevelProbe_zero c)
      (PDE.Analysis.Calculus.abs_smoothLevelProbeSlope_le_one c)
      U
  let v : ℝ^n → ℝ :=
    ((V : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ)
  let dv : ℝ^n → ℝ :=
    ((V : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : ℝ^n → ℝ)
  have hbase :
      v =ᵐ[domainMeasure n Set.univ]
        fun x ↦ PDE.Analysis.Calculus.smoothLevelProbe c (u x) := by
    simpa [v, V, u] using
      smoothComposition_base_ae
        ((PDE.Analysis.Calculus.contDiff_smoothLevelProbe c).of_le
          (by simp))
        (PDE.Analysis.Calculus.hasDerivAt_smoothLevelProbe c)
        (PDE.Analysis.Calculus.smoothLevelProbe_zero c)
        (PDE.Analysis.Calculus.abs_smoothLevelProbeSlope_le_one c)
        U
  have hderiv :
      dv =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          PDE.Analysis.Calculus.smoothLevelProbeSlope c (u x) * du x := by
    simpa [dv, V, u, du] using
      smoothComposition_derivative_ae
        ((PDE.Analysis.Calculus.contDiff_smoothLevelProbe c).of_le
          (by simp))
        (PDE.Analysis.Calculus.hasDerivAt_smoothLevelProbe c)
        (PDE.Analysis.Calculus.smoothLevelProbe_zero c)
        (PDE.Analysis.Calculus.abs_smoothLevelProbeSlope_le_one c)
        U i
  filter_upwards [
    derivative_eq_zero_ae_of_base_eq_zero V i,
    hbase, hderiv] with x hzero hbase hderiv
  intro hu
  have hu' : u x = c := by
    simpa [u] using hu
  have hv0 : v x = 0 := by
    rw [hbase, hu']
    exact PDE.Analysis.Calculus.smoothLevelProbe_level c
  have hdv0 : dv x = 0 := hzero hv0
  have hmul :
      PDE.Analysis.Calculus.smoothLevelProbeSlope c c * du x = 0 := by
    calc
      _ = PDE.Analysis.Calculus.smoothLevelProbeSlope c (u x) * du x := by
        rw [hu']
      _ = dv x := hderiv.symm
      _ = 0 := hdv0
  exact
    (mul_eq_zero.mp hmul).resolve_left
      (PDE.Analysis.Calculus.smoothLevelProbeSlope_level_ne_zero hc)

/-- The `i`th weak derivative of the positive part is `∂ᵢu` on `{u > 0}`
and zero elsewhere, almost everywhere. -/
theorem positivePart_derivative_indicator_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((positivePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          if 0 <
              ((U : WkpAmbientOn n 1 p Set.univ)
                (baseIndex n 1) : ℝ^n → ℝ) x then
            ((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x
          else 0 := by
  let u : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ)
  let du : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : ℝ^n → ℝ)
  filter_upwards [
    positivePart_derivative_ae U i,
    derivative_eq_zero_ae_of_base_eq_zero U i] with x hderiv hzero
  change
    (((positivePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
      if 0 < u x then du x else 0
  rcases lt_trichotomy (u x) 0 with hneg | hz | hpos
  · rw [show
      (((positivePart U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        ((1 + (SignType.sign (u x) : ℝ)) / 2) * du x by
          simpa [u, du] using hderiv,
      ite_eq_right (not_lt.mpr (le_of_lt hneg)),
      sign_eq_neg_one_iff.mpr hneg]
    norm_num
  · have hdu : du x = 0 := by
      apply hzero
      simpa [u] using hz
    rw [show
      (((positivePart U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        ((1 + (SignType.sign (u x) : ℝ)) / 2) * du x by
          simpa [u, du] using hderiv,
      ite_eq_right (by simp [hz]),
      hz, hdu]
    norm_num
  · rw [show
      (((positivePart U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        ((1 + (SignType.sign (u x) : ℝ)) / 2) * du x by
          simpa [u, du] using hderiv,
      ite_eq_left hpos,
      sign_eq_one_iff.mpr hpos]
    norm_num

/-- The `i`th weak derivative of the negative part is `-∂ᵢu` on `{u < 0}`
and zero elsewhere, almost everywhere. -/
theorem negativePart_derivative_indicator_ae
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (U : W^{1,p}(ℝ^n)) (i : Fin n) :
    (((negativePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        fun x ↦
          if
              ((U : WkpAmbientOn n 1 p Set.univ)
                (baseIndex n 1) : ℝ^n → ℝ) x < 0 then
            -((U : WkpAmbientOn n 1 p Set.univ)
              (singleDerivIndex n i) : ℝ^n → ℝ) x
          else 0 := by
  let u : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (baseIndex n 1) : ℝ^n → ℝ)
  let du : ℝ^n → ℝ :=
    ((U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : ℝ^n → ℝ)
  filter_upwards [
    negativePart_derivative_ae U i,
    derivative_eq_zero_ae_of_base_eq_zero U i] with x hderiv hzero
  change
    (((negativePart U : WkpAmbientOn n 1 p Set.univ)
      (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
      if u x < 0 then -du x else 0
  rcases lt_trichotomy (u x) 0 with hneg | hz | hpos
  · rw [show
      (((negativePart U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        (((SignType.sign (u x) : ℝ) - 1) / 2) * du x by
          simpa [u, du] using hderiv,
      ite_eq_left hneg,
      sign_eq_neg_one_iff.mpr hneg,
      SignType.coe_neg_one]
    ring
  · have hdu : du x = 0 := by
      apply hzero
      simpa [u] using hz
    rw [show
      (((negativePart U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        (((SignType.sign (u x) : ℝ) - 1) / 2) * du x by
          simpa [u, du] using hderiv,
      ite_eq_right (by simp [hz]),
      hz, hdu]
    norm_num
  · rw [show
      (((negativePart U : WkpAmbientOn n 1 p Set.univ)
        (singleDerivIndex n i) : DerivLp n p Set.univ) : ℝ^n → ℝ) x =
        (((SignType.sign (u x) : ℝ) - 1) / 2) * du x by
          simpa [u, du] using hderiv,
      ite_eq_right (not_lt.mpr (le_of_lt hpos)),
      sign_eq_one_iff.mpr hpos,
      SignType.coe_one]
    ring

end SobolevSpace.GraphSpace
