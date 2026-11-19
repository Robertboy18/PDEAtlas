/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.TangentialDifferenceQuotient
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Elliptic.Regularity.Boundary.H2.TangentialCommutator
import PDE.Elliptic.Regularity.Boundary.H2.TangentialTest
import PDE.Elliptic.Regularity.Interior.DifferenceQuotientEnergy.ScalarEstimates
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Boundary regularity: tangential energy estimates

The quantitative core of boundary `H²` regularity on the flattened half-space
`Ω⁺ = {xₙ > 0}`. Let `u ∈ H¹₀(Ω⁺)` be a weak solution of

`-∂ᵢ(aᵢⱼ ∂ⱼ u) = f` in `Ω⁺`

with `aᵢⱼ ∈ L∞` uniformly elliptic with constant `α`, each `aᵢⱼ` having a
Lipschitz representative with constant `Cᵢⱼ`, and `f ∈ L²(Ω⁺)`. Testing the
equation with the signed backward tangential quotient `-Dₖ⁻ʰ(Dₖʰ u)`
(`k ≠ n`) and integrating by parts discretely produces a translated elliptic
energy plus a coefficient commutator. Ellipticity, the Lipschitz commutator
bound and Young's inequality then give the step-independent estimate

`(α/2) ∑ᵢ ‖Dₖʰ ∂ᵢ u‖² ≤ (∑ᵢ (∑ⱼ Cᵢⱼ ‖∂ⱼ u‖)²)/α + ‖f‖²/α + (α/4) ‖u‖²_{H¹₀}`

for every `h ≠ 0`. The `L²` difference-quotient compactness criterion then
yields the tangential second weak derivatives `∂ₖ ∂ᵢ u ∈ L²(Ω⁺)`.

## Main results

* `inner_tangentialDifferenceQuotientL2_left`: discrete integration by parts
  on `L²(Ω⁺)`.
* `tangentialPrincipal_energyBalance`: the exact energy identity for the
  principal part with the coefficient commutator isolated.
* `aeUniformlyElliptic_tangentialTranslateLp`,
  `tangentialPrincipal_coercive_energy_le`: ellipticity survives tangential
  translation and gives coercivity of the translated principal term.
* `tangentialDifferenceQuotient_gradient_energy_le`: the uniform tangential
  estimate displayed above.
* `tangentialSecondWeakDerivative.exists_with_norm`,
  `tangentialSecondWeakDerivative.exists`: existence of every tangential
  second weak derivative `∂ₖ ∂ᵢ u` in `L²(Ω⁺)`, with and without the
  quantitative bound.

## Implementation notes

The normal direction is `PDE.Common.lastIndex`; tangential means
`k ≠ lastIndex`. The coefficients enter twice, as the `L∞` classes `A i j`
used in the weak equation and as Lipschitz functions `a i j` agreeing with
them almost everywhere; this is how the commutator bound is stated without a
Sobolev structure on `L∞`. The second derivatives are first produced on `ℝ^n`
for the zero extension of `∂ᵢ u` and then restricted.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity) and steps 3-4 of
  its proof, (46)-(51), pp. 334-336.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 8 (Generalized Solutions and Regularity),
  pp. 177-218.
  <https://doi.org/10.1007/978-3-642-61798-0_8>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- Elementary `L²` bound for a tangential difference quotient. -/
theorem tangentialDifferenceQuotientL2.norm_le
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ) (u : DerivLp n 2 (HalfSpace.upper n)) :
    ‖tangentialDifferenceQuotientLp 2 k hk h u‖ ≤
      2 * |h|⁻¹ * ‖u‖ := by
  simp only [tangentialDifferenceQuotientLp]
  rw [norm_smul,
    Real.norm_eq_abs, abs_inv]
  calc
    |h|⁻¹ * ‖tangentialTranslateLp 2 k hk h u - u‖ ≤
        |h|⁻¹ *
          (‖tangentialTranslateLp 2 k hk h u‖ + ‖u‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _)
        (inv_nonneg.mpr (abs_nonneg h))
    _ = 2 * |h|⁻¹ * ‖u‖ := by
      rw [tangentialTranslateLp.norm 2]
      ring

/-- Discrete integration by parts for tangential difference quotients on
the upper half-space.  This is the exact boundary analogue of Evans'
whole-space difference-quotient identity. -/
theorem inner_tangentialDifferenceQuotientL2_left
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0)
    (u v : DerivLp n 2 (HalfSpace.upper n)) :
    inner ℝ (tangentialDifferenceQuotientLp 2 k hk h u) v =
      -inner ℝ u (tangentialDifferenceQuotientLp 2 k hk (-h) v) := by
  simp only [tangentialDifferenceQuotientLp]
  rw [
    real_inner_smul_left, inner_sub_left,
    inner_tangentialTranslateL2_left,
    real_inner_smul_right, inner_sub_right]
  field_simp

/-- Move a signed backward tangential quotient from the test factor onto the
flux as a forward quotient. -/
theorem inner_neg_tangentialBackwardDifference_eq
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0)
    (flux w : DerivLp n 2 (HalfSpace.upper n)) :
    inner ℝ flux (-tangentialDifferenceQuotientLp 2 k hk (-h) w) =
      inner ℝ (tangentialDifferenceQuotientLp 2 k hk h flux) w := by
  rw [inner_neg_right]
  exact (inner_tangentialDifferenceQuotientL2_left
    k hk hh flux w).symm

/-- Tangential principal-part energy identity.  Testing the flattened
weak equation with the signed backward quotient and applying discrete
integration by parts produces a translated elliptic energy plus the exact
coefficient commutator.  This is the algebraic center of Evans §6.3.2. -/
theorem tangentialPrincipal_energyBalance
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0)
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (du : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i j • du j)
          (-tangentialDifferenceQuotientLp 2 k hk (-h)
            (tangentialDifferenceQuotientLp 2 k hk h (du i)))) =
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ
          (tangentialTranslateLp ∞ k hk h (A i j) •
            tangentialDifferenceQuotientLp 2 k hk h (du j))
          (tangentialDifferenceQuotientLp 2 k hk h (du i))) +
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ
          (tangentialDifferenceQuotientLp ∞ k hk h (A i j) • du j)
          (tangentialDifferenceQuotientLp 2 k hk h (du i)) := by
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i j • du j)
          (-tangentialDifferenceQuotientLp 2 k hk (-h)
            (tangentialDifferenceQuotientLp 2 k hk h (du i)))) =
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ
          (tangentialDifferenceQuotientLp 2 k hk h (A i j • du j))
          (tangentialDifferenceQuotientLp 2 k hk h (du i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact inner_neg_tangentialBackwardDifference_eq
        k hk hh (A i j • du j)
          (tangentialDifferenceQuotientLp 2 k hk h (du i))
    _ = ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ
          (tangentialTranslateLp ∞ k hk h (A i j) •
              tangentialDifferenceQuotientLp 2 k hk h (du j) +
            tangentialDifferenceQuotientLp ∞ k hk h (A i j) • du j)
          (tangentialDifferenceQuotientLp 2 k hk h (du i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [tangentialDifferenceQuotientL2_lpSMul]
    _ = _ := by
      simp only [inner_add_left, Finset.sum_add_distrib]

/-- Almost-everywhere ellipticity is preserved by a common tangential
translation of every coefficient entry. -/
theorem aeUniformlyElliptic_tangentialTranslateLp
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ) :
    AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦ tangentialTranslateLp ∞ k hk h (A i j)) alpha := by
  refine ⟨hA.1, ?_⟩
  have hell :
      ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), ∀ ξ : Fin n → ℝ,
        alpha * ∑ i : Fin n, ξ i * ξ i ≤
          ∑ i : Fin n, ∑ j : Fin n,
            A i j (x + DifferenceQuotient.coordinateStep k h) * ξ j * ξ i := by
    simpa [Function.comp_def,
      SobolevSpace.GraphSpace.Rellich.translationContinuousMap] using
      (tangentialTranslation_measurePreserving k hk h).quasiMeasurePreserving.tendsto_ae.eventually
        hA.2
  have hcoeff :
      ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), ∀ i j : Fin n,
        tangentialTranslateLp ∞ k hk h (A i j) x =
          A i j (x + DifferenceQuotient.coordinateStep k h) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    exact tangentialTranslateLp.apply_ae ∞ k hk h (A i j)
  filter_upwards [hell, hcoeff] with x hx hcx
  intro ξ
  simpa only [hcx] using hx ξ

/-- Integrated coercivity of the translated coefficient matrix for an
arbitrary `L²` vector field on the flattened half-space. -/
theorem tangentialTranslatedCoefficient_energy_le
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (v : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    alpha * ∑ i : Fin n, inner ℝ (v i) (v i) ≤
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ
          (tangentialTranslateLp ∞ k hk h (A i j) • v j) (v i) := by
  simpa only [multiplicationCoefficientOperator_apply] using
    aeUniformlyElliptic_energy_le
      (n := n) (Ω := HalfSpace.upper n)
      (fun i j ↦ tangentialTranslateLp ∞ k hk h (A i j))
      (aeUniformlyElliptic_tangentialTranslateLp A hA k hk h) v

/-- Coercive form of the tangential energy balance.  The translated
principal matrix controls all tangential quotients of the gradient; the
coefficient commutator is isolated as the sole principal-part error. -/
theorem tangentialPrincipal_coercive_energy_le
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0)
    (du : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    alpha * ∑ i : Fin n,
        inner ℝ
          (tangentialDifferenceQuotientLp 2 k hk h (du i))
          (tangentialDifferenceQuotientLp 2 k hk h (du i)) ≤
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i j • du j)
          (-tangentialDifferenceQuotientLp 2 k hk (-h)
            (tangentialDifferenceQuotientLp 2 k hk h (du i)))) -
      ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ
          (tangentialDifferenceQuotientLp ∞ k hk h (A i j) • du j)
          (tangentialDifferenceQuotientLp 2 k hk h (du i)) := by
  let v : Fin n → DerivLp n 2 (HalfSpace.upper n) := fun i ↦
    tangentialDifferenceQuotientLp 2 k hk h (du i)
  have hcoercive := tangentialTranslatedCoefficient_energy_le
    A hA k hk h v
  have hbalance := tangentialPrincipal_energyBalance k hk hh A du
  change alpha * ∑ i : Fin n, inner ℝ (v i) (v i) ≤ _
  rw [hbalance]
  simpa [v] using hcoercive

/-- The tangential principal estimate after absorbing the Lipschitz
coefficient commutator.  This is the quantitative inequality at the heart
of the boundary difference-quotient argument in Evans §6.3.2. -/
theorem tangentialPrincipal_energy_le_after_commutator
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0)
    (du : Fin n → DerivLp n 2 (HalfSpace.upper n)) :
    (3 * alpha / 4) * ∑ i : Fin n,
        inner ℝ
          (tangentialDifferenceQuotientLp 2 k hk h (du i))
          (tangentialDifferenceQuotientLp 2 k hk h (du i)) ≤
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i j • du j)
          (-tangentialDifferenceQuotientLp 2 k hk (-h)
            (tangentialDifferenceQuotientLp 2 k hk h (du i)))) +
      ∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) * ‖du j‖) ^ 2 / alpha := by
  let q : Fin n → DerivLp n 2 (HalfSpace.upper n) := fun i ↦
    tangentialDifferenceQuotientLp 2 k hk h (du i)
  let principal : ℝ := ∑ i : Fin n, ∑ j : Fin n,
    inner ℝ (A i j • du j)
      (-tangentialDifferenceQuotientLp 2 k hk (-h) (q i))
  let commutator : ℝ := ∑ i : Fin n, ∑ j : Fin n,
    inner ℝ
      (tangentialDifferenceQuotientLp ∞ k hk h (A i j) • du j)
      (q i)
  let lower : ℝ := ∑ i : Fin n,
    (∑ j : Fin n, (C i j : ℝ) * ‖du j‖) ^ 2 / alpha
  have hcoercive :
      alpha * ∑ i : Fin n, inner ℝ (q i) (q i) ≤
        principal - commutator := by
    simpa [q, principal, commutator] using
      tangentialPrincipal_coercive_energy_le A hA k hk hh du
  have hcommutator :
      |commutator| ≤ lower +
        (alpha / 4) * ∑ i : Fin n, inner ℝ (q i) (q i) := by
    simpa only [commutator, lower, sum_inner,
      real_inner_self_eq_norm_sq] using
      (tangentialCoefficientCommutatorL2.abs_sum_inner_le_young
        k hk A a C haLip haRep h hh du q halpha)
  have hcommutatorLower : -commutator ≤ lower +
      (alpha / 4) * ∑ i : Fin n, inner ℝ (q i) (q i) :=
    (neg_le_abs commutator).trans hcommutator
  change (3 * alpha / 4) * ∑ i : Fin n, inner ℝ (q i) (q i) ≤
    principal + lower
  nlinarith

/-- Uniform tangential boundary estimate.  For a weak solution on the
flattened half-space, every nonzero tangential step controls the complete
quotient of the gradient with a bound independent of the step size.  Both
the coefficient commutator and the forcing term have been absorbed, leaving
one half of the elliptic energy on the left. -/
theorem tangentialDifferenceQuotient_gradient_energy_le
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0) :
    (alpha / 2) * ∑ i : Fin n,
        ‖tangentialDifferenceQuotientLp 2 k hk h
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u)‖ ^ 2 ≤
      (∑ i : Fin n,
        (∑ j : Fin n, (C i j : ℝ) *
          ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u‖) ^ 2 / alpha) +
      ‖f‖ ^ 2 / alpha + (alpha / 4) * ‖u‖ ^ 2 := by
  let du : Fin n → DerivLp n 2 (HalfSpace.upper n) := fun i ↦
    derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u
  let energy : ℝ := ∑ i : Fin n,
    ‖tangentialDifferenceQuotientLp 2 k hk h (du i)‖ ^ 2
  let lower : ℝ := ∑ i : Fin n,
    (∑ j : Fin n, (C i j : ℝ) * ‖du j‖) ^ 2 / alpha
  let principal : ℝ := ∑ i : Fin n, ∑ j : Fin n,
    inner ℝ (A i j • du j)
      (-tangentialDifferenceQuotientLp 2 k hk (-h)
        (tangentialDifferenceQuotientLp 2 k hk h (du i)))
  let source : ℝ := inner ℝ f
    (baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
      (signedBackwardTangentialTestH10 k hk h u))
  have hprincipal : (3 * alpha / 4) * energy ≤ principal + lower := by
    simpa only [du, energy, lower, principal,
      real_inner_self_eq_norm_sq] using
      (tangentialPrincipal_energy_le_after_commutator
        A a C haLip haRep hA halpha k hk hh du)
  have hweak : principal = source := by
    have hw := weakDivergence_multiplication_signedBackwardTangential
      A f u hu k hk h
    simpa only [principal, source, du,
      baseCoord_signedBackwardTangentialTestH10] using hw
  have hsourceAbs :
      |source| ≤ ‖f‖ ^ 2 / alpha + (alpha / 4) * (‖u‖ ^ 2 + energy) := by
    simpa only [source, energy, du] using
      (abs_source_pairing_signedBackwardTangentialTestH10_le_young
        f k hk hh u halpha)
  have hsource :
      source ≤ ‖f‖ ^ 2 / alpha + (alpha / 4) * (‖u‖ ^ 2 + energy) :=
    (le_abs_self source).trans hsourceAbs
  change (alpha / 2) * energy ≤ lower + ‖f‖ ^ 2 / alpha +
    (alpha / 4) * ‖u‖ ^ 2
  rw [hweak] at hprincipal
  nlinarith

/-!
## Tangential second derivatives and cross-flux recovery

Evans' boundary `H²` proof first estimates tangential difference quotients of
the gradient in the flattened half-space.  Compactness of bounded difference
quotients gives tangential second derivatives.  Commutation of weak mixed
derivatives turns these into the normal derivatives of tangential gradient
components, and the product rule then differentiates the non-normal terms in a
flux row.  The normal-normal derivative is recovered later from the weak
divergence equation.
-/

/-- Each component of the tangential gradient quotient satisfies the same
step-independent bound after zero extension to the whole space.  This is the
quantitative input required by the `L²` difference-quotient compactness
criterion. -/
theorem norm_zeroExtend_tangentialGradientQuotient_le
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (i : Fin n) {h : ℝ} (hh : h ≠ 0) :
    ‖DifferenceQuotient.differenceQuotientLp 2 k h
      (Extension.Lp.zeroExtendLp
        (n := n) (p := 2) (Ω := HalfSpace.upper n)
        (HalfSpace.measurableSet_upper (n := n))
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u))‖ ≤
      Real.sqrt (((∑ r : Fin n,
          (∑ j : Fin n, (C r j : ℝ) *
            ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u‖) ^ 2 / alpha) +
        ‖f‖ ^ 2 / alpha + (alpha / 4) * ‖u‖ ^ 2) / (alpha / 2)) := by
  rw [tangentialDifferenceQuotientL2.norm_zeroExtend_eq k hk h]
  exact norm_component_le_sqrt_of_weighted_energy
    (fun r : Fin n ↦
      tangentialDifferenceQuotientLp 2 k hk h
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) r u))
    i (div_pos halpha (by norm_num))
    (tangentialDifferenceQuotient_gradient_energy_le
      A a C haLip haRep hA halpha f u hu k hk hh)

/-- Tangential weak second derivatives at a flattened boundary.  Every
tangential derivative of every first weak derivative exists in `L²`.  The
derivative is first produced on the whole space for the zero extension; this
is the compactness endpoint of Evans' boundary difference-quotient estimate.
-/
theorem tangentialSecondWeakDerivative.exists_global_with_norm
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (i : Fin n) :
    ∃ g : DerivLp n 2 Set.univ,
      ‖g‖ ≤ Real.sqrt (((∑ r : Fin n,
          (∑ j : Fin n, (C r j : ℝ) *
            ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u‖) ^ 2 / alpha) +
        ‖f‖ ^ 2 / alpha + (alpha / 4) * ‖u‖ ^ 2) / (alpha / 2)) ∧
      HasWeakDerivativeOn (n := n) Set.univ [k]
        ((Extension.Lp.zeroExtendLp
          (n := n) (p := 2) (Ω := HalfSpace.upper n)
          (HalfSpace.measurableSet_upper (n := n))
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u) :
            DerivLp n 2 Set.univ) : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  let step : ℕ → ℝ := DifferenceQuotient.collarStep 1
  have hstepZero : Filter.Tendsto step Filter.atTop (nhds 0) := by
    simpa [step] using DifferenceQuotient.tendsto_collarStep_zero (1 : ℝ)
  have hstepNe (m : ℕ) : step m ≠ 0 := by
    exact DifferenceQuotient.collarStep_ne_zero (by norm_num) m
  apply DifferenceQuotient.exists_L2_weakDerivative_of_bounded_differenceQuotients_with_norm
    k step hstepZero hstepNe
  intro m
  exact norm_zeroExtend_tangentialGradientQuotient_le
    A a C haLip haRep hA halpha f u hu k hk i (hstepNe m)

/-- Every tangential derivative of every first derivative exists locally on
the flattened half-space, with the same quantitative bound as its
whole-space zero extension. -/
theorem tangentialSecondWeakDerivative.exists_with_norm
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (i : Fin n) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤ Real.sqrt (((∑ r : Fin n,
          (∑ j : Fin n, (C r j : ℝ) *
            ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u‖) ^ 2 / alpha) +
        ‖f‖ ^ 2 / alpha + (alpha / 4) * ‖u‖ ^ 2) / (alpha / 2)) ∧
        HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [k]
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  obtain ⟨G, hGnorm, hG⟩ :=
    tangentialSecondWeakDerivative.exists_global_with_norm
      A a C haLip haRep hA halpha f u hu k hk i
  obtain ⟨g, hgNorm, hg⟩ :=
    exists_restrictedWeakDerivative_of_zeroExtend_with_norm
      (HalfSpace.measurableSet_upper (n := n)) k
      (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u) G hG
  exact ⟨g, hgNorm.trans hGnorm, hg⟩

/-- Qualitative form of tangential second-derivative recovery on the
flattened half-space. -/
theorem tangentialSecondWeakDerivative.exists
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (i : Fin n) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [k]
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  obtain ⟨g, _hgNorm, hg⟩ := tangentialSecondWeakDerivative.exists_with_norm
    A a C haLip haRep hA halpha f u hu k hk i
  exact ⟨g, hg⟩

end GraphSpace.BoundaryRegularity
end SobolevSpace
