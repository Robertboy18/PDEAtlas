/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.ContinuousRepresentatives
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
import PDE.Hyperbolic.WeakWave.EnergyUniqueness.BackwardIdentity

/-!
# Evans backward energy estimates

From the backward identity `½ ‖u_H(σ)‖² + ∫_c^σ B(t)(u, v) dt = 0` of `BackwardIdentity` to the
coercive estimate used for uniqueness in Evans, §7.2.2. Write `B(t) = A(t) + R(t)` with
`A(t)` symmetric and absolutely continuous in time, derivative `Adot(t)`, and `R(t)` of lower
order. Since `v' = -u` and `v(σ) = 0`, the chain rule for the nonautonomous quadratic form gives

`∫_c^σ A(t)(u, v) dt = ½ A(c)(v(c), v(c)) + ½ ∫_c^σ Adot(t)(v, v) dt`,

so the identity becomes an exact energy balance in which `‖u_H(σ)‖²` and `A(c)(v(c), v(c))`
appear with positive sign. Coercivity `κ ‖x‖²_V ≤ A(t)(x, x)`, the bound `|Adot(t)(x, x)| ≤
L_A ‖x‖²_V`, and the mixed bound `|R(t)(x, y)| ≤ L_R ‖J x‖_H ‖y‖_V` then yield

`½ ‖u_H(σ)‖²_H + ½ κ ‖v(c)‖²_V ≤ ½ L_A ∫ ‖v‖²_V + ½ L_R (∫ ‖J u‖²_H + ∫ ‖v‖²_V)`.

The lower-order form is measured in `H × V` rather than `V × V` because the identity controls
`u` only in the pivot norm.

## Main results

* `integrated_waveCoefficientError_le`: the scalar bookkeeping lemma. If the negative parts of
  the principal-variation and lower-order integrands are dominated pointwise by multiples of the
  energy densities, the same holds for the oriented interval integrals.
* `evans_backward_energy_on_subinterval`: the exact energy balance on a restarted interval
  `[c, σ]`, retaining the full `Adot` and `R` contributions.
* `evans_backward_estimate_on_subinterval`: the coercive estimate on `[d, σ]` under the three
  coefficient bounds; Young's inequality is applied only to the mixed `R` term.

## Implementation notes

The three interval-integrability hypotheses on `Adot(v, v)`, `A(u, v)` and `R(u, v)` are the
scalar products needed by the quadratic-form chain rule. In concrete coefficient realizations
they follow from the coefficient bounds and the energy-class membership of `u`; they are kept
as hypotheses so that these theorems do not depend on one set of coefficient hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4, equations (39)-(40).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

namespace IsGelfandWeakWaveSolution

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}
  {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {u : Lp V 2 (volume.restrict (Set.Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
  {acceleration : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q₀ : V} {p₀ : H}
/--
Integrated coefficient-error estimate used in Evans's weak-wave uniqueness
argument.

The functions `principalVariation` and `lowerOrderWork` stand for
`Adot(t)(v(t),v(t))` and `R(t)(u(t),v(t))`.  If their negative parts are
bounded pointwise by the energy densities, monotonicity of the oriented
interval integral gives the corresponding integrated estimate.  This lemma
contains the measure-theoretic bookkeeping only; Young's inequality and the
operator bounds are used by applications to establish `hprincipal` and
`hlower`.
-/
theorem integrated_waveCoefficientError_le
    {principalVariation lowerOrderWork energyDensity kineticDensity : ℝ → ℝ}
    {a s principalConstant lowerConstant : ℝ} (has : a ≤ s)
    (hprincipalIntegrable : IntervalIntegrable principalVariation volume a s)
    (hlowerIntegrable : IntervalIntegrable lowerOrderWork volume a s)
    (henergyIntegrable : IntervalIntegrable energyDensity volume a s)
    (hkineticIntegrable : IntervalIntegrable kineticDensity volume a s)
    (hprincipal : ∀ t ∈ Set.Icc a s, -principalVariation t ≤ principalConstant * energyDensity t)
    (hlower : ∀ t ∈ Set.Icc a s,
      -lowerOrderWork t ≤ lowerConstant * (kineticDensity t + energyDensity t)) :
    -((1 / 2 : ℝ) * (∫ t in a..s, principalVariation t) + (∫ t in a..s, lowerOrderWork t)) ≤
      (1 / 2 : ℝ) * principalConstant * (∫ t in a..s, energyDensity t) +
        lowerConstant * ((∫ t in a..s, kineticDensity t) + (∫ t in a..s, energyDensity t)) := by
  have h1 := intervalIntegral.integral_mono_on has hprincipalIntegrable.neg
    (henergyIntegrable.const_mul principalConstant) hprincipal
  have h2 := intervalIntegral.integral_mono_on has hlowerIntegrable.neg
    ((hkineticIntegrable.add henergyIntegrable).const_mul lowerConstant) hlower
  simp only [Pi.neg_apply] at h1 h2
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at h1
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hkineticIntegrable henergyIntegrable] at h2
  linarith

/--
Exact Evans backward energy identity on a restarted interval `[c,σ]`.

This theorem combines the arbitrary-subinterval form of equation (39) with
the nonautonomous symmetric-form chain rule. It retains the full `Adot` contribution and the
lower-order form `R`.
-/
theorem evans_backward_energy_on_subinterval [CompleteSpace V]
    {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b)
    (Edisplacement : ContinuousPivotEvolutionOn T (fun t ↦ u t)
      (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b)
    (Evelocity : ContinuousPivotEvolutionOn (GelfandTriple.identity V)
      (fun t ↦ rieszVelocityLp T velocity t) (fun t ↦ acceleration t) a b)
    {c σ : ℝ} (hc : c ∈ Set.Icc a b) (hσ : σ ∈ Set.Icc a b) (hcσ : c ≤ σ)
    (hdisplacementC : Edisplacement.representative c = 0)
    (hvelocityC : Evelocity.representative c = 0)
    (hBsplit : ∀ t ∈ Set.uIcc c σ, ∀ x y : V, B t x y = A t x y + R t x y)
    (hAAC : AbsolutelyContinuousOnInterval A c σ)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc c σ), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.uIcc c σ, ∀ x y : V, A t x y = A t y x)
    (hAdotIntegrable : IntervalIntegrable (fun t ↦ Adot t (backwardTimePrimitive (fun r ↦ u r) σ t)
      (backwardTimePrimitive (fun r ↦ u r) σ t)) volume c σ)
    (hAIntegrable :
      IntervalIntegrable (fun t ↦ A t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume c σ)
    (hRIntegrable :
      IntervalIntegrable (fun t ↦ R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume c σ) :
    (1 / 2 : ℝ) * ‖Edisplacement.representative σ‖ ^ 2 +
        (1 / 2 : ℝ) *
          A c (backwardTimePrimitive (fun r ↦ u r) σ c) (backwardTimePrimitive (fun r ↦ u r) σ c) +
        (1 / 2 : ℝ) * (∫ t in c..σ, Adot t (backwardTimePrimitive (fun r ↦ u r) σ t)
          (backwardTimePrimitive (fun r ↦ u r) σ t)) +
        (∫ t in c..σ, R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) = 0 := by
  have hbackward := h.homogeneous_backward_identity_on_subinterval hab Edisplacement Evelocity hc
    hσ hcσ hdisplacementC hvelocityC
  rw [intervalIntegral.integral_congr (g := fun t ↦
      A t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t) +
        R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t))
      (fun t ht ↦ hBsplit t ht _ _), intervalIntegral.integral_add hAIntegrable hRIntegrable,
    integral_symmetric_form_backwardTimePrimitive (A := A) (Adot := Adot) (u := fun t ↦ u t) hAAC
      hAderiv hAsymm ((intervalIntegrable_coeFn_L2_restrict_Ioc u hab.le).mono_set
        (uIcc_subset_uIcc (Icc_subset_uIcc hc) (Icc_subset_uIcc hσ))) hAdotIntegrable
      hAIntegrable] at hbackward
  linarith

/--
Evans's coercive backward estimate (40) on an arbitrary restarted interval.

Three coefficient bounds control the energy: coercivity of the symmetric
principal form, a quadratic bound for its time derivative, and an `H × V`
bound for the lower-order part. Young's inequality is applied only to the
last mixed term.
-/
theorem evans_backward_estimate_on_subinterval [CompleteSpace V]
    {A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V}
    (h : IsGelfandWeakWaveSolution T B 0 u velocity acceleration 0 0) (hab : a < b)
    (Edisplacement : ContinuousPivotEvolutionOn T (fun t ↦ u t)
      (fun t ↦ T.pivotToDual.compLpL 2 (volume.restrict (Set.Ioc a b)) velocity t) a b)
    (Evelocity : ContinuousPivotEvolutionOn (GelfandTriple.identity V)
      (fun t ↦ rieszVelocityLp T velocity t) (fun t ↦ acceleration t) a b)
    {d σ : ℝ} (hd : d ∈ Set.Icc a b) (hσ : σ ∈ Set.Icc a b) (hdσ : d ≤ σ)
    (hdisplacementD : Edisplacement.representative d = 0)
    (hvelocityD : Evelocity.representative d = 0)
    (hBsplit : ∀ t ∈ Set.uIcc d σ, ∀ x y : V, B t x y = A t x y + R t x y)
    (hAAC : AbsolutelyContinuousOnInterval A d σ)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc d σ), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.uIcc d σ, ∀ x y : V, A t x y = A t y x)
    (hAdotIntegrable : IntervalIntegrable (fun t ↦ Adot t (backwardTimePrimitive (fun r ↦ u r) σ t)
      (backwardTimePrimitive (fun r ↦ u r) σ t)) volume d σ)
    (hAIntegrable :
      IntervalIntegrable (fun t ↦ A t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume d σ)
    (hRIntegrable :
      IntervalIntegrable (fun t ↦ R t (u t) (backwardTimePrimitive (fun r ↦ u r) σ t)) volume d σ)
    (κ LA LR : ℝ) (hLR : 0 ≤ LR)
    (hcoercive : ∀ t ∈ Set.uIcc d σ, ∀ x : V, κ * ‖x‖ ^ 2 ≤ A t x x)
    (hAdotBound : ∀ t ∈ Set.uIcc d σ, ∀ x : V, |Adot t x x| ≤ LA * ‖x‖ ^ 2)
    (hRBound : ∀ t ∈ Set.uIcc d σ, ∀ x y : V, |R t x y| ≤ LR * ‖T.inclusion x‖ * ‖y‖) :
    (1 / 2 : ℝ) * ‖Edisplacement.representative σ‖ ^ 2 +
        (1 / 2 : ℝ) * κ * ‖backwardTimePrimitive (fun r ↦ u r) σ d‖ ^ 2 ≤
      (1 / 2 : ℝ) * LA * (∫ t in d..σ, ‖backwardTimePrimitive (fun r ↦ u r) σ t‖ ^ 2) +
        (1 / 2 : ℝ) * LR * ((∫ t in d..σ, ‖T.inclusion (u t)‖ ^ 2) +
          (∫ t in d..σ, ‖backwardTimePrimitive (fun r ↦ u r) σ t‖ ^ 2)) := by
  have hidentity := h.evans_backward_energy_on_subinterval hab Edisplacement Evelocity hd hσ hdσ
    hdisplacementD hvelocityD hBsplit hAAC hAderiv hAsymm hAdotIntegrable hAIntegrable hRIntegrable
  let v : ℝ → V := backwardTimePrimitive (fun r ↦ u r) σ
  have hvContinuous : ContinuousOn v (Icc d σ) := by
    simpa only [uIcc_of_le hdσ, v] using continuousOn_backwardTimePrimitive
      ((intervalIntegrable_coeFn_L2_restrict_Ioc u hab.le).mono_set
        (uIcc_subset_uIcc (Icc_subset_uIcc hd) (Icc_subset_uIcc hσ))) right_mem_uIcc
  have hkineticAB : Integrable (fun t ↦ ‖T.inclusion (u t)‖ ^ 2)
      (volume.restrict (Set.Ioc a b)) := by
    simpa only [Function.comp_apply] using
      (T.inclusion.comp_memLp u).integrable_norm_pow (by norm_num)
  have herror := integrated_waveCoefficientError_le (energyDensity := fun t ↦ ‖v t‖ ^ 2)
    (principalConstant := LA) (lowerConstant := (1 / 2 : ℝ) * LR) hdσ hAdotIntegrable hRIntegrable
    ((hvContinuous.norm.pow 2).intervalIntegrable_of_Icc hdσ)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hdσ).2 (hkineticAB.mono_measure
      ((volume : Measure ℝ).restrict_mono_set (Ioc_subset_Ioc hd.1 hσ.2))))
    (fun t ht ↦ (neg_le_abs _).trans (hAdotBound t (Icc_subset_uIcc ht) (v t)))
    (fun t ht ↦ (neg_le_abs _).trans ((hRBound t (Icc_subset_uIcc ht) (u t) (v t)).trans (by
      nlinarith [mul_nonneg hLR (sq_nonneg (‖T.inclusion (u t)‖ - ‖v t‖))])))
  have hcoerciveInitial := hcoercive d left_mem_uIcc (v d)
  simp only [v] at herror hcoerciveInitial
  linarith

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
