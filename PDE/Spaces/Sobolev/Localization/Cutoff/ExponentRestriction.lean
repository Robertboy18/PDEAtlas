/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction

/-!
# Exponent restriction after cutoff localization

Multiplying a global `W^{1,p}(ℝ^n)` function by a smooth compactly supported cutoff `ψ` gives a
function whose base and first-derivative coordinates all vanish outside the compact set
`tsupport ψ`. On a set of finite measure Hölder's inequality gives `L^p ⊆ L^1` for every
`1 ≤ p ≤ ∞`, so the localized function may be regarded as an element of `W^{1,1}(ℝ^n)`. The
resulting map is a bounded linear operator with an explicit norm bound.

## Main results

* `cutoffToW11`: the localized `W^{1,p}` value viewed in `W^{1,1}`, with `cutoffToW11_apply_ae`
  recording that every coordinate is unchanged almost everywhere.
* `cutoffToW11CLM`: the same map as a continuous linear operator `W^{1,p} → W^{1,1}`.
* `norm_cutoffToW11_le`, `norm_cutoffToW11CLM_le`: the bound
  `‖cutoffToW11 ψ U‖ ≤ cutoffToW11NormBound ψ · ‖U‖`. The constant is the product of the
  finite-measure exponent-restriction constant for `tsupport ψ` and the operator norm of the
  cutoff multiplier `cutoffCLM ψ`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every coordinate of a smoothly localized global Sobolev element is
supported almost everywhere in the support of the cutoff. -/
theorem cutoff_all_coordinates_supported
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{1,p}(ℝ^n)) :
    HasCoordinateSupportIn (tsupport ψ.toFun)
      (cutoffCLM (n := n) (p := p) (Ω := Set.univ) ψ U) := by
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    exact cutoffCLM_base_tsupport_indicator_ae
      (n := n) (p := p) (Ω := Set.univ) ψ U
  · subst a
    exact cutoffCLM_singleDeriv_tsupport_indicator_ae
      (n := n) (p := p) (Ω := Set.univ) ψ U i

/-- The support of a compactly supported cutoff has finite Lebesgue measure. -/
theorem cutoff_tsupport_measure_ne_top
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    domainMeasure n Set.univ (tsupport ψ.toFun) ≠ ∞ := by
  simpa [domainMeasure] using
    (ψ.hasCompactSupport.isCompact.measure_ne_top :
      (volume : Measure (ℝ^n)) (tsupport ψ.toFun) ≠ ∞)

/-- View a smoothly localized global `W^{1,p}` value as a global
`W^{1,1}` value. -/
noncomputable def cutoffToW11
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{1,p}(ℝ^n)) :
    W^{1,1}(ℝ^n) :=
  lowerExponentOfFiniteMeasureSupport
    (q := (1 : ℝ≥0∞)) (Fact.out : (1 : ℝ≥0∞) ≤ p)
    (tsupport ψ.toFun)
    (cutoff_tsupport_measure_ne_top ψ)
    (cutoffCLM (n := n) (p := p) (Ω := Set.univ) ψ U)
    (cutoff_all_coordinates_supported ψ U)

/-- Every coordinate of `cutoffToW11 ψ U` agrees almost everywhere with the
corresponding coordinate of the localized `W^{1,p}` value. -/
theorem cutoffToW11_apply_ae
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{1,p}(ℝ^n)) (a : DerivIndex n 1) :
    (((cutoffToW11 ψ U : WkpAmbientOn n 1 1 Set.univ) a :
        DerivLp n 1 Set.univ) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        (((cutoffCLM (n := n) (p := p) (Ω := Set.univ) ψ U :
            WkpAmbientOn n 1 p Set.univ) a :
          DerivLp n p Set.univ) : ℝ^n → ℝ) := by
  exact lowerExponentOfFiniteMeasureSupport_apply_ae
    (q := (1 : ℝ≥0∞)) (Fact.out : (1 : ℝ≥0∞) ≤ p)
    (tsupport ψ.toFun)
    (cutoff_tsupport_measure_ne_top ψ)
    (cutoffCLM (n := n) (p := p) (Ω := Set.univ) ψ U)
    (cutoff_all_coordinates_supported ψ U) a

/-- An explicit operator bound for cutoff localization followed by exponent
restriction to `W^{1,1}`. -/
noncomputable def cutoffToW11NormBound
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) : ℝ :=
  finiteMeasureSupportExponentRestrictionNormBound
      n 1 p 1 Set.univ (tsupport ψ.toFun) *
    ‖cutoffCLM (n := n) (p := p) (Ω := Set.univ) ψ‖

/-- The cutoff-to-`W^{1,1}` operator bound is nonnegative. -/
theorem cutoffToW11NormBound_nonneg
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    0 ≤ cutoffToW11NormBound (n := n) (p := p) ψ :=
  mul_nonneg finiteMeasureSupportExponentRestrictionNormBound_nonneg
    (norm_nonneg
      (cutoffCLM (n := n) (p := p) (Ω := Set.univ) ψ))

/-- Quantitative bound for cutoff localization followed by exponent
restriction to `W^{1,1}`. -/
theorem norm_cutoffToW11_le
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{1,p}(ℝ^n)) :
    ‖cutoffToW11 ψ U‖ ≤
      cutoffToW11NormBound (n := n) (p := p) ψ * ‖U‖ := by
  simpa only [lowerExponentOfFiniteMeasureSupportCLM_apply, cutoffToW11,
    cutoffToW11NormBound] using
    norm_lowerExponentOfFiniteMeasureSupportCLM_apply_le
      (q := (1 : ℝ≥0∞)) (Fact.out : (1 : ℝ≥0∞) ≤ p)
      (tsupport ψ.toFun) (cutoff_tsupport_measure_ne_top ψ)
      (cutoffCLM (n := n) (p := p) (Ω := Set.univ) ψ)
      (cutoff_all_coordinates_supported ψ) U

/-- Bounded linear cutoff localization from global `W^{1,p}` to global
`W^{1,1}`. -/
noncomputable def cutoffToW11CLM
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    W^{1,p}(ℝ^n) →L[ℝ] W^{1,1}(ℝ^n) :=
  lowerExponentOfFiniteMeasureSupportCLM
    (q := (1 : ℝ≥0∞)) (Fact.out : (1 : ℝ≥0∞) ≤ p)
    (tsupport ψ.toFun) (cutoff_tsupport_measure_ne_top ψ)
    (cutoffCLM (n := n) (p := p) (Ω := Set.univ) ψ)
    (cutoff_all_coordinates_supported ψ)

/-- The bounded operator `cutoffToW11CLM` agrees with the construction `cutoffToW11` on
elements. -/
@[simp]
theorem cutoffToW11CLM_apply
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{1,p}(ℝ^n)) :
    cutoffToW11CLM ψ U = cutoffToW11 ψ U :=
  rfl

/-- Operator-norm bound for cutoff localization into `W^{1,1}`. -/
theorem norm_cutoffToW11CLM_le
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ‖cutoffToW11CLM (n := n) (p := p) ψ‖ ≤
      cutoffToW11NormBound (n := n) (p := p) ψ :=
  norm_lowerExponentOfFiniteMeasureSupportCLM_le
    (q := (1 : ℝ≥0∞)) (Fact.out : (1 : ℝ≥0∞) ≤ p)
    (tsupport ψ.toFun) (cutoff_tsupport_measure_ne_top ψ)
    (cutoffCLM (n := n) (p := p) (Ω := Set.univ) ψ)
    (cutoff_all_coordinates_supported ψ)

end SobolevSpace.GraphSpace
