/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Products
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Subcritical.ZeroTrace

/-!
# The compact `L⁴` inclusion of `H¹₀` in dimensions one to three

On a bounded open set `Ω ⊆ ℝⁿ` with `n ≤ 3`, the exponent `4` lies strictly below the Sobolev
exponent, so `H¹₀(Ω)` embeds compactly into `L⁴(Ω)`. The inclusion `h10L4Inclusion` takes values
in `DerivLp n 4 Ω`, the space in which the convection forms of the fluid library take their
coefficients. It is the finite-exponent embedding `h10LpEmbedding` at `q = 4`, with the exponent
`ENNReal.ofReal 4` rewritten as `4`; its representative is the base coordinate, it is injective,
and it is compact.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Exponent four lies below the Sobolev exponent in dimensions at most three. -/
theorem four_lt_sobolevExponent_of_lt_four (hn4 : n < 4) (hn2 : 2 < n) :
    (4 : ℝ) < 2 * (n : ℝ) / ((n : ℝ) - 2) := by
  have hn : n = 3 := by omega
  subst hn
  norm_num

/-- The identity of `L⁴(Ω)` from the exponent `ENNReal.ofReal 4` to the exponent `4`. -/
def ofRealFourToFour : DerivLp n (ENNReal.ofReal 4) Ω →L[ℝ] DerivLp n 4 Ω :=
  (ContinuousLinearMap.id ℝ (DerivLp n (ENNReal.ofReal 4) Ω)).liftLpExponent (q := 4)
    (fun f ↦ by rw [ContinuousLinearMap.id_apply, ← ENNReal.ofReal_ofNat 4]; exact Lp.memLp f)

/-- The compact inclusion `H¹₀(Ω) → L⁴(Ω)` on a bounded open set in dimension at most three. -/
def h10L4Inclusion (hn : 0 < n) (hn4 : n < 4) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    H¹₀(Ω) →L[ℝ] DerivLp n 4 Ω :=
  haveI := isFiniteMeasure_domainMeasure_of_isBounded hb
  ofRealFourToFour.comp (h10LpEmbedding hn hΩ.measurableSet (q := 4) (by norm_num)
    (fun h ↦ (four_lt_sobolevExponent_of_lt_four hn4 h).le))

/-- The `L⁴` class of a field represents its base coordinate. -/
theorem h10L4Inclusion_ae (hn : 0 < n) (hn4 : n < 4) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (u : H¹₀(Ω)) :
    (h10L4Inclusion hn hn4 hΩ hb u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (baseCoordCLM u : ℝ^n → ℝ) := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hb
  have h₁ := (ContinuousLinearMap.id ℝ (DerivLp n (ENNReal.ofReal 4) Ω)).coeFn_liftLpExponent
    (q := 4)
    (fun f ↦ by rw [ContinuousLinearMap.id_apply, ← ENNReal.ofReal_ofNat 4]; exact Lp.memLp f)
    (h10LpEmbedding hn hΩ.measurableSet (q := 4) (by norm_num)
      (fun h ↦ (four_lt_sobolevExponent_of_lt_four hn4 h).le) u)
  have h₂ := h10LpEmbedding_ae hn hΩ.measurableSet (q := 4) (by norm_num)
    (fun h ↦ (four_lt_sobolevExponent_of_lt_four hn4 h).le) u
  exact h₁.trans h₂

/-- The `L⁴` inclusion is injective: weak derivatives on an open set are determined by the base
coordinate. -/
theorem h10L4Inclusion_injective (hn : 0 < n) (hn4 : n < 4) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) : Function.Injective (h10L4Inclusion hn hn4 hΩ hb) := by
  intro u v huv
  apply baseCoordCLM_injective hΩ
  apply Lp.ext
  have h := (h10L4Inclusion_ae hn hn4 hΩ hb u).symm
  rw [huv] at h
  exact h.trans (h10L4Inclusion_ae hn hn4 hΩ hb v)

/-- Rellich compactness of the `L⁴` inclusion; no boundary regularity is needed. -/
theorem h10L4Inclusion_isCompactOperator (hn : 0 < n) (hn4 : n < 4) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) : IsCompactOperator (h10L4Inclusion hn hn4 hΩ hb) :=
  (h10LpEmbedding_isCompactOperator hn hΩ.measurableSet hb (q := 4) (by norm_num)
    (four_lt_sobolevExponent_of_lt_four hn4)).clm_comp ofRealFourToFour

end SobolevSpace.GraphSpace
