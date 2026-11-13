/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TestFunctions

/-!
# Integral identities for half-space reflection

Let `ū` and `ũ` be the even and odd reflections of `u ∈ L^p(ℝ^n₊)` across `{xₙ = 0}`, and let
`φ` be a test function on `ℝ^n`. Splitting `ℝ^n` into the two half-spaces and changing variables
`x ↦ (x', -xₙ)` on the lower one gives

* `∫_{ℝ^n} ū φ = ∫_{ℝ^n₊} u · (φ + φ ∘ reflect)`, and
* `∫_{ℝ^n} ũ φ = ∫_{ℝ^n₊} u · (φ - φ ∘ reflect)`.

The bracketed test functions are the even and odd parts `evenPartTestFunction φ` and
`oddPartTestFunction φ` from `Reflection.FirstOrder.TestFunctions` (without the factor `1/2`). These
identities are the bookkeeping step in the reflection lemma for `W^{1,p}(ℝ^n₊)` (Brezis, *Functional
Analysis, Sobolev Spaces and PDE*, Chapter 9): they convert a weak-derivative
identity on the whole space into one on the half-space tested against a symmetrised test function.

## Main results

* `integral_evenExtendLp_mul_testFunction`: the even-extension identity above.
* `integral_oddExtendLp_mul_testFunction`: the odd-extension identity above.

## Implementation notes

`evenExtendLp` and `oddExtendLp` are defined as `embedUpper ± embedLower ∘ pullbackLower`, so
each identity is proved by treating the two summands separately: the upper summand is a zero
extension, and the reflected lower summand is handled with the measure-preserving property of
`reflect` between the two half-spaces.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for extension by reflection across a flat boundary.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

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

/-- Pairing a zero extension restricts the integral to the original set. -/
private theorem integral_zeroExtendLp_mul {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    (u : DerivLp n p Ω) (ψ : ℝ^n → ℝ) :
    ∫ x, (SobolevSpace.Extension.Lp.zeroExtendLp (n := n) (p := p) hΩ u x) * ψ x ∂ μ =
      ∫ x, (u : ℝ^n → ℝ) x * ψ x ∂ domainMeasure n Ω := by
  calc
    _ = ∫ x, Ω.indicator (fun y ↦ (u : ℝ^n → ℝ) y * ψ y) x ∂ μ := by
      refine integral_congr_ae ?_
      filter_upwards [SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae hΩ u] with x hx
      by_cases hxΩ : x ∈ Ω <;> simp [hx, SobolevSpace.Extension.Lp.extensionByZero, hxΩ]
    _ = _ := by simp [integral_indicator hΩ, domainMeasure]

/-- The pairing with a test function is additive in the `Lᵖ` field. -/
private theorem integral_add_mul_testFunction (A B : DerivLp n p Set.univ)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∫ x, ((A + B : DerivLp n p Set.univ) x) * φ.toFun x ∂ μ =
      ∫ x, (A : ℝ^n → ℝ) x * φ.toFun x ∂ μ + ∫ x, (B : ℝ^n → ℝ) x * φ.toFun x ∂ μ := by
  rw [← integral_add
    (integrable_mul_of_memLp_measure (n := n) (p := p) (ψ := φ.toFun) (Lp.memLp A)
      φ.contDiff.continuous φ.hasCompactSupport)
    (integrable_mul_of_memLp_measure (n := n) (p := p) (ψ := φ.toFun) (Lp.memLp B)
      φ.contDiff.continuous φ.hasCompactSupport)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add A B] with x hx
  rw [hx, Pi.add_apply, add_mul]

/-- The pairing with a test function is subtractive in the `Lᵖ` field. -/
private theorem integral_sub_mul_testFunction (A B : DerivLp n p Set.univ)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∫ x, ((A - B : DerivLp n p Set.univ) x) * φ.toFun x ∂ μ =
      ∫ x, (A : ℝ^n → ℝ) x * φ.toFun x ∂ μ - ∫ x, (B : ℝ^n → ℝ) x * φ.toFun x ∂ μ := by
  rw [← integral_sub
    (integrable_mul_of_memLp_measure (n := n) (p := p) (ψ := φ.toFun) (Lp.memLp A)
      φ.contDiff.continuous φ.hasCompactSupport)
    (integrable_mul_of_memLp_measure (n := n) (p := p) (ψ := φ.toFun) (Lp.memLp B)
      φ.contDiff.continuous φ.hasCompactSupport)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub A B] with x hx
  rw [hx, Pi.sub_apply, sub_mul]

section PositiveDimension

variable [Fact (0 < n)]

/-! #### Integral identities for even/odd reflection extension -/

/-- Pairing an upper zero extension restricts the integral to the upper half-space. -/
theorem integral_embedUpper_mul (u : DerivLp n p ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x,
      ((_root_.SobolevSpace.HalfSpace.embedUpper (n := n) (p := p) u :
          DerivLp n p Set.univ) x) * φ.toFun x ∂ μ)
      =
    (∫ x, (u : ℝ^n → ℝ) x * φ.toFun x ∂ μ₊) :=
  integral_zeroExtendLp_mul n p (measurableSet_upper (n := n)) u φ.toFun

/-- Pairing a lower zero extension restricts the integral to the lower half-space. -/
theorem integral_embedLower_mul (v : DerivLp n p ℝ^n₋) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x,
      ((_root_.SobolevSpace.HalfSpace.embedLower (n := n) (p := p) v :
          DerivLp n p Set.univ) x) * φ.toFun x ∂ μ)
      =
    (∫ x, (v : ℝ^n → ℝ) x * φ.toFun x ∂ μ₋) :=
  integral_zeroExtendLp_mul n p (measurableSet_lower (n := n)) v φ.toFun

/-- Pairing the reflected pullback on the lower half-space equals pairing the original
function with the reflected test function on the upper half-space. -/
theorem integral_pullbackLower_mul
    (u : DerivLp n p ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x, ((_root_.SobolevSpace.HalfSpace.pullbackLower (n := n) (p := p) u :
        DerivLp n p ℝ^n₋) x) * φ.toFun x ∂ μ₋)
      =
    ∫ x, (u : ℝ^n → ℝ) x * φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n x) ∂ μ₊ := by
  have hreflect : MeasurableEmbedding (_root_.SobolevSpace.HalfSpace.reflect n) := by
    simpa using (_root_.SobolevSpace.HalfSpace.reflectLinearIsometryEquiv
      (n := n)).toHomeomorph.measurableEmbedding
  calc
    _ = ∫ x, (u : ℝ^n → ℝ) (_root_.SobolevSpace.HalfSpace.reflect n x) * φ.toFun x ∂ μ₋ := by
      refine integral_congr_ae ?_
      filter_upwards [_root_.SobolevSpace.HalfSpace.pullbackLower_apply_ae (n := n) (p := p) u]
        with x hx
      rw [hx]
    _ = _ := by
      simpa [Function.comp, _root_.SobolevSpace.HalfSpace.reflect_involutive (n := n) _,
        mul_assoc] using
        (_root_.SobolevSpace.HalfSpace.measurePreserving_reflect_restrict_lower
          (n := n)).integral_comp hreflect fun y ↦
            (u : ℝ^n → ℝ) y * φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n y)

/-- The upper-half-space pairing with the reflected test function is integrable. -/
private theorem integrable_mul_testFunction_reflect
    (u : DerivLp n p ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Integrable (fun x ↦ (u : ℝ^n → ℝ) x *
      φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n x)) μ₊ := by
  let e := (_root_.SobolevSpace.HalfSpace.reflectLinearIsometryEquiv (n := n)).toHomeomorph
  exact integrable_mul_of_memLp (n := n) (p := p) (Lp.memLp u)
    (φ.contDiff.continuous.comp e.continuous) (φ.hasCompactSupport.comp_homeomorph e)

/-- Pairing the lower extension of the reflected pullback equals pairing the original
function with the reflected test function on the upper half-space. -/
private theorem integral_embedLower_pullbackLower_mul
    (u : DerivLp n p ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x,
      ((_root_.SobolevSpace.HalfSpace.embedLower (n := n) (p := p)
          (_root_.SobolevSpace.HalfSpace.pullbackLower (n := n) (p := p) u) :
          DerivLp n p Set.univ) x) * φ.toFun x ∂ μ)
      =
    ∫ x, (u : ℝ^n → ℝ) x * φ.toFun (_root_.SobolevSpace.HalfSpace.reflect n x) ∂ μ₊ :=
  (integral_embedLower_mul (n := n) (p := p)
    (_root_.SobolevSpace.HalfSpace.pullbackLower (n := n) (p := p) u) φ).trans
    (integral_pullbackLower_mul (n := n) (p := p) u φ)

/-- Integrating an even extension against a test function equals integrating against its even
part on the upper half-space. -/
theorem integral_evenExtendLp_mul_testFunction
    (u : DerivLp n p ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x,
      ((_root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p) u :
          DerivLp n p Set.univ) x) * φ.toFun x ∂ μ)
      =
    (∫ x, (u : ℝ^n → ℝ) x * (evenPartTestFunction (n := n) φ).toFun x ∂ μ₊) := by
  -- the even extension is the upper zero extension plus the reflected lower one
  have hsplit : _root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := p) u =
      _root_.SobolevSpace.HalfSpace.embedUpper (n := n) (p := p) u +
        _root_.SobolevSpace.HalfSpace.embedLower (n := n) (p := p)
          (_root_.SobolevSpace.HalfSpace.pullbackLower (n := n) (p := p) u) := by
    simp [_root_.SobolevSpace.HalfSpace.evenExtendLp]
  rw [hsplit, integral_add_mul_testFunction, integral_embedUpper_mul,
    integral_embedLower_pullbackLower_mul, ← integral_add
      (integrable_mul_of_memLp (n := n) (p := p) (ψ := φ.toFun) (Lp.memLp u) φ.contDiff.continuous
        φ.hasCompactSupport) (integrable_mul_testFunction_reflect (n := n) (p := p) u φ)]
  simp only [evenPartTestFunction_toFun, mul_add]

/-- Integrating an odd extension against a test function equals integrating against its odd
part on the upper half-space. -/
theorem integral_oddExtendLp_mul_testFunction
    (u : DerivLp n p ℝ^n₊) (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ x,
      ((_root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := p) u :
          DerivLp n p Set.univ) x) * φ.toFun x ∂ μ)
      =
    (∫ x, (u : ℝ^n → ℝ) x * (oddPartTestFunction (n := n) φ).toFun x ∂ μ₊) := by
  -- the odd extension is the upper zero extension minus the reflected lower one
  have hsplit : _root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := p) u =
      _root_.SobolevSpace.HalfSpace.embedUpper (n := n) (p := p) u -
        _root_.SobolevSpace.HalfSpace.embedLower (n := n) (p := p)
          (_root_.SobolevSpace.HalfSpace.pullbackLower (n := n) (p := p) u) := by
    simp [_root_.SobolevSpace.HalfSpace.oddExtendLp]
  rw [hsplit, integral_sub_mul_testFunction, integral_embedUpper_mul,
    integral_embedLower_pullbackLower_mul, ← integral_sub
      (integrable_mul_of_memLp (n := n) (p := p) (ψ := φ.toFun) (Lp.memLp u) φ.contDiff.continuous
        φ.hasCompactSupport) (integrable_mul_testFunction_reflect (n := n) (p := p) u φ)]
  simp only [oddPartTestFunction_toFun, mul_sub]

end PositiveDimension

end Proofs

end HalfSpace

end GraphSpace

end Extension

end

end SobolevSpace
