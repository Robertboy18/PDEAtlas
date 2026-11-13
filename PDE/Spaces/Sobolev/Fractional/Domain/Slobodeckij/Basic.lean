/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The raw Sobolev–Slobodeckij condition

A function with values in a normed real vector space satisfies `MemGagliardo` if both the
function and its weighted difference belong to `Lᵖ`, on the domain and its square respectively.
For finite positive `p`, the difference quotient has distance exponent `n / p.toReal + s`;
its p-th power gives the Gagliardo kernel of order `s`. At `p = ∞`, the exponent is `s`, so
membership expresses an essential Hölder difference bound, without choosing a continuous
representative. The default exponent is `2`.

The predicate is defined for every real order and every exponent. Its usual interpretation
as fractional Sobolev regularity requires `0 < s < 1` and `1 ≤ p`. Almost-everywhere
classes and the complete graph norm are constructed in `Slobodeckij.Graph`.

The difference vanishes on the diagonal, including in dimension zero. All algebraic laws
hold even when the distance power is zero, using totalized real inversion. Domains need
not be open or bounded; measurability of the domain is required only where stated.

## References

* E. Di Nezza, G. Palatucci and E. Valdinoci, "Hitchhiker's guide to the fractional Sobolev spaces",
  *Bull. Sci. Math.* 136 (2012), 521-573, numbering of arXiv:1104.4345v3, Section 2, (2.1)-(2.2):
  for an open set `Ω`, `s ∈ (0, 1)` and `1 ≤ p < ∞`, `W^{s,p}(Ω)` is the space of `u ∈ L^p(Ω)` with
  `|u(x) - u(y)| / |x - y|^{n/p + s} ∈ L^p(Ω × Ω)`.
  <https://arxiv.org/abs/1104.4345v3>
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Fractional

/-- The weighted difference with distance exponent `n / p.toReal + s`.
The point argument precedes the default exponent, so pointwise and function-valued
applications both default to exponent two. -/
def diffQuot (n : ℕ) (s : ℝ) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (u : ℝ^n → F) (z : ℝ^n × ℝ^n) (p : ℝ≥0∞ := 2) : F :=
  (‖z.1 - z.2‖ ^ ((n : ℝ) / p.toReal + s))⁻¹ • (u z.1 - u z.2)

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a real-valued function, scalar multiplication by the inverse distance power
is the usual quotient. This includes exponent two and zero denominators. -/
theorem diffQuot_apply_real (u : ℝ^n → ℝ) (z : ℝ^n × ℝ^n) :
    diffQuot n s u z (p := p) =
      (u z.1 - u z.2) / ‖z.1 - z.2‖ ^ ((n : ℝ) / p.toReal + s) := by
  simp only [diffQuot, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The difference quotient of the zero function is zero. -/
theorem diffQuot_zero : diffQuot n s (0 : ℝ^n → F) (p := p) = 0 := by
  funext z
  simp only [diffQuot, Pi.zero_apply, sub_self, smul_zero]

/-- Pointwise simplification of the zero difference quotient. -/
@[simp] theorem diffQuot_zero_apply (z : ℝ^n × ℝ^n) :
    diffQuot n s (0 : ℝ^n → F) z (p := p) = 0 := by
  simp only [diffQuot, Pi.zero_apply, sub_self, smul_zero]

/-- The difference quotient is additive, including on the diagonal. -/
theorem diffQuot_add (u v : ℝ^n → F) :
    diffQuot n s (u + v) (p := p) =
      diffQuot n s u (p := p) + diffQuot n s v (p := p) := by
  funext z
  simp only [diffQuot, Pi.add_apply, add_sub_add_comm, smul_add]

/-- The difference quotient commutes with real scalar multiplication. -/
theorem diffQuot_smul (c : ℝ) (u : ℝ^n → F) :
    diffQuot n s (c • u) (p := p) = c • diffQuot n s u (p := p) := by
  funext z
  simpa only [diffQuot, Pi.smul_apply, smul_sub] using
    smul_comm (‖z.1 - z.2‖ ^ ((n : ℝ) / p.toReal + s))⁻¹ c (u z.1 - u z.2)

/-- The product of the restricted volume measure with itself. -/
abbrev gagliardoProductMeasure (n : ℕ) (Ω : Set (ℝ^n)) :
    Measure (ℝ^n × ℝ^n) :=
  ((volume : Measure (ℝ^n)).restrict Ω).prod ((volume : Measure (ℝ^n)).restrict Ω)

/-- The Gagliardo product measure is monotone under inclusion of domains. -/
theorem gagliardoProductMeasure_mono {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    gagliardoProductMeasure n Ω₁ ≤ gagliardoProductMeasure n Ω₂ :=
  Measure.prod_mono
    (Measure.restrict_mono hΩ le_rfl)
    (Measure.restrict_mono hΩ le_rfl)

/-- The difference quotient depends only on the input's almost-everywhere class
on the domain. -/
theorem diffQuot_congr_ae {u v : ℝ^n → F}
    (huv : u =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] v) :
    diffQuot n s u (p := p) =ᵐ[gagliardoProductMeasure n Ω]
      diffQuot n s v (p := p) := by
  have hfst := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (ℝ^n)).restrict Ω)
    (ν := (volume : Measure (ℝ^n)).restrict Ω)).ae huv
  have hsnd := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (ℝ^n)).restrict Ω)
    (ν := (volume : Measure (ℝ^n)).restrict Ω)).ae huv
  filter_upwards [hfst, hsnd] with z hz₁ hz₂
  simp only [diffQuot, hz₁, hz₂]

/-- The difference quotient inherits almost-everywhere strong measurability from
its input, without a measurable-space assumption on the codomain. -/
theorem aestronglyMeasurable_diffQuot {u : ℝ^n → F}
    (hu : AEStronglyMeasurable u ((volume : Measure (ℝ^n)).restrict Ω)) :
    AEStronglyMeasurable (diffQuot n s u (p := p)) (gagliardoProductMeasure n Ω) := by
  have hw : Measurable (fun z : ℝ^n × ℝ^n ↦
      (‖z.1 - z.2‖ ^ ((n : ℝ) / p.toReal + s))⁻¹) := by
    fun_prop
  exact hw.aestronglyMeasurable.smul (hu.comp_fst.sub hu.comp_snd)

/-- Membership in `Lᵖ` on the domain and of the weighted difference on its square.
For `0 < s < 1` and finite `p ≥ 1`, this is the raw Sobolev–Slobodeckij condition. -/
def MemGagliardo (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (u : ℝ^n → F) (p : ℝ≥0∞ := 2) : Prop :=
  MemLp u p ((volume : Measure (ℝ^n)).restrict Ω) ∧
    MemLp (diffQuot n s u (p := p)) p (gagliardoProductMeasure n Ω)

/-- The zero function satisfies the Gagliardo condition at every exponent. -/
theorem memGagliardo_zero : MemGagliardo n s Ω (0 : ℝ^n → F) (p := p) :=
  ⟨MemLp.zero, by rw [diffQuot_zero]; exact MemLp.zero⟩

/-- Addition preserves the Gagliardo condition. -/
theorem MemGagliardo.add {u v : ℝ^n → F}
    (hu : MemGagliardo n s Ω u (p := p)) (hv : MemGagliardo n s Ω v (p := p)) :
    MemGagliardo n s Ω (u + v) (p := p) := by
  refine ⟨hu.1.add hv.1, ?_⟩
  rw [diffQuot_add]
  exact hu.2.add hv.2

/-- Real scalar multiplication preserves the Gagliardo condition. -/
theorem MemGagliardo.smul {u : ℝ^n → F} (c : ℝ)
    (hu : MemGagliardo n s Ω u (p := p)) :
    MemGagliardo n s Ω (c • u) (p := p) := by
  refine ⟨hu.1.const_smul c, ?_⟩
  rw [diffQuot_smul]
  exact hu.2.const_smul c

/-- Restriction to a smaller domain preserves the Gagliardo condition. -/
theorem MemGagliardo.mono {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂)
    {u : ℝ^n → F} (hu : MemGagliardo n s Ω₂ u (p := p)) :
    MemGagliardo n s Ω₁ u (p := p) :=
  ⟨hu.1.mono_measure (Measure.restrict_mono hΩ le_rfl),
    hu.2.mono_measure (gagliardoProductMeasure_mono hΩ)⟩

/-- Almost-everywhere equality on the domain preserves the Gagliardo condition. -/
theorem MemGagliardo.congr_ae {u v : ℝ^n → F}
    (hu : MemGagliardo n s Ω u (p := p))
    (huv : u =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] v) :
    MemGagliardo n s Ω v (p := p) :=
  ⟨(memLp_congr_ae huv).1 hu.1,
    (memLp_congr_ae (diffQuot_congr_ae huv)).1 hu.2⟩

/-- The Gagliardo condition as a real submodule of functions.
Its almost-everywhere quotient and graph norm are separate constructions. -/
def gagliardoSubmodule (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) (p : ℝ≥0∞ := 2)
    (F : Type* := by exact ℝ) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Submodule ℝ (ℝ^n → F) where
  carrier := {u | MemGagliardo n s Ω u (p := p)}
  zero_mem' := memGagliardo_zero
  add_mem' := MemGagliardo.add
  smul_mem' c _ h := h.smul c

/-- Membership in the raw function submodule is the Gagliardo condition. -/
@[simp] theorem mem_gagliardoSubmodule_iff {u : ℝ^n → F} :
    u ∈ gagliardoSubmodule n s Ω (p := p) (F := F) ↔
      MemGagliardo n s Ω u (p := p) := Iff.rfl

/-- The raw function submodule is antitone in the domain. -/
theorem gagliardoSubmodule_mono {Ω₁ Ω₂ : Set (ℝ^n)} (hΩ : Ω₁ ⊆ Ω₂) :
    gagliardoSubmodule n s Ω₂ (p := p) (F := F) ≤
      gagliardoSubmodule n s Ω₁ (p := p) (F := F) :=
  fun _ hu ↦ hu.mono hΩ

/-- On a finite-measure domain a constant satisfies the Gagliardo condition:
its difference quotient is zero, at every order and exponent. -/
theorem memGagliardo_const (hΩ : volume Ω ≠ ⊤) (c : F) (p : ℝ≥0∞ := 2) :
    MemGagliardo n s Ω (fun _ ↦ c) (p := p) := by
  have : IsFiniteMeasure ((volume : Measure (ℝ^n)).restrict Ω) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hΩ
  refine ⟨memLp_const c, ?_⟩
  have hzero : diffQuot n s (fun _ ↦ c) (p := p) = 0 := by
    funext z
    simp only [diffQuot, sub_self, smul_zero, Pi.zero_apply]
  rw [hzero]
  exact MemLp.zero

/-- A function vanishing on the measurable domain satisfies the Gagliardo
condition, regardless of its values outside the domain. -/
theorem memGagliardo_of_eqOn_zero (hΩ : MeasurableSet Ω) (u : ℝ^n → F)
    (hu : ∀ x ∈ Ω, u x = 0) (p : ℝ≥0∞ := 2) :
    MemGagliardo n s Ω u (p := p) := by
  have hzero : u =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] 0 := by
    filter_upwards [ae_restrict_mem hΩ] with x hx
    exact hu x hx
  exact memGagliardo_zero.congr_ae hzero.symm

end SobolevSpace.Fractional
