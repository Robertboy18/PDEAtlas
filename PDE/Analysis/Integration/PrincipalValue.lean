/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Spherical principal values

A principal value uses integrable punctured kernels and the limit of their integrals as the
deleted radius decreases to zero. Integrability includes the tail at infinity; convergence of
totalized Bochner integrals alone does not define a principal value.

`principalValue` is the limit when it exists. Enlarging the domain of integration by a
region at positive distance from the evaluation point adds the absolutely convergent integral
over that region (`hasPrincipalValueAt_iff_of_ball_subset`); this splits a principal value
into a localized one and a far part.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

/-- The singular integral with a ball of radius `ε` deleted around the output point. -/
def principalValueTruncation
    {n : ℕ} (U : Set (ℝ^n)) (K : ℝ^n → ℝ^n → ℝ) (f : ℝ^n → ℝ)
    (x : ℝ^n) (ε : ℝ) : ℝ :=
  ∫ y in U ∩ {y | ε < ‖x - y‖}, K x y * f y

/-- Existence of a spherical principal value. The truncated integrands must be integrable
for all sufficiently small positive radii, not just assigned a totalized integral. -/
def HasPrincipalValueAt
    {n : ℕ} (U : Set (ℝ^n)) (K : ℝ^n → ℝ^n → ℝ) (f : ℝ^n → ℝ)
    (x : ℝ^n) (v : ℝ) : Prop :=
  (∀ᶠ ε : ℝ in 𝓝[>] 0,
    IntegrableOn (fun y ↦ K x y * f y) (U ∩ {y | ε < ‖x - y‖})) ∧
    Tendsto (principalValueTruncation U K f x) (𝓝[>] 0) (𝓝 v)

/-- A spherical principal value, when it exists, is unique. -/
theorem HasPrincipalValueAt.unique
    {n : ℕ} {U : Set (ℝ^n)} {K : ℝ^n → ℝ^n → ℝ} {f : ℝ^n → ℝ}
    {x : ℝ^n} {v w : ℝ}
    (hv : HasPrincipalValueAt U K f x v) (hw : HasPrincipalValueAt U K f x w) :
    v = w :=
  tendsto_nhds_unique hv.2 hw.2

/-- The principal value, defined as the limit of the truncations; it is meaningful when
`HasPrincipalValueAt` holds. -/
def principalValue
    {n : ℕ} (U : Set (ℝ^n)) (K : ℝ^n → ℝ^n → ℝ) (f : ℝ^n → ℝ) (x : ℝ^n) : ℝ :=
  limUnder (𝓝[>] 0) (principalValueTruncation U K f x)

/-- An existing principal value is the value of `principalValue`. -/
theorem HasPrincipalValueAt.principalValue_eq
    {n : ℕ} {U : Set (ℝ^n)} {K : ℝ^n → ℝ^n → ℝ} {f : ℝ^n → ℝ} {x : ℝ^n} {v : ℝ}
    (h : HasPrincipalValueAt U K f x v) : principalValue U K f x = v :=
  h.2.limUnder_eq

/-- Principal values add: if `K f` and `K g` have principal values `v` and `w` at `x`, then
`K (f + g)` has the principal value `v + w`. -/
theorem HasPrincipalValueAt.add
    {n : ℕ} {U : Set (ℝ^n)} {K : ℝ^n → ℝ^n → ℝ} {f g : ℝ^n → ℝ} {x : ℝ^n} {v w : ℝ}
    (hf : HasPrincipalValueAt U K f x v) (hg : HasPrincipalValueAt U K g x w) :
    HasPrincipalValueAt U K (f + g) x (v + w) := by
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0, principalValueTruncation U K f x ε +
      principalValueTruncation U K g x ε = principalValueTruncation U K (f + g) x ε := by
    filter_upwards [hf.1, hg.1] with ε hfε hgε
    unfold principalValueTruncation
    rw [← integral_add hfε hgε]
    simp only [Pi.add_apply, mul_add]
  refine ⟨?_, (tendsto_congr' heq).mp (hf.2.add hg.2)⟩
  filter_upwards [hf.1, hg.1] with ε hfε hgε
  have h := hfε.add hgε
  simp only [Pi.add_apply, mul_add]
  exact h

/-- **Localization of principal values.** If `U ⊆ V` contains a ball around `x` and the
integrand is integrable on `V \ U`, then the principal value over `V` exists if and only if
the one over `U` does, and they differ by the integral over `V \ U`. -/
theorem hasPrincipalValueAt_iff_of_ball_subset
    {n : ℕ} {U V : Set (ℝ^n)} {K : ℝ^n → ℝ^n → ℝ} {f : ℝ^n → ℝ} {x : ℝ^n} {v r : ℝ}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V) (hr : 0 < r)
    (hball : Metric.ball x r ⊆ U)
    (hfar : IntegrableOn (fun y ↦ K x y * f y) (V \ U)) :
    HasPrincipalValueAt U K f x v ↔
      HasPrincipalValueAt V K f x (v + ∫ y in V \ U, K x y * f y) := by
  have hsplit : ∀ ε ∈ Ioo 0 r, V ∩ {y | ε < ‖x - y‖} = (U ∩ {y | ε < ‖x - y‖}) ∪ (V \ U) := by
    intro ε hε
    ext y
    constructor
    · rintro ⟨hyV, hyε⟩
      by_cases hyU : y ∈ U
      · exact Or.inl ⟨hyU, hyε⟩
      · exact Or.inr ⟨hyV, hyU⟩
    · rintro (⟨hyU, hyε⟩ | ⟨hyV, hyU⟩)
      · exact ⟨hUV hyU, hyε⟩
      · refine ⟨hyV, ?_⟩
        have : y ∉ Metric.ball x r := fun h ↦ hyU (hball h)
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at this
        exact lt_of_lt_of_le hε.2 (le_of_not_gt this)
  have hdisj : ∀ ε ∈ Ioo 0 r, Disjoint (U ∩ {y | ε < ‖x - y‖}) (V \ U) :=
    fun ε _ ↦ Set.disjoint_left.mpr fun y hy hy' ↦ hy'.2 hy.1
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
  constructor
  · rintro ⟨hint, hlim⟩
    refine ⟨?_, ?_⟩
    · filter_upwards [hint, hev] with ε hε hεr
      rw [hsplit ε hεr]
      exact hε.union hfar
    · have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), principalValueTruncation V K f x ε =
          principalValueTruncation U K f x ε + ∫ y in V \ U, K x y * f y := by
        filter_upwards [hint, hev] with ε hε hεr
        unfold principalValueTruncation
        rw [hsplit ε hεr, setIntegral_union (hdisj ε hεr) (hV.diff hU) hε hfar]
      exact (tendsto_congr' heq).mpr (hlim.add_const _)
  · rintro ⟨hint, hlim⟩
    refine ⟨?_, ?_⟩
    · filter_upwards [hint, hev] with ε hε hεr
      rw [hsplit ε hεr] at hε
      exact hε.mono_set subset_union_left
    · have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), principalValueTruncation U K f x ε =
          principalValueTruncation V K f x ε - ∫ y in V \ U, K x y * f y := by
        filter_upwards [hint, hev] with ε hε hεr
        have hε' := hε
        rw [hsplit ε hεr] at hε'
        unfold principalValueTruncation
        rw [hsplit ε hεr, setIntegral_union (hdisj ε hεr) (hV.diff hU)
          (hε'.mono_set subset_union_left) hfar]
        ring
      have := (tendsto_congr' heq).mpr (hlim.sub_const (∫ y in V \ U, K x y * f y))
      simpa using this

end PDE.Analysis
