/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.Model

/-!
# Life spans, bounded supports and the continuation quantity

The basic notions for solutions of the half-plane Boussinesq system on the times `[0, T)`: the
life span `lifeSpan T = {t | 0 ≤ t < T}` for `T ∈ [0, ∞]`, supports bounded uniformly on compact
time intervals (`HasBoundedSupportOn`), and the continuation quantity
`continuationIntegral sol T = ∫₀^T (‖∇u(t)‖_∞ + ‖∇θ(t)‖_∞) dt`, with the sup norms over the open
upper half-plane.

## Main definitions

* `lifeSpan`: the times `0 ≤ t < T` of a solution with life span `T ∈ [0, ∞]`.
* `HasBoundedSupportOn`: the vorticity and the temperature vanish on the closed half-plane outside
  a disc common to all times of every compact interval.
* `continuationIntegral`: the continuation quantity `∫₀^T (‖∇u(t)‖_∞ + ‖∇θ(t)‖_∞) dt`.

## Main results

* `lifeSpan_of_ne_top`: a finite life span `T` is `[0, T.toReal)`.
* `lifeSpan_top`: the infinite life span is `[0, ∞)`.
* `ordConnected_lifeSpan`: a life span is an interval.
* `Icc_subset_lifeSpan`: `[0, t₀]` lies in the life span for every `t₀` in it.
* `HasBoundedSupportOn.mono`: bounded supports restrict to smaller sets of times.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Boussinesq.HalfPlane

/-! ### Life spans -/

/-- The times `0 ≤ t < T` of a solution with life span `T ∈ [0, ∞]`. -/
def lifeSpan (T : ℝ≥0∞) : Set ℝ :=
  {t | 0 ≤ t ∧ ENNReal.ofReal t < T}

/-- The life span is monotone in `T`. -/
theorem lifeSpan_mono {T T' : ℝ≥0∞} (h : T ≤ T') : lifeSpan T ⊆ lifeSpan T' :=
  fun _ ht ↦ ⟨ht.1, ht.2.trans_le h⟩

/-- For `τ > 0` the life span `ENNReal.ofReal τ` is `[0, τ)`. -/
theorem lifeSpan_ofReal {τ : ℝ} (hτ : 0 < τ) : lifeSpan (ENNReal.ofReal τ) = Ico 0 τ := by
  ext t
  simp only [lifeSpan, mem_ofPred_eq, mem_Ico, ENNReal.ofReal_lt_ofReal_iff hτ]

/-- A finite life span `T` is `[0, T.toReal)`. -/
theorem lifeSpan_of_ne_top {T : ℝ≥0∞} (hT : T ≠ ⊤) : lifeSpan T = Ico 0 T.toReal := by
  ext t
  simp only [lifeSpan, mem_ofPred_eq, mem_Ico]
  constructor
  · rintro ⟨ht0, ht⟩
    exact ⟨ht0, (ENNReal.ofReal_lt_iff_lt_toReal ht0 hT).mp ht⟩
  · rintro ⟨ht0, ht⟩
    exact ⟨ht0, (ENNReal.ofReal_lt_iff_lt_toReal ht0 hT).mpr ht⟩

/-- The infinite life span is `[0, ∞)`. -/
theorem lifeSpan_top : lifeSpan ⊤ = Ici 0 := by
  ext t
  simp [lifeSpan]

/-- A life span is an interval. -/
theorem ordConnected_lifeSpan (T : ℝ≥0∞) : (lifeSpan T).OrdConnected :=
  ⟨fun _ ha _ hb _ hc ↦ ⟨ha.1.trans hc.1, (ENNReal.ofReal_le_ofReal hc.2).trans_lt hb.2⟩⟩

/-- A positive life span contains `0`. -/
theorem zero_mem_lifeSpan {T : ℝ≥0∞} (hT : 0 < T) : (0 : ℝ) ∈ lifeSpan T :=
  ⟨le_rfl, by simpa using hT⟩

/-- A nonempty life span is positive. -/
theorem pos_of_mem_lifeSpan {T : ℝ≥0∞} {t : ℝ} (ht : t ∈ lifeSpan T) : 0 < T :=
  lt_of_le_of_lt zero_le ht.2

/-- `[0, t₀]` lies in the life span for every `t₀` in it. -/
theorem Icc_subset_lifeSpan {T : ℝ≥0∞} {t₀ : ℝ} (ht₀ : t₀ ∈ lifeSpan T) :
    Icc 0 t₀ ⊆ lifeSpan T :=
  fun _ ht ↦ ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt ht₀.2⟩

/-- Derivatives within a life span are unique. -/
theorem uniqueDiffOn_lifeSpan (T : ℝ≥0∞) : UniqueDiffOn ℝ (lifeSpan T) := by
  by_cases htop : T = ⊤
  · rw [htop, lifeSpan_top]
    exact uniqueDiffOn_Ici 0
  · rw [lifeSpan_of_ne_top htop]
    exact uniqueDiffOn_Ico 0 _

/-- A life span is measurable. -/
theorem measurableSet_lifeSpan (T : ℝ≥0∞) : MeasurableSet (lifeSpan T) :=
  (measurableSet_le measurable_const measurable_id).inter
    (measurableSet_lt ENNReal.measurable_ofReal measurable_const)

/-! ### Bounded supports -/

/-- The vorticity and the temperature vanish on the closed half-plane outside a disc that is
common to all times of every compact interval `[a, b] ⊆ I`. -/
def HasBoundedSupportOn (sol : VorticityStreamFields) (I : Set ℝ) : Prop :=
  ∀ a b : ℝ, Icc a b ⊆ I → ∃ R : ℝ, ∀ t ∈ Icc a b, ∀ x : ℝ^2, 0 ≤ x 1 → R < ‖x‖ →
    sol.vorticity x t = 0 ∧ sol.temperature x t = 0

/-- Bounded supports restrict to smaller sets of times. -/
theorem HasBoundedSupportOn.mono {sol : VorticityStreamFields} {I J : Set ℝ}
    (h : HasBoundedSupportOn sol I) (hJ : J ⊆ I) : HasBoundedSupportOn sol J :=
  fun a b hab ↦ h a b (hab.trans hJ)

/-! ### The continuation quantity -/

/-- The continuation quantity `∫₀^T (‖∇u(t)‖_∞ + ‖∇θ(t)‖_∞) dt`, with the sup norms over the open
upper half-plane. -/
def continuationIntegral (sol : VorticityStreamFields) (T : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ t in lifeSpan T,
    (⨆ x ∈ upperHalfPlane, ‖fderiv ℝ (fun y ↦ vorticityStreamVelocity sol y t) x‖ₑ) +
      ⨆ x ∈ upperHalfPlane, ‖fderiv ℝ (fun y ↦ sol.temperature y t) x‖ₑ

end Boussinesq.HalfPlane
