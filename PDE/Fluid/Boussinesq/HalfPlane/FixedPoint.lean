/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Convergence
import PDE.Analysis.Calculus.HolderInterpolation
import PDE.Analysis.Calculus.HolderLimit

/-!
# The fixed point of the Picard iteration for half-plane Boussinesq

Let the iteration map `carriedHistory ω₀ θ₀ (-T) T` preserve the class of `C^{1,α}` histories with
fixed bounds `IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁`, and let the carried amplitude of
every history of the class be `L`-Lipschitz in the label (`IsPicardSetting`).

Then the iterates `ωⁿ` from a history of the class converge, with their gradients within the closed
half-plane, uniformly on `[-T, T] × H̄`, with no smallness condition on `T`. The limit is a history
of the class and a fixed point of the iteration map on the closed half-plane
(`IsPicardSetting.exists_fixedPoint`, `exists_fixedPoint_of_isHolderData`).

## Main definitions

* `IsPicardSetting`: the hypotheses of the convergence argument, an invariant class of histories
  with an `L`-Lipschitz carried amplitude.
* `picardIterate`: the Picard iterates `(carriedHistory ω₀ θ₀ (-T) T)^[n] ω`.
* `runningSup`: the supremum of `|ω - ω'|` over the times `|r| ≤ s` and the closed half-plane.
* `picardLimit`: the pointwise limit of the Picard iterates.

## Main results

* `IsPicardSetting.runningSup_succ_le`: the step inequality `Dₙ₊₁,ₘ₊₁(s) ≤ C ∫₀ˢ φ_A(Dₙ,ₘ)`.
* `IsPicardSetting.picardIterate_cauchy`: the iterates are Cauchy uniformly on `[-T, T] × H̄`.
* `IsPicardSetting.fderivWithin_iterate_cauchy`: so are their derivatives within the closed
  half-plane.
* `IsPicardSetting.isC1VorticityHistory_picardLimit`: the limit is a history of the class.
* `IsPicardSetting.picardLimit_eq_carriedVorticity`: the limit is a fixed point of the iteration
  map on the closed half-plane.
* `exists_fixedPoint_of_isHolderData`: for data `IsHolderData ω₀ θ₀ α R N` and an invariant class
  with a Lipschitz carried amplitude, the iteration map has a fixed point in the class.

## How it works

The difference estimate `abs_carriedHistory_sub_le` gives the step inequality
`Dₙ₊₁,ₘ₊₁(s) ≤ C ∫₀ˢ φ_A(Dₙ,ₘ)` for the running suprema `Dₙ,ₘ` of `|ωⁿ - ωᵐ|`
(`IsPicardSetting.runningSup_succ_le`). The Cauchy form of Osgood's lemma for iterates,
`PDE.Analysis.forall_le_of_le_integral_osgoodModulus`, then makes `Dₙ,ₘ` small uniformly on `[0, T]`
(`IsPicardSetting.picardIterate_cauchy`). The gradients follow by interpolation between the sup norm
of the difference and the common Hölder bound of the gradients
(`PDE.Analysis.exists_norm_le_of_halfPlane`, in `IsPicardSetting.fderivWithin_iterate_cauchy`). The
limit is a history of the class: its derivative is the limit of the derivatives
(`PDE.Analysis.hasFDerivWithinAt_of_tendsto_of_holder`), and the bounds of the class pass to the
limit (`IsPicardSetting.isC1VorticityHistory_picardLimit`). The difference estimate, applied to the
limit and an iterate close to it, then shows that the limit is a fixed point
(`IsPicardSetting.picardLimit_eq_carriedVorticity`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace Boussinesq.HalfPlane

open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The hypotheses of the convergence argument: an interval `[-T, T]`, an exponent
`α ∈ (0, 1)`, a temperature datum `C²` within the closed half-plane with `‖Dθ₀‖ ≤ N` there, a
starting history of the class `IsC1VorticityHistory · (-T) T α R₁ B M B₁ M₁`, the invariance of
the class under the iteration map, and a Lipschitz bound `L` in the label of the carried
amplitude of every history of the class. -/
structure IsPicardSetting (ω₀ θ₀ : ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ)
    (T α R₁ B M B₁ M₁ N L : ℝ) : Prop where
  /-- The interval is nonempty. -/
  nonneg : 0 ≤ T
  /-- The exponent is positive. -/
  pos : 0 < α
  /-- The exponent is less than one. -/
  lt_one : α < 1
  /-- The temperature datum is `C²` within the closed half-plane. -/
  temperature_contDiffOn : ContDiffOn ℝ 2 θ₀ H̄
  /-- The gradient of the temperature datum is bounded by `N` on the closed half-plane. -/
  norm_fderivWithin_temperature_le : ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ θ₀ H̄ y‖ ≤ N
  /-- The Lipschitz constant is nonnegative. -/
  lipschitz_nonneg : 0 ≤ L
  /-- The starting history is in the class. -/
  start : IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁
  /-- The class is invariant under the iteration map. -/
  invariant : ∀ ω' : ℝ → ℝ^2 → ℝ, IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁ →
    IsC1VorticityHistory (carriedHistory ω₀ θ₀ (-T) T ω') (-T) T α R₁ B M B₁ M₁
  /-- The carried amplitude of every history of the class is `L`-Lipschitz in the label. -/
  lipschitz : ∀ ω' : ℝ → ℝ^2 → ℝ, IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁ →
    ∀ t ∈ Icc (-T) T, ∀ a' a'' : ℝ^2, 0 ≤ a' 1 → 0 ≤ a'' 1 →
      |forcedAmplitude (dataVorticity ω₀) (labelForcing (historyField ω') (historyFieldDeriv ω')
          (-T) T (dataTemperature θ₀) (EuclideanSpace.single 0 1)) a' t -
        forcedAmplitude (dataVorticity ω₀) (labelForcing (historyField ω') (historyFieldDeriv ω')
          (-T) T (dataTemperature θ₀) (EuclideanSpace.single 0 1)) a'' t| ≤ L * ‖a' - a''‖

/-- The Picard iterates `(carriedHistory ω₀ θ₀ (-T) T)^[n] ω`. -/
def picardIterate (ω₀ θ₀ : ℝ^2 → ℝ) (T : ℝ) (ω : ℝ → ℝ^2 → ℝ) (n : ℕ) : ℝ → ℝ^2 → ℝ :=
  (carriedHistory ω₀ θ₀ (-T) T)^[n] ω

/-- The iterate `n + 1` is the iteration map `carriedHistory ω₀ θ₀ (-T) T` applied to the
iterate `n`. -/
theorem picardIterate_succ (ω₀ θ₀ : ℝ^2 → ℝ) (T : ℝ) (ω : ℝ → ℝ^2 → ℝ) (n : ℕ) :
    picardIterate ω₀ θ₀ T ω (n + 1) = carriedHistory ω₀ θ₀ (-T) T (picardIterate ω₀ θ₀ T ω n) :=
  Function.iterate_succ_apply' _ _ _

/-! ### Running suprema of differences -/

section RunningSup

variable {ω ω' : ℝ → ℝ^2 → ℝ} {T B : ℝ}

/-- The supremum over the times `|r| ≤ s` and the closed half-plane of `|ω - ω'|`. -/
def runningSup (ω ω' : ℝ → ℝ^2 → ℝ) (s : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ^2 ↦ |ω p.1 p.2 - ω' p.1 p.2|) '' (Icc (-s) s ×ˢ H̄))

/-- If `|ω|, |ω'| ≤ B` on `[-T, T] × H̄`, the values of `|ω - ω'|` on `[-s, s] × H̄`, `s ≤ T`, are
bounded above. -/
theorem bddAbove_runningSup (hω : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y| ≤ B)
    (hω' : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω' r y| ≤ B) {s : ℝ} (hs : s ≤ T) :
    BddAbove ((fun p : ℝ × ℝ^2 ↦ |ω p.1 p.2 - ω' p.1 p.2|) '' (Icc (-s) s ×ˢ H̄)) := by
  refine ⟨2 * B, ?_⟩
  rintro _ ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩
  have hrT : r ∈ Icc (-T) T := ⟨by linarith [hr.1], hr.2.trans hs⟩
  calc |ω r y - ω' r y| ≤ |ω r y| + |ω' r y| := abs_sub _ _
    _ ≤ B + B := add_le_add (hω r hrT y hy) (hω' r hrT y hy)
    _ = 2 * B := by ring

/-- For `s ≥ 0` the set of values whose supremum is `runningSup ω ω' s` is nonempty. -/
theorem nonempty_runningSup {s : ℝ} (hs : 0 ≤ s) :
    ((fun p : ℝ × ℝ^2 ↦ |ω p.1 p.2 - ω' p.1 p.2|) '' (Icc (-s) s ×ˢ H̄)).Nonempty :=
  ⟨_, ⟨(0, 0), ⟨⟨by linarith, hs⟩, by simp⟩, rfl⟩⟩

/-- If `|ω|, |ω'| ≤ B` on `[-T, T] × H̄`, then `|ω r y - ω' r y| ≤ runningSup ω ω' s` for
`|r| ≤ s ≤ T` and `y` in the closed half-plane. -/
theorem le_runningSup (hω : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y| ≤ B)
    (hω' : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω' r y| ≤ B) {s : ℝ} (hs : s ≤ T) {r : ℝ}
    (hr : r ∈ Icc (-s) s) {y : ℝ^2} (hy : 0 ≤ y 1) : |ω r y - ω' r y| ≤ runningSup ω ω' s :=
  le_csSup (bddAbove_runningSup hω hω' hs) ⟨(r, y), ⟨hr, hy⟩, rfl⟩

/-- If `|ω - ω'| ≤ c` on `[-s, s] × H̄` with `s ≥ 0`, then `runningSup ω ω' s ≤ c`. -/
theorem runningSup_le {s c : ℝ} (hs : 0 ≤ s)
    (hc : ∀ r ∈ Icc (-s) s, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y - ω' r y| ≤ c) :
    runningSup ω ω' s ≤ c := by
  refine csSup_le (nonempty_runningSup hs) ?_
  rintro _ ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩
  exact hc r hr y hy

/-- If `|ω|, |ω'| ≤ B` on `[-T, T] × H̄`, the running supremum is monotone on `[0, T]`. -/
theorem monotoneOn_runningSup (hω : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y| ≤ B)
    (hω' : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω' r y| ≤ B) :
    MonotoneOn (runningSup ω ω') (Icc 0 T) := fun _ hs _ hs' hss' ↦
  csSup_le_csSup (bddAbove_runningSup hω hω' hs'.2) (nonempty_runningSup hs.1)
    (image_mono (prod_mono (Icc_subset_Icc (neg_le_neg hss') hss') subset_rfl))

/-- If `|ω|, |ω'| ≤ B` on `[-T, T] × H̄`, the running supremum is nonnegative on `[0, T]`. -/
theorem runningSup_nonneg (hω : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y| ≤ B)
    (hω' : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω' r y| ≤ B) {s : ℝ} (hs : s ∈ Icc 0 T) :
    0 ≤ runningSup ω ω' s :=
  (abs_nonneg _).trans (le_runningSup hω hω' hs.2 (r := 0) ⟨by linarith [hs.1], hs.1⟩
    (y := 0) (by simp))

/-- If `|ω|, |ω'| ≤ B` on `[-T, T] × H̄`, the running supremum is at most `2 B` on `[0, T]`. -/
theorem runningSup_le_two_mul {s : ℝ} (hω : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y| ≤ B)
    (hω' : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω' r y| ≤ B) (hs : s ∈ Icc 0 T) :
    runningSup ω ω' s ≤ 2 * B :=
  runningSup_le hs.1 fun r hr y hy ↦ by
    have hrT : r ∈ Icc (-T) T := ⟨by linarith [hr.1, hs.2], hr.2.trans hs.2⟩
    calc |ω r y - ω' r y| ≤ |ω r y| + |ω' r y| := abs_sub _ _
      _ ≤ B + B := add_le_add (hω r hrT y hy) (hω' r hrT y hy)
      _ = 2 * B := by ring

/-- If `|ω|, |ω'| ≤ B` on `[-T, T] × H̄`, then `|ω r y - ω' r y| ≤ runningSup ω ω' |r|` for
`r ∈ [-T, T]` and `y` in the closed half-plane. -/
theorem abs_sub_le_runningSup (hω : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y| ≤ B)
    (hω' : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω' r y| ≤ B) {r : ℝ} (hr : r ∈ Icc (-T) T)
    {y : ℝ^2} (hy : 0 ≤ y 1) : |ω r y - ω' r y| ≤ runningSup ω ω' |r| :=
  le_runningSup hω hω' (abs_le.mpr ⟨hr.1, hr.2⟩) ⟨neg_abs_le r, le_abs_self r⟩ hy

end RunningSup

/-- Two histories of the class with their running supremum as majorant form a comparison
pair. -/
theorem isHistoryPair_runningSup {ω ω' : ℝ → ℝ^2 → ℝ} {T α R₁ B M B₁ M₁ : ℝ} (hT : 0 ≤ T)
    (hα : 0 < α) (hα1 : α < 1) (hω : IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁)
    (hω' : IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁) (hB : 0 ≤ B) :
    IsHistoryPair ω ω' T α R₁ B M B₁ M₁ (runningSup ω ω') (2 * B + 1) where
  nonneg := hT
  pos := hα
  lt_one := hα1
  left := hω
  right := hω'
  bound_pos := by linarith
  monotoneOn := monotoneOn_runningSup hω.abs_le hω'.abs_le
  nonneg_majorant _ hs := runningSup_nonneg hω.abs_le hω'.abs_le hs
  le_bound _ hs := (runningSup_le_two_mul hω.abs_le hω'.abs_le hs).trans (by linarith)
  abs_sub_le _ hr _ hy := abs_sub_le_runningSup hω.abs_le hω'.abs_le hr hy

/-- The pointwise limit of the Picard iterates. -/
def picardLimit (ω₀ θ₀ : ℝ^2 → ℝ) (T : ℝ) (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) (x : ℝ^2) : ℝ :=
  limUnder atTop fun n ↦ picardIterate ω₀ θ₀ T ω n t x

/-- The pointwise limit of the derivatives within the closed half-plane of the Picard
iterates. -/
def picardLimitDeriv (ω₀ θ₀ : ℝ^2 → ℝ) (T : ℝ) (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) (x : ℝ^2) :
    ℝ^2 →L[ℝ] ℝ :=
  limUnder atTop fun n ↦ fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ x

namespace IsPicardSetting

variable {ω₀ θ₀ : ℝ^2 → ℝ} {ω : ℝ → ℝ^2 → ℝ} {T α R₁ B M B₁ M₁ N L : ℝ}
variable (hP : IsPicardSetting ω₀ θ₀ ω T α R₁ B M B₁ M₁ N L)
include hP

/-- The base time `0` lies in `[-T, T]`. -/
theorem zero_mem : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith [hP.nonneg], hP.nonneg⟩

/-- Every iterate is in the class. -/
theorem iterate_mem (n : ℕ) :
    IsC1VorticityHistory (picardIterate ω₀ θ₀ T ω n) (-T) T α R₁ B M B₁ M₁ := by
  induction n with
  | zero => exact hP.start
  | succ n ih => rw [picardIterate_succ]; exact hP.invariant _ ih

/-- The bound `B` of the vorticity histories is nonnegative. -/
theorem bound_nonneg : 0 ≤ B :=
  (abs_nonneg _).trans (hP.start.abs_le 0 hP.zero_mem 0 (by simp))

/-- The bound `N` of the temperature gradient is nonnegative. -/
theorem gradient_bound_nonneg : 0 ≤ N :=
  (norm_nonneg _).trans (hP.norm_fderivWithin_temperature_le 0 (by simp))

/-- The Hölder constant `M₁` of the vorticity gradient of the histories is nonnegative. -/
theorem holder_gradient_nonneg : 0 ≤ M₁ := by
  have h := hP.start.holder_fderivWithin 0 hP.zero_mem (EuclideanSpace.single 0 1) 0
    (by simp) (by simp)
  have hn : ‖(EuclideanSpace.single 0 1 : ℝ^2) - 0‖ = 1 := by simp
  rw [hn, Real.one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

/-- The histories of the iteration with their running supremum as majorant form comparison
pairs. -/
theorem isHistoryPair_iterate (n m : ℕ) :
    IsHistoryPair (picardIterate ω₀ θ₀ T ω n) (picardIterate ω₀ θ₀ T ω m) T α R₁ B M B₁ M₁
      (runningSup (picardIterate ω₀ θ₀ T ω n) (picardIterate ω₀ θ₀ T ω m)) (2 * B + 1) :=
  isHistoryPair_runningSup hP.nonneg hP.pos hP.lt_one (hP.iterate_mem n) (hP.iterate_mem m)
    hP.bound_nonneg

/-- The contraction constant `carriedSubConst` of the iteration map is nonnegative. -/
theorem carriedSubConst_nonneg : 0 ≤ carriedSubConst T α R₁ B M B₁ M₁ N L := by
  have h1 := (hP.isHistoryPair_iterate 0 0).variationSubConst_nonneg
  have h2 := IsHistoryPair.flowSubConst_nonneg (T := T) (α := α) (R₁ := R₁) (B := B) (M := M)
  have h3 := hP.gradient_bound_nonneg
  have h4 := hP.lipschitz_nonneg
  have h5 := hP.nonneg
  unfold carriedSubConst
  positivity

/-- **The step inequality of the iteration**: the running supremum of the difference of two
iterates is at most `C ∫₀ˢ φ_A` of the running supremum of the previous difference. -/
theorem runningSup_succ_le (n m : ℕ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    runningSup (picardIterate ω₀ θ₀ T ω (n + 1)) (picardIterate ω₀ θ₀ T ω (m + 1)) s ≤
      carriedSubConst T α R₁ B M B₁ M₁ N L *
        ∫ r in (0)..s, PDE.Analysis.osgoodModulus (pairModulusBound (2 * B + 1) M)
          (runningSup (picardIterate ω₀ θ₀ T ω n) (picardIterate ω₀ θ₀ T ω m) r) := by
  have hp := hP.isHistoryPair_iterate n m
  refine runningSup_le hs.1 fun r hr y hy ↦ ?_
  rw [picardIterate_succ, picardIterate_succ]
  have hrs : |r| ≤ s := abs_le.mpr ⟨hr.1, hr.2⟩
  have hrT : r ∈ Icc (-T) T := ⟨by linarith [hr.1, hs.2], hr.2.trans hs.2⟩
  have h := abs_carriedHistory_sub_le hp hP.temperature_contDiffOn
    hP.norm_fderivWithin_temperature_le hP.lipschitz_nonneg
    (hP.lipschitz _ (hP.iterate_mem n)) hrT hy
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hP.carriedSubConst_nonneg)
  exact integral_osgoodModulus_mono IsHistoryPair.modulus_pos hp.monotoneOn hp.nonneg_majorant
    hp.le_modulus (abs_nonneg r) hrs hs.2

/-- **The iterates are Cauchy** uniformly on `[-T, T] × H̄`. -/
theorem picardIterate_cauchy : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ t ∈ Icc (-T) T,
    ∀ x : ℝ^2, 0 ≤ x 1 →
      |picardIterate ω₀ θ₀ T ω n t x - picardIterate ω₀ θ₀ T ω m t x| ≤ ε := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := PDE.Analysis.forall_le_of_le_integral_osgoodModulus
    (fun n m ↦ runningSup (picardIterate ω₀ θ₀ T ω n) (picardIterate ω₀ θ₀ T ω m))
    (A := pairModulusBound (2 * B + 1) M) (T := T) IsHistoryPair.modulus_pos
    hP.carriedSubConst_nonneg (fun n m ↦ (hP.isHistoryPair_iterate n m).monotoneOn)
    (fun n m ↦ (hP.isHistoryPair_iterate n m).nonneg_majorant)
    (fun n m ↦ (hP.isHistoryPair_iterate n m).le_modulus)
    (fun n m _ hs ↦ hP.runningSup_succ_le n m hs) ε hε
  refine ⟨n₀, fun n hn m hm t ht x hx ↦ ?_⟩
  have hp := hP.isHistoryPair_iterate n m
  exact (hp.abs_sub_le t ht x hx).trans
    (hn₀ n hn m hm |t| ⟨abs_nonneg t, abs_le.mpr ⟨ht.1, ht.2⟩⟩)

/-- The iterates converge on `[-T, T] × H̄`. -/
theorem tendsto_picardLimit {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    Tendsto (fun n ↦ picardIterate ω₀ θ₀ T ω n t x) atTop
      (𝓝 (picardLimit ω₀ θ₀ T ω t x)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
  obtain ⟨n₀, hn₀⟩ := hP.picardIterate_cauchy (ε / 2) (half_pos hε)
  refine ⟨n₀, fun n hn ↦ ?_⟩
  rw [Real.dist_eq]
  exact (hn₀ n hn n₀ le_rfl t ht x hx).trans_lt (half_lt_self hε)

/-- The iterates converge uniformly on `[-T, T] × H̄`. -/
theorem picardIterate_uniform : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (-T) T,
    ∀ x : ℝ^2, 0 ≤ x 1 → |picardIterate ω₀ θ₀ T ω n t x - picardLimit ω₀ θ₀ T ω t x| ≤ ε := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hP.picardIterate_cauchy ε hε
  refine ⟨n₀, fun n hn t ht x hx ↦ ?_⟩
  exact le_of_tendsto ((tendsto_const_nhds.sub (hP.tendsto_picardLimit ht hx)).abs)
    (eventually_atTop.mpr ⟨n₀, fun m hm ↦ hn₀ n hn m hm t ht x hx⟩)

/-- Every iterate has its derivative within the closed half-plane. -/
theorem hasFDerivWithinAt_iterate (n : ℕ) {t : ℝ} (ht : t ∈ Icc (-T) T) {y : ℝ^2}
    (hy : 0 ≤ y 1) :
    HasFDerivWithinAt (picardIterate ω₀ θ₀ T ω n t)
      (fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ y) H̄ y :=
  (((hP.iterate_mem n).contDiffOn t ht).differentiableOn one_ne_zero y hy).hasFDerivWithinAt

/-- The derivatives within the closed half-plane of the iterates are Cauchy uniformly on
`[-T, T] × H̄`: interpolation between the sup norm and the common Hölder bound `2 M₁` of the
derivatives of differences. -/
theorem fderivWithin_iterate_cauchy : ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
    ∀ t ∈ Icc (-T) T, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ x -
        fderivWithin ℝ (picardIterate ω₀ θ₀ T ω m t) H̄ x‖ ≤ δ := by
  intro δ hδ
  have hM₁ := hP.holder_gradient_nonneg
  obtain ⟨η, hη, hint⟩ := PDE.Analysis.exists_norm_le_of_halfPlane (F := ℝ) (M := 2 * M₁)
    (by positivity) hP.pos hδ
  obtain ⟨n₀, hn₀⟩ := hP.picardIterate_cauchy η hη
  refine ⟨n₀, fun n hn m hm t ht x hx ↦ ?_⟩
  refine hint (fun y ↦ picardIterate ω₀ θ₀ T ω n t y - picardIterate ω₀ θ₀ T ω m t y)
    (fun y ↦ fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ y -
      fderivWithin ℝ (picardIterate ω₀ θ₀ T ω m t) H̄ y)
    (fun y hy ↦ (hP.hasFDerivWithinAt_iterate n ht hy).sub (hP.hasFDerivWithinAt_iterate m ht hy))
    (fun y hy ↦ by rw [Real.norm_eq_abs]; exact hn₀ n hn m hm t ht y hy) (fun y z hy hz ↦ ?_) x hx
  have h1 := (hP.iterate_mem n).holder_fderivWithin t ht y z hy hz
  have h2 := (hP.iterate_mem m).holder_fderivWithin t ht y z hy hz
  rw [sub_sub_sub_comm]
  calc _ ≤ ‖fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ y -
        fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ z‖ +
      ‖fderivWithin ℝ (picardIterate ω₀ θ₀ T ω m t) H̄ y -
        fderivWithin ℝ (picardIterate ω₀ θ₀ T ω m t) H̄ z‖ := norm_sub_le _ _
    _ ≤ M₁ * ‖y - z‖ ^ α + M₁ * ‖y - z‖ ^ α := add_le_add h1 h2
    _ = 2 * M₁ * ‖y - z‖ ^ α := by ring

/-- The derivatives of the iterates converge on `[-T, T] × H̄`. -/
theorem tendsto_picardLimitDeriv {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    Tendsto (fun n ↦ fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ x) atTop
      (𝓝 (picardLimitDeriv ω₀ θ₀ T ω t x)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
  obtain ⟨n₀, hn₀⟩ := hP.fderivWithin_iterate_cauchy (ε / 2) (half_pos hε)
  refine ⟨n₀, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  exact (hn₀ n hn n₀ le_rfl t ht x hx).trans_lt (half_lt_self hε)

/-- The derivatives of the iterates converge uniformly on `[-T, T] × H̄`. -/
theorem fderivWithin_iterate_uniform : ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (-T) T,
    ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ x - picardLimitDeriv ω₀ θ₀ T ω t x‖ ≤
        δ := by
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := hP.fderivWithin_iterate_cauchy δ hδ
  refine ⟨n₀, fun n hn t ht x hx ↦ ?_⟩
  exact le_of_tendsto ((tendsto_const_nhds.sub (hP.tendsto_picardLimitDeriv ht hx)).norm)
    (eventually_atTop.mpr ⟨n₀, fun m hm ↦ hn₀ n hn m hm t ht x hx⟩)

/-- The limit has the limit derivative within the closed half-plane. -/
theorem hasFDerivWithinAt_picardLimit {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    HasFDerivWithinAt (picardLimit ω₀ θ₀ T ω t) (picardLimitDeriv ω₀ θ₀ T ω t x) H̄ x :=
  PDE.Analysis.hasFDerivWithinAt_of_tendsto_of_holder PDE.Analysis.convex_closedUpperHalfPlane
    hP.holder_gradient_nonneg hP.pos (g := fun n ↦ picardIterate ω₀ θ₀ T ω n t)
    (G := fun n y ↦ fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ y)
    (fun n _ hy ↦ hP.hasFDerivWithinAt_iterate n ht hy)
    (fun n y hy z hz ↦ (hP.iterate_mem n).holder_fderivWithin t ht y z hy hz)
    (fun _ hy ↦ hP.tendsto_picardLimit ht hy) (fun _ hy ↦ hP.tendsto_picardLimitDeriv ht hy) hx

/-- The derivative of the limit within the closed half-plane is the limit derivative. -/
theorem fderivWithin_picardLimit {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (picardLimit ω₀ θ₀ T ω t) H̄ x = picardLimitDeriv ω₀ θ₀ T ω t x :=
  (hP.hasFDerivWithinAt_picardLimit ht hx).fderivWithin (uniqueDiffOn_closedUpper x hx)

/-- The limit derivative keeps the Hölder bound of the derivatives. -/
theorem picardLimitDeriv_holder {t : ℝ} (ht : t ∈ Icc (-T) T) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖picardLimitDeriv ω₀ θ₀ T ω t y - picardLimitDeriv ω₀ θ₀ T ω t z‖ ≤ M₁ * ‖y - z‖ ^ α := by
  have h := PDE.Analysis.norm_sub_le_of_tendsto_of_holder (T := H̄) (M := M₁) (α := α)
    (G := fun n y ↦ fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n t) H̄ y)
    (G' := picardLimitDeriv ω₀ θ₀ T ω t)
    (fun n y hy z hz ↦ by
      rw [dist_eq_norm]
      exact (hP.iterate_mem n).holder_fderivWithin t ht y z hy hz)
    (fun _ hy ↦ hP.tendsto_picardLimitDeriv ht hy) hy hz
  rwa [dist_eq_norm] at h

/-- **The limit is a history of the class.** -/
theorem isC1VorticityHistory_picardLimit :
    IsC1VorticityHistory (picardLimit ω₀ θ₀ T ω) (-T) T α R₁ B M B₁ M₁ where
  continuousOn t ht y hy := (hP.hasFDerivWithinAt_picardLimit ht hy).continuousWithinAt
  eq_zero t ht y hy hyR := tendsto_nhds_unique (hP.tendsto_picardLimit ht hy)
    (tendsto_const_nhds.congr fun n ↦ ((hP.iterate_mem n).eq_zero t ht y hy hyR).symm)
  abs_le t ht y hy := le_of_tendsto' (hP.tendsto_picardLimit ht hy).abs
    fun n ↦ (hP.iterate_mem n).abs_le t ht y hy
  holder t ht y z hy hz := le_of_tendsto'
    ((hP.tendsto_picardLimit ht hy).sub (hP.tendsto_picardLimit ht hz)).abs
    fun n ↦ (hP.iterate_mem n).holder t ht y z hy hz
  uniform t ht ε hε := by
    obtain ⟨n₀, hn₀⟩ := hP.picardIterate_uniform (ε / 3) (by positivity)
    obtain ⟨δ, hδ, hδε⟩ := (hP.iterate_mem n₀).uniform t ht (ε / 3) (by positivity)
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    have h1 := hn₀ n₀ le_rfl s hs y hy
    have h2 := hδε s hs hst y hy
    have h3 := hn₀ n₀ le_rfl t ht y hy
    calc |picardLimit ω₀ θ₀ T ω s y - picardLimit ω₀ θ₀ T ω t y|
        ≤ |picardIterate ω₀ θ₀ T ω n₀ s y - picardLimit ω₀ θ₀ T ω s y| +
          |picardIterate ω₀ θ₀ T ω n₀ s y - picardIterate ω₀ θ₀ T ω n₀ t y| +
          |picardIterate ω₀ θ₀ T ω n₀ t y - picardLimit ω₀ θ₀ T ω t y| := by
          have heq : picardLimit ω₀ θ₀ T ω s y - picardLimit ω₀ θ₀ T ω t y =
              -(picardIterate ω₀ θ₀ T ω n₀ s y - picardLimit ω₀ θ₀ T ω s y) +
              (picardIterate ω₀ θ₀ T ω n₀ s y - picardIterate ω₀ θ₀ T ω n₀ t y) +
              (picardIterate ω₀ θ₀ T ω n₀ t y - picardLimit ω₀ θ₀ T ω t y) := by ring
          rw [heq]
          exact (abs_add_three _ _ _).trans (by rw [abs_neg])
      _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add h1 h2) h3
      _ = ε := by ring
  contDiffOn t ht := by
    have hU := uniqueDiffOn_closedUpper
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm,
      contDiffOn_succ_iff_fderivWithin hU]
    refine ⟨fun y hy ↦ (hP.hasFDerivWithinAt_picardLimit ht hy).differentiableWithinAt,
      fun h ↦ absurd h (by simp), ?_⟩
    refine contDiffOn_zero.mpr (ContinuousOn.congr ?_ fun y hy ↦ hP.fderivWithin_picardLimit ht hy)
    exact PDE.Analysis.continuousOn_of_norm_sub_le_rpow hP.pos
      fun y hy z hz ↦ hP.picardLimitDeriv_holder ht hy hz
  norm_fderivWithin_le t ht y hy := by
    rw [hP.fderivWithin_picardLimit ht hy]
    exact le_of_tendsto' (hP.tendsto_picardLimitDeriv ht hy).norm
      fun n ↦ (hP.iterate_mem n).norm_fderivWithin_le t ht y hy
  holder_fderivWithin t ht y z hy hz := by
    rw [hP.fderivWithin_picardLimit ht hy, hP.fderivWithin_picardLimit ht hz]
    exact hP.picardLimitDeriv_holder ht hy hz
  uniform_fderivWithin t ht ε hε := by
    obtain ⟨n₀, hn₀⟩ := hP.fderivWithin_iterate_uniform (ε / 3) (by positivity)
    obtain ⟨δ, hδ, hδε⟩ := (hP.iterate_mem n₀).uniform_fderivWithin t ht (ε / 3) (by positivity)
    refine ⟨δ, hδ, fun s hs hst y hy ↦ ?_⟩
    rw [hP.fderivWithin_picardLimit hs hy, hP.fderivWithin_picardLimit ht hy]
    have h1 := hn₀ n₀ le_rfl s hs y hy
    have h2 := hδε s hs hst y hy
    have h3 := hn₀ n₀ le_rfl t ht y hy
    calc ‖picardLimitDeriv ω₀ θ₀ T ω s y - picardLimitDeriv ω₀ θ₀ T ω t y‖
        ≤ ‖fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n₀ s) H̄ y - picardLimitDeriv ω₀ θ₀ T ω s y‖ +
          ‖fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n₀ s) H̄ y -
            fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n₀ t) H̄ y‖ +
          ‖fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n₀ t) H̄ y -
            picardLimitDeriv ω₀ θ₀ T ω t y‖ := by
          have heq : picardLimitDeriv ω₀ θ₀ T ω s y - picardLimitDeriv ω₀ θ₀ T ω t y =
              -(fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n₀ s) H̄ y -
                picardLimitDeriv ω₀ θ₀ T ω s y) +
              (fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n₀ s) H̄ y -
                fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n₀ t) H̄ y) +
              (fderivWithin ℝ (picardIterate ω₀ θ₀ T ω n₀ t) H̄ y -
                picardLimitDeriv ω₀ θ₀ T ω t y) := by abel
          rw [heq]
          exact (norm_add₃_le).trans (by rw [norm_neg])
      _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add h1 h2) h3
      _ = ε := by ring

/-- **The limit is a fixed point** of the iteration map on the closed half-plane: at every
`t ∈ [-T, T]` and every `x` of the closed half-plane the limit history equals the vorticity it
carries. -/
theorem picardLimit_eq_carriedVorticity {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    picardLimit ω₀ θ₀ T ω t x = carriedVorticity ω₀ θ₀ (picardLimit ω₀ θ₀ T ω) (-T) T x t := by
  set ωl := picardLimit ω₀ θ₀ T ω
  have hl := hP.isC1VorticityHistory_picardLimit
  have hB := hP.bound_nonneg
  set C := carriedSubConst T α R₁ B M B₁ M₁ N L
  have hC := hP.carriedSubConst_nonneg
  set A := pairModulusBound (2 * B + 1) M
  have hA : 0 < A := IsHistoryPair.modulus_pos
  have htT : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
  have key : ∀ ε > 0, |carriedHistory ω₀ θ₀ (-T) T ωl t x - ωl t x| ≤
      C * (T * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hP.picardIterate_uniform ε hε
    set ωn := picardIterate ω₀ θ₀ T ω n₀
    have hmin0 : 0 ≤ min ε (2 * B) := le_min hε.le (by linarith)
    have hp : IsHistoryPair ωl ωn T α R₁ B M B₁ M₁ (fun _ ↦ min ε (2 * B)) (2 * B + 1) :=
      { nonneg := hP.nonneg
        pos := hP.pos
        lt_one := hP.lt_one
        left := hl
        right := hP.iterate_mem n₀
        bound_pos := by linarith
        monotoneOn := monotoneOn_const
        nonneg_majorant := fun _ _ ↦ hmin0
        le_bound := fun _ _ ↦ (min_le_right _ _).trans (by linarith)
        abs_sub_le := fun r hr y hy ↦ le_min
          (by rw [abs_sub_comm]; exact hn₀ n₀ le_rfl r hr y hy)
          (by
            calc |ωl r y - ωn r y| ≤ |ωl r y| + |ωn r y| := abs_sub _ _
              _ ≤ B + B := add_le_add (hl.abs_le r hr y hy)
                  ((hP.iterate_mem n₀).abs_le r hr y hy)
              _ = 2 * B := by ring) }
    have h := abs_carriedHistory_sub_le hp hP.temperature_contDiffOn
      hP.norm_fderivWithin_temperature_le hP.lipschitz_nonneg (hP.lipschitz _ hl) ht hx
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    have h2 := hn₀ (n₀ + 1) (by omega) t ht x hx
    rw [picardIterate_succ] at h2
    have hφ0 : 0 ≤ PDE.Analysis.osgoodModulus A (min ε (2 * B)) :=
      PDE.Analysis.osgoodModulus_nonneg hmin0 (hp.le_modulus 0 ⟨le_rfl, hP.nonneg⟩)
    calc |carriedHistory ω₀ θ₀ (-T) T ωl t x - ωl t x|
        ≤ |carriedHistory ω₀ θ₀ (-T) T ωl t x - carriedHistory ω₀ θ₀ (-T) T ωn t x| +
          |carriedHistory ω₀ θ₀ (-T) T ωn t x - ωl t x| := abs_sub_le _ _ _
      _ ≤ C * (|t| * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε := add_le_add h h2
      _ ≤ C * (T * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε := by
          gcongr
  have hcont : Continuous fun ε : ℝ ↦
      C * (T * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε :=
    (continuous_const.mul (continuous_const.mul
      ((PDE.Analysis.continuous_osgoodModulus hA).comp
        (continuous_id.min continuous_const)))).add continuous_id
  have hlim : Tendsto (fun ε : ℝ ↦ C * (T * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε)
      (𝓝[>] 0) (𝓝 0) := by
    have h := hcont.tendsto 0
    simp only [min_eq_left (by linarith : (0 : ℝ) ≤ 2 * B), PDE.Analysis.osgoodModulus_zero,
      mul_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  change ωl t x = carriedHistory ω₀ θ₀ (-T) T ωl t x
  by_contra hne
  have hd : 0 < |carriedHistory ω₀ θ₀ (-T) T ωl t x - ωl t x| :=
    abs_pos.mpr (sub_ne_zero.mpr fun h ↦ hne h.symm)
  obtain ⟨ε, hεd, hε⟩ := ((hlim.eventually (Iio_mem_nhds hd)).and self_mem_nhdsWithin).exists
  exact absurd (key ε hε) (not_le.mpr hεd)

/-- **Existence of a fixed point** of the iteration map in the class. -/
theorem exists_fixedPoint : ∃ ω' : ℝ → ℝ^2 → ℝ,
    IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁ ∧
      ∀ t ∈ Icc (-T) T, ∀ x : ℝ^2, 0 ≤ x 1 → ω' t x = carriedVorticity ω₀ θ₀ ω' (-T) T x t :=
  ⟨_, hP.isC1VorticityHistory_picardLimit,
    fun _ ht _ hx ↦ hP.picardLimit_eq_carriedVorticity ht hx⟩

end IsPicardSetting

/-- **The fixed point of the Picard iteration.** For data `IsHolderData ω₀ θ₀ α R N`,
`0 < α < 1`, `T ≥ 0`, a class `IsC1VorticityHistory · (-T) T α R₁ B M B₁ M₁` that contains a
starting history and is invariant under the iteration map, and a Lipschitz bound `L ≥ 0` in the
label of the carried amplitude of every history of the class, there is a history of the class
that equals the vorticity it carries on `[-T, T] × H̄`. -/
theorem exists_fixedPoint_of_isHolderData {ω₀ θ₀ : ℝ^2 → ℝ} {ω : ℝ → ℝ^2 → ℝ}
    {T α R N R₁ B M B₁ M₁ L : ℝ} (hdata : IsHolderData ω₀ θ₀ α R N) (hT : 0 ≤ T) (hα : 0 < α)
    (hα1 : α < 1) (hL0 : 0 ≤ L) (h0 : IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁)
    (hinv : ∀ ω' : ℝ → ℝ^2 → ℝ, IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁ →
      IsC1VorticityHistory (carriedHistory ω₀ θ₀ (-T) T ω') (-T) T α R₁ B M B₁ M₁)
    (hLip : ∀ ω' : ℝ → ℝ^2 → ℝ, IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁ →
      ∀ t ∈ Icc (-T) T, ∀ a' a'' : ℝ^2, 0 ≤ a' 1 → 0 ≤ a'' 1 →
        |forcedAmplitude (dataVorticity ω₀) (labelForcing (historyField ω')
            (historyFieldDeriv ω') (-T) T (dataTemperature θ₀) (EuclideanSpace.single 0 1)) a' t -
          forcedAmplitude (dataVorticity ω₀) (labelForcing (historyField ω')
            (historyFieldDeriv ω') (-T) T (dataTemperature θ₀) (EuclideanSpace.single 0 1)) a''
            t| ≤ L * ‖a' - a''‖) :
    ∃ ω' : ℝ → ℝ^2 → ℝ, IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁ ∧
      ∀ t ∈ Icc (-T) T, ∀ x : ℝ^2, 0 ≤ x 1 → ω' t x = carriedVorticity ω₀ θ₀ ω' (-T) T x t :=
  (IsPicardSetting.mk hT hα hα1 hdata.temperature_contDiffOn
    hdata.norm_fderivWithin_temperature_le hL0 h0 hinv hLip (ω := ω)).exists_fixedPoint

end Boussinesq.HalfPlane
