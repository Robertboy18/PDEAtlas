/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.FixedPoint
import PDE.Analysis.Calculus.HolderInterpolation
import PDE.Analysis.Calculus.HolderLimit

/-!
# Fixed points of maps of Osgood type on vorticity histories

A map with a small Lipschitz constant has a fixed point by the contraction principle. The iteration
map of a transport system with a log-Lipschitz velocity satisfies only an estimate with the Osgood
modulus `φ_A(r) = r (1 + log (A / r))`. This module proves that the iteration still converges, on a
time interval of any length, and that the limit is a fixed point in the same class.

Let a map `Φ` on vorticity histories preserve the class of `C^{1,α}` histories with fixed bounds,
`IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁`, and satisfy on it a difference estimate of Osgood
type: if `|ω - ω'| ≤ Dm(|r|)` on the closed half-plane at time `r`, with `Dm` nondecreasing with
values in `[0, 2 B + 1]`, then `|Φ ω - Φ ω'| ≤ c ∫₀^{|t|} φ_A(Dm)` at time `t`
(`IsOsgoodIteration`). Then:

* the iterates `Φⁿ ω` from a history of the class are Cauchy uniformly on `[-T, T] × H̄`, by the
  Osgood tail argument applied to the running suprema of the differences, with no smallness of `T`;
* their gradients within the closed half-plane are Cauchy as well, by interpolation between the sup
  norm and the common Hölder bound of the gradients;
* the limit is a history of the class and a fixed point of `Φ` on the closed half-plane.

No rate of convergence is stated, and uniqueness of the fixed point is not proved here; uniqueness
of solutions is in `Uniqueness.lean`.

## Main results

* `IsOsgoodIteration`: maps of Osgood type on a class of `C^{1,α}` histories.
* `picardIterate`, `picardLimit`, `picardLimitDeriv`: the iterates, their pointwise limit and the
  pointwise limit of their gradients.
* `IsOsgoodIteration.runningSup_succ_le`: the step inequality: the running supremum of the
  difference of two iterates is at most `c ∫₀ˢ φ_A` of the running supremum of the difference of the
  two iterates before them.
* `IsOsgoodIteration.picardIterate_cauchy`, `IsOsgoodIteration.fderivWithin_iterate_cauchy`: the
  iterates and their gradients are Cauchy uniformly on `[-T, T] × H̄`.
* `IsOsgoodIteration.isC1VorticityHistory_picardLimit`: the limit is a history of the class, with
  the same bounds.
* `IsOsgoodIteration.picardLimit_eq`, `IsOsgoodIteration.exists_fixedPoint`: the limit is a fixed
  point of `Φ` on the closed half-plane at every time of `[-T, T]`.

The module uses no other module of this folder. `LocalExistence.lean` proves that the iteration map
of a half-plane system is of Osgood type (`isOsgoodIteration_carriedHistory`) and takes the fixed
point as the vorticity of a solution; `IterationHigher.lean` uses the convergence of the iterates to
pass regularity of order `k` to the limit.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal Topology
open IncompressibleFlow Boussinesq.HalfPlane

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- A map `Φ` of Osgood type on the class `IsC1VorticityHistory · (-T) T α R₁ B M B₁ M₁` with a
starting history `ω` of the class: the class is invariant, and two histories of the class that
differ by at most `Dm |r|` on the closed half-plane, `Dm` nondecreasing with values in
`[0, 2 B + 1]`, have images that differ by at most `c ∫₀^{|t|} φ_A(Dm)`. -/
structure IsOsgoodIteration (Φ : (ℝ → ℝ^2 → ℝ) → ℝ → ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ)
    (T α R₁ B M B₁ M₁ c A : ℝ) : Prop where
  /-- The interval is nonempty. -/
  nonneg : 0 ≤ T
  /-- The exponent is positive. -/
  pos : 0 < α
  /-- The constant of the difference estimate is nonnegative. -/
  const_nonneg : 0 ≤ c
  /-- The Osgood parameter is positive. -/
  modulus_pos : 0 < A
  /-- The majorants are at most the Osgood parameter. -/
  le_modulus : 2 * B + 1 ≤ A
  /-- The starting history is in the class. -/
  start : IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁
  /-- The class is invariant. -/
  invariant : ∀ ω' : ℝ → ℝ^2 → ℝ, IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁ →
    IsC1VorticityHistory (Φ ω') (-T) T α R₁ B M B₁ M₁
  /-- The difference estimate of Osgood type. -/
  abs_map_sub_le : ∀ ω₁ ω₂ : ℝ → ℝ^2 → ℝ, IsC1VorticityHistory ω₁ (-T) T α R₁ B M B₁ M₁ →
    IsC1VorticityHistory ω₂ (-T) T α R₁ B M B₁ M₁ → ∀ Dm : ℝ → ℝ, MonotoneOn Dm (Icc 0 T) →
    (∀ s ∈ Icc 0 T, 0 ≤ Dm s) → (∀ s ∈ Icc 0 T, Dm s ≤ 2 * B + 1) →
    (∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω₁ r y - ω₂ r y| ≤ Dm |r|) →
    ∀ t ∈ Icc (-T) T, ∀ x : ℝ^2, 0 ≤ x 1 →
      |Φ ω₁ t x - Φ ω₂ t x| ≤ c * ∫ r in (0)..|t|, PDE.Analysis.osgoodModulus A (Dm r)

/-- The iterates `Φ^[n] ω`. -/
def picardIterate (Φ : (ℝ → ℝ^2 → ℝ) → ℝ → ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ) (n : ℕ) :
    ℝ → ℝ^2 → ℝ :=
  Φ^[n] ω

/-- The iterate of order `n + 1` is the map applied to the iterate of order `n`. -/
theorem picardIterate_succ (Φ : (ℝ → ℝ^2 → ℝ) → ℝ → ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ) (n : ℕ) :
    picardIterate Φ ω (n + 1) = Φ (picardIterate Φ ω n) :=
  Function.iterate_succ_apply' _ _ _

/-- The pointwise limit of the iterates. -/
def picardLimit (Φ : (ℝ → ℝ^2 → ℝ) → ℝ → ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) (x : ℝ^2) : ℝ :=
  limUnder atTop fun n ↦ picardIterate Φ ω n t x

/-- The pointwise limit of the derivatives within the closed half-plane of the iterates. -/
def picardLimitDeriv (Φ : (ℝ → ℝ^2 → ℝ) → ℝ → ℝ^2 → ℝ) (ω : ℝ → ℝ^2 → ℝ) (t : ℝ) (x : ℝ^2) :
    ℝ^2 →L[ℝ] ℝ :=
  limUnder atTop fun n ↦ fderivWithin ℝ (picardIterate Φ ω n t) H̄ x

namespace IsOsgoodIteration

variable {Φ : (ℝ → ℝ^2 → ℝ) → ℝ → ℝ^2 → ℝ} {ω : ℝ → ℝ^2 → ℝ} {T α R₁ B M B₁ M₁ c A : ℝ}
variable (hP : IsOsgoodIteration Φ ω T α R₁ B M B₁ M₁ c A)
include hP

/-- The time `0` lies in `[-T, T]`. -/
theorem zero_mem : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith [hP.nonneg], hP.nonneg⟩

/-- Every iterate is in the class. -/
theorem iterate_mem (n : ℕ) :
    IsC1VorticityHistory (picardIterate Φ ω n) (-T) T α R₁ B M B₁ M₁ := by
  induction n with
  | zero => exact hP.start
  | succ n ih => rw [picardIterate_succ]; exact hP.invariant _ ih

/-- The bound `B` of the class is nonnegative. -/
theorem bound_nonneg : 0 ≤ B :=
  (abs_nonneg _).trans (hP.start.abs_le 0 hP.zero_mem 0 (by simp))

/-- The Hölder constant `M₁` of the gradient is nonnegative. -/
theorem holder_gradient_nonneg : 0 ≤ M₁ := by
  have h := hP.start.holder_fderivWithin 0 hP.zero_mem (EuclideanSpace.single 0 1) 0
    (by simp) (by simp)
  have hn : ‖(EuclideanSpace.single 0 1 : ℝ^2) - 0‖ = 1 := by simp
  rw [hn, Real.one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

/-- The running suprema of the differences of the iterates are majorants. -/
theorem runningSup_le_bound (n m : ℕ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    runningSup (picardIterate Φ ω n) (picardIterate Φ ω m) s ≤ 2 * B + 1 :=
  (runningSup_le_two_mul (hP.iterate_mem n).abs_le (hP.iterate_mem m).abs_le hs).trans
    (by linarith)

/-- **The step inequality of the iteration**: the running supremum of the difference of two
iterates is at most `c ∫₀ˢ φ_A` of the running supremum of the previous difference. -/
theorem runningSup_succ_le (n m : ℕ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    runningSup (picardIterate Φ ω (n + 1)) (picardIterate Φ ω (m + 1)) s ≤
      c * ∫ r in (0)..s, PDE.Analysis.osgoodModulus A
        (runningSup (picardIterate Φ ω n) (picardIterate Φ ω m) r) := by
  have hn := hP.iterate_mem n
  have hm := hP.iterate_mem m
  have hmono := monotoneOn_runningSup hn.abs_le hm.abs_le
  have h0 := fun s hs ↦ runningSup_nonneg hn.abs_le hm.abs_le (s := s) hs
  have hle := fun s hs ↦ hP.runningSup_le_bound n m (s := s) hs
  refine runningSup_le hs.1 fun r hr y hy ↦ ?_
  rw [picardIterate_succ, picardIterate_succ]
  have hrs : |r| ≤ s := abs_le.mpr ⟨hr.1, hr.2⟩
  have hrT : r ∈ Icc (-T) T := ⟨by linarith [hr.1, hs.2], hr.2.trans hs.2⟩
  have h := hP.abs_map_sub_le _ _ hn hm _ hmono h0 hle
    (fun r hr y hy ↦ abs_sub_le_runningSup hn.abs_le hm.abs_le hr hy) r hrT y hy
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hP.const_nonneg)
  exact integral_osgoodModulus_mono hP.modulus_pos hmono h0
    (fun s hs ↦ (hle s hs).trans hP.le_modulus) (abs_nonneg r) hrs hs.2

/-- **The iterates are Cauchy** uniformly on `[-T, T] × H̄`. This replaces the contraction
principle: no smallness of `T` is needed. Proof: the running suprema of the differences of the
iterates are nondecreasing in time, bounded by `2 B + 1` and satisfy the step inequality
`runningSup_succ_le`, so the Osgood tail lemma makes them uniformly small from some index on. -/
theorem picardIterate_cauchy : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ t ∈ Icc (-T) T,
    ∀ x : ℝ^2, 0 ≤ x 1 → |picardIterate Φ ω n t x - picardIterate Φ ω m t x| ≤ ε := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := PDE.Analysis.forall_le_of_le_integral_osgoodModulus
    (fun n m ↦ runningSup (picardIterate Φ ω n) (picardIterate Φ ω m)) (A := A) (T := T)
    hP.modulus_pos hP.const_nonneg
    (fun n m ↦ monotoneOn_runningSup (hP.iterate_mem n).abs_le (hP.iterate_mem m).abs_le)
    (fun n m _ hs ↦ runningSup_nonneg (hP.iterate_mem n).abs_le (hP.iterate_mem m).abs_le hs)
    (fun n m _ hs ↦ (hP.runningSup_le_bound n m hs).trans hP.le_modulus)
    (fun n m _ hs ↦ hP.runningSup_succ_le n m hs) ε hε
  refine ⟨n₀, fun n hn m hm t ht x hx ↦ ?_⟩
  exact (abs_sub_le_runningSup (hP.iterate_mem n).abs_le (hP.iterate_mem m).abs_le ht hx).trans
    (hn₀ n hn m hm |t| ⟨abs_nonneg t, abs_le.mpr ⟨ht.1, ht.2⟩⟩)

/-- The iterates converge on `[-T, T] × H̄`. -/
theorem tendsto_picardLimit {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    Tendsto (fun n ↦ picardIterate Φ ω n t x) atTop (𝓝 (picardLimit Φ ω t x)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
  obtain ⟨n₀, hn₀⟩ := hP.picardIterate_cauchy (ε / 2) (half_pos hε)
  refine ⟨n₀, fun n hn ↦ ?_⟩
  rw [Real.dist_eq]
  exact (hn₀ n hn n₀ le_rfl t ht x hx).trans_lt (half_lt_self hε)

/-- The iterates converge uniformly on `[-T, T] × H̄`. -/
theorem picardIterate_uniform : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (-T) T,
    ∀ x : ℝ^2, 0 ≤ x 1 → |picardIterate Φ ω n t x - picardLimit Φ ω t x| ≤ ε := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hP.picardIterate_cauchy ε hε
  refine ⟨n₀, fun n hn t ht x hx ↦ ?_⟩
  exact le_of_tendsto ((tendsto_const_nhds.sub (hP.tendsto_picardLimit ht hx)).abs)
    (eventually_atTop.mpr ⟨n₀, fun m hm ↦ hn₀ n hn m hm t ht x hx⟩)

/-- Every iterate has its derivative within the closed half-plane. -/
theorem hasFDerivWithinAt_iterate (n : ℕ) {t : ℝ} (ht : t ∈ Icc (-T) T) {y : ℝ^2}
    (hy : 0 ≤ y 1) :
    HasFDerivWithinAt (picardIterate Φ ω n t)
      (fderivWithin ℝ (picardIterate Φ ω n t) H̄ y) H̄ y :=
  (((hP.iterate_mem n).contDiffOn t ht).differentiableOn one_ne_zero y hy).hasFDerivWithinAt

/-- The derivatives within the closed half-plane of the iterates are Cauchy uniformly on
`[-T, T] × H̄`: interpolation between the sup norm and the common Hölder bound `2 M₁` of the
derivatives of differences. -/
theorem fderivWithin_iterate_cauchy : ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
    ∀ t ∈ Icc (-T) T, ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (picardIterate Φ ω n t) H̄ x -
        fderivWithin ℝ (picardIterate Φ ω m t) H̄ x‖ ≤ δ := by
  intro δ hδ
  have hM₁ := hP.holder_gradient_nonneg
  obtain ⟨η, hη, hint⟩ := PDE.Analysis.exists_norm_le_of_halfPlane (F := ℝ) (M := 2 * M₁)
    (by positivity) hP.pos hδ
  obtain ⟨n₀, hn₀⟩ := hP.picardIterate_cauchy η hη
  refine ⟨n₀, fun n hn m hm t ht x hx ↦ ?_⟩
  refine hint (fun y ↦ picardIterate Φ ω n t y - picardIterate Φ ω m t y)
    (fun y ↦ fderivWithin ℝ (picardIterate Φ ω n t) H̄ y -
      fderivWithin ℝ (picardIterate Φ ω m t) H̄ y)
    (fun y hy ↦ (hP.hasFDerivWithinAt_iterate n ht hy).sub (hP.hasFDerivWithinAt_iterate m ht hy))
    (fun y hy ↦ by rw [Real.norm_eq_abs]; exact hn₀ n hn m hm t ht y hy) (fun y z hy hz ↦ ?_) x hx
  have h1 := (hP.iterate_mem n).holder_fderivWithin t ht y z hy hz
  have h2 := (hP.iterate_mem m).holder_fderivWithin t ht y z hy hz
  rw [sub_sub_sub_comm]
  calc _ ≤ ‖fderivWithin ℝ (picardIterate Φ ω n t) H̄ y -
        fderivWithin ℝ (picardIterate Φ ω n t) H̄ z‖ +
      ‖fderivWithin ℝ (picardIterate Φ ω m t) H̄ y -
        fderivWithin ℝ (picardIterate Φ ω m t) H̄ z‖ := norm_sub_le _ _
    _ ≤ M₁ * ‖y - z‖ ^ α + M₁ * ‖y - z‖ ^ α := add_le_add h1 h2
    _ = 2 * M₁ * ‖y - z‖ ^ α := by ring

/-- The derivatives of the iterates converge on `[-T, T] × H̄`. -/
theorem tendsto_picardLimitDeriv {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    Tendsto (fun n ↦ fderivWithin ℝ (picardIterate Φ ω n t) H̄ x) atTop
      (𝓝 (picardLimitDeriv Φ ω t x)) := by
  refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
  refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
  obtain ⟨n₀, hn₀⟩ := hP.fderivWithin_iterate_cauchy (ε / 2) (half_pos hε)
  refine ⟨n₀, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  exact (hn₀ n hn n₀ le_rfl t ht x hx).trans_lt (half_lt_self hε)

/-- The derivatives of the iterates converge uniformly on `[-T, T] × H̄`. -/
theorem fderivWithin_iterate_uniform : ∀ δ > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (-T) T,
    ∀ x : ℝ^2, 0 ≤ x 1 →
      ‖fderivWithin ℝ (picardIterate Φ ω n t) H̄ x - picardLimitDeriv Φ ω t x‖ ≤ δ := by
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := hP.fderivWithin_iterate_cauchy δ hδ
  refine ⟨n₀, fun n hn t ht x hx ↦ ?_⟩
  exact le_of_tendsto ((tendsto_const_nhds.sub (hP.tendsto_picardLimitDeriv ht hx)).norm)
    (eventually_atTop.mpr ⟨n₀, fun m hm ↦ hn₀ n hn m hm t ht x hx⟩)

/-- The limit has the limit derivative within the closed half-plane. -/
theorem hasFDerivWithinAt_picardLimit {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    HasFDerivWithinAt (picardLimit Φ ω t) (picardLimitDeriv Φ ω t x) H̄ x :=
  PDE.Analysis.hasFDerivWithinAt_of_tendsto_of_holder PDE.Analysis.convex_closedUpperHalfPlane
    hP.holder_gradient_nonneg hP.pos (g := fun n ↦ picardIterate Φ ω n t)
    (G := fun n y ↦ fderivWithin ℝ (picardIterate Φ ω n t) H̄ y)
    (fun n _ hy ↦ hP.hasFDerivWithinAt_iterate n ht hy)
    (fun n y hy z hz ↦ (hP.iterate_mem n).holder_fderivWithin t ht y z hy hz)
    (fun _ hy ↦ hP.tendsto_picardLimit ht hy) (fun _ hy ↦ hP.tendsto_picardLimitDeriv ht hy) hx

/-- The derivative of the limit within the closed half-plane is the limit derivative. -/
theorem fderivWithin_picardLimit {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (picardLimit Φ ω t) H̄ x = picardLimitDeriv Φ ω t x :=
  (hP.hasFDerivWithinAt_picardLimit ht hx).fderivWithin (uniqueDiffOn_closedUpper x hx)

/-- The limit derivative keeps the Hölder bound of the derivatives. -/
theorem picardLimitDeriv_holder {t : ℝ} (ht : t ∈ Icc (-T) T) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖picardLimitDeriv Φ ω t y - picardLimitDeriv Φ ω t z‖ ≤ M₁ * ‖y - z‖ ^ α := by
  have h := PDE.Analysis.norm_sub_le_of_tendsto_of_holder (T := H̄) (M := M₁) (α := α)
    (G := fun n y ↦ fderivWithin ℝ (picardIterate Φ ω n t) H̄ y)
    (G' := picardLimitDeriv Φ ω t)
    (fun n y hy z hz ↦ by
      rw [dist_eq_norm]
      exact (hP.iterate_mem n).holder_fderivWithin t ht y z hy hz)
    (fun _ hy ↦ hP.tendsto_picardLimitDeriv ht hy) hy hz
  rwa [dist_eq_norm] at h

/-- **The limit is a history of the class**, with the same support radius and the same bounds.
So the class of the iteration is closed under the limit. Proof: the values and the gradients of
the iterates converge uniformly, so the support, the bounds, the Hölder constants and the
continuity in time pass to the limit, and the limit of the gradients is the gradient of the
limit. -/
theorem isC1VorticityHistory_picardLimit :
    IsC1VorticityHistory (picardLimit Φ ω) (-T) T α R₁ B M B₁ M₁ where
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
    calc |picardLimit Φ ω s y - picardLimit Φ ω t y|
        ≤ |picardIterate Φ ω n₀ s y - picardLimit Φ ω s y| +
          |picardIterate Φ ω n₀ s y - picardIterate Φ ω n₀ t y| +
          |picardIterate Φ ω n₀ t y - picardLimit Φ ω t y| := by
          have heq : picardLimit Φ ω s y - picardLimit Φ ω t y =
              -(picardIterate Φ ω n₀ s y - picardLimit Φ ω s y) +
              (picardIterate Φ ω n₀ s y - picardIterate Φ ω n₀ t y) +
              (picardIterate Φ ω n₀ t y - picardLimit Φ ω t y) := by ring
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
    calc ‖picardLimitDeriv Φ ω s y - picardLimitDeriv Φ ω t y‖
        ≤ ‖fderivWithin ℝ (picardIterate Φ ω n₀ s) H̄ y - picardLimitDeriv Φ ω s y‖ +
          ‖fderivWithin ℝ (picardIterate Φ ω n₀ s) H̄ y -
            fderivWithin ℝ (picardIterate Φ ω n₀ t) H̄ y‖ +
          ‖fderivWithin ℝ (picardIterate Φ ω n₀ t) H̄ y - picardLimitDeriv Φ ω t y‖ := by
          have heq : picardLimitDeriv Φ ω s y - picardLimitDeriv Φ ω t y =
              -(fderivWithin ℝ (picardIterate Φ ω n₀ s) H̄ y - picardLimitDeriv Φ ω s y) +
              (fderivWithin ℝ (picardIterate Φ ω n₀ s) H̄ y -
                fderivWithin ℝ (picardIterate Φ ω n₀ t) H̄ y) +
              (fderivWithin ℝ (picardIterate Φ ω n₀ t) H̄ y - picardLimitDeriv Φ ω t y) := by
            abel
          rw [heq]
          exact (norm_add₃_le).trans (by rw [norm_neg])
      _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add (add_le_add h1 h2) h3
      _ = ε := by ring

/-- **The limit is a fixed point** of `Φ` on the closed half-plane at every time of
`[-T, T]`. Proof: for `ε > 0` an iterate is within `ε` of the limit, uniformly. The difference
estimate bounds `|Φ(limit) - Φ(iterate)|` by `c T φ_A(min ε (2B))`, and the next iterate is
within `ε` of the limit, so `|Φ(limit) - limit|` is at most a quantity that tends to zero
with `ε`. -/
theorem picardLimit_eq {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    picardLimit Φ ω t x = Φ (picardLimit Φ ω) t x := by
  set ωl := picardLimit Φ ω
  have hl := hP.isC1VorticityHistory_picardLimit
  have hB := hP.bound_nonneg
  have hC := hP.const_nonneg
  have hA := hP.modulus_pos
  have htT : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
  -- For every `ε > 0` the defect `|Φ(limit) - limit|` is at most `c T φ_A(min ε (2B)) + ε`:
  -- compare with an iterate that is within `ε` of the limit and with the next iterate.
  have key : ∀ ε > 0, |Φ ωl t x - ωl t x| ≤
      c * (T * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hP.picardIterate_uniform ε hε
    set ωn := picardIterate Φ ω n₀
    have hmin0 : 0 ≤ min ε (2 * B) := le_min hε.le (by linarith)
    have hminA : min ε (2 * B) ≤ A := (min_le_right _ _).trans (by linarith [hP.le_modulus])
    have h := hP.abs_map_sub_le ωl ωn hl (hP.iterate_mem n₀) (fun _ ↦ min ε (2 * B))
      monotoneOn_const (fun _ _ ↦ hmin0) (fun _ _ ↦ (min_le_right _ _).trans (by linarith))
      (fun r hr y hy ↦ le_min
        (by rw [abs_sub_comm]; exact hn₀ n₀ le_rfl r hr y hy)
        (by
          calc |ωl r y - ωn r y| ≤ |ωl r y| + |ωn r y| := abs_sub _ _
            _ ≤ B + B := add_le_add (hl.abs_le r hr y hy) ((hP.iterate_mem n₀).abs_le r hr y hy)
            _ = 2 * B := by ring)) t ht x hx
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    have h2 := hn₀ (n₀ + 1) (by omega) t ht x hx
    rw [picardIterate_succ] at h2
    have hφ0 : 0 ≤ PDE.Analysis.osgoodModulus A (min ε (2 * B)) :=
      PDE.Analysis.osgoodModulus_nonneg hmin0 hminA
    calc |Φ ωl t x - ωl t x| ≤ |Φ ωl t x - Φ ωn t x| + |Φ ωn t x - ωl t x| := abs_sub_le _ _ _
      _ ≤ c * (|t| * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε := add_le_add h h2
      _ ≤ c * (T * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε := by
          gcongr
  -- The bound tends to zero with `ε`, so the defect vanishes.
  have hcont : Continuous fun ε : ℝ ↦
      c * (T * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε :=
    (continuous_const.mul (continuous_const.mul
      ((PDE.Analysis.continuous_osgoodModulus hA).comp
        (continuous_id.min continuous_const)))).add continuous_id
  have hlim : Tendsto (fun ε : ℝ ↦ c * (T * PDE.Analysis.osgoodModulus A (min ε (2 * B))) + ε)
      (𝓝[>] 0) (𝓝 0) := by
    have h := hcont.tendsto 0
    simp only [min_eq_left (by linarith : (0 : ℝ) ≤ 2 * B), PDE.Analysis.osgoodModulus_zero,
      mul_zero, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  by_contra hne
  have hd : 0 < |Φ ωl t x - ωl t x| := abs_pos.mpr (sub_ne_zero.mpr fun h ↦ hne h.symm)
  obtain ⟨ε, hεd, hε⟩ := ((hlim.eventually (Iio_mem_nhds hd)).and self_mem_nhdsWithin).exists
  exact absurd (key ε hε) (not_le.mpr hεd)

/-- **Existence of a fixed point** of `Φ` in the class: a `C^{1,α}` history with the bounds of
the class that agrees with its image on the closed half-plane at every time of `[-T, T]`. For
the iteration map of a half-plane system such a history is the vorticity of a solution. Proof:
the limit of the iterates, by `isC1VorticityHistory_picardLimit` and `picardLimit_eq`. -/
theorem exists_fixedPoint : ∃ ω' : ℝ → ℝ^2 → ℝ,
    IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁ ∧
      ∀ t ∈ Icc (-T) T, ∀ x : ℝ^2, 0 ≤ x 1 → ω' t x = Φ ω' t x :=
  ⟨_, hP.isC1VorticityHistory_picardLimit, fun _ ht _ hx ↦ hP.picardLimit_eq ht hx⟩

end IsOsgoodIteration

end HalfPlaneSystem
