/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.HolderInterpolation
public import PDE.Analysis.Calculus.HolderLimit
public import PDE.Analysis.Calculus.HalfSpaceGluing
import PDE.Analysis.Calculus.HolderProduct

/-!
# Limits of functions with uniform `C^{k,α}` bounds on the closed half-plane

Let `gₙ` be functions that are `C^k` within the closed upper half-plane `H̄`, whose derivatives
within `H̄` of order at most `k` are bounded by `N` there and whose `k`-th derivative is
`α`-Hölder there with constant `N`, `0 < α ≤ 1`. If the `gₙ` are Cauchy uniformly on `H̄`, then
so are their derivatives of every order `j ≤ k` (`iteratedFDerivWithin_cauchy`): the derivative of
order `j + 1` of a difference is controlled by the sup norm of its derivative of order `j` and the
common Hölder bound `4N` of its derivative, by interpolation on the half-plane
(`exists_norm_le_of_halfPlane`). The pointwise limit `g` is then `C^k` within `H̄` and the
derivatives of the `gₙ` converge to those of `g` (`contDiffOn_of_tendsto`): the limits of the
derivatives form a Taylor series of `g` within `H̄`, by `hasFDerivWithinAt_of_tendsto_of_holder`.

The statements carry a parameter `i` ranging over a set `I` (in the applications, the times of a
history), with all hypotheses and the Cauchy property uniform in `i`.

## Main results

* `norm_iteratedFDerivWithin_sub_le_two_mul`: if the derivatives of order at most `k` are bounded
  by `N` on `H̄` and the top derivative is `α`-Hölder with constant `N`, every derivative of order
  at most `k` is `α`-Hölder on `H̄` with constant `2N`.
* `norm_iteratedFDerivWithin_zero_sub_apply`: the derivatives of order zero of two functions differ
  by their values.
* `iteratedFDerivWithin_cauchy`, `contDiffOn_of_tendsto`: the Cauchy property of the derivatives
  and the regularity of the limit.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped Topology

namespace PDE.Analysis

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `0`-th iterated derivatives within a set of two functions at a point differ by their
values. -/
theorem norm_iteratedFDerivWithin_zero_sub_apply (f g : ℝ^2 → F) (s : Set (ℝ^2)) (x : ℝ^2) :
    ‖iteratedFDerivWithin ℝ 0 f s x - iteratedFDerivWithin ℝ 0 g s x‖ = ‖f x - g x‖ := by
  rw [iteratedFDerivWithin_zero_eq_comp, iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
    Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map]

/-- If the derivatives within the closed half-plane of order at most `k` of a `C^k` function are
bounded by `N` there and the `k`-th is `α`-Hölder there with constant `N`, `0 ≤ α ≤ 1`, every
derivative of order at most `k` is `α`-Hölder on the closed half-plane with constant `2N`. -/
theorem norm_iteratedFDerivWithin_sub_le_two_mul {f : ℝ^2 → F} {k : ℕ} {α N : ℝ}
    (hf : ContDiffOn ℝ k f H̄)
    (hb : ∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ N)
    (hH : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ N * ‖y - z‖ ^ α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {j : ℕ} (hj : j ≤ k) {y z : ℝ^2} (hy : 0 ≤ y 1)
    (hz : 0 ≤ z 1) :
    ‖iteratedFDerivWithin ℝ j f H̄ y - iteratedFDerivWithin ℝ j f H̄ z‖ ≤
      2 * N * ‖y - z‖ ^ α := by
  have hN : 0 ≤ N := (norm_nonneg _).trans (hb 0 (Nat.zero_le k) 0 (by simp))
  rcases hj.lt_or_eq with hjk | rfl
  · have h := norm_sub_le_max_mul_rpow (f := iteratedFDerivWithin ℝ j f H̄)
      (S := H̄) (L := N) (M := N) (fun y hy z hz ↦ by
        rw [dist_eq_norm]
        exact norm_iteratedFDerivWithin_sub_le_of_convex convex_closedUpperHalfPlane
          (uniqueDiffOn_coordinateHalfSpace (1 : Fin 2)) hf (by exact_mod_cast hjk)
          (fun w hw ↦ hb (j + 1) hjk w hw) hy hz)
      (fun y hy ↦ hb j hj y hy) hα0 hα1 hy hz
    rwa [max_eq_right (by linarith), dist_eq_norm] at h
  · exact (hH y z hy hz).trans (by
      gcongr
      linarith)

variable {X : Type*} {I : Set X} {g : ℕ → X → ℝ^2 → F} {k : ℕ} {α N : ℝ}

/-- **Uniform Cauchy property of the derivatives.** Functions with uniform `C^{k,α}` bounds on
the closed half-plane that are Cauchy uniformly there have derivatives of every order `j ≤ k`
that are Cauchy uniformly there, uniformly in the parameter. -/
theorem iteratedFDerivWithin_cauchy (hα : 0 < α) (hα1 : α ≤ 1) (hN : 0 ≤ N)
    (hg : ∀ n, ∀ i ∈ I, ContDiffOn ℝ k (g n i) H̄)
    (hb : ∀ n, ∀ i ∈ I, ∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (g n i) H̄ y‖ ≤ N)
    (hH : ∀ n, ∀ i ∈ I, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k (g n i) H̄ y - iteratedFDerivWithin ℝ k (g n i) H̄ z‖ ≤
        N * ‖y - z‖ ^ α)
    (hc : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ i ∈ I, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖g n i y - g m i y‖ ≤ ε) :
    ∀ j ≤ k, ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ i ∈ I, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (g n i) H̄ y - iteratedFDerivWithin ℝ j (g m i) H̄ y‖ ≤ ε := by
  intro j
  induction j with
  | zero =>
    intro _ ε hε
    obtain ⟨n₀, hn₀⟩ := hc ε hε
    refine ⟨n₀, fun n hn m hm i hi y hy ↦ ?_⟩
    rw [norm_iteratedFDerivWithin_zero_sub_apply]
    exact hn₀ n hn m hm i hi y hy
  | succ j ih =>
    intro hj ε hε
    have hM : 0 ≤ 4 * N := by positivity
    obtain ⟨η, hη, hint⟩ := exists_norm_le_of_halfPlane (F := ContinuousMultilinearMap ℝ
      (fun _ : Fin j ↦ ℝ^2) F) hM hα hε
    obtain ⟨n₀, hn₀⟩ := ih (by omega) η hη
    refine ⟨n₀, fun n hn m hm i hi y hy ↦ ?_⟩
    have hd (p : ℕ) : DifferentiableOn ℝ (iteratedFDerivWithin ℝ j (g p i) H̄) H̄ :=
      (hg p i hi).differentiableOn_iteratedFDerivWithin (by exact_mod_cast hj)
        (uniqueDiffOn_coordinateHalfSpace (1 : Fin 2))
    have hholder (p : ℕ) {z w : ℝ^2} (hz : 0 ≤ z 1) (hw : 0 ≤ w 1) :
        ‖fderivWithin ℝ (iteratedFDerivWithin ℝ j (g p i) H̄) H̄ z -
          fderivWithin ℝ (iteratedFDerivWithin ℝ j (g p i) H̄) H̄ w‖ ≤ 2 * N * ‖z - w‖ ^ α := by
      rw [norm_fderivWithin_iteratedFDerivWithin_sub]
      exact norm_iteratedFDerivWithin_sub_le_two_mul (hg p i hi) (hb p i hi)
        (hH p i hi) hα.le hα1 hj hz hw
    rw [← norm_fderivWithin_iteratedFDerivWithin_sub]
    refine hint (fun z ↦ iteratedFDerivWithin ℝ j (g n i) H̄ z -
        iteratedFDerivWithin ℝ j (g m i) H̄ z)
      (fun z ↦ fderivWithin ℝ (iteratedFDerivWithin ℝ j (g n i) H̄) H̄ z -
        fderivWithin ℝ (iteratedFDerivWithin ℝ j (g m i) H̄) H̄ z)
      (fun z hz ↦ ((hd n z hz).hasFDerivWithinAt).sub ((hd m z hz).hasFDerivWithinAt))
      (fun z hz ↦ hn₀ n hn m hm i hi z hz) (fun z w hz hw ↦ ?_) y hy
    calc _ = ‖(fderivWithin ℝ (iteratedFDerivWithin ℝ j (g n i) H̄) H̄ z -
            fderivWithin ℝ (iteratedFDerivWithin ℝ j (g n i) H̄) H̄ w) -
          (fderivWithin ℝ (iteratedFDerivWithin ℝ j (g m i) H̄) H̄ z -
            fderivWithin ℝ (iteratedFDerivWithin ℝ j (g m i) H̄) H̄ w)‖ := by
          congr 1; abel
      _ ≤ 2 * N * ‖z - w‖ ^ α + 2 * N * ‖z - w‖ ^ α :=
          (norm_sub_le (E := ℝ^2 →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ ℝ^2) F)
            _ _).trans (add_le_add (hholder n hz hw) (hholder m hz hw))
      _ = 4 * N * ‖z - w‖ ^ α := by ring

/-- **Limits with uniform `C^{k,α}` bounds.** Under the hypotheses of
`iteratedFDerivWithin_cauchy`, a pointwise limit `g'` on the closed half-plane of the functions
`g n i` is `C^k` within `H̄`, and the derivatives of order at most `k` of the `g n i` converge to
those of `g'` at every point of `H̄`. -/
theorem contDiffOn_of_tendsto [CompleteSpace F] (hα : 0 < α) (hα1 : α ≤ 1) (hN : 0 ≤ N)
    (hg : ∀ n, ∀ i ∈ I, ContDiffOn ℝ k (g n i) H̄)
    (hb : ∀ n, ∀ i ∈ I, ∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖iteratedFDerivWithin ℝ j (g n i) H̄ y‖ ≤ N)
    (hH : ∀ n, ∀ i ∈ I, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k (g n i) H̄ y - iteratedFDerivWithin ℝ k (g n i) H̄ z‖ ≤
        N * ‖y - z‖ ^ α)
    (hc : ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀, ∀ i ∈ I, ∀ y : ℝ^2, 0 ≤ y 1 →
      ‖g n i y - g m i y‖ ≤ ε) {i : X} (hi : i ∈ I) {g' : ℝ^2 → F}
    (hg' : ∀ y : ℝ^2, 0 ≤ y 1 → Tendsto (fun n ↦ g n i y) atTop (𝓝 (g' y))) :
    ContDiffOn ℝ k g' H̄ ∧ ∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 →
      Tendsto (fun n ↦ iteratedFDerivWithin ℝ j (g n i) H̄ y) atTop
        (𝓝 (iteratedFDerivWithin ℝ j g' H̄ y)) := by
  have hcd := iteratedFDerivWithin_cauchy hα hα1 hN hg hb hH hc
  set p : ℝ^2 → FormalMultilinearSeries ℝ (ℝ^2) F := fun y j ↦
    limUnder atTop fun n ↦ iteratedFDerivWithin ℝ j (g n i) H̄ y
  have hp : ∀ j ≤ k, ∀ y : ℝ^2, 0 ≤ y 1 →
      Tendsto (fun n ↦ iteratedFDerivWithin ℝ j (g n i) H̄ y) atTop (𝓝 (p y j)) := by
    intro j hj y hy
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
    obtain ⟨n₀, hn₀⟩ := hcd j hj (ε / 2) (half_pos hε)
    refine ⟨n₀, fun n hn ↦ ?_⟩
    rw [dist_eq_norm]
    exact (hn₀ n hn n₀ le_rfl i hi y hy).trans_lt (half_lt_self hε)
  have hholder (n : ℕ) {j : ℕ} (hj : j ≤ k) {z w : ℝ^2} (hz : 0 ≤ z 1) (hw : 0 ≤ w 1) :
      ‖iteratedFDerivWithin ℝ j (g n i) H̄ z - iteratedFDerivWithin ℝ j (g n i) H̄ w‖ ≤
        2 * N * ‖z - w‖ ^ α :=
    norm_iteratedFDerivWithin_sub_le_two_mul (hg n i hi) (hb n i hi)
      (hH n i hi) hα.le hα1 hj hz hw
  have hpH {j : ℕ} (hj : j ≤ k) {z w : ℝ^2} (hz : 0 ≤ z 1) (hw : 0 ≤ w 1) :
      ‖p z j - p w j‖ ≤ 2 * N * ‖z - w‖ ^ α :=
    le_of_tendsto' ((hp j hj z hz).sub (hp j hj w hw)).norm fun n ↦ hholder n hj hz hw
  have htaylor : HasFTaylorSeriesUpToOn (k : ℕ∞) g' p H̄ := by
    refine ⟨fun y hy ↦ ?_, fun m hm y hy ↦ ?_, fun m hm ↦ ?_⟩
    · have h0 := hp 0 (Nat.zero_le k) y hy
      have h0' : Tendsto (fun n ↦ iteratedFDerivWithin ℝ 0 (g n i) H̄ y) atTop
          (𝓝 ((continuousMultilinearCurryFin0 ℝ (ℝ^2) F).symm (g' y))) := by
        simp only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply]
        exact ((continuousMultilinearCurryFin0 ℝ (ℝ^2) F).symm.continuous.tendsto _).comp
          (hg' y hy)
      rw [tendsto_nhds_unique h0 h0']
      simp
    · have hmk : m < k := by exact_mod_cast hm
      refine PDE.Analysis.hasFDerivWithinAt_of_tendsto_of_holder
        PDE.Analysis.convex_closedUpperHalfPlane (by positivity : 0 ≤ 2 * N) hα
        (g := fun n ↦ iteratedFDerivWithin ℝ m (g n i) H̄)
        (G := fun n ↦ fderivWithin ℝ (iteratedFDerivWithin ℝ m (g n i) H̄) H̄)
        (G' := fun z ↦ (p z m.succ).curryLeft)
        (fun n z hz ↦ (((hg n i hi).differentiableOn_iteratedFDerivWithin
          (by exact_mod_cast hmk) (uniqueDiffOn_coordinateHalfSpace (1 : Fin 2))) z
            hz).hasFDerivWithinAt)
        (fun n z hz w hw ↦ ?_) (fun z hz ↦ hp m hmk.le z hz) (fun z hz ↦ ?_) hy
      · rw [norm_fderivWithin_iteratedFDerivWithin_sub]
        exact hholder n (by omega) hz hw
      · have h := ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ ℝ^2)
          F).continuous.tendsto _).comp (hp (m + 1) (by omega) z hz)
        refine h.congr fun n ↦ ?_
        simp only [Function.comp_apply, iteratedFDerivWithin_succ_eq_comp_left,
          LinearIsometryEquiv.apply_symm_apply]
    · have hmk : m ≤ k := by exact_mod_cast hm
      exact continuousOn_of_norm_sub_le_rpow hα fun z hz w hw ↦ hpH hmk hz hw
  have heq {j : ℕ} (hj : j ≤ k) {y : ℝ^2} (hy : 0 ≤ y 1) :
      p y j = iteratedFDerivWithin ℝ j g' H̄ y :=
    htaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hj)
      (uniqueDiffOn_coordinateHalfSpace (1 : Fin 2)) hy
  refine ⟨htaylor.contDiffOn, fun j hj y hy ↦ ?_⟩
  rw [← heq hj hy]
  exact hp j hj y hy

end PDE.Analysis
