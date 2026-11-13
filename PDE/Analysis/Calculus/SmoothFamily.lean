/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Families of smooth maps with jointly continuous derivatives

A family `F r : P → Q`, `r ∈ I`, is smooth of order `m` on the times `I` when every map `F r` is
`C^m` and the derivatives `D^j (F r) p`, `j ≤ m`, are jointly continuous in `(r, p)` on `I × P`.
The maps need not depend smoothly on `r`: this is the regularity of a velocity field that is `C^m`
in space and only continuous in time, and of the flows and variations built from it.

The class is characterized recursively: it is of order `m + 1` if and only if the maps are
differentiable, the family is jointly continuous, and the family of derivatives is of order `m`.
With this characterization the class is closed under sums, scalar multiples, composition with
continuous linear maps, bounded bilinear maps applied to two families and composition of
families, and its first derivatives are bounded on compact sets of times and points. All spaces
live in one universe, so that the spaces of continuous linear maps met in the induction stay in
it.

## Main definitions

* `IsSmoothFamilyOn`: every `F r` is `C^m` and the derivatives of order at most `m` are jointly
  continuous on `I × P`.

## Main results

* `isSmoothFamilyOn_succ_iff`: a family is smooth of order `m + 1` exactly when its maps are
  differentiable, it is jointly continuous, and its family of derivatives is smooth of order `m`.
* `IsSmoothFamilyOn.add`: sums of smooth families are smooth.
* `IsSmoothFamilyOn.clm_comp`: a continuous linear map applied to a smooth family gives a smooth
  family.
* `IsSmoothFamilyOn.bilinear`: a bounded bilinear map applied to two smooth families gives a
  smooth family.
* `IsSmoothFamilyOn.comp`: the composition `F r (G r p)` of smooth families is smooth.
* `IsSmoothFamilyOn.exists_norm_fderiv_le`: for order at least one, `‖D(F r)(p)‖ ≤ M` for `r` in
  a compact `K ⊆ I` and `p` in a compact `L`.
-/

@[expose] public section

noncomputable section

open Set Function ContinuousLinearMap

namespace PDE.Analysis

universe u

variable {P Q R S : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R] [NormedAddCommGroup S]
  [NormedSpace ℝ S]

/-- The family `F r : P → Q`, `r ∈ I`, is smooth of order `m`: every `F r` is `C^m` and the
derivatives of order at most `m` are jointly continuous in `(r, p)` on `I × P`. -/
def IsSmoothFamilyOn (m : ℕ) (F : ℝ → P → Q) (I : Set ℝ) : Prop :=
  (∀ r ∈ I, ContDiff ℝ m (F r)) ∧
    ∀ j ≤ m, ContinuousOn (fun q : ℝ × P ↦ iteratedFDeriv ℝ j (F q.1) q.2) (I ×ˢ univ)

variable {m n : ℕ} {F G : ℝ → P → Q} {I J : Set ℝ}

namespace IsSmoothFamilyOn

/-- The maps of a smooth family are `C^m`. -/
theorem contDiff (h : IsSmoothFamilyOn m F I) {r : ℝ} (hr : r ∈ I) : ContDiff ℝ m (F r) :=
  h.1 r hr

/-- The derivatives of a smooth family are jointly continuous. -/
theorem continuousOn_iteratedFDeriv (h : IsSmoothFamilyOn m F I) {j : ℕ} (hj : j ≤ m) :
    ContinuousOn (fun q : ℝ × P ↦ iteratedFDeriv ℝ j (F q.1) q.2) (I ×ˢ univ) :=
  h.2 j hj

/-- A smooth family is jointly continuous. -/
theorem continuousOn (h : IsSmoothFamilyOn m F I) :
    ContinuousOn (fun q : ℝ × P ↦ F q.1 q.2) (I ×ˢ univ) := by
  have heq : (fun q : ℝ × P ↦ F q.1 q.2) =
      fun q ↦ continuousMultilinearCurryFin0 ℝ P Q (iteratedFDeriv ℝ 0 (F q.1) q.2) := by
    funext q
    simp [iteratedFDeriv_zero_eq_comp]
  rw [heq]
  exact (continuousMultilinearCurryFin0 ℝ P Q).continuous.comp_continuousOn (h.2 0 (Nat.zero_le _))

/-- The class only depends on the maps at the times of `I`. -/
theorem congr (h : IsSmoothFamilyOn m F I) (heq : ∀ r ∈ I, F r = G r) :
    IsSmoothFamilyOn m G I := by
  refine ⟨fun r hr ↦ heq r hr ▸ h.1 r hr, fun j hj ↦ (h.2 j hj).congr fun q hq ↦ ?_⟩
  simp only [heq q.1 hq.1]

/-- A smooth family of order `m` is smooth of every lower order. -/
theorem mono (h : IsSmoothFamilyOn m F I) (hnm : n ≤ m) : IsSmoothFamilyOn n F I :=
  ⟨fun r hr ↦ (h.1 r hr).of_le (by exact_mod_cast hnm), fun j hj ↦ h.2 j (hj.trans hnm)⟩

/-- A smooth family restricts to fewer times. -/
theorem mono_set (h : IsSmoothFamilyOn m F I) (hJ : J ⊆ I) : IsSmoothFamilyOn m F J :=
  ⟨fun r hr ↦ h.1 r (hJ hr), fun j hj ↦ (h.2 j hj).mono (prod_mono hJ subset_rfl)⟩

end IsSmoothFamilyOn

/-- A family is smooth of order `0` exactly when it is jointly continuous. -/
theorem isSmoothFamilyOn_zero_iff :
    IsSmoothFamilyOn 0 F I ↔ ContinuousOn (fun q : ℝ × P ↦ F q.1 q.2) (I ×ˢ univ) := by
  refine ⟨IsSmoothFamilyOn.continuousOn, fun h ↦ ⟨fun r hr ↦ ?_, fun j hj ↦ ?_⟩⟩
  · rw [Nat.cast_zero, contDiff_zero]
    exact h.comp_continuous (continuous_const.prodMk continuous_id) fun p ↦ ⟨hr, mem_univ p⟩
  · obtain rfl : j = 0 := Nat.le_zero.mp hj
    have heq : (fun q : ℝ × P ↦ iteratedFDeriv ℝ 0 (F q.1) q.2) =
        fun q ↦ (continuousMultilinearCurryFin0 ℝ P Q).symm (F q.1 q.2) := by
      funext q
      simp [iteratedFDeriv_zero_eq_comp]
    rw [heq]
    exact (continuousMultilinearCurryFin0 ℝ P Q).symm.continuous.comp_continuousOn h

/-- **Recursive characterization.** A family is smooth of order `m + 1` exactly when its maps are
differentiable, it is jointly continuous, and its family of derivatives is smooth of order `m`. -/
theorem isSmoothFamilyOn_succ_iff :
    IsSmoothFamilyOn (m + 1) F I ↔ (∀ r ∈ I, Differentiable ℝ (F r)) ∧
      ContinuousOn (fun q : ℝ × P ↦ F q.1 q.2) (I ×ˢ univ) ∧
      IsSmoothFamilyOn m (fun r p ↦ fderiv ℝ (F r) p) I := by
  constructor
  · intro h
    have hcd (r : ℝ) (hr : r ∈ I) : ContDiff ℝ ((m : WithTop ℕ∞) + 1) (F r) := by
      exact_mod_cast h.1 r hr
    refine ⟨fun r hr ↦ (contDiff_succ_iff_fderiv.mp (hcd r hr)).1, h.continuousOn,
      fun r hr ↦ (contDiff_succ_iff_fderiv.mp (hcd r hr)).2.2, fun j hj ↦ ?_⟩
    have heq : (fun q : ℝ × P ↦ iteratedFDeriv ℝ j (fun p ↦ fderiv ℝ (F q.1) p) q.2) =
        fun q ↦ continuousMultilinearCurryRightEquiv' ℝ j P Q
          (iteratedFDeriv ℝ (j + 1) (F q.1) q.2) := by
      funext q
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp
    rw [heq]
    exact (continuousMultilinearCurryRightEquiv' ℝ j P Q).continuous.comp_continuousOn
      (h.2 (j + 1) (by omega))
  · rintro ⟨hd, hc, h⟩
    refine ⟨fun r hr ↦ ?_, fun j hj ↦ ?_⟩
    · have : ContDiff ℝ ((m : WithTop ℕ∞) + 1) (F r) :=
        contDiff_succ_iff_fderiv.mpr ⟨hd r hr, fun h ↦ absurd h (by simp), h.1 r hr⟩
      exact_mod_cast this
    · rcases j with _ | j
      · exact (isSmoothFamilyOn_zero_iff.mpr hc).2 0 le_rfl
      · have heq : (fun q : ℝ × P ↦ iteratedFDeriv ℝ (j + 1) (F q.1) q.2) =
            fun q ↦ (continuousMultilinearCurryRightEquiv' ℝ j P Q).symm
              (iteratedFDeriv ℝ j (fun p ↦ fderiv ℝ (F q.1) p) q.2) := by
          funext q
          exact iteratedFDeriv_succ_eq_comp_right
        rw [heq]
        exact (continuousMultilinearCurryRightEquiv' ℝ j P Q).symm.continuous.comp_continuousOn
          (h.2 j (by omega))

/-- A family of one `C^m` map is smooth of order `m`. -/
theorem isSmoothFamilyOn_const {f : P → Q} (hf : ContDiff ℝ m f) :
    IsSmoothFamilyOn m (fun _ ↦ f) I :=
  ⟨fun _ _ ↦ hf, fun j hj ↦
    ((hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp continuous_snd).continuousOn⟩

/-- The identity family is smooth of every order. -/
theorem isSmoothFamilyOn_id : IsSmoothFamilyOn m (fun (_ : ℝ) (p : P) ↦ p) I :=
  isSmoothFamilyOn_const contDiff_id

namespace IsSmoothFamilyOn

/-- Sums of smooth families are smooth. -/
theorem add {Q : Type u} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {F G : ℝ → P → Q}
    (hF : IsSmoothFamilyOn m F I) (hG : IsSmoothFamilyOn m G I) :
    IsSmoothFamilyOn m (fun r p ↦ F r p + G r p) I := by
  induction m generalizing Q with
  | zero =>
    rw [isSmoothFamilyOn_zero_iff] at *
    exact hF.add hG
  | succ m ih =>
    rw [isSmoothFamilyOn_succ_iff] at *
    refine ⟨fun r hr ↦ (hF.1 r hr).add (hG.1 r hr), hF.2.1.add hG.2.1,
      (ih hF.2.2 hG.2.2).congr fun r hr ↦ ?_⟩
    funext p
    exact (fderiv_add (hF.1 r hr p) (hG.1 r hr p)).symm

/-- Differences of smooth families are smooth. -/
theorem sub {Q : Type u} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {F G : ℝ → P → Q}
    (hF : IsSmoothFamilyOn m F I) (hG : IsSmoothFamilyOn m G I) :
    IsSmoothFamilyOn m (fun r p ↦ F r p - G r p) I := by
  induction m generalizing Q with
  | zero =>
    rw [isSmoothFamilyOn_zero_iff] at *
    exact hF.sub hG
  | succ m ih =>
    rw [isSmoothFamilyOn_succ_iff] at *
    refine ⟨fun r hr ↦ (hF.1 r hr).sub (hG.1 r hr), hF.2.1.sub hG.2.1,
      (ih hF.2.2 hG.2.2).congr fun r hr ↦ ?_⟩
    funext p
    exact (fderiv_sub (hF.1 r hr p) (hG.1 r hr p)).symm

/-- Constant multiples of smooth families are smooth. -/
theorem const_smul {Q : Type u} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {F : ℝ → P → Q}
    (hF : IsSmoothFamilyOn m F I) (c : ℝ) : IsSmoothFamilyOn m (fun r p ↦ c • F r p) I := by
  induction m generalizing Q with
  | zero =>
    rw [isSmoothFamilyOn_zero_iff] at *
    exact hF.const_smul c
  | succ m ih =>
    rw [isSmoothFamilyOn_succ_iff] at *
    refine ⟨fun r hr ↦ (hF.1 r hr).const_smul c, hF.2.1.const_smul c,
      (ih hF.2.2).congr fun r hr ↦ ?_⟩
    funext p
    exact (fderiv_const_smul (hF.1 r hr p) c).symm

/-- A continuous linear map applied to a smooth family gives a smooth family. -/
theorem clm_comp {Q R : Type u} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R]
    [NormedSpace ℝ R] {F : ℝ → P → Q} (L : Q →L[ℝ] R) (hF : IsSmoothFamilyOn m F I) :
    IsSmoothFamilyOn m (fun r p ↦ L (F r p)) I := by
  induction m generalizing Q R with
  | zero =>
    rw [isSmoothFamilyOn_zero_iff] at *
    exact L.continuous.comp_continuousOn hF
  | succ m ih =>
    rw [isSmoothFamilyOn_succ_iff] at *
    refine ⟨fun r hr ↦ L.differentiable.comp (hF.1 r hr), L.continuous.comp_continuousOn hF.2.1,
      (ih (compL ℝ P Q R L) hF.2.2).congr fun r hr ↦ ?_⟩
    funext p
    exact ((L.hasFDerivAt.comp p (hF.1 r hr p).hasFDerivAt).fderiv).symm

/-- **Bilinear maps.** A bounded bilinear map applied to two smooth families gives a smooth
family. -/
theorem bilinear {Q R S : Type u} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R]
    [NormedSpace ℝ R] [NormedAddCommGroup S] [NormedSpace ℝ S] {F : ℝ → P → Q} {G : ℝ → P → R}
    (B : Q →L[ℝ] R →L[ℝ] S) (hF : IsSmoothFamilyOn m F I) (hG : IsSmoothFamilyOn m G I) :
    IsSmoothFamilyOn m (fun r p ↦ B (F r p) (G r p)) I := by
  induction m generalizing Q R S with
  | zero =>
    rw [isSmoothFamilyOn_zero_iff] at *
    exact (B.continuous.comp_continuousOn hF).clm_apply hG
  | succ m ih =>
    have hF' := hF.mono (Nat.le_succ m)
    have hG' := hG.mono (Nat.le_succ m)
    rw [isSmoothFamilyOn_succ_iff] at hF hG ⊢
    have hderiv (r : ℝ) (hr : r ∈ I) (p : P) :
        HasFDerivAt (fun y ↦ B (F r y) (G r y))
          (precompR P B (F r p) (fderiv ℝ (G r) p) +
            precompL P B (fderiv ℝ (F r) p) (G r p)) p :=
      B.hasFDerivAt_of_bilinear (hF.1 r hr p).hasFDerivAt (hG.1 r hr p).hasFDerivAt
    refine ⟨fun r hr p ↦ (hderiv r hr p).differentiableAt,
      (B.continuous.comp_continuousOn hF.2.1).clm_apply hG.2.1,
      ((ih (precompR P B) hF' hG.2.2).add (ih (precompL P B) hF.2.2 hG')).congr
        fun r hr ↦ ?_⟩
    funext p
    exact ((hderiv r hr p).fderiv).symm

/-- **Composition.** The composition `F r (G r p)` of smooth families is a smooth family. -/
theorem comp {Q R : Type u} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R]
    [NormedSpace ℝ R] {F : ℝ → Q → R} {G : ℝ → P → Q} (hF : IsSmoothFamilyOn m F I)
    (hG : IsSmoothFamilyOn m G I) : IsSmoothFamilyOn m (fun r p ↦ F r (G r p)) I := by
  induction m generalizing R with
  | zero =>
    rw [isSmoothFamilyOn_zero_iff] at *
    exact hF.comp (continuousOn_fst.prodMk hG) fun q hq ↦ ⟨hq.1, mem_univ _⟩
  | succ m ih =>
    have hG' := hG.mono (Nat.le_succ m)
    have hG₁ := hG
    rw [isSmoothFamilyOn_succ_iff] at hF hG ⊢
    have hderiv (r : ℝ) (hr : r ∈ I) (p : P) :
        HasFDerivAt (fun y ↦ F r (G r y))
          (compL ℝ P Q R (fderiv ℝ (F r) (G r p)) (fderiv ℝ (G r) p)) p :=
      (hF.1 r hr (G r p)).hasFDerivAt.comp p (hG.1 r hr p).hasFDerivAt
    refine ⟨fun r hr p ↦ (hderiv r hr p).differentiableAt,
      hF.2.1.comp (continuousOn_fst.prodMk hG.2.1) fun q hq ↦ ⟨hq.1, mem_univ _⟩,
      (bilinear (compL ℝ P Q R) (ih hF.2.2 hG') hG.2.2).congr fun r hr ↦ ?_⟩
    funext p
    exact ((hderiv r hr p).fderiv).symm

/-- **The first derivatives of a smooth family are bounded on compact sets**: for a family of
order at least one, `‖D(F r)(p)‖ ≤ M` for `r` in a compact `K ⊆ I` and `p` in a compact `L`. -/
theorem exists_norm_fderiv_le (h : IsSmoothFamilyOn (m + 1) F I) {K : Set ℝ} {L : Set P}
    (hK : IsCompact K) (hKI : K ⊆ I) (hL : IsCompact L) :
    ∃ M, 0 ≤ M ∧ ∀ r ∈ K, ∀ p ∈ L, ‖fderiv ℝ (F r) p‖ ≤ M := by
  have hD : ContinuousOn (fun q : ℝ × P ↦ fderiv ℝ (F q.1) q.2) (I ×ˢ univ) :=
    (isSmoothFamilyOn_succ_iff.mp h).2.2.continuousOn
  obtain ⟨M, hM⟩ := (hK.prod hL).exists_bound_of_continuousOn
    (hD.mono (prod_mono hKI (subset_univ _)))
  exact ⟨max M 0, le_max_right _ _, fun r hr p hp ↦ (hM (r, p) ⟨hr, hp⟩).trans (le_max_left _ _)⟩

end IsSmoothFamilyOn

end PDE.Analysis
