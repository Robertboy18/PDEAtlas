/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Covering.SubboxGrowth
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Geometric decay of continuous superlevels

A uniform dense-child implication, together with one initial density bound,
gives geometric decay at the levels `Mᵏ`. The induction uses the separation of
distinct continuous superlevels and Mathlib's subbox partition theorem.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open BoxIntegral BoxIntegral.Prepartition MeasureTheory Set

variable {ι : Type*} [Fintype ι]

/-- Iteration of the dense-child implication gives geometric level-set decay. -/
theorem measure_superlevel_pow_le
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : Box ι) {u : (ι → ℝ) → ℝ} (hu : ContinuousOn u I.Icc)
    {M δ : ℝ} (hM : 1 < M) (hδ : 0 ≤ δ)
    (P : Box ι → Prop) (hPI : P I)
    (hPsplit : ∀ J ≤ I, P J → ∀ Q ∈ splitCenter J, P Q)
    (hparent : ∀ t : ℝ, 1 ≤ t → ∀ J ≤ I, P J → ∀ Q ∈ splitCenter J,
      δ * μ.real Q < (μ.restrict {x | M * t < u x}).real Q →
        (J : Set (ι → ℝ)) ⊆ {x | t < u x})
    (hinitial : (μ.restrict {x | M < u x}).real I ≤ δ * μ.real I) :
    ∀ k : ℕ, (μ.restrict {x | M ^ k < u x}).real I ≤ δ ^ k * μ.real I := by
  have hmono {s t : ℝ} (hst : s ≤ t) :
      (μ.restrict {x | t < u x}).real I ≤ (μ.restrict {x | s < u x}).real I := by
    rw [measureReal_restrict_apply I.measurableSet_coe,
      measureReal_restrict_apply I.measurableSet_coe]
    exact measureReal_mono (inter_subset_inter_right _ (fun _ hx ↦ hst.trans_lt hx))
      (measure_mono inter_subset_left |>.trans_lt (I.measure_coe_lt_top μ)).ne
  intro k
  induction k with
  | zero =>
    simp only [pow_zero, one_mul]
    rw [measureReal_restrict_apply I.measurableSet_coe]
    exact measureReal_mono inter_subset_left (I.measure_coe_lt_top μ).ne
  | succ k ih =>
    have hsmall : (μ.restrict {x | M ^ (k + 1) < u x}).real I ≤ δ * μ.real I :=
      (hmono (le_self_pow₀ hM.le (Nat.succ_ne_zero k))).trans hinitial
    have hgrowth := measure_restrict_le_mul_of_subbox_parent μ I hδ P hPI hPsplit
      (fun J hJI hPJ Q hQ hdense ↦
        hparent (M ^ k) (one_le_pow₀ hM.le) J hJI hPJ Q hQ
          (by simpa only [pow_succ'] using hdense))
      (superlevel_subbox_separation I hu (pow_lt_pow_right₀ hM (Nat.lt_succ_self k)))
      hsmall
    calc
      (μ.restrict {x | M ^ (k + 1) < u x}).real I ≤
          δ * (μ.restrict {x | M ^ k < u x}).real I := hgrowth
      _ ≤ δ * (δ ^ k * μ.real I) := mul_le_mul_of_nonneg_left ih hδ
      _ = δ ^ (k + 1) * μ.real I := by rw [pow_succ', mul_assoc]

end PDE.Analysis
