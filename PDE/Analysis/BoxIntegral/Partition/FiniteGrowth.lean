/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.BoxIntegral.Partition.ForwardGrowth

/-!
# Finite growth through enlarging boxes

Forward extensions may leave their original time window. A finite sequence
of larger windows accommodates these extensions without an invariance
assumption. Unless a partition member is dense, each step increases the
lower superlevel's measure by the inverse covering factor. A finite volume
budget forces a dense member before the last window.
-/

@[expose] public noncomputable section

namespace BoxIntegral.Prepartition

open Set MeasureTheory Filter
open scoped Topology ENNReal

/-- Geometric decay eventually dominates the linear increase in the volume
of a sequence of time windows. -/
theorem exists_geometric_affine_lt {ρ β : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hβ : 0 < β) (A B : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ρ ^ N * (A + (N : ℝ) * B) < β := by
  have hzero : Tendsto (fun k : ℕ ↦ ρ ^ k * (A + (k : ℝ) * B)) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ₁).mul_const A).add
      ((tendsto_self_mul_const_pow_of_lt_one hρ hρ₁).mul_const B)
    simpa only [zero_mul, mul_zero, zero_add, add_zero, mul_add, mul_comm,
      mul_left_comm, mul_assoc] using h
  obtain ⟨N, hN, hbound⟩ :=
    ((eventually_gt_atTop 0).and (hzero.eventually (gt_mem_nhds hβ))).exists
  exact ⟨N, hN, hbound⟩

/-- A finite forward-cover iteration forces a dense partition member.
Each forward extension is placed in the next window, whose volume may be
larger. The final budget is the only condition on the number of steps. -/
theorem exists_dense_partition_member_of_forward_growth
    {n N : ℕ} (W : ℕ → Box (Fin (n + 1)))
    (π : ∀ k : ℕ, Prepartition (W k)) (hπ : ∀ k < N, (π k).IsPartition)
    (j : Fin (n + 1))
    (division : Fin (n + 1) → ℝ) (hdivision : ∀ i, 1 < division i)
    (split : ∀ J : Box (Fin (n + 1)), Prepartition J)
    (hpartition : ∀ J, (split J).IsPartition)
    (hside : ∀ J K, K ∈ split J → ∀ i,
      K.upper i - K.lower i = (J.upper i - J.lower i) / division i)
    (P : Box (Fin (n + 1)) → Prop) (hPπ : ∀ k < N, ∀ J ∈ π k, P J)
    (hPsplit : ∀ k < N, ∀ J ≤ W k, P J → ∀ K ∈ split J, P K)
    {A : Set (Fin (n + 1) → ℝ)} (hWA : ∀ k ≤ N, (W k).Icc ⊆ A)
    {u : (Fin (n + 1) → ℝ) → ℝ} (hu : ContinuousOn u A)
    (t : ℕ → ℝ) (ht : ∀ k < N, t (k + 1) < t k)
    {δ lag m β : ℝ} (hδ : 0 ≤ δ) (hlag : 0 ≤ lag) (hm : 0 < m)
    (hnext : ∀ k < N, ∀ J ≤ W k, P J →
      (J.forwardExtension j lag m hm : Set (Fin (n + 1) → ℝ)) ⊆ W (k + 1))
    (hparent : ∀ k < N, ∀ J ≤ W k, P J → ∀ K ∈ split J,
      δ * volume.real (K : Set (Fin (n + 1) → ℝ)) <
        (volume.restrict {x | t k < u x}).real K →
          (J.forwardExtension j lag m hm : Set (Fin (n + 1) → ℝ)) ⊆
            {x | t (k + 1) < u x})
    (hinitial : β ≤ (volume.restrict {x | t 0 < u x}).real (W 0))
    (hbudget : (δ * (1 + (lag + 1) / m)) ^ N *
      volume.real (W N : Set (Fin (n + 1) → ℝ)) < β) :
    ∃ k < N, ∃ J ∈ π k, δ * volume.real (J : Set (Fin (n + 1) → ℝ)) <
      (volume.restrict {x | t k < u x}).real J := by
  by_contra hnone
  let ρ := δ * (1 + (lag + 1) / m)
  have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
  let a := fun k : ℕ ↦ (volume.restrict {x | t k < u x}).real (W k)
  have hstep (k : ℕ) (hk : k < N) : a k ≤ ρ * a (k + 1) := by
    obtain ⟨σ, hcover, hσ⟩ := exists_forward_superlevel_cover_of_partition
      (π k) (hπ k hk) j division hdivision split hpartition hside P
      (hPπ k hk) (hPsplit k hk) (hWA k hk.le) hu (ht k hk) hlag hm
      (fun J hJ hPJ ↦ (hnext k hk J hJ hPJ).trans
        (Box.coe_subset_Icc.trans (hWA (k + 1) hk)))
      (hparent k hk)
      (fun J hJ ↦ le_of_not_gt (fun hdense ↦ hnone ⟨k, hk, J, hJ, hdense⟩))
    have hfinite : volume
        ((W (k + 1) : Set (Fin (n + 1) → ℝ)) ∩ {x | t (k + 1) < u x}) ≠ ∞ :=
      (measure_mono inter_subset_left |>.trans_lt
        ((W (k + 1)).measure_coe_lt_top volume)).ne
    have hbound := σ.volume_restrict_le_mul_of_forward_cover j hδ hlag hm hfinite
      hcover (fun J hJ ↦ (hσ J hJ).2.1)
      (fun J hJ x hx ↦
        ⟨hnext k hk J (σ.le_of_mem hJ) (hσ J hJ).1 hx, (hσ J hJ).2.2 hx⟩)
    simpa only [ρ, a, measureReal_restrict_apply (W (k + 1)).measurableSet_coe]
      using hbound
  have hiter : ∀ k ≤ N, a 0 ≤ ρ ^ k * a k := by
    intro k
    induction k with
    | zero => intro _; simp only [pow_zero, one_mul, le_refl]
    | succ k ih =>
      intro hk
      calc
        a 0 ≤ ρ ^ k * a k := ih (Nat.le_of_succ_le hk)
        _ ≤ ρ ^ k * (ρ * a (k + 1)) :=
          mul_le_mul_of_nonneg_left (hstep k hk) (pow_nonneg hρ k)
        _ = ρ ^ (k + 1) * a (k + 1) := by
          rw [pow_succ]
          exact (mul_assoc (ρ ^ k) ρ (a (k + 1))).symm
  have hfinal : a N ≤ volume.real (W N : Set (Fin (n + 1) → ℝ)) := by
    dsimp only [a]
    rw [measureReal_restrict_apply (W N).measurableSet_coe]
    exact measureReal_mono inter_subset_left ((W N).measure_coe_lt_top volume).ne
  exact (not_lt_of_ge (hinitial.trans ((hiter N le_rfl).trans
    (mul_le_mul_of_nonneg_left hfinal (pow_nonneg hρ N))))) hbudget

end BoxIntegral.Prepartition
