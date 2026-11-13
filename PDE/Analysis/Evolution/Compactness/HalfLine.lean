/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Evolution.Compactness.FixedTests

/-!
# A weak trajectory limit for all future times

We extract all bounded time windows together. Their limits agree wherever the
windows overlap, since every scalar pairing comes from the same sequence.
This gives one weakly continuous trajectory on the whole future half-line,
with the original energy bound.
-/

@[expose] public section

noncomputable section


open Filter Set
open scoped Topology BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {H R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- Uniform energy bounds and eventual fixed-test time moduli give one weakly
continuous limit for all future times. The subsequence is the same on every
bounded time window, and every fixed Hilbert pairing converges uniformly there.
Neither a full dual-valued derivative bound nor an assumed limiting path is
needed. -/
theorem exists_weak_trajectory_limit_Ici
    (a : ℝ) (test : R → H) (htest : DenseRange test)
    (u : ℕ → Ici a → H) (hu : ∀ n, Continuous (u n))
    (M : ℝ) (hbound : ∀ n t, ‖u n t‖ ≤ M)
    (hpair : ∀ k : ℕ, ∀ r, ∃ N : ℕ, Equicontinuous
      (fun n : Ici N ↦ fun t : Icc a (a + k) ↦
        inner ℝ (test r) (u n.val ⟨t.val, t.property.1⟩))) :
    ∃ uLimit : Ici a → H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, ‖uLimit t‖ ≤ M) ∧
      Continuous (fun t ↦ toWeakSpace ℝ H (uLimit t)) ∧
      ∀ k : ℕ, ∀ v : H, TendstoUniformly
        (fun n (t : Icc a (a + k)) ↦ inner ℝ v (u (φ n) ⟨t.val, t.property.1⟩))
        (fun t : Icc a (a + k) ↦ inner ℝ v (uLimit ⟨t.val, t.property.1⟩)) atTop := by
  let X (k : ℕ) : Type := Icc a (a + k)
  let incl (k : ℕ) (t : X k) : Ici a := ⟨t.val, t.property.1⟩
  have hinc (k : ℕ) : Continuous (incl k) :=
    continuous_subtype_val.subtype_mk _
  let w (n k : ℕ) : X k →ᵇ H :=
    BoundedContinuousFunction.mkOfCompact ⟨fun t ↦ u n (incl k t), (hu n).comp (hinc k)⟩
  have hwbound : ∀ n k (t : X k), ‖w n k t‖ ≤ M := by
    intro n k t
    exact hbound n (incl k t)
  have hwpair : ∀ k r, ∃ N : ℕ, Equicontinuous
      (fun n : Ici N ↦ fun t : X k ↦ inner ℝ (test r) (w n.val k t)) := by
    intro k r
    exact hpair k r
  obtain ⟨p, φ, hφ, hM, hc, hp⟩ :=
    exists_subsequence_tendstoUniformly_pairings_family X test htest w (fun _ ↦ M)
      hwbound hwpair
  let index (t : Ici a) : ℕ := Classical.choose (exists_nat_gt (t.val - a))
  have hindex (t : Ici a) : t.val < a + index t := by
    have h := Classical.choose_spec (exists_nat_gt (t.val - a))
    change t.val - a < (index t : ℝ) at h
    linarith
  let inWindow (t : Ici a) : X (index t) := ⟨t.val, t.property, (hindex t).le⟩
  let uLimit (t : Ici a) : H := p (index t) (inWindow t)
  have hagree (k : ℕ) (t : X k) : uLimit (incl k t) = p k t := by
    apply ext_inner_left ℝ
    intro v
    exact tendsto_nhds_unique
      ((hp (index (incl k t)) v).tendsto_at (inWindow (incl k t)))
      ((hp k v).tendsto_at t)
  refine ⟨uLimit, φ, hφ, fun t ↦ hM (index t) (inWindow t), ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro t
    let k := index t
    have hk : a ≤ a + (k : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg k)
    have hcont : Continuous (fun s : Ici a ↦
        toWeakSpace ℝ H (p k (projIcc a (a + k) hk s.val))) :=
      (hc k).comp (continuous_projIcc.comp continuous_subtype_val)
    apply hcont.continuousAt.congr_of_eventuallyEq
    have hnear : ∀ᶠ s : Ici a in 𝓝 t, s.val < a + (k : ℝ) :=
      (isOpen_lt continuous_subtype_val continuous_const).mem_nhds (hindex t)
    filter_upwards [hnear] with s hs
    rw [projIcc_of_mem hk ⟨s.property, hs.le⟩]
    exact congrArg (toWeakSpace ℝ H) (hagree k ⟨s.val, s.property, hs.le⟩)
  · intro k v
    change TendstoUniformly (fun n (t : X k) ↦ inner ℝ v (w (φ n) k t))
      (fun t ↦ inner ℝ v (uLimit (incl k t))) atTop
    simpa only [hagree] using hp k v

end PDE.Analysis.Evolution
