/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.JointRegularity

/-!
# Higher joint regularity from Sobolev time curves

Finite time regularity in a sufficiently high Sobolev space gives the same
joint spacetime regularity. The proof uses continuous evaluation and commutes
the spatial partial derivatives with the canonical Sobolev representative.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

private theorem contDiffOn_partialDerivCLM_comp {n r k : ℕ} {s : Set ℝ}
    {u : ℝ → W^{k + 1,2}(ℝ^n)} (hu : ContDiffOn ℝ (r + 1) u s) (i : Fin n) :
    ContDiffOn ℝ r (fun t ↦ partialDerivCLM i (u t)) s := by
  let D : W^{k + 1,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) := partialDerivCLM i
  have hu' : ContDiffOn ℝ r u s := hu.of_le (by simp)
  exact D.contDiff.comp_contDiffOn hu'

private theorem contDiffOn_joint_classicalRepresentative_succ {n r k : ℕ} {s : Set ℝ}
    (hs : IsOpen s) (hk : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hl : (n : ℝ) < 2 * ((k : ℝ) - 1))
    {u : ℝ → W^{k + 1,2}(ℝ^n)} (hu : ContDiffOn ℝ (r + 1) u s)
    (hv : ContDiffOn ℝ r (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hk (deriv u p.1) p.2)
      (s ×ˢ univ))
    (hd : ∀ i : Fin n, ContDiffOn ℝ r (fun p : ℝ × ℝ^n ↦
      classicalRepresentativeCLM hl (partialDerivCLM i (u p.1)) p.2) (s ×ˢ univ)) :
    ContDiffOn ℝ (r + 1)
      (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hk (u p.1) p.2) (s ×ˢ univ) := by
  apply contDiffOn_succ_of_spaceTime_derivatives hs (hv := hv) (hd := hd)
  · intro t ht x
    have ht' : HasDerivAt u (deriv u t) t :=
      (hu.differentiableOn (by simp)).differentiableAt (hs.mem_nhds ht) |>.hasDerivAt
    exact ((BoundedContinuousFunction.evalCLM ℝ x).comp
      (classicalRepresentativeCLM hk)).hasFDerivAt.comp_hasDerivAt t ht'
  · exact fun t _ x ↦ hasFDerivAt_classicalRepresentative hl hk (u t) x

/-- A C^r time curve in H^k gives a jointly C^r representative when the
Sobolev order also controls r spatial derivatives. -/
theorem contDiffOn_joint_classicalRepresentative {n r k : ℕ} {s : Set ℝ} (hs : IsOpen s)
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hr : (n : ℝ) < 2 * ((k : ℝ) - r - 1)) {u : ℝ → W^{k,2}(ℝ^n)}
    (hu : ContDiffOn ℝ r u s) :
    ContDiffOn ℝ r (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hk (u p.1) p.2) (s ×ˢ univ) := by
  induction r generalizing k with
  | zero =>
    apply contDiffOn_zero.mpr
    exact continuous_eval.comp_continuousOn
      (((classicalRepresentativeCLM hk).continuous.comp_continuousOn hu.continuousOn).comp
        continuousOn_fst (fun _ hp ↦ hp.1) |>.prodMk continuousOn_snd)
  | succ r ih =>
    have hr0 := Nat.cast_nonneg (α := ℝ) r
    cases k with
    | zero =>
      have hn := Nat.cast_nonneg (α := ℝ) n
      simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hr
      linarith
    | succ k =>
      have hl : (n : ℝ) < 2 * ((k : ℝ) - 1) := by
        push_cast at hr
        linarith
      have hrl : (n : ℝ) < 2 * ((k : ℝ) - r - 1) := by
        push_cast at hr
        linarith
      have hrh : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - r - 1) := by
        push_cast at hr ⊢
        linarith
      apply contDiffOn_joint_classicalRepresentative_succ hs hk hl hu
      · exact ih (k := k + 1) hk hrh (u := deriv u)
          (hu.deriv_of_isOpen hs (by simp))
      · intro i
        let D : W^{k + 1,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) := partialDerivCLM i
        have hspace : ContDiffOn ℝ r (fun t ↦ D (u t)) s :=
          contDiffOn_partialDerivCLM_comp (n := n) (r := r) (k := k) hu i
        exact ih (k := k) hl hrl (u := fun t ↦ D (u t)) hspace

end PDE.Hyperbolic.NonlinearWave.Cauchy
