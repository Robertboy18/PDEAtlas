/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData

/-!
# Arithmetic of functions smooth up to the boundary

Uniform continuity of each derivative is preserved by sums and by products on a
bounded domain. The product proof uses the first-order product rule inductively;
no smooth extension across the boundary is assumed.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open Set

variable {n k : ℕ} {Ω : Set (ℝ^n)} {f g : ℝ^n → ℝ}

/-- At order zero the closure condition is precisely uniform continuity. -/
theorem of_uniformContinuousOn (hf : UniformContinuousOn f Ω) :
    ContDiffUpToBoundary 0 f Ω := by
  refine ⟨contDiffOn_zero.mpr hf.continuousOn, fun α hα ↦ ?_⟩
  have hnil : α = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hα)
  simpa only [hnil, iteratedPartialDeriv] using hf

/-- Closure regularity of all first partial derivatives supplies the higher
derivative uniform-continuity conditions. -/
theorem of_partialDeriv (hc : ContDiffOn ℝ (k + 1) f Ω)
    (hf : UniformContinuousOn f Ω)
    (hpartial : ∀ i, ContDiffUpToBoundary k (∂[i] f) Ω) :
    ContDiffUpToBoundary (k + 1) f Ω := by
  refine ⟨hc, fun α hα ↦ ?_⟩
  cases α using List.reverseRecOn with
  | nil => simpa only [iteratedPartialDeriv] using hf
  | append_singleton α i =>
    have hlen : α.length ≤ k := by
      simp only [List.length_append, List.length_singleton] at hα
      omega
    rw [funext (PDE.iteratedPartialDeriv_append_single α i f)]
    exact (hpartial i).uniformContinuousOn α hlen

/-- Addition preserves every finite order of classical closure regularity. -/
theorem add (hf : ContDiffUpToBoundary k f Ω) (hg : ContDiffUpToBoundary k g Ω)
    (hopen : IsOpen Ω) : ContDiffUpToBoundary k (fun x ↦ f x + g x) Ω := by
  induction k generalizing f g with
  | zero =>
    exact of_uniformContinuousOn
      (uniformContinuousOn_iff_restrict.mpr
        ((uniformContinuousOn_iff_restrict.mp (hf.uniformContinuousOn [] (by simp))).add
          (uniformContinuousOn_iff_restrict.mp (hg.uniformContinuousOn [] (by simp)))))
  | succ k ih =>
    apply of_partialDeriv (hf.contDiffOn.add hg.contDiffOn)
      (uniformContinuousOn_iff_restrict.mpr
        ((uniformContinuousOn_iff_restrict.mp (hf.uniformContinuousOn [] (by simp))).add
          (uniformContinuousOn_iff_restrict.mp (hg.uniformContinuousOn [] (by simp)))))
    intro i
    apply (ih (hf.partialDeriv_of_succ hopen i)
      (hg.partialDeriv_of_succ hopen i)).congr hopen
    intro x hx
    exact PDE.partialDeriv_add
      ((hf.contDiffOn.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp))
      ((hg.contDiffOn.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp))

/-- Negation preserves classical closure regularity. -/
theorem neg (hf : ContDiffUpToBoundary k f Ω) (hopen : IsOpen Ω) :
    ContDiffUpToBoundary k (fun x ↦ -f x) Ω := by
  induction k generalizing f with
  | zero => exact of_uniformContinuousOn (uniformContinuousOn_iff_restrict.mpr
      (uniformContinuousOn_iff_restrict.mp (hf.uniformContinuousOn [] (by simp))).neg)
  | succ k ih =>
    apply of_partialDeriv hf.contDiffOn.neg (uniformContinuousOn_iff_restrict.mpr
      (uniformContinuousOn_iff_restrict.mp (hf.uniformContinuousOn [] (by simp))).neg)
    intro i
    apply (ih (hf.partialDeriv_of_succ hopen i)).congr hopen
    intro x _
    exact PDE.partialDeriv_neg

/-- Subtraction preserves classical closure regularity. -/
theorem sub (hf : ContDiffUpToBoundary k f Ω) (hg : ContDiffUpToBoundary k g Ω)
    (hopen : IsOpen Ω) : ContDiffUpToBoundary k (fun x ↦ f x - g x) Ω := by
  simpa only [sub_eq_add_neg] using hf.add (hg.neg hopen) hopen

private theorem uniformContinuousOn_mul (hf : ContDiffUpToBoundary k f Ω)
    (hg : ContDiffUpToBoundary k g Ω) (hbounded : Bornology.IsBounded Ω) :
    UniformContinuousOn (fun x ↦ f x * g x) Ω := by
  obtain ⟨F, hF, hFf⟩ := hf.exists_continuous_eqOn
  obtain ⟨G, hG, hGg⟩ := hg.exists_continuous_eqOn
  apply ((hbounded.isCompact_closure.uniformContinuousOn_of_continuous
    (hF.mul hG).continuousOn).mono subset_closure).congr
  intro x hx
  change F x * G x = f x * g x
  rw [hFf hx, hGg hx]

/-- Products preserve closure regularity on a bounded open domain. -/
theorem mul (hf : ContDiffUpToBoundary k f Ω) (hg : ContDiffUpToBoundary k g Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ContDiffUpToBoundary k (fun x ↦ f x * g x) Ω := by
  induction k generalizing f g with
  | zero => exact of_uniformContinuousOn (uniformContinuousOn_mul hf hg hbounded)
  | succ k ih =>
    apply of_partialDeriv (hf.contDiffOn.mul hg.contDiffOn)
      (uniformContinuousOn_mul hf hg hbounded)
    intro i
    have hleft := ih (hf.partialDeriv_of_succ hopen i) (hg.of_le (Nat.le_succ k))
    have hright := ih (hf.of_le (Nat.le_succ k)) (hg.partialDeriv_of_succ hopen i)
    apply (hleft.add hright hopen).congr hopen
    intro x hx
    exact PDE.partialDeriv_mul
      ((hf.contDiffOn.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp))
      ((hg.contDiffOn.contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp))

/-- A finite sum preserves classical closure regularity. -/
theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ^n → ℝ}
    (hF : ∀ i ∈ s, ContDiffUpToBoundary k (F i) Ω)
    (hopen : IsOpen Ω) :
    ContDiffUpToBoundary k (fun x ↦ ∑ i ∈ s, F i x) Ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using const (k := k) 0
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hF i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)) hopen

end SobolevSpace.ContDiffUpToBoundary
