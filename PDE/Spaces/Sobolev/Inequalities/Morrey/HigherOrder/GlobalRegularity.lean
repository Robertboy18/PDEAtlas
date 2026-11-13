/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Embedding
import PDE.Spaces.Sobolev.Calculus.Differentiation.WeakToClassical

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Classical representatives for global higher-order Sobolev fields

When `p > n`, global Morrey representatives of adjacent weak derivatives are continuous.
Their weak derivative identities reconstruct the classical jet on all of Euclidean space.
No boundary extension atlas is required.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Topology Sobolev

/-- Adjacent global Morrey representatives satisfy the original weak derivative identity. -/
theorem finiteMorreyDerivativeEmbedding_hasWeakDerivativeOn
    {n m : ℕ} {p q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 2 ≤ m)
    (i : Fin n) (U : W^{m,ENNReal.ofReal p}((Set.univ : Set (ℝ^n)))) :
    HasWeakDerivativeOn (n := n) Set.univ [i]
      (finiteMorreyDerivativeEmbedding hn hp hpq α (by omega) U)
      (finiteMorreyDerivativeEmbedding
        hn hp hpq (α ++ [i]) (by
          simp only [List.length_append, List.length_singleton]; omega) U) := by
  let hαone : α.length + 1 ≤ m := by omega
  let hαi : (α ++ [i]).length + 1 ≤ m := by
    simp
    omega
  let V : W^{1,ENNReal.ofReal p}((Set.univ : Set (ℝ^n))) :=
    derivativeWordCLM
      (n := n) (m := m) (r := 1) (p := ENNReal.ofReal p)
      (Ω := Set.univ) α hαone U
  have hraw :
      HasWeakDerivativeOn (n := n) Set.univ [i]
        (((V : WkpAmbientOn n 1 (ENNReal.ofReal p) Set.univ)
          (baseIndex n 1) :
            DerivLp n (ENNReal.ofReal p) Set.univ) :
          ℝ^n → ℝ)
        (((V : WkpAmbientOn n 1 (ENNReal.ofReal p) Set.univ)
          (singleDerivIndex n i) :
            DerivLp n (ENNReal.ofReal p) Set.univ) :
          ℝ^n → ℝ) := by
    simpa only [firstDerivIndex_one] using
      V.property.hasWeakDerivativeOn_first (by norm_num) i
  have hbase :
      finiteMorreyDerivativeEmbedding hn hp hpq α hαone U
          =ᵐ[volume]
        (((V : WkpAmbientOn n 1 (ENNReal.ofReal p) Set.univ)
          (baseIndex n 1) :
            DerivLp n (ENNReal.ofReal p) Set.univ) :
          ℝ^n → ℝ) := by
    simpa [V] using
      finiteMorreyDerivativeEmbedding_ae
        hn hp hpq α hαone U
  have hderiv :
      finiteMorreyDerivativeEmbedding
          hn hp hpq (α ++ [i]) hαi U
          =ᵐ[volume]
        (((V : WkpAmbientOn n 1 (ENNReal.ofReal p) Set.univ)
          (singleDerivIndex n i) :
            DerivLp n (ENNReal.ofReal p) Set.univ) :
          ℝ^n → ℝ) := by
    have h :=
      finiteMorreyDerivativeEmbedding_ae
        hn hp hpq (α ++ [i]) hαi U
    rw [derivativeWordIndex_append_singleton_baseIndex
      α i hαone hαi (by norm_num), firstDerivIndex_one] at h
    simpa [V] using h
  exact
    (hasWeakDerivativeOn_congr_ae
      (n := n) (Ω := Set.univ) (α := [i])
      (by simpa only [domainMeasure, Measure.restrict_univ] using hbase)
      (by simpa only [domainMeasure, Measure.restrict_univ] using hderiv)).mpr hraw

/-- Global Morrey representatives have the derivative given by the adjacent weak jet. -/
theorem finiteMorreyDerivativeEmbedding_hasFDerivAt
    {n m : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (α : List (Fin n)) (hα : α.length + 2 ≤ m)
    (U : W^{m,(ENNReal.ofReal p)}(ℝ^n)) (x : ℝ^n) :
    HasFDerivAt
      (finiteMorreyDerivativeEmbedding hn hp hpq α (by omega) U)
      (innerSL ℝ (WithLp.toLp 2 fun i ↦
        finiteMorreyDerivativeEmbedding hn hp hpq (α ++ [i]) (by
          simp only [List.length_append, List.length_singleton]; omega) U x)) x := by
  apply Approximation.hasFDerivAt_of_continuous_weakPartialDerivatives
  · exact (finiteMorreyDerivativeEmbedding hn hp hpq α (by omega) U).continuous
  · intro i
    exact (finiteMorreyDerivativeEmbedding hn hp hpq (α ++ [i]) (by
      simp only [List.length_append, List.length_singleton]; omega) U).continuous
  · intro i
    exact finiteMorreyDerivativeEmbedding_hasWeakDerivativeOn hn hp hpq α hα i U

/-- A global Morrey derivative representative is `C^k` when the Sobolev field contains
one further weak derivative beyond its order-`k` jet. -/
theorem finiteMorreyDerivativeEmbedding_contDiff
    {n m : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hn : 0 < n) (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (k : ℕ) (α : List (Fin n)) (hα : α.length + k + 1 ≤ m)
    (U : W^{m,(ENNReal.ofReal p)}(ℝ^n)) :
    ContDiff ℝ k (finiteMorreyDerivativeEmbedding hn hp hpq α (by omega) U) := by
  induction k generalizing α with
  | zero =>
      exact contDiff_zero.mpr
        (finiteMorreyDerivativeEmbedding hn hp hpq α (by omega) U).continuous
  | succ k ih =>
      let f' : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦
        innerSL ℝ (WithLp.toLp 2 fun i ↦
          finiteMorreyDerivativeEmbedding hn hp hpq (α ++ [i]) (by
            simp only [List.length_append, List.length_singleton]; omega) U x)
      have hf' : ContDiff ℝ k f' := by
        have hvec : ContDiff ℝ k
            (fun x ↦ WithLp.toLp 2 fun i ↦
              finiteMorreyDerivativeEmbedding hn hp hpq (α ++ [i])
                (by simp only [List.length_append, List.length_singleton]; omega) U x) := by
          apply contDiff_piLp' 2
          intro i
          exact ih (α ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega)
        exact (innerSL ℝ).contDiff.comp hvec
      apply contDiff_succ_iff_hasFDerivAt.mpr
      exact ⟨f', hf', fun x ↦
        finiteMorreyDerivativeEmbedding_hasFDerivAt hn hp hpq α (by omega) U x⟩

end SobolevSpace.GraphSpace
