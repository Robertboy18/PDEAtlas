/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.Differentiable

/-!
# Smooth nonlinear maps on the Sobolev algebra

The centered derivative coefficients are themselves smooth reactions fixing zero.
Induction therefore gives every derivative of the composition operator, using
the same strict threshold `n < 2k` at each step.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev Topology

namespace SobolevSpace.Composition

open GraphSpace

variable {n k : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

/-- Smooth reactions fixing zero act smoothly on finite families of Hᵏ functions when `n < 2k`. -/
theorem contDiff_finiteComposition
    (hk : (n : ℝ) < 2 * (k : ℝ)) {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (finiteComposition hk hf hf0) := by
  classical
  let : NormedAddCommGroup ((ι → W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n)) :=
    ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)
      (E := ι → W^{k,2}(ℝ^n)) (F := W^{k,2}(ℝ^n))
  let : NormedSpace ℝ ((ι → W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n)) :=
    ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)
      (E := ι → W^{k,2}(ℝ^n)) (F := W^{k,2}(ℝ^n))
  have horder (j : ℕ) : ∀ (g : (ι → ℝ) → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hg0 : g 0 = 0), ContDiff ℝ j (finiteComposition hk hg hg0) := by
    induction j with
    | zero =>
      intro g hg hg0
      exact contDiff_zero.mpr (locallyLipschitz_finiteComposition hk hg hg0).continuous
    | succ j ih =>
      intro g hg hg0
      simp only [Nat.cast_add, Nat.cast_one]
      rw [contDiff_succ_iff_hasFDerivAt]
      refine ⟨finiteCompositionDerivative hk hg, ?_, hasFDerivAt_finiteComposition hk hg hg0⟩
      apply ContDiff.sum
      intro i _
      have hcoeff : ContDiff ℝ j (finiteComposition hk
          (contDiff_centeredPartial hg i) (centeredPartial_zero g i)) :=
        ih _ (contDiff_centeredPartial hg i) (centeredPartial_zero g i)
      have hmul : ContDiff ℝ j (fun U : ι → W^{k,2}(ℝ^n) ↦ multiplication hk
          (finiteComposition hk (contDiff_centeredPartial hg i)
            (centeredPartial_zero g i) U)) :=
        ContDiff.continuousLinearMap_comp (𝕜 := ℝ)
          (E := ι → W^{k,2}(ℝ^n)) (F := W^{k,2}(ℝ^n))
          (G := W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n)) (multiplication hk) hcoeff
      have hcomp : ContDiff ℝ j (fun U : ι → W^{k,2}(ℝ^n) ↦
          (multiplication hk (finiteComposition hk (contDiff_centeredPartial hg i)
            (centeredPartial_zero g i) U)).comp
            (ContinuousLinearMap.proj i : (ι → W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n))) :=
        ContDiff.clm_comp (𝕜 := ℝ) (X := ι → W^{k,2}(ℝ^n))
          (E := ι → W^{k,2}(ℝ^n)) (F := W^{k,2}(ℝ^n)) (G := W^{k,2}(ℝ^n))
          hmul (contDiff_const (c :=
            (ContinuousLinearMap.proj i : (ι → W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n))))
      have hconst : ContDiff ℝ j (fun _ : ι → W^{k,2}(ℝ^n) ↦
          fderiv ℝ g 0 (Pi.single i 1) •
            (ContinuousLinearMap.proj i : (ι → W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n))) :=
        contDiff_const
      exact hcomp.add hconst
  exact contDiff_infty.mpr (fun j ↦ horder j f hf hf0)
end SobolevSpace.Composition
