/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Mixed spatial and temporal derivatives within a domain

Insert the unit time vector into the first `l` arguments of the actual joint
jet and spatial vectors into its remaining `k` arguments. This gives a
continuous multilinear spatial derivative, also at a terminal time where
only derivatives within the domain are intrinsic.

The norm is the operator norm on spatial directions; no identification with
a componentwise Euclidean tensor norm is made.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- The actual mixed jet with `k` spatial and `l` temporal derivatives,
taken within `S`. Temporal arguments come first in the joint jet. -/
def spaceTimeMixedFDerivWithin (k l : ℕ) (f : E × ℝ → F)
    (S : Set (E × ℝ)) (p : E × ℝ) : E [×k]→L[ℝ] F :=
  (((iteratedFDerivWithin ℝ (l + k) f S p).domDomCongr finSumFinEquiv.symm).currySum
    (fun _ : Fin l ↦ (0, 1))).compContinuousLinearMap
      (fun _ : Fin k ↦ ContinuousLinearMap.inl ℝ E ℝ)

/-- Evaluation of a mixed jet is evaluation of the joint jet on the
concatenated time and spatial directions. -/
theorem spaceTimeMixedFDerivWithin_apply (k l : ℕ) (f : E × ℝ → F)
    (S : Set (E × ℝ)) (p : E × ℝ) (v : Fin k → E) :
    spaceTimeMixedFDerivWithin k l f S p v =
      iteratedFDerivWithin ℝ (l + k) f S p
        (Fin.append (fun _ : Fin l ↦ (0, 1)) (fun i ↦ (v i, 0))) := by
  simp only [spaceTimeMixedFDerivWithin,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.currySum_apply, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  cases i using Fin.addCases <;> simp

/-- Inserting unit time vectors and spatial isometries cannot increase the
norm of the joint jet. This includes either zero derivative order. -/
theorem norm_spaceTimeMixedFDerivWithin_le (k l : ℕ) (f : E × ℝ → F)
    (S : Set (E × ℝ)) (p : E × ℝ) :
    ‖spaceTimeMixedFDerivWithin k l f S p‖ ≤
      ‖iteratedFDerivWithin ℝ (l + k) f S p‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  rw [spaceTimeMixedFDerivWithin_apply]
  simpa [Fin.prod_univ_add, Prod.norm_def] using
    (iteratedFDerivWithin ℝ (l + k) f S p).le_opNorm
      (Fin.append (fun _ : Fin l ↦ (0, 1)) (fun i ↦ (v i, 0)))

end PDE

open PDE (spaceTimeMixedFDerivWithin)

/-- Mixed jets are continuous on a set with unique derivatives as soon as
the corresponding joint jet is continuous there. -/
theorem ContDiffOn.continuousOn_spaceTimeMixedFDerivWithin
    {f : E × ℝ → F} {S : Set (E × ℝ)} {a : ℕ∞ω}
    (hf : ContDiffOn ℝ a f S) (k l : ℕ) (hkl : (l + k : ℕ) ≤ a)
    (hS : UniqueDiffOn ℝ S) :
    ContinuousOn (spaceTimeMixedFDerivWithin k l f S) S := by
  have hjet := hf.continuousOn_iteratedFDerivWithin hkl hS
  have hperm := (ContinuousMultilinearMap.domDomCongrₗᵢ
    ℝ (E × ℝ) F finSumFinEquiv.symm).continuous.comp_continuousOn hjet
  have hcurry := (ContinuousMultilinearMap.currySumEquiv
    ℝ (Fin l) (Fin k) (E × ℝ) F).continuous.comp_continuousOn hperm
  have heval := (continuous_eval_const (fun _ : Fin l ↦ ((0 : E), (1 : ℝ)))).comp_continuousOn
    hcurry
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin k ↦ ContinuousLinearMap.inl ℝ E ℝ)).continuous.comp_continuousOn heval
