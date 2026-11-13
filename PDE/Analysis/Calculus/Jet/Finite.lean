/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.Derivative
public import PDE.Analysis.Calculus.Jet.Finite.Composition
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Finite tuples of ordinary derivatives

`jetLT` collects the derivatives of orders strictly below a given natural
number. Its derivatives are determined by the corresponding higher derivatives
of the original map.
-/

@[expose] public noncomputable section

open scoped ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace PDE

/-- The tuple of derivatives of orders strictly below `k`, including the value
as a zero-linear map when `k > 0`. -/
def jetLT (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (k : ℕ) (f : E → F) (x : E) : ∀ i : Fin k, E [×(i : ℕ)]→L[𝕜] F :=
  fun i ↦ iteratedFDeriv 𝕜 i f x

/-- Every finite tuple of derivatives of a smooth map is smooth. -/
theorem _root_.ContDiff.jetLT {f : E → F} (hf : ContDiff 𝕜 ∞ f) (k : ℕ) :
    ContDiff 𝕜 ∞ (jetLT 𝕜 k f) :=
  contDiff_pi.mpr fun _ ↦ hf.iteratedFDeriv_right (by simp)

/-- The `r`th derivative of the lower `k` jets only uses original derivatives
of orders strictly below `r + k`. -/
theorem iteratedFDeriv_jetLT_eq_of_iteratedFDeriv_eq
    {f g : E → F} (hf : ContDiff 𝕜 ∞ f) (hg : ContDiff 𝕜 ∞ g)
    (k r : ℕ) (x : E)
    (heq : ∀ i < r + k, iteratedFDeriv 𝕜 i f x = iteratedFDeriv 𝕜 i g x) :
    iteratedFDeriv 𝕜 r (jetLT 𝕜 k f) x =
      iteratedFDeriv 𝕜 r (jetLT 𝕜 k g) x := by
  apply ContinuousMultilinearMap.ext
  intro w
  funext i
  apply ContinuousMultilinearMap.ext
  intro v
  let L : (∀ j : Fin k, E [×(j : ℕ)]→L[𝕜] F) →L[𝕜] F :=
    (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin (i : ℕ) ↦ E) F v).comp
      (ContinuousLinearMap.proj i)
  have hL (u : E → F) (hu : ContDiff 𝕜 ∞ u) :
      iteratedFDeriv 𝕜 r (fun y ↦ iteratedFDeriv 𝕜 i u y v) x w =
        (iteratedFDeriv 𝕜 r (jetLT 𝕜 k u) x w) i v := by
    simpa only [L, jetLT, ContinuousLinearMap.comp_apply, Function.comp_def,
      ContinuousLinearMap.proj_apply, ContinuousMultilinearMap.apply_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe] using
      congrArg (fun A ↦ A w)
        (L.iteratedFDeriv_comp_left (hu.jetLT k).contDiffAt (by simp : (r : ℕ∞ω) ≤ ∞))
  rw [← hL f hf, ← hL g hg, iteratedFDeriv_eval_iteratedFDeriv hf,
    iteratedFDeriv_eval_iteratedFDeriv hg, heq (r + i) (by omega)]

/-- A smooth function of position and lower jets has the expected finite
dependence on the original derivatives. -/
theorem iteratedFDeriv_comp_jetLT_eq_of_iteratedFDeriv_eq
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f g : E → F} (hf : ContDiff 𝕜 ∞ f) (hg : ContDiff 𝕜 ∞ g)
    (k r : ℕ) (x : E)
    {Φ : E × (∀ i : Fin k, E [×(i : ℕ)]→L[𝕜] F) → G}
    (hΦ : ContDiff 𝕜 ∞ Φ)
    (heq : ∀ i < r + k, iteratedFDeriv 𝕜 i f x = iteratedFDeriv 𝕜 i g x) :
    iteratedFDeriv 𝕜 r (fun y ↦ Φ (y, jetLT 𝕜 k f y)) x =
      iteratedFDeriv 𝕜 r (fun y ↦ Φ (y, jetLT 𝕜 k g y)) x := by
  apply iteratedFDeriv_comp_eq_of_iteratedFDeriv_eq
    ((contDiff_id.prodMk (hf.jetLT k)).contDiffAt.of_le (by simp))
    ((contDiff_id.prodMk (hg.jetLT k)).contDiffAt.of_le (by simp))
    (hΦ.contDiffAt.of_le (by simp))
  intro i hi
  rw [iteratedFDeriv_prodMk contDiffAt_id (hf.jetLT k).contDiffAt
      (by simp : (i : ℕ∞ω) ≤ ∞),
    iteratedFDeriv_prodMk contDiffAt_id (hg.jetLT k).contDiffAt
      (by simp : (i : ℕ∞ω) ≤ ∞)]
  rw [iteratedFDeriv_jetLT_eq_of_iteratedFDeriv_eq hf hg k i x
    (fun j hj ↦ heq j (by omega))]

end PDE
