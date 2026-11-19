/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.GlobalClassical
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.SmoothOperator
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.ScaleSmoothness
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Compatible higher wave trajectories and time smoothness

Higher lifts of the same energy wave agree after forgetting spatial orders.
Their first time derivatives therefore form an equation across the Sobolev
scale. Smoothness of the scalar composition operators gives smooth time
curves at every order by simultaneous induction along this scale.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} [NeZero n] {f : ℝ → ℝ} {K : ℝ≥0}

omit [NeZero n] in
/-- Higher lifts of one energy curve are compatible on the forward half-line. -/
theorem higher_lifts_compatible
    (U : ∀ j : ℕ, C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)))
    {e : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}
    (hU : ∀ j t, 0 ≤ t →
      (lowerOrderCLM (by omega : 1 ≤ j + 4) (U j t).1,
        wkpBaseCoordinateCLM (U j t).2) = e t)
    (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (lowerOrderCLM (by omega : j + 4 ≤ (j + 1) + 4) (U (j + 1) t).1,
      lowerOrderCLM (by omega : j + 3 ≤ (j + 1) + 3) (U (j + 1) t).2) = U j t := by
  have he := (hU (j + 1) t ht).trans (hU j t ht).symm
  apply Prod.ext
  · apply wkpBaseCoordinateCLM_injective isOpen_univ
    exact congrArg (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := univ))
      (congrArg Prod.fst he)
  · apply wkpBaseCoordinateCLM_injective isOpen_univ
    exact congrArg Prod.snd he

/-- At every level, a higher lift has the time derivative prescribed by the
velocity and the semilinear acceleration at the next spatial level. -/
theorem IsEnergySolution.hasDerivAt_higher_lifts
    (hk : ∀ j : ℕ, (n : ℝ) < 2 * (((j + 3 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {e : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (he : IsEnergySolution hf hf0 x e)
    (U : ∀ j : ℕ, C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)))
    (hU : ∀ j t, 0 ≤ t →
      (lowerOrderCLM (by omega : 1 ≤ j + 4) (U j t).1,
        wkpBaseCoordinateCLM (U j t).2) = e t)
    (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (U j)
      ((U (j + 1) t).2, higherSmoothAcceleration (hk j) hs hf0 (U (j + 1) t).1) t := by
  have he' : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ (j + 3) + 2) (U (j + 1) 0).1,
        wkpBaseCoordinateCLM (U (j + 1) 0).2) e := by
    rw [hU (j + 1) 0 le_rfl, he.initial]
    exact he
  have hd := he'.hasDerivWithinAt_higherOrder_smoothReaction (hk j) hs hf hf0
    (U (j + 1) 0) (U (j + 1)) rfl (b := t + 1)
    (fun s hst ↦ hU (j + 1) s hst.1) (t := t) ⟨ht.le, by linarith⟩
  have hq := hd.1.hasDerivAt (Icc_mem_nhds ht (by linarith))
  have hv := hd.2.hasDerivAt (Icc_mem_nhds ht (by linarith))
  apply (hq.prodMk hv).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs using (higher_lifts_compatible U hU j hs.le).symm

/-- Smooth scalar composition at each high Sobolev order upgrades every
compatible continuous higher lift to a smooth time curve. -/
theorem IsEnergySolution.contDiffOn_higher_lifts
    (hk : ∀ j : ℕ, (n : ℝ) < 2 * (((j + 3 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {e : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (he : IsEnergySolution hf hf0 x e)
    (U : ∀ j : ℕ, C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)))
    (hU : ∀ j t, 0 ≤ t →
      (lowerOrderCLM (by omega : 1 ≤ j + 4) (U j t).1,
        wkpBaseCoordinateCLM (U j t).2) = e t) :
    ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (U j) (Ioi 0) := by
  let F (j : ℕ) (z : W^{(j + 1) + 4,2}(ℝ^n) × W^{(j + 1) + 3,2}(ℝ^n)) :
      W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n) := (z.2, higherSmoothAcceleration (hk j) hs hf0 z.1)
  have hF (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (F j) := by
    let Q : (W^{(j + 1) + 4,2}(ℝ^n) × W^{(j + 1) + 3,2}(ℝ^n)) →L[ℝ]
        W^{(j + 3) + 2,2}(ℝ^n) := ContinuousLinearMap.fst ℝ _ _
    let L : W^{(j + 3) + 2,2}(ℝ^n) →L[ℝ] W^{j + 3,2}(ℝ^n) := higherOrderLaplacianCLM le_rfl
    let R : W^{(j + 3) + 2,2}(ℝ^n) →L[ℝ] W^{j + 3,2}(ℝ^n) :=
      lowerOrderCLM (by omega)
    have hA : ContDiff ℝ (⊤ : ℕ∞) (higherSmoothAcceleration (hk j) hs hf0) :=
      L.contDiff.sub ((contDiff_higherComposition (hk j) hs hf0).comp R.contDiff)
    exact contDiff_snd.prodMk (hA.comp Q.contDiff)
  exact contDiffOn_scale_of_hasDerivAt isOpen_Ioi (fun j ↦ j + 1)
    (fun j ↦ U j) F (fun j ↦ (U j).continuous.continuousOn) hF
    (fun j _ ht ↦ he.hasDerivAt_higher_lifts hk hs hf hf0 U hU j ht)

end PDE.Hyperbolic.NonlinearWave.Cauchy
