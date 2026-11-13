/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothTrajectory
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiniteForwardUniqueness
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.TraceOperator

/-!
# Classical comparison for smooth higher Sobolev trajectories

The canonical representative of a finite higher Sobolev trajectory agrees with
any classical wave having the same smooth compact Cauchy data. The competitor
needs only interior C² regularity and C¹ regularity at the initial face.
-/

@[expose] public noncomputable section

open Filter PDE.Common Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open WaveEquation

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- A classical wave with the prescribed data agrees with the canonical
higher Sobolev trajectory throughout every common finite time strip. -/
theorem eq_classical_higherSmooth_trajectory_of_smoothCompact (hn : n < 4)
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) {τ : ℝ≥0} {T : ℝ} (hτ : 0 < (τ : ℝ))
    (hτT : (τ : ℝ) ≤ T) (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n (k + 1)).IsMildSolutionOn (higherSmoothMap hv hs hf0)
      (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc) τ V)
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiffOn ℝ 2 u {p | p 0 ∈ Ioo 0 T})
    (hu₀ : ContDiffOn ℝ 1 u {p | p 0 ∈ Ico 0 T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) :
    ∀ t ∈ Ico 0 (τ : ℝ), ∀ x, u (timeSpaceCons t x) =
      classicalRepresentativeCLM hq (IccExtend τ.property V t).1 x := by
  let U := IccExtend τ.property V
  let q : ℝ × ℝ^n → ℝ := fun p ↦ classicalRepresentativeCLM hq (U p.1).1 p.2
  let v : ℝ^(n + 1) → ℝ := fun p ↦ q (timeSpaceContinuousLinearEquiv n p)
  have hslice (t : ℝ) (x : ℝ^n) : v (timeSpaceCons t x) = q (t, x) :=
    congrArg q ((timeSpaceContinuousLinearEquiv n).apply_symm_apply (t, x))
  have hqs : ContDiffOn ℝ (⊤ : ℕ∞) q (Icc 0 (τ : ℝ) ×ˢ univ) :=
    contDiffOn_infty_higherSmooth_trajectory_of_smoothCompact hn hv hq hs hf0 g h hg hh hgc hhc V hV
  have hvs : ContDiffOn ℝ (⊤ : ℕ∞) v {p | p 0 ∈ Ico 0 (τ : ℝ)} :=
    hqs.comp (timeSpaceContinuousLinearEquiv n).contDiff.contDiffOn
      (fun _ hp ↦ ⟨⟨hp.1, hp.2.le⟩, mem_univ _⟩)
  have hvi : ContDiffOn ℝ 2 v {p | p 0 ∈ Ioo 0 (τ : ℝ)} :=
    (hvs.of_le (by simp)).mono (fun _ hp ↦ ⟨hp.1.le, hp.2⟩)
  have hzero : U 0 = (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc) :=
    (IccExtend_of_mem τ.property V ⟨le_rfl, τ.property⟩).trans hV.initial_value
  have hvpos (x : ℝ^n) : v (timeSpaceCons 0 x) = g x := by
    rw [hslice]
    change classicalRepresentativeCLM hq (U 0).1 x = g x
    rw [hzero]
    exact congrFun (classicalRepresentative_mkWkpSpaceOnOfContDiff hq hg hgc) x
  have hvvel (x : ℝ^n) :
      HasDerivWithinAt (fun t ↦ v (timeSpaceCons t x)) (h x) (Ici 0) 0 := by
    simp only [hslice]
    have hd := (hasDerivWithinAt_classical_higherSmooth_trajectory
      hk hv hq hs hf0 V hV ⟨le_rfl, τ.property⟩ x).1
    change HasDerivWithinAt (fun t ↦ q (t, x))
      (classicalRepresentativeCLM hv (U 0).2 x) (Icc 0 (τ : ℝ)) 0 at hd
    rw [hzero, classicalRepresentative_mkWkpSpaceOnOfContDiff] at hd
    exact hd.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hτ)
  have hvwave (t : ℝ) (ht : t ∈ Ioo 0 (τ : ℝ)) (x : ℝ^n) :
      waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0 := by
    have hopen : IsOpen {p : ℝ^(n + 1) | p 0 ∈ Ioo 0 (τ : ℝ)} :=
      isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous
    rw [waveOperator_timeSpaceCons_of_contDiffAt ((hvi _ ht).contDiffAt (hopen.mem_nhds ht))]
    simp only [hslice]
    exact higherSmooth_trajectory_wave_equation hk hv hq hs hf0 V hV ht x
  have heq := eq_on_finite_forward_strip ((hs.of_le (by simp)).locallyLipschitz)
    (hu.mono (fun _ hp ↦ ⟨hp.1, hp.2.trans_le hτT⟩)) hvi
    (hu₀.mono (fun _ hp ↦ ⟨hp.1, hp.2.trans_le hτT⟩)) (hvs.of_le (by simp))
    (fun t ht x ↦ hwave t ⟨ht.1, ht.2.trans_le hτT⟩ x) hvwave
    (fun x ↦ (hpos x).trans (hvpos x).symm)
    (fun x ↦ (hvel x).trans ((hvvel x).derivWithin (uniqueDiffWithinAt_Ici 0)).symm)
  exact fun t ht x ↦ (heq t ht x).trans (hslice t x)

end PDE.Hyperbolic.NonlinearWave.Cauchy
