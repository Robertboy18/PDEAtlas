/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.FiniteTrajectory
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.ReversibleHigherScale
import PDE.Spaces.Sobolev.GraphSpace.Topology.OrderDensity

/-!
# All-orders regularity along a finite higher trajectory

A finite higher Sobolev trajectory has bounded amplitude. Truncating the
reaction outside this range preserves its mild equation, and uniqueness of
the energy projection identifies it with the smooth compatible Sobolev lifts.
Thus smooth compact data retain every order on the entire closed time interval.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- Smooth compact data retain joint smoothness throughout every finite higher
mild trajectory, including both time endpoints. The reaction only needs to be smooth. -/
theorem contDiffOn_infty_higherSmooth_trajectory_of_smoothCompact (hn : n < 4)
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) {τ : ℝ≥0}
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n k).IsMildSolutionOn (higherSmoothMap hk hs hf0)
      (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc) τ V) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hq
      (IccExtend τ.property V p.1).1 p.2) (Icc 0 (τ : ℝ) ×ˢ univ) := by
  obtain ⟨F, K, hFs, hF, hF0, hVF, _⟩ :=
    exists_lipschitz_truncation_higherSmooth_trajectory hk hq hs hf0 V hV
  obtain ⟨e, he, U, _, hU, htime⟩ :=
    exists_smooth_higher_lifts_of_smoothCompact hn hFs hF hF0 g h hg hh hgc hhc
  have hx : (lowerOrderCLM (Nat.succ_pos k)
        (mkWkpSpaceOnOfContDiff (k := k + 1) (p := 2) (Ω := univ) g hg hgc),
        wkpBaseCoordinateCLM (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) h hh hhc)) =
      (mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := univ) g hg hgc,
        wkpBaseCoordinateCLM (mkWkpSpaceOnOfContDiff (k := 3) (p := 2) (Ω := univ) h hh hhc)) := by
    apply Prod.ext
    · exact lowerOrderCLM_mkWkpSpaceOnOfContDiff (Nat.succ_pos k) g hg hgc
    · apply Lp.ext
      exact (wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae hh hhc).trans
        (wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae hh hhc).symm
  have he' : IsEnergySolution hF hF0 (lowerOrderCLM (Nat.succ_pos k)
        (mkWkpSpaceOnOfContDiff (k := k + 1) (p := 2) (Ω := univ) g hg hgc), wkpBaseCoordinateCLM
          (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) h hh hhc)) e := by
    rw [hx]
    exact he
  have hproj := he'.eq_higherSmooth_mild_projection hk hFs hF hF0
    (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc) V hVF
  have hn' : (n : ℝ) < 4 := by exact_mod_cast hn
  refine contDiffOn_infty.mpr fun r ↦ ?_
  have hkr : (n : ℝ) < 2 * (((r + 4 : ℕ) : ℝ) - 1) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hrr : (n : ℝ) < 2 * (((r + 4 : ℕ) : ℝ) - r - 1) := by push_cast; linarith
  have hut : ContDiffOn ℝ r (fun t ↦ (U r t).1) univ :=
    (contDiff_fst.comp ((htime r).of_le (by simp))).contDiffOn
  have hfield := contDiffOn_joint_classicalRepresentative isOpen_univ hkr hrr hut
  refine (hfield.mono (prod_mono (subset_univ _) Subset.rfl)).congr fun p hp ↦ ?_
  have hb : baseRepresentative (IccExtend τ.property V p.1).1 =
      baseRepresentative (U r p.1).1 := by
    have heq := congrArg Prod.fst ((hproj p.1 hp.1).trans (hU r p.1 hp.1.1).symm)
    exact congrArg (fun z : H¹(ℝ^n) ↦ baseRepresentative z) heq
  have ha : (classicalRepresentativeCLM hq (IccExtend τ.property V p.1).1 : ℝ^n → ℝ)
      =ᵐ[volume] baseRepresentative (U r p.1).1 := by
    rw [← hb]
    exact classicalRepresentativeCLM_ae hq (IccExtend τ.property V p.1).1
  exact congrFun (eq_classicalRepresentativeCLM_of_ae_eq hkr _
    (classicalRepresentativeCLM hq (IccExtend τ.property V p.1).1).continuous ha) p.2

end PDE.Hyperbolic.NonlinearWave.Cauchy
