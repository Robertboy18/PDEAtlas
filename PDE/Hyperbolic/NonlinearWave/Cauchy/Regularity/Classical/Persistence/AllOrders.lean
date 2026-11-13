/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.HigherScale
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.JointHigherRegularity
import PDE.Spaces.Sobolev.GraphSpace.Topology.OrderDensity

/-!
# All-orders spacetime regularity of scalar wave trajectories

Every finite spacetime derivative is obtained from a sufficiently high Sobolev
time curve. Compatibility of the higher lifts identifies their pointwise
representatives, so all finite orders hold for the same field on the same
forward time interval.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} [NeZero n] {f : ℝ → ℝ} {K : ℝ≥0}

omit [NeZero n] in
/-- Smooth time dependence at every Sobolev order gives a single jointly
smooth representative of the common energy displacement. -/
theorem contDiffOn_joint_of_higher_lifts
    (U : ∀ j : ℕ, C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)))
    {e : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}
    (hU : ∀ j t, 0 ≤ t →
      (lowerOrderCLM (by omega : 1 ≤ j + 4) (U j t).1,
        wkpBaseCoordinateCLM (U j t).2) = e t)
    (hs : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (U j) (Ioi 0))
    (h0 : (n : ℝ) < 2 * ((4 : ℝ) - 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM h0 (U 0 p.1).1 p.2)
      (Ioi 0 ×ˢ univ) := by
  refine contDiffOn_infty.mpr fun r ↦ ?_
  have hr0 := Nat.cast_nonneg (α := ℝ) r
  have hkr : (n : ℝ) < 2 * (((r + 4 : ℕ) : ℝ) - 1) := by push_cast; linarith
  have hrr : (n : ℝ) < 2 * (((r + 4 : ℕ) : ℝ) - r - 1) := by push_cast; linarith
  have htime : ContDiffOn ℝ r (fun t ↦ (U r t).1) (Ioi 0) :=
    contDiff_fst.comp_contDiffOn ((hs r).of_le (by simp))
  have hfield := contDiffOn_joint_classicalRepresentative isOpen_Ioi hkr hrr htime
  refine hfield.congr fun p hp ↦ ?_
  have hb : baseRepresentative (U 0 p.1).1 = baseRepresentative (U r p.1).1 := by
    have he := congrArg Prod.fst ((hU 0 p.1 hp.1.le).trans (hU r p.1 hp.1.le).symm)
    exact congrArg (fun z : H¹(ℝ^n) ↦ baseRepresentative z) he
  have ha : (classicalRepresentativeCLM h0 (U 0 p.1).1 : ℝ^n → ℝ)
      =ᵐ[volume] baseRepresentative (U r p.1).1 := by
    rw [← hb]
    exact classicalRepresentativeCLM_ae h0 (U 0 p.1).1
  exact congrFun (eq_classicalRepresentativeCLM_of_ae_eq hkr _
    (classicalRepresentativeCLM h0 (U 0 p.1).1).continuous ha) p.2

omit [NeZero n] in
/-- Any continuous representative of the common energy displacement inherits
joint smoothness from compatible smooth higher time curves. -/
theorem contDiffOn_of_higher_lifts (hn : n < 4)
    (U : ∀ j : ℕ, C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)))
    {e : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}
    (hU : ∀ j t, 0 ≤ t →
      (lowerOrderCLM (by omega : 1 ≤ j + 4) (U j t).1,
        wkpBaseCoordinateCLM (U j t).2) = e t)
    (hs : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (U j) (Ioi 0))
    {q : C(ℝ × ℝ^n, ℝ)}
    (hq : ∀ t, 0 ≤ t → (fun y ↦ q (t, y)) =ᵐ[volume] baseRepresentative (e t).1) :
    ContDiffOn ℝ (⊤ : ℕ∞) q (Ioi 0 ×ˢ univ) := by
  have hn' : (n : ℝ) < 4 := by exact_mod_cast hn
  have h0 : (n : ℝ) < 2 * ((4 : ℝ) - 1) := by linarith
  refine (contDiffOn_joint_of_higher_lifts U hU hs h0).congr fun p hp ↦ ?_
  have he := hq p.1 hp.1.le
  rw [← hU 0 p.1 hp.1.le] at he
  exact congrFun (eq_classicalRepresentativeCLM_of_ae_eq h0 (U 0 p.1).1
    (q.continuous.comp (continuous_const.prodMk continuous_id)) he) p.2

/-- Smooth compact data give compatible continuous higher lifts at all
integer orders on the whole forward half-line in dimensions below four. -/
theorem exists_global_higher_lifts_of_smoothCompact
    (hn : n < 4) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ e : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      IsEnergySolution hf hf0
        (mkWkpSpaceOnOfContDiff g hg hgc,
          wkpBaseCoordinateCLM (mkWkpSpaceOnOfContDiff (k := 3) h hh hhc)) e ∧
      ∃ U : ∀ j : ℕ, C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)),
        (∀ j, U j 0 = (mkWkpSpaceOnOfContDiff g hg hgc,
          mkWkpSpaceOnOfContDiff h hh hhc)) ∧
        ∀ j t, 0 ≤ t →
          (lowerOrderCLM (by omega : 1 ≤ j + 4) (U j t).1,
            wkpBaseCoordinateCLM (U j t).2) = e t := by
  let G (j : ℕ) : W^{j,2}(ℝ^n) := mkWkpSpaceOnOfContDiff g hg hgc
  let H (j : ℕ) : W^{j,2}(ℝ^n) := mkWkpSpaceOnOfContDiff h hh hhc
  obtain ⟨e, he⟩ := exists_energySolution hf hf0 (G 1, wkpBaseCoordinateCLM (H 3))
  have heq (j : ℕ) :
      (lowerOrderCLM (by omega : 1 ≤ j + 4) (G (j + 4)),
        wkpBaseCoordinateCLM (H (j + 3))) = (G 1, wkpBaseCoordinateCLM (H 3)) := by
    apply Prod.ext
    · exact lowerOrderCLM_mkWkpSpaceOnOfContDiff (by omega) g hg hgc
    · have hh' := lowerOrderCLM_mkWkpSpaceOnOfContDiff
        (n := n) (k := 3) (m := j + 3) (p := 2) (Ω := univ)
        (by omega : 3 ≤ j + 3) h hh hhc
      exact congrArg wkpBaseCoordinateCLM hh'
  have hex (j : ℕ) : ∃ U : C(ℝ, W^{j + 4,2}(ℝ^n) × W^{j + 3,2}(ℝ^n)),
      U 0 = (G (j + 4), H (j + 3)) ∧ ∀ t, 0 ≤ t →
        (lowerOrderCLM (by omega : 1 ≤ j + 4) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = e t := by
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hn' : (n : ℝ) < 4 := by exact_mod_cast hn
    have hk : (n : ℝ) < 2 * (((j + 3 : ℕ) : ℝ) - 1) := by push_cast; linarith
    apply IsEnergySolution.exists_global_higherOrder_smoothReaction hn hk hs hf hf0
      (G (j + 4), H (j + 3))
    rw [heq j]
    exact he
  choose U hzero hU using hex
  exact ⟨e, he, U, hzero, hU⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy
