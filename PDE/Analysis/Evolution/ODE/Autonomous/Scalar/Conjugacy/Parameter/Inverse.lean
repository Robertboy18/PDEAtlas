/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Conjugacy.Parameter
import Mathlib.Analysis.Calculus.Deriv.Prod
import PDE.Analysis.Calculus.ImplicitFunction.RegularLevel

/-!
# A joint inverse for the scalar integral conjugacy

The equation `scalarConjugacy c b s = y` has state derivative one at `(c0, 0, 0)`.
A regular level graph gives one jointly smooth inverse for nearby coefficients
and target values. A uniform denominator margin makes every scalar slice
strictly increasing, so the graph fixes zero and also inverts the conjugacy on
a common interval of signed states.
-/

@[expose] public section

open Filter Metric Set
open scoped ContDiff Topology

namespace PDE.Analysis.Evolution.Scalar

/-- Near a positive coefficient, the integral conjugacy has a jointly smooth
inverse on one product neighborhood. The coefficient window, target radius,
source interval, and smaller interval for the second inverse identity are chosen
before all coefficients and signed states. The source interval retains a uniform
positive denominator margin. -/
theorem exists_contDiffOn_scalarConjugacy_joint_inverse
    {c0 : ℝ} {b : ℝ → ℝ} (hc0 : 0 < c0) (hb : ContDiff ℝ ∞ b) :
    ∃ K : ℝ × ℝ → ℝ, ∃ r ε η δ : ℝ,
      0 < r ∧ 0 < ε ∧ 0 < η ∧ 0 < δ ∧ δ ≤ r ∧
      ball c0 ε ⊆ Ioo (c0 / 2) (3 * c0 / 2) ∧
      (∀ c ∈ ball c0 ε, ∀ s ∈ Icc (-r) r, c0 / 4 < c + s * b s) ∧
      ContDiffOn ℝ ∞ K (ball c0 ε ×ˢ ball 0 η) ∧
      (∀ c ∈ ball c0 ε, K (c, 0) = 0) ∧
      (∀ c ∈ ball c0 ε, ∀ y ∈ ball 0 η,
        K (c, y) ∈ Ioo (-r) r ∧ scalarConjugacy c b (K (c, y)) = y) ∧
      ∀ c ∈ ball c0 ε, ∀ s ∈ ball 0 δ,
        scalarConjugacy c b s ∈ ball 0 η ∧ K (c, scalarConjugacy c b s) = s := by
  obtain ⟨r, hr, hmargin, hclosed⟩ := exists_pos_contDiffOn_scalarConjugacy_joint hc0 hb
  let C : Set ℝ := Ioo (c0 / 2) (3 * c0 / 2)
  let I : Set ℝ := Ioo (-r) r
  have hC0 : c0 ∈ C := ⟨by linarith, by linarith⟩
  have hzero : (0 : ℝ) ∈ I := ⟨neg_lt_zero.mpr hr, hr⟩
  have hden (c : ℝ) (hc : c ∈ C) : ∀ s ∈ I, 0 < c + s * b s := fun s hs ↦
    (by linarith : (0 : ℝ) < c0 / 4).trans (hmargin c hc s ⟨hs.1.le, hs.2.le⟩)
  have hopen : IsOpen (C ×ˢ I) := isOpen_Ioo.prod isOpen_Ioo
  have hjoint : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ scalarConjugacy p.1 b p.2) (C ×ˢ I) :=
    hclosed.mono fun p hp ↦ ⟨hp.1, hp.2.1.le, hp.2.2.le⟩
  let G : (ℝ × ℝ) × ℝ → ℝ := fun p ↦ scalarConjugacy p.1.1 b p.2 - p.1.2
  let U : Set ((ℝ × ℝ) × ℝ) := (C ×ˢ univ) ×ˢ I
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_univ).prod isOpen_Ioo
  have hx : ((c0, (0 : ℝ)), (0 : ℝ)) ∈ U := ⟨⟨hC0, mem_univ _⟩, hzero⟩
  have hG : ContDiffOn ℝ ∞ G U :=
    (hjoint.comp (contDiff_fst.fst.prodMk contDiff_snd).contDiffOn
      (fun _ hp ↦ ⟨hp.1.1, hp.2⟩)).sub contDiffOn_fst.snd
  have hslice : HasDerivAt (fun s : ℝ ↦ G ((c0, 0), s))
      (fderiv ℝ G ((c0, 0), 0) (0, 1)) 0 := by
    simpa only [Function.comp_def, id_eq] using
      ((hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
        ((hasDerivAt_const 0 (c0, (0 : ℝ))).prodMk (hasDerivAt_id 0))
  have hsliceOne : HasDerivAt (fun s : ℝ ↦ G ((c0, 0), s)) 1 0 := by
    simpa only [G, sub_zero] using
      hasDerivAt_scalarConjugacy_zero hr hb.continuous.continuousOn (hden c0 hC0)
  obtain ⟨K, S, hSopen, hS0, hK, _, hgraph, _⟩ :=
    hG.exists_implicitFunction_of_fderiv_snd_ne_zero (m := ⊤) hU (by simp) hx
      (by rw [hslice.unique hsliceOne]; exact one_ne_zero)
  have hgraphBounds (c y : ℝ) (hq : (c, y) ∈ S) :
      c ∈ C ∧ K (c, y) ∈ I ∧ scalarConjugacy c b (K (c, y)) = y := by
    obtain ⟨hqU, heq⟩ := hgraph (c, y) hq
    exact ⟨hqU.1.1, hqU.2,
      sub_eq_zero.mp (by simpa only [G, scalarConjugacy_zero, sub_zero] using heq)⟩
  obtain ⟨η, hη, hηgraph⟩ := Metric.mem_nhds_iff.mp (hSopen.mem_nhds hS0)
  have hsmall : (fun p : ℝ × ℝ ↦ scalarConjugacy p.1 b p.2) ⁻¹' ball (0 : ℝ) η ∈ 𝓝 (c0, 0) :=
    (hjoint.contDiffAt (hopen.mem_nhds ⟨hC0, hzero⟩)).continuousAt.preimage_mem_nhds
      (by simpa only [scalarConjugacy_zero] using ball_mem_nhds (0 : ℝ) hη)
  obtain ⟨β, hβ, hβmap⟩ :=
    Metric.mem_nhds_iff.mp (inter_mem (hopen.mem_nhds ⟨hC0, hzero⟩) hsmall)
  have hrectangle : ball c0 (min η β) ×ˢ ball (0 : ℝ) η ⊆ S := fun p hp ↦ hηgraph <| by
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_left η β) hp.1, hp.2⟩
  have hcoeff : ball c0 (min η β) ⊆ C := fun c hc ↦
    (hgraphBounds c 0 (hrectangle ⟨hc, mem_ball_self hη⟩)).1
  have hright (c : ℝ) (hc : c ∈ ball c0 (min η β)) (y : ℝ) (hy : y ∈ ball 0 η) :
      K (c, y) ∈ I ∧ scalarConjugacy c b (K (c, y)) = y :=
    (hgraphBounds c y (hrectangle ⟨hc, hy⟩)).2
  have hinj (c : ℝ) (hc : c ∈ C) :=
    (strictMonoOn_scalarConjugacy hb.continuous.continuousOn (hden c hc)).injOn
  refine ⟨K, r, min η β, η, min r β, hr, lt_min hη hβ, hη, lt_min hr hβ, min_le_left r β,
    hcoeff, fun c hc s hs ↦ hmargin c (hcoeff hc) s hs, hK.mono hrectangle,
    fun c hc ↦ ?_, hright, fun c hc s hs ↦ ?_⟩
  · have hroot := hright c hc 0 (mem_ball_self hη)
    exact hinj c (hcoeff hc) hroot.1 hzero (by simpa only [scalarConjugacy_zero] using hroot.2)
  · have hcs : (c, s) ∈ ball (c0, (0 : ℝ)) β := by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball (min_le_right η β) hc, ball_subset_ball (min_le_right r β) hs⟩
    obtain ⟨⟨hcC, hsI⟩, hsmall⟩ := hβmap hcs
    have hroot := hright c hc _ hsmall
    exact ⟨hsmall, hinj c hcC hroot.1 hsI hroot.2⟩

end PDE.Analysis.Evolution.Scalar
