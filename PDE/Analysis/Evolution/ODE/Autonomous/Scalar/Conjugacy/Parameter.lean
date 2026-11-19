/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.Conjugacy
public import PDE.Analysis.Integration.Primitive.MovingEndpoint

/-!
# Joint smoothness of the scalar integral conjugacy

Near a positive linear coefficient, one state interval works for a whole open
coefficient window. A uniform positive denominator margin gives joint smoothness
of the integral coordinate, including both signs of the state variable.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace PDE.Analysis.Evolution.Scalar

/-- A common state interval gives a uniform denominator margin and joint smoothness
of the conjugacy as the positive linear coefficient varies near `c0`. The state
interval is closed, so the same radius controls every segment from zero. -/
theorem exists_pos_contDiffOn_scalarConjugacy_joint
    {c0 : ℝ} {b : ℝ → ℝ} (hc0 : 0 < c0) (hb : ContDiff ℝ ∞ b) :
    ∃ r : ℝ, 0 < r ∧
      (∀ c ∈ Ioo (c0 / 2) (3 * c0 / 2), ∀ s ∈ Icc (-r) r,
        c0 / 4 < c + s * b s) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ scalarConjugacy p.1 b p.2)
        (Ioo (c0 / 2) (3 * c0 / 2) ×ˢ Icc (-r) r) := by
  let C : Set ℝ := Ioo (c0 / 2) (3 * c0 / 2)
  have hcquarter : (0 : ℝ) < c0 / 4 := by linarith only [hc0]
  have hmul : ContinuousAt (fun s : ℝ ↦ s * b s) 0 :=
    continuousAt_id.mul hb.continuous.continuousAt
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0, |s * b s| < c0 / 4 :=
    hmul.abs.tendsto.eventually (gt_mem_nhds (by simpa using hcquarter))
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.eventually_nhds_iff.mp hsmall
  -- Halving the neighborhood radius preserves the strict margin at both endpoints.
  let r : ℝ := δ / 2
  have hr : 0 < r := by dsimp only [r]; linarith only [hδ]
  have hrδ : r < δ := by dsimp only [r]; linarith only [hδ]
  have hab : -r ≤ r := by linarith only [hr]
  have hsmall_closed (s : ℝ) (hs : s ∈ Icc (-r) r) : |s * b s| < c0 / 4 := by
    have hsδ : |s| < δ := (abs_le.mpr hs).trans_lt hrδ
    exact hδsmall (by simpa only [dist_zero_right, Real.norm_eq_abs] using hsδ)
  have hmargin (c : ℝ) (hc : c ∈ C) (s : ℝ) (hs : s ∈ Icc (-r) r) :
      c0 / 4 < c + s * b s := by
    have hlower := (abs_lt.mp (hsmall_closed s hs)).1
    linarith only [hc.1, hlower]
  have hbprod : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ b p.2)
      (C ×ˢ uIcc (-r) r) :=
    (hb.comp contDiff_snd).contDiffOn
  have hquotient : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ ↦ b p.2 / (p.1 + p.2 * b p.2)) (C ×ˢ uIcc (-r) r) :=
    hbprod.div (contDiffOn_fst.add (contDiffOn_snd.mul hbprod)) (fun p hp ↦ by
      have hs : p.2 ∈ Icc (-r) r := by
        simpa only [uIcc_of_le hab] using hp.2
      exact ne_of_gt (hcquarter.trans (hmargin p.1 hp.1 p.2 hs)))
  have hzero : (0 : ℝ) ∈ uIcc (-r) r := by
    rw [uIcc_of_le hab]
    exact ⟨neg_nonpos.mpr hr.le, hr.le⟩
  have hprimitive : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..p.2, b s / (p.1 + s * b s))
      (C ×ˢ uIcc (-r) r) :=
    PDE.Analysis.contDiffOn_intervalIntegral_moving_upper
      (n := (⊤ : ℕ∞)) (a := -r) (b := r) (c := 0)
      (show IsOpen C from isOpen_Ioo) hquotient hzero
  have hjoint : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ ↦ scalarConjugacy p.1 b p.2)
      (C ×ˢ Icc (-r) r) := by
    simpa only [scalarConjugacy, uIcc_of_le hab] using
      (contDiffOn_snd.mul hprimitive.neg.exp)
  exact ⟨r, hr, hmargin, hjoint⟩

end PDE.Analysis.Evolution.Scalar
