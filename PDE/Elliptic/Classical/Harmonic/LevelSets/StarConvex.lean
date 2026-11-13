/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.LevelSets.Radial
public import PDE.Analysis.Convex.Star.Superlevel
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.RegularLevel

/-!
# Smooth star-convex harmonic superlevel sets on bounded domains

This is the bounded, positive-dimensional version of the harmonic level-set
argument for star-shaped sets. Boundedness of the outer open set is an explicit
hypothesis. Star-convexity is required of the inner closure and of the outer open
set. No regularity of their boundaries or connectedness of the annulus is assumed.

The starting data are the harmonic equation, continuity on the closure of
the annulus, and the values one and zero on its inner and outer frontiers. Dilation
comparison and a componentwise finite-exit argument give strict radial decrease.
Interior harmonic regularity and the implicit-function theorem then give smooth
graph boundary with its local side on one neighborhood.

The inner set may be empty, and the origin may lie on its frontier. Only its closure
enters the construction; the result therefore also permits inner sets that are not open.
-/

@[expose] public section

open Set PDE.Analysis
open scoped ContDiff

namespace LaplacianEquation

/-- Intermediate filled superlevel sets of a harmonic potential are bounded, open
and star-convex, with smooth regular level boundary. All regularity and local graph
data follow from the harmonic equation and the stated boundary values. -/
theorem IsHarmonicPDE.filledSuperlevel_geometry
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {V W : Set (ℝ^n)} {c : ℝ}
    (hu : IsHarmonicPDE n u (W \ closure V))
    (hV : StarConvex ℝ 0 (closure V)) (hW : StarConvex ℝ 0 W)
    (hWopen : IsOpen W) (hWbdd : Bornology.IsBounded W) (hVW : closure V ⊆ W)
    (hcont : ContinuousOn u (closure (W \ closure V)))
    (hinner : ∀ x ∈ frontier V, u x = 1)
    (houter : ∀ x ∈ frontier W, u x = 0) (hc0 : 0 < c) (hc1 : c < 1) :
    IsOpen (filledSuperlevel (closure V) W u c) ∧
      Bornology.IsBounded (filledSuperlevel (closure V) W u c) ∧
      StarConvex ℝ 0 (filledSuperlevel (closure V) W u c) ∧
      frontier (filledSuperlevel (closure V) W u c) =
        {x | x ∈ W \ closure V ∧ u x = c} ∧
      SobolevSpace.Boundary.HasContDiffGraphBoundary ⊤ (filledSuperlevel (closure V) W u c) ∧
      ∀ x ∈ W \ closure V, u x = c → fderiv ℝ u x ≠ 0 := by
  have hinner' (x : ℝ^n) (hx : x ∈ frontier (closure V)) : u x = 1 :=
    hinner x (frontier_closure_subset hx)
  have hUopen : IsOpen (W \ closure V) := hWopen.sdiff isClosed_closure
  have hzero (hVempty : V = ∅) (x : ℝ^n) (hx : x ∈ closure W) : u x = 0 := by
    have huW : IsHarmonicPDE n u W := by simpa only [hVempty, closure_empty, sdiff_empty] using hu
    have hcW : ContinuousOn u (closure W) := by
      simpa only [hVempty, closure_empty, sdiff_empty] using hcont
    apply le_antisymm
    · exact huW.le_on_closure_of_boundary_le hWopen hWbdd hcW
        (fun y hy ↦ (houter y hy).le) x hx
    · have hle := huW.neg.le_on_closure_of_boundary_le hWopen hWbdd hcW.neg
        (M := 0) (fun y hy ↦ by simp only [Pi.neg_apply, houter y hy, neg_zero, le_refl]) x hx
      exact neg_nonpos.mp hle
  have hregular (x : ℝ^n) (hx : x ∈ W \ closure V) (hlevel : u x = c) :
      fderiv ℝ u x ≠ 0 := by
    rcases V.eq_empty_or_nonempty with hVempty | hVne
    · exact False.elim (hc0.ne' (hlevel.symm.trans (hzero hVempty x (subset_closure hx.1))))
    · have hneg := hu.fderiv_self_neg hV hW isClosed_closure hWopen hWbdd hVW
        hVne.closure hcont hinner' houter hx
      intro hz
      rw [hz, zero_apply] at hneg
      exact (lt_irrefl 0) hneg
  have hstar : StarConvex ℝ 0 (filledSuperlevel (closure V) W u c) := by
    rcases V.eq_empty_or_nonempty with hVempty | hVne
    · have hempty : filledSuperlevel (closure V) W u c = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        rcases hx with hx | ⟨hx, hcx⟩
        · simp only [hVempty, closure_empty, mem_empty_iff_false] at hx
        · rw [hzero hVempty x (subset_closure hx.1)] at hcx
          exact hc0.not_gt hcx
      rw [hempty]
      exact starConvex_empty 0
    · exact hV.filledSuperlevel hW hVne.closure
        (fun ha _ hx hax ↦ hu.le_of_one_lt_dilation hV hW isClosed_closure hWopen hWbdd
          hcont hinner' houter ha hx hax)
  have hfront := frontier_filledSuperlevel isClosed_closure hWopen hVW hcont
    hinner' houter hc0 hc1 hregular
  refine ⟨isOpen_filledSuperlevel isClosed_closure hWopen hVW hcont hinner' hc1,
    hWbdd.subset (fun x hx ↦ hx.elim (fun h ↦ hVW h) (fun h ↦ h.1.1)),
    hstar, hfront, ?_, hregular⟩
  apply SobolevSpace.Boundary.hasContDiffGraphBoundary_of_regular_level
    (hu.contDiffOn_of_isOpen hUopen) hUopen (by simp)
  · intro x hx
    exact hfront ▸ hx
  · intro x hx
    obtain ⟨hxU, hlevel⟩ := hfront ▸ hx
    exact hregular x hxU hlevel
  · intro x hx
    simp only [filledSuperlevel, mem_union, mem_ofPred_eq, hx.2, false_or, hx, true_and]

end LaplacianEquation
