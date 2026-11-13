/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Star.RadialSections
public import PDE.Elliptic.Classical.Harmonic.LevelSets.Comparison
public import PDE.Elliptic.Classical.Harmonic.Derivatives
public import PDE.Elliptic.Classical.Harmonic.StrongMaximumPrinciple

/-!
# Strict radial decrease on bounded star-convex annuli

Dilation comparison gives radial nonincrease, and the strong maximum principle
makes it strict. The argument is applied to the connected component of the chosen point.
A finite radial interval then connects the inner and outer data in that same
component. No connectedness assumption on the whole annulus is needed.
-/

@[expose] public section

open Set

namespace LaplacianEquation

/-- On a bounded annulus between star-convex sets, the radial derivative
of a harmonic function with distinct constant boundary values is strictly negative.
The radial derivative is harmonic by interior regularity and the Laplacian identity. -/
theorem IsHarmonicPDE.fderiv_self_neg
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {K W : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u (W \ K))
    (hK : StarConvex ℝ 0 K) (hW : StarConvex ℝ 0 W)
    (hKclosed : IsClosed K) (hWopen : IsOpen W)
    (hWbdd : Bornology.IsBounded W) (hKW : K ⊆ W) (hKne : K.Nonempty)
    (hcont : ContinuousOn u (closure (W \ K)))
    (hinner : ∀ y ∈ frontier K, u y = 1)
    (houter : ∀ y ∈ frontier W, u y = 0)
    {x : ℝ^n} (hx : x ∈ W \ K) :
    fderiv ℝ u x x < 0 := by
  have hUopen : IsOpen (W \ K) := hWopen.sdiff hKclosed
  have hnonpos (y : ℝ^n) (hy : y ∈ W \ K) : fderiv ℝ u y y ≤ 0 :=
    hu.fderiv_self_nonpos hK hW hKclosed hWopen hWbdd hcont hinner houter hy
  by_contra hneg
  have hxzero : fderiv ℝ u x x = 0 :=
    le_antisymm (hnonpos x hx) (le_of_not_gt hneg)
  have hCsub := connectedComponentIn_subset (W \ K) x
  have hself := (hu.fderiv_self hUopen).mono hCsub
  have hconstant := hself.eqOn_const_of_isPreconnected_of_forall_le hUopen.connectedComponentIn
      isPreconnected_connectedComponentIn (mem_connectedComponentIn hx)
      (fun y hy ↦ by simpa only [hxzero] using hnonpos y (hCsub hy))
  obtain ⟨a, b, ha0, ha1, hb1, haK, hbW, hinterval⟩ :=
    hK.exists_radial_frontier_interval hW hKclosed hWopen hWbdd hKW hKne hx
  have hab : a < b := ha1.trans hb1
  have hray : Continuous (fun t : ℝ ↦ t • x) := continuous_id.smul continuous_const
  have hcomponent : (fun t : ℝ ↦ t • x) '' Ioo a b ⊆
      connectedComponentIn (W \ K) x :=
    (isPreconnected_Ioo.image _ hray.continuousOn).subset_connectedComponentIn
      ⟨1, ⟨ha1, hb1⟩, one_smul ℝ x⟩ (by
        rintro _ ⟨t, ht, rfl⟩
        exact hinterval t ht)
  have hderiv (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s : ℝ ↦ u (s • x)) 0 t := by
    have hd := (hu.contDiffAt_of_isOpen hUopen (hinterval t ht)).differentiableAt (by norm_num)
    have hz : fderiv ℝ u (t • x) (t • x) = 0 := by
      simpa only [hxzero] using hconstant (hcomponent ⟨t, ht, rfl⟩)
    have ht0 : t ≠ 0 := (lt_of_le_of_lt ha0 ht.1).ne'
    have hz' : fderiv ℝ u (t • x) x = 0 := by
      rw [map_smul, smul_eq_mul] at hz
      exact (mul_eq_zero.mp hz).resolve_left ht0
    simpa only [Function.comp_def, id_eq, one_smul, hz'] using
      hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
  have heq : EqOn (fun t : ℝ ↦ u (t • x)) (fun _ ↦ u x) (Ioo a b) := by
    intro t ht
    simpa only [one_smul] using isOpen_Ioo.is_const_of_deriv_eq_zero
      isPreconnected_Ioo (fun s hs ↦ (hderiv s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hderiv s hs).deriv) ht ⟨ha1, hb1⟩
  have hmap : MapsTo (fun t : ℝ ↦ t • x) (closure (Ioo a b)) (closure (W \ K)) :=
    fun _ ht ↦ map_mem_closure (f := fun t : ℝ ↦ t • x) hray ht hinterval
  have heqclosed := heq.of_subset_closure (hcont.comp hray.continuousOn hmap)
    continuousOn_const subset_closure Subset.rfl
  have hleft : u (a • x) = u x :=
    heqclosed (by rw [closure_Ioo hab.ne]; exact left_mem_Icc.mpr hab.le)
  have hright : u (b • x) = u x :=
    heqclosed (by rw [closure_Ioo hab.ne]; exact right_mem_Icc.mpr hab.le)
  rw [hinner _ haK] at hleft
  rw [houter _ hbW] at hright
  exact one_ne_zero (hleft.trans hright.symm)

end LaplacianEquation
