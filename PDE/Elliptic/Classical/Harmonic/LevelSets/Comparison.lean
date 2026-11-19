/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Dilation
public import PDE.Elliptic.Classical.Harmonic.WeakMaximumPrinciple.BoundedDomain
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Dilation comparison on star-convex annuli

For a dilation factor greater than one, comparison takes place where both the point
and its dilate lie in the original annulus. Continuity maps the closure of this
comparison domain into the closure of the annulus. Thus the argument only evaluates
the given boundary data and does not extend the function across either boundary.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace LaplacianEquation

/-- Constant inner and outer boundary values bound a harmonic function throughout
the closure of a bounded annulus. No connectedness or boundary regularity is needed. -/
theorem IsHarmonicPDE.mem_Icc_of_annulus_boundary
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {K W : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u (W \ K)) (hKclosed : IsClosed K) (hWopen : IsOpen W)
    (hWbdd : Bornology.IsBounded W) (hcont : ContinuousOn u (closure (W \ K)))
    (hinner : ∀ y ∈ frontier K, u y = 1) (houter : ∀ y ∈ frontier W, u y = 0)
    {x : ℝ^n} (hx : x ∈ closure (W \ K)) :
    u x ∈ Icc (0 : ℝ) 1 := by
  have hboundary (y : ℝ^n) (hy : y ∈ frontier (W \ K)) : u y ∈ Icc (0 : ℝ) 1 := by
    rcases frontier_inter_subset W Kᶜ hy with hy | hy
    · simp only [houter y hy.1, mem_Icc, le_refl, zero_le_one, and_self]
    · have hyK : y ∈ frontier K := by simpa only [frontier_compl] using hy.2
      simp only [hinner y hyK, mem_Icc, zero_le_one, le_refl, and_self]
  have hUopen := hWopen.sdiff hKclosed
  have hUbdd := hWbdd.subset (sdiff_subset : W \ K ⊆ W)
  have hupper := hu.le_on_closure_of_boundary_le hUopen hUbdd hcont
    (fun y hy ↦ (hboundary y hy).2) x hx
  have hlower := hu.neg.le_on_closure_of_boundary_le hUopen hUbdd hcont.neg
    (M := 0) (fun y hy ↦ by simpa only [Pi.neg_apply, neg_nonpos] using
      (hboundary y hy).1) x hx
  exact ⟨by simpa only [Pi.neg_apply, neg_nonpos] using hlower, hupper⟩

/-- Expanding a point radially decreases the harmonic potential between star-convex
inner and outer sets, as long as the expanded point stays in the outer set. -/
theorem IsHarmonicPDE.le_of_one_lt_dilation
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {K W : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u (W \ K))
    (hK : StarConvex ℝ 0 K) (hW : StarConvex ℝ 0 W)
    (hKclosed : IsClosed K) (hWopen : IsOpen W) (hWbdd : Bornology.IsBounded W)
    (hcont : ContinuousOn u (closure (W \ K)))
    (hinner : ∀ y ∈ frontier K, u y = 1) (houter : ∀ y ∈ frontier W, u y = 0)
    {c : ℝ} (hc : 1 < c) {x : ℝ^n} (hxK : x ∉ K) (hcxW : c • x ∈ W) :
    u (c • x) ≤ u x := by
  let D := ((fun y : ℝ^n ↦ c • y) ⁻¹' W) \ K
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hcinv0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hcpos.le
  have hcinv1 : c⁻¹ ≤ 1 := (inv_le_one₀ hcpos).mpr hc.le
  have hDU : D ⊆ W \ K := by
    intro y hy
    refine ⟨?_, hy.2⟩
    simpa only [inv_smul_smul₀ hcpos.ne'] using hW.smul_mem hy.1 hcinv0 hcinv1
  have hmap : MapsTo (fun y : ℝ^n ↦ c • y) D (W \ K) := by
    intro y hy
    refine ⟨hy.1, fun hyK ↦ hy.2 ?_⟩
    simpa only [inv_smul_smul₀ hcpos.ne'] using hK.smul_mem hyK hcinv0 hcinv1
  have hmapclosed : MapsTo (fun y : ℝ^n ↦ c • y) (closure D) (closure (W \ K)) :=
    fun _ hy ↦ map_mem_closure (f := fun y : ℝ^n ↦ c • y)
      (continuous_const_smul c) hy hmap
  have hDopen : IsOpen D := (hWopen.preimage (continuous_const_smul c)).sdiff hKclosed
  have hDbdd : Bornology.IsBounded D := hWbdd.subset (hDU.trans sdiff_subset)
  have hdil := (hu.comp_const_smul c).mono hmap
  have hdiff := hdil.sub (hu.mono hDU) hDopen
  have hdiffcont : ContinuousOn ((fun y ↦ u (c • y)) - u) (closure D) :=
    (hcont.comp (continuous_const_smul c).continuousOn hmapclosed).sub
      (hcont.mono (closure_mono hDU))
  have hboundary (y : ℝ^n) (hy : y ∈ frontier D) :
      ((fun z ↦ u (c • z)) - u) y ≤ 0 := by
    have hyclosed := frontier_subset_closure hy
    have hybounds := hu.mem_Icc_of_annulus_boundary hKclosed hWopen hWbdd
      hcont hinner houter (closure_mono hDU hyclosed)
    have hcybounds := hu.mem_Icc_of_annulus_boundary hKclosed hWopen hWbdd
      hcont hinner houter (hmapclosed hyclosed)
    change u (c • y) - u y ≤ 0
    rcases frontier_inter_subset ((fun y : ℝ^n ↦ c • y) ⁻¹' W) Kᶜ hy with hy | hy
    · have hcy : c • y ∈ frontier W := by
        change y ∈ (fun y : ℝ^n ↦ c • y) ⁻¹' frontier W
        rw [(isOpenMap_smul₀ hcpos.ne').preimage_frontier_eq_frontier_preimage
          (continuous_const_smul c)]
        exact hy.1
      rw [houter _ hcy, zero_sub]
      exact neg_nonpos.mpr hybounds.1
    · have hyK : y ∈ frontier K := by simpa only [frontier_compl] using hy.2
      rw [hinner _ hyK]
      exact sub_nonpos.mpr hcybounds.2
  have hle := hdiff.le_on_closure_of_boundary_le hDopen hDbdd hdiffcont hboundary
    x (subset_closure ⟨hcxW, hxK⟩)
  exact sub_nonpos.mp hle

/-- The radial derivative is nonpositive, derived from dilation comparison and the
right derivative at dilation factor one. -/
theorem IsHarmonicPDE.fderiv_self_nonpos
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {K W : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u (W \ K))
    (hK : StarConvex ℝ 0 K) (hW : StarConvex ℝ 0 W)
    (hKclosed : IsClosed K) (hWopen : IsOpen W) (hWbdd : Bornology.IsBounded W)
    (hcont : ContinuousOn u (closure (W \ K)))
    (hinner : ∀ y ∈ frontier K, u y = 1) (houter : ∀ y ∈ frontier W, u y = 0)
    {x : ℝ^n} (hx : x ∈ W \ K) :
    fderiv ℝ u x x ≤ 0 := by
  have hd := (hu.contDiffAt_of_isOpen (hWopen.sdiff hKclosed) hx).differentiableAt
    (by norm_num)
  have hderiv : HasDerivAt (fun t : ℝ ↦ u (t • x)) (fderiv ℝ u x x) 1 := by
    have hd' : HasFDerivAt u (fderiv ℝ u x) ((1 : ℝ) • x) := by
      simpa only [one_smul] using hd.hasFDerivAt
    simpa only [Function.comp_def, id_eq, one_smul] using
      hd'.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have hray : Continuous (fun c : ℝ ↦ c • x) := continuous_id.smul continuous_const
  have hnear : ∀ᶠ c : ℝ in 𝓝 1, c • x ∈ W :=
    hray.continuousAt
      (by simpa only [one_smul] using hWopen.mem_nhds hx.1)
  apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hderiv).2
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with c hcW hc
  rw [slope_def_field, one_smul]
  exact div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (hu.le_of_one_lt_dilation hK hW hKclosed hWopen hWbdd
      hcont hinner houter hc hx.2 hcW)) (sub_nonneg.mpr hc.le)

end LaplacianEquation
