/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Laplacian
public import PDE.Elliptic.Classical.Harmonic.Smoothness

/-!
# Derivatives of harmonic functions

Every fixed directional derivative and every fixed evaluation of an iterated Fréchet
derivative of a classical harmonic function is harmonic on its open domain.

The original harmonicity hypothesis provides `C²` regularity. Interior smoothness follows
from the local Poisson representation, and commutation of the Laplacian with directional
differentiation proves derivative closure. Thus neither smoothness nor harmonicity of any
derivative is an extra hypothesis. These are the closure statements underlying the
interior derivative estimates in Evans, *Partial Differential Equations*, §2.2.3.
The radial derivative is also harmonic: its Laplacian differs from the radial
derivative of the Laplacian by twice the original Laplacian.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, step 1 of the proof of Theorem 7 (the derivatives
  `u_{x_i}` are harmonic), p. 29.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Topology
open scoped Laplacian

noncomputable section

namespace LaplacianEquation

/-- Every fixed directional derivative of a classical harmonic function is harmonic
on its open domain. Interior smoothness is derived from harmonicity. -/
theorem IsHarmonicPDE.fderiv_apply
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U)
    (v : ℝ^n) :
    IsHarmonicPDE n (fun y ↦ fderiv ℝ u y v) U := by
  have hsmooth : ContDiffOn ℝ 3 u U := hu.contDiffOn_of_isOpen hU
  have hreg : ContDiffOn ℝ 2 (fun y ↦ fderiv ℝ u y v) U :=
    (hsmooth.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  refine ⟨hreg, ?_⟩
  intro x hx
  have hu3 : ContDiffAt ℝ 3 u x :=
    (hsmooth x hx).contDiffAt (hU.mem_nhds hx)
  rw [((hreg x hx).contDiffAt (hU.mem_nhds hx)).coordinate_laplacian_eq_laplacian,
    hu3.laplacian_fderiv_apply]
  have hzero : Δ u =ᶠ[𝓝 x] (fun _ : ℝ^n ↦ (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [← (hu.contDiffAt_of_isOpen hU hy).coordinate_laplacian_eq_laplacian,
      hu.laplacian_eq_zero hy]
  rw [hzero.fderiv_eq]
  simp

/-- The radial derivative of a classical harmonic function is harmonic on its
open domain. Its smoothness and the commutator identity follow from the original
`C²` harmonicity hypothesis. -/
theorem IsHarmonicPDE.fderiv_self
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U) :
    IsHarmonicPDE n (fun y ↦ fderiv ℝ u y y) U := by
  have hsmooth : ContDiffOn ℝ 3 u U := hu.contDiffOn_of_isOpen hU
  have hid : ContDiffOn ℝ 2 (fun y : ℝ^n ↦ y) U := contDiffOn_id
  have hreg : ContDiffOn ℝ 2 (fun y ↦ fderiv ℝ u y y) U :=
    (hsmooth.fderiv_of_isOpen hU (by norm_num)).clm_apply hid
  refine ⟨hreg, ?_⟩
  intro x hx
  have hu3 : ContDiffAt ℝ 3 u x := (hsmooth x hx).contDiffAt (hU.mem_nhds hx)
  have hzero : Δ u =ᶠ[𝓝 x] (fun _ : ℝ^n ↦ (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [← (hu.contDiffAt_of_isOpen hU hy).coordinate_laplacian_eq_laplacian,
      hu.laplacian_eq_zero hy]
  rw [((hreg x hx).contDiffAt (hU.mem_nhds hx)).coordinate_laplacian_eq_laplacian,
    hu3.laplacian_fderiv_self, hzero.fderiv_eq, hzero.eq_of_nhds]
  simp

/-- Every fixed evaluation of every iterated Fréchet derivative of a classical harmonic
function is harmonic on its open domain. The directions are arbitrary vectors, and
interior smoothness is derived from the original harmonicity hypothesis. -/
theorem IsHarmonicPDE.iteratedFDeriv_apply
    {n : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U)
    (k : ℕ) (v : Fin k → ℝ^n) :
    IsHarmonicPDE n (fun y ↦ iteratedFDeriv ℝ k u y v) U := by
  have hsmooth : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) u U :=
    hu.contDiffOn_of_isOpen (m := ⊤) hU
  have hreg (j : ℕ) (w : Fin j → ℝ^n) :
      ContDiffOn ℝ 3 (fun y ↦ iteratedFDeriv ℝ j u y w) U := by
    intro x hx
    have hiter : ContDiffAt ℝ 3 (iteratedFDeriv ℝ j u) x :=
      ((hsmooth x hx).contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl (3 + j))
    exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ ℝ^n) ℝ w).contDiff.contDiffAt.comp
      x hiter).contDiffWithinAt
  induction k with
  | zero =>
      simpa only [iteratedFDeriv_zero_apply] using hu
  | succ k ih =>
      have hdir :=
        (ih (Fin.tail v)).fderiv_apply hU (v 0)
      have hreg2 : ContDiffOn ℝ 2 (fun y ↦ iteratedFDeriv ℝ (k + 1) u y v) U :=
        (hreg (k + 1) v).of_le (by norm_num)
      refine ⟨hreg2, ?_⟩
      intro x hx
      have heq :
          (fun y ↦ iteratedFDeriv ℝ (k + 1) u y v) =ᶠ[𝓝 x]
            (fun y ↦ fderiv ℝ (fun z ↦ iteratedFDeriv ℝ k u z (Fin.tail v)) y (v 0)) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        have hiter : DifferentiableAt ℝ (iteratedFDeriv ℝ k u) y :=
          ((hsmooth y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt_iteratedFDeriv
            (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)
        exact hiter.iteratedFDeriv_succ_apply_left'
      rw [((hreg2 x hx).contDiffAt (hU.mem_nhds hx)).coordinate_laplacian_eq_laplacian,
        (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds,
        ← (hdir.contDiffAt_of_isOpen hU hx).coordinate_laplacian_eq_laplacian]
      exact hdir.laplacian_eq_zero hx

end LaplacianEquation
