/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import PDE.FDeriv.Calculus.Symmetric

/-!
# Commuting the Laplacian with differentiation

For a `C³` map on a finite-dimensional real inner product space, the Laplacian commutes
with every fixed directional derivative. The codomain may be any real normed space.
For the radial derivative, the commutator contributes twice the Laplacian.

The proof expresses Mathlib's Laplacian in an orthonormal basis and commutes successive
directional derivatives using symmetry of the second Fréchet derivative. The regularity
hypothesis is local at the point where the identity is asserted.
-/

@[expose] public section

open Filter Topology

noncomputable section

section Laplacian

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : E → F} {x : E}

private theorem laplacian_eq_sum_fderiv_fderiv_of_contDiffAt
    (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian f x =
      ∑ i, fderiv ℝ
        (fun y ↦ fderiv ℝ f y ((stdOrthonormalBasis ℝ E) i))
        x ((stdOrthonormalBasis ℝ E) i) := by
  classical
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) x]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply,
    fderiv_clm_apply hdf (differentiableAt_const ((stdOrthonormalBasis ℝ E) i))]
  simp

/-- At a point of `C³` regularity, the Laplacian commutes with differentiation in a fixed
direction. The codomain can be any real normed space. -/
theorem ContDiffAt.laplacian_fderiv_apply
    (hf : ContDiffAt ℝ 3 f x) (v : E) :
    Laplacian.laplacian (fun y ↦ fderiv ℝ f y v) x =
      fderiv ℝ (Laplacian.laplacian f) x v := by
  classical
  let e := stdOrthonormalBasis ℝ E
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hdf : ContDiffAt ℝ 2 (fderiv ℝ f) x :=
    hf.fderiv_right (by norm_num)
  have hdir (a : E) : ContDiffAt ℝ 2 (fun y ↦ fderiv ℝ f y a) x :=
    hdf.clm_apply contDiffAt_const
  have hdiag (a : E) :
      DifferentiableAt ℝ
        (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z a) y a) x :=
    (((hdir a).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt one_ne_zero
  have hcomm (a : E) :
      fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z v) y a) x a =
        fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z a) y a) x v := by
    have hswap :
        (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z v) y a) =ᶠ[𝓝 x]
          (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z a) y v) := by
      filter_upwards [hf2.eventually (by norm_num)] with y hy
      exact PDE.fderiv_fderiv_apply_comm f y v a hy
    calc
      fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z v) y a) x a =
          fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z a) y v) x a :=
        congrArg (fun L : E →L[ℝ] F ↦ L a) hswap.fderiv_eq
      _ = fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z a) y a) x v :=
        PDE.fderiv_fderiv_apply_comm (fun z ↦ fderiv ℝ f z a) x v a (hdir a)
  have htrace :
      Laplacian.laplacian f =ᶠ[𝓝 x]
        (fun y ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ f z (e i)) y (e i)) := by
    filter_upwards [hf2.eventually (by norm_num)] with y hy
    exact laplacian_eq_sum_fderiv_fderiv_of_contDiffAt hy
  rw [laplacian_eq_sum_fderiv_fderiv_of_contDiffAt (hdir v), htrace.fderiv_eq,
    fderiv_fun_sum (fun i _ ↦ hdiag (e i)), sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ hcomm (e i)

/-- The Laplacian of the radial derivative is the radial derivative of the Laplacian,
plus twice the Laplacian. Only local `C³` regularity is required. -/
theorem ContDiffAt.laplacian_fderiv_self (hf : ContDiffAt ℝ 3 f x) :
    Laplacian.laplacian (fun y ↦ fderiv ℝ f y y) x =
      fderiv ℝ (Laplacian.laplacian f) x x + (2 : ℝ) • Laplacian.laplacian f x := by
  classical
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  have hg2 : ContDiffAt ℝ 2 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hgd := hg2.differentiableAt (by norm_num)
  have hggd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    (hg2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdir (v : E) : ContDiffAt ℝ 2 (fun y ↦ fderiv ℝ f y v) x :=
    hg2.clm_apply contDiffAt_const
  have hid (y : E) : DifferentiableAt ℝ (fun z : E ↦ z) y := differentiableAt_id
  have hid2 : ContDiffAt ℝ 2 (fun y : E ↦ y) x := contDiffAt_id
  have hsecond (v : E) :
      fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z z) y v) x v =
        fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z x) y v) x v +
          (fderiv ℝ (fun y ↦ fderiv ℝ f y v) x v +
            fderiv ℝ (fun y ↦ fderiv ℝ f y v) x v) := by
    have hradial :
        (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z z) y v) =ᶠ[𝓝 x]
          (fun y ↦ fderiv ℝ (fderiv ℝ f) y v y + fderiv ℝ f y v) := by
      filter_upwards [hg2.eventually (by norm_num)] with y hy
      rw [fderiv_clm_apply (hy.differentiableAt (by norm_num)) (hid y)]
      simp [add_comm]
    have hfixed :
        (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z x) y v) =ᶠ[𝓝 x]
          (fun y ↦ fderiv ℝ (fderiv ℝ f) y v x) := by
      filter_upwards [hg2.eventually (by norm_num)] with y hy
      rw [fderiv_clm_apply (hy.differentiableAt (by norm_num))
        (differentiableAt_const x)]
      simp
    have hdv : DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fderiv ℝ f) y v) x :=
      hggd.clm_apply (differentiableAt_const v)
    rw [hradial.fderiv_eq, hfixed.fderiv_eq,
      fderiv_fun_add (hdv.clm_apply (hid x))
        (hgd.clm_apply (differentiableAt_const v)),
      fderiv_clm_apply hdv (hid x),
      fderiv_clm_apply hdv (differentiableAt_const x),
      fderiv_clm_apply hgd (differentiableAt_const v)]
    simp [add_assoc, add_left_comm, add_comm]
  rw [laplacian_eq_sum_fderiv_fderiv_of_contDiffAt (hg2.clm_apply hid2)]
  simp_rw [hsecond]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← laplacian_eq_sum_fderiv_fderiv_of_contDiffAt (hdir x),
    ← laplacian_eq_sum_fderiv_fderiv_of_contDiffAt hf2,
    hf.laplacian_fderiv_apply]
  simp [two_smul ℝ]

end Laplacian
