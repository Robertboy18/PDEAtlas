/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Coordinate differentiation of convolution

Derivatives fall on a compactly supported smooth kernel. The other factor need only be locally
integrable with respect to the source measure. Evaluating the Fréchet derivative on a
coordinate vector gives the partial derivative identity; applying it twice gives the
Laplacian identity. No translation invariance is needed, so restricted volume and boundary
measures are allowed.
-/

@[expose] public section

open PDE (partialDeriv laplacian)

open MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace PDE

/-- Differentiate a convolution by differentiating its compactly supported `C¹` factor. -/
theorem partialDeriv_convolution_right {n : ℕ} {μ : Measure (ℝ^n)}
    (i : Fin n) {f g : ℝ^n → ℝ} (x : ℝ^n)
    (hf : LocallyIntegrable f μ)
    (hg_cs : HasCompactSupport g) (hg1 : ContDiff ℝ 1 g) :
    (∂[i] (fun y ↦ (f ⋆[mul ℝ ℝ, μ] g) y)) x =
      (f ⋆[mul ℝ ℝ, μ] (fun y ↦ (∂[i] g) y)) x := by
  -- The parameter theorem permits arbitrary source measures. Its unused first parameter
  -- lets us obtain the spatial derivative without a Haar-measure assumption.
  let kernel : ℝ^n × ℝ^n → ℝ := fun q ↦ g q.2
  have hkernel : ContDiff ℝ 1 kernel := hg1.comp contDiff_snd
  have hD (y : ℝ^n) : fderiv ℝ kernel (0, y) =
      (fderiv ℝ g y).comp (ContinuousLinearMap.snd ℝ (ℝ^n) (ℝ^n)) := by
    exact ((hg1.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp (0, y)
      hasFDerivAt_snd).fderiv
  have hDc : HasCompactSupport (fun y ↦ fderiv ℝ kernel (0, y)) := by
    apply HasCompactSupport.intro (hg_cs.fderiv ℝ).isCompact
    intro y hy
    rw [hD y, image_eq_zero_of_notMem_tsupport hy]
    simp
  have hDcont : Continuous (fun y ↦ fderiv ℝ kernel (0, y)) :=
    (hkernel.continuous_fderiv one_ne_zero).comp (continuous_const.prodMk continuous_id)
  have hparam := hasFDerivAt_convolution_right_with_param (mul ℝ ℝ)
    (g := fun _ y ↦ g y) isOpen_univ hg_cs.isCompact
    (fun _ y _ hy ↦ image_eq_zero_of_notMem_tsupport hy) hf hkernel.contDiffOn
    (0, x) (Set.mem_univ (0 : ℝ^n))
  have hspatial := hparam.comp x
    ((hasFDerivAt_const (0 : ℝ^n) x).prodMk (hasFDerivAt_id x))
  have happly := congrArg
    (fun T : ℝ^n →L[ℝ] ℝ ↦ T (EuclideanSpace.single i (1 : ℝ))) hspatial.fderiv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] at happly
  change (fderiv ℝ (f ⋆[mul ℝ ℝ, μ] g) x) (EuclideanSpace.single i 1) =
    ((f ⋆[(mul ℝ ℝ).precompR (ℝ^n × ℝ^n), μ]
      (fun y ↦ fderiv ℝ kernel (0, y))) x) (0, EuclideanSpace.single i 1) at happly
  rw [convolution_precompR_apply (mul ℝ ℝ) hf hDc hDcont] at happly
  simpa [partialDeriv, hD] using happly

/-- The coordinate Laplacian of a convolution is obtained by applying the Laplacian to
its compactly supported `C²` factor. -/
theorem laplacian_convolution_right {n : ℕ} {μ : Measure (ℝ^n)}
    {f g : ℝ^n → ℝ}
    (hf : LocallyIntegrable f μ) (hg : HasCompactSupport g)
    (hg2 : ContDiff ℝ 2 g) (x : ℝ^n) :
    laplacian (f ⋆[mul ℝ ℝ, μ] g) x =
      (f ⋆[mul ℝ ℝ, μ] laplacian g) x := by
  have hg1 : ContDiff ℝ 1 g := hg2.of_le (by norm_num)
  have hpartial (i : Fin n) :
      ContDiff ℝ 1 (fun y ↦ (∂[i] g) y) :=
    contDiff_partialDeriv_of_succ (m := 1) hg2
  have hpartial_cs (i : Fin n) :
      HasCompactSupport (fun y ↦ (∂[i] g) y) := by
    simpa only [partialDeriv] using
      hg.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hsecond_int (i : Fin n) :
      Integrable (fun y ↦
        f y * (∂[i] (fun z ↦ (∂[i] g) z)) (x - y)) μ := by
    have hsecond_cs :
        HasCompactSupport (fun y ↦ (∂[i] (fun z ↦ (∂[i] g) z)) y) := by
      simpa only [partialDeriv] using
        (hpartial_cs i).fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
    have hsecond_cont :
        Continuous (fun y ↦ (∂[i] (fun z ↦ (∂[i] g) z)) y) :=
      (contDiff_partialDeriv_of_succ (m := 0) (hpartial i)).continuous
    exact hsecond_cs.convolutionExists_right (mul ℝ ℝ) hf hsecond_cont x
  unfold laplacian
  calc
    (∑ i : Fin n, (∂[i] (fun y ↦ (∂[i] (f ⋆[mul ℝ ℝ, μ] g)) y)) x) =
        ∑ i : Fin n,
          (f ⋆[mul ℝ ℝ, μ] fun y ↦ (∂[i] (fun z ↦ (∂[i] g) z)) y) x := by
      apply Finset.sum_congr rfl
      intro i _
      have hfirst :
          (fun y ↦ (∂[i] (f ⋆[mul ℝ ℝ, μ] g)) y) =
            f ⋆[mul ℝ ℝ, μ] (fun y ↦ (∂[i] g) y) :=
        funext fun y ↦ partialDeriv_convolution_right i y hf hg hg1
      rw [hfirst]
      exact partialDeriv_convolution_right i x hf (hpartial_cs i) (hpartial i)
    _ = ∫ y, ∑ i : Fin n,
        f y * (∂[i] (fun z ↦ (∂[i] g) z)) (x - y) ∂μ := by
      simp only [convolution_def, mul_apply']
      exact (integral_finsetSum Finset.univ fun i _ ↦ hsecond_int i).symm
    _ = (f ⋆[mul ℝ ℝ, μ] fun y ↦
        ∑ i : Fin n, (∂[i] (fun z ↦ (∂[i] g) z)) y) x := by
      simp only [convolution_def, mul_apply', Finset.mul_sum]

end PDE
