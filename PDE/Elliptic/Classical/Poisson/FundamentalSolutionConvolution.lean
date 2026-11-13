/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import PDE.Analysis.Integration.ConvolutionDerivative
public import PDE.Elliptic.PotentialTheory.FundamentalSolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Fundamental-solution convolution for Poisson data

We define `fundamentalSolutionConvolution n f = Φ ⋆ f` for a compactly supported `C²` datum `f`,
where `Φ` is the fundamental solution normalized by `-ΔΦ = δ₀`. The convolution is `C²`
(`contDiff_two_fundamentalSolutionConvolution`, by Mathlib's
`HasCompactSupport.contDiff_convolution_right` and the local integrability of `Φ`), and the
Laplacian moves onto the datum, `Δ(Φ ⋆ f) = Φ ⋆ Δf` (`laplacian_fundamentalSolutionConvolution`).
These are the two conclusions of step 1 of Evans's proof of §2.2.1, Theorem 1, where his formula
(10) gives all second derivatives of `Φ ⋆ f`. The source identity `-Δ(Φ ⋆ f) = f`, which also
needs `-ΔΦ = δ₀`, is proved in `PDE.Elliptic.Classical.Poisson.FundamentalSolution`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1(b), the convolution (8), Theorem 1 (Solving Poisson's
  equation) and step 1 of its proof, (9)-(10), pp. 23-24.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian iteratedPartialDeriv)

namespace PoissonEquation

open MeasureTheory Filter Topology PotentialTheory

/-- The convolution candidate `Φ ⋆ f` for a compactly supported `C²` datum.

Together with the pole identity `-ΔΦ = δ₀`, the regularity and derivative-transfer theorems
below give classical inversion in every dimension at least two, in
`PDE.Elliptic.Classical.Poisson.FundamentalSolution`. -/
noncomputable def fundamentalSolutionConvolution (n : ℕ)
    (f : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^n)) ℝ 2)
    (x : ℝ^n) : ℝ :=
  (convolution (PotentialTheory.fundamentalSolution n) f
    (ContinuousLinearMap.mul ℝ ℝ) : ℝ^n → ℝ) x

/-- The fundamental-solution convolution has continuous second derivatives. -/
theorem contDiff_two_fundamentalSolutionConvolution
    (n : ℕ)
    (f : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^n)) ℝ 2) :
    ContDiff ℝ 2 (fundamentalSolutionConvolution n f) := by
  have h_supp : HasCompactSupport (f : ℝ^n → ℝ) := f.hasCompactSupport
  have h_diff : ContDiff ℝ 2 (f : ℝ^n → ℝ) := f.contDiff
  apply h_supp.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (PotentialTheory.locallyIntegrable_fundamentalSolution n) h_diff

private theorem sum_convolution_right
    {ι : Type*} [Fintype ι] {n : ℕ}
    (f : ℝ^n → ℝ) (g : ι → ℝ^n → ℝ)
    (hf : LocallyIntegrable f volume)
    (hgc : ∀ i, HasCompactSupport (g i))
    (hg : ∀ i, Continuous (g i)) (x : ℝ^n) :
    (∑ i, convolution f (g i) (ContinuousLinearMap.mul ℝ ℝ) volume x) =
      convolution f (fun y ↦ ∑ i, g i y)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  classical
  have hInt :
      ∀ i ∈ (Finset.univ : Finset ι),
        Integrable (fun t : ℝ^n ↦ f t * g i (x - t)) volume := by
    intro i _hi
    exact (((hgc i).convolutionExists_right
      (L := ContinuousLinearMap.mul ℝ ℝ) hf (hg i)) x).integrable
  simpa [MeasureTheory.convolution_mul] using (by
    calc
      (∑ i : ι, ∫ t : ℝ^n, f t * g i (x - t) ∂volume) =
          ∫ t : ℝ^n, ∑ i : ι, f t * g i (x - t) ∂volume := by
        simpa using
          (MeasureTheory.integral_finsetSum
            (s := (Finset.univ : Finset ι))
            (f := fun i t ↦ f t * g i (x - t)) hInt).symm
      _ = ∫ t : ℝ^n, f t * ∑ i : ι, g i (x - t) ∂volume := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro t
        exact (Finset.mul_sum (Finset.univ : Finset ι) (fun i ↦ g i (x - t)) (f t)).symm)

/-- For `f ∈ C²_c(ℝ^n)`, the Laplacian can be moved onto `f`:
`Δ(Φ ⋆ f) = Φ ⋆ (Δf)`. -/
theorem laplacian_fundamentalSolutionConvolution
    (n : ℕ)
    (f : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^n)) ℝ 2)
    (x : ℝ^n) :
    laplacian (fundamentalSolutionConvolution n f) x =
      convolution (PotentialTheory.fundamentalSolution n)
        (fun y ↦ laplacian f y)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := by
  classical
  have hΦ := PotentialTheory.locallyIntegrable_fundamentalSolution n
  have hg2 : ContDiff ℝ 2 (f : ℝ^n → ℝ) := f.contDiff
  let Δi : Fin n → ℝ^n → ℝ := fun i y ↦ (∂[i] (fun z ↦ (∂[i] (f : ℝ^n → ℝ)) z)) y
  have hΔi_supp (i : Fin n) : HasCompactSupport (Δi i) := by
    simpa [Δi, partialDeriv] using (f.hasCompactSupport.fderiv_apply (𝕜 := ℝ)
      (EuclideanSpace.single i 1)).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hΔi_cont (i : Fin n) : Continuous (Δi i) := by
    simpa [Δi, iteratedPartialDeriv] using
      (PDE.contDiff_iteratedPartialDeriv_of_le hg2 [i, i] (by simp)).continuous
  unfold laplacian
  calc
    _ = ∑ i : Fin n, convolution (PotentialTheory.fundamentalSolution n) (Δi i)
        (ContinuousLinearMap.mul ℝ ℝ) volume x := Finset.sum_congr rfl fun i _ ↦
      PDE.Analysis.convolution_iteratedPartialDeriv_two_right _ _ hΦ f.hasCompactSupport hg2 i i x
    _ = _ := sum_convolution_right _ Δi hΦ hΔi_supp hΔi_cont x

end PoissonEquation
