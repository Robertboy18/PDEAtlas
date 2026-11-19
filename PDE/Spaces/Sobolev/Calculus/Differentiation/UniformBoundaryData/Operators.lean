/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Sobolev
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian
public import PDE.FDeriv.Euclidean.Laplacian

/-!
# Classical representatives of weak differential operators

The Sobolev realization of classical closure data keeps the same gradient and
Laplacian almost everywhere. These identities let a weak integration-by-parts
argument meet a classical Green identity without choosing another extension or
another representative.

Only openness and boundedness of the domain enter this construction. No boundary
chart or extension theorem is needed.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open MeasureTheory Set GraphSpace
open scoped ENNReal Gradient Laplacian

variable {n : ℕ} {Ω : Set ℝ^n} {f : ℝ^n → ℝ}

/-- The vector weak gradient of classical first-order closure data is its
ordinary gradient, almost everywhere on the domain. -/
theorem gradient_toWkpSpaceOn_ae (hf : ContDiffUpToBoundary 1 f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (wkpGradientCLM (hf.toWkpSpaceOn hopen hbounded p) : ℝ^n → ℝ^n)
      =ᵐ[domainMeasure n Ω] ∇ f := by
  filter_upwards [wkpGradientCLM_apply_ae (hf.toWkpSpaceOn hopen hbounded p),
    ae_all_iff.mpr (fun i : Fin n ↦
      hf.toWkpSpaceOn_apply_ae hopen hbounded p (singleDerivIndex n i))] with x hx hd
  ext i
  rw [hx i, PDE.gradient_apply_eq_partialDeriv]
  simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using hd i

/-- The weak Laplacian of classical second-order closure data has the
coordinate Laplacian as its almost-everywhere representative. -/
theorem coordinate_laplacian_toWkpSpaceOn_ae (hf : ContDiffUpToBoundary 2 f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (wkpLaplacianCLM (hf.toWkpSpaceOn hopen hbounded p) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] PDE.laplacian f := by
  filter_upwards [wkpLaplacianCLM_coeFn (hf.toWkpSpaceOn hopen hbounded p),
    ae_all_iff.mpr (fun i : Fin n ↦
      hf.toWkpSpaceOn_apply_ae hopen hbounded p (pairDerivIndex n i i))] with x hx hd
  rw [hx]
  apply Finset.sum_congr rfl
  intro i _
  have hlist : (pairDerivIndex n i i).toList = [i, i] := by
    apply (List.perm_replicate (n := 2) (a := i)).mp
    simpa using pairDerivIndex_toList_perm i i
  simpa only [hlist, iteratedPartialDeriv] using hd i

/-- For classical second-order closure data, the weak Laplacian agrees almost
everywhere with Mathlib's Laplacian defined through the second Fréchet derivative. -/
theorem laplacian_toWkpSpaceOn_ae (hf : ContDiffUpToBoundary 2 f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (wkpLaplacianCLM (hf.toWkpSpaceOn hopen hbounded p) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] Δ f := by
  filter_upwards [hf.coordinate_laplacian_toWkpSpaceOn_ae hopen hbounded p,
    ae_restrict_mem hopen.measurableSet] with x hx hxΩ
  exact hx.trans
    (hf.contDiffOn.contDiffAt (hopen.mem_nhds hxΩ)).coordinate_laplacian_eq_laplacian

end SobolevSpace.ContDiffUpToBoundary
