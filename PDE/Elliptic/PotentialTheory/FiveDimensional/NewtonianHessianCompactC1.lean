/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianHessianL2
public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianNoncompactHessian
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# Compact C¹ sources and the bounded Newtonian Hessian

One source derivative suffices to identify the Hessian with the
bounded L² extension. The first partial of the potential is C¹ because its
kernel is locally integrable. Two first-order weak derivative identities
therefore give the classical Hessian, and weak derivative uniqueness
identifies it with the bounded operator of `NewtonianHessianL2`.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory

namespace PotentialTheory

local notation "H" => Lp ℝ 2 (volume : Measure (ℝ^5))

/-- The bounded Newtonian Hessian acts classically on compact C¹ sources.
The proof uses the C¹ regularity of the potential's first partials, so it
requires no second source derivative or assumed Hessian integrability. -/
theorem newtonianHessianL2_apply_ae_eq_of_contDiff_one
    (i j : Fin 5) (S : H →L[ℝ] H)
    (hS : ∀ (g : ℝ^5 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g),
      S ((hg.continuous.memLp_of_hasCompactSupport hgc).toLp g) =ᵐ[volume]
        fun X ↦ (∂[i] (∂[j]
          (convolution (fundamentalSolution 5) g (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    S ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f) =ᵐ[volume]
      fun X ↦ (∂[i] (∂[j]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X := by
  let P := convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume
  have hP : ContDiff ℝ 1 P :=
    hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) hf
  have hPj : ContDiff ℝ 1 (∂[j] P) :=
    contDiff_one_partialDeriv_fundamentalSolution_five_convolution f hf hfc j
  have hfirst : SobolevSpace.HasWeakDerivativeOn Set.univ [j] P (∂[j] P) := by
    simpa only [iteratedPartialDeriv] using
      SobolevSpace.GraphSpace.hasWeakDerivativeOn_iteratedPartialDeriv_finite
        (Ω := Set.univ) [j] (by simpa using hP)
  have hsecond : SobolevSpace.HasWeakDerivativeOn Set.univ [i]
      (∂[j] P) (∂[i] (∂[j] P)) := by
    simpa only [iteratedPartialDeriv] using
      SobolevSpace.GraphSpace.hasWeakDerivativeOn_iteratedPartialDeriv_finite
        (Ω := Set.univ) [i] (by simpa using hPj)
  have hclassical : SobolevSpace.HasWeakDerivativeOn Set.univ [i, j]
      P (∂[i] (∂[j] P)) := by
    have hji : SobolevSpace.HasWeakDerivativeOn Set.univ [j, i]
        P (∂[i] (∂[j] P)) := by
      simpa only [List.cons_append, List.nil_append] using hfirst.append_single i hsecond
    exact hji.perm (List.Perm.swap _ _ [])
  have hf0 : ∀ᵐ X ∂volume, X ∉ tsupport f → f X = 0 := by
    filter_upwards [] with X hX
    exact image_eq_zero_of_notMem_tsupport hX
  have hweak := hasWeakDerivativeOn_newtonianHessianL2_of_ae_compact_support
    i j S hS (K := tsupport f)
    (hf.continuous.memLp_of_hasCompactSupport hfc) hfc hf0
  simpa only [SobolevSpace.domainMeasure, Measure.restrict_univ] using
    SobolevSpace.HasWeakDerivativeOn.unique_ae isOpen_univ hweak hclassical

/-- The Hessian of a compact C¹ Newtonian source belongs to L²,
as a consequence of its agreement with the bounded weak operator. -/
theorem fundamentalSolution_five_convolution_hessian_memLp_of_contDiff_one
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (i j : Fin 5) :
    MemLp (fun X ↦ (∂[i] (∂[j]
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume))) X)
      2 volume := by
  obtain ⟨T, hT, _⟩ := exists_newtonianHessianL2
  have haction := newtonianHessianL2_apply_ae_eq_of_contDiff_one i j (T i j)
    (fun g hg hgc ↦ hT.1 g hg hgc i j) f hf hfc
  exact (memLp_congr_ae haction).mp
    (Lp.memLp (T i j ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f)))

end PotentialTheory
