/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.InitialDomain
public import PDE.FDeriv.Operators
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Schwartz tests for the whole-space weak Laplacian

Schwartz functions and their classical derivatives define real Sobolev bundles
of every finite order. The order-two bundle identifies the gradient pairing
against an arbitrary H¹ function with its distributional Laplacian pairing.
This connects the variational wave equation to whole-space Fourier regularity.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE (laplacian iteratedPartialDeriv)
open scoped Sobolev SobolevSpace.WholeSpaceHilbert SchwartzMap LineDeriv Laplacian
  InnerProductSpace

namespace SchwartzMap

variable {n k : ℕ}

/-- Every finite coordinate derivative of a real Schwartz function is in L². -/
theorem memLp_iteratedPartialDeriv (φ : 𝓢(ℝ^n, ℝ)) (a : List (Fin n)) :
    MemLp (iteratedPartialDeriv a φ) 2 (volume : Measure (ℝ^n)) := by
  have hex : ∃ ψ : 𝓢(ℝ^n, ℝ), (ψ : ℝ^n → ℝ) = iteratedPartialDeriv a φ := by
    induction a with
    | nil => exact ⟨φ, rfl⟩
    | cons i a ih =>
      obtain ⟨ψ, hψ⟩ := ih
      refine ⟨∂_{EuclideanSpace.single i (1 : ℝ)} ψ, ?_⟩
      ext x
      change fderiv ℝ (ψ : ℝ^n → ℝ) x _ = _
      rw [hψ]
      rfl
  obtain ⟨ψ, hψ⟩ := hex
  rw [← hψ]
  exact ψ.memLp 2 volume

/-- A real Schwartz function as a whole-space weak-derivative Sobolev bundle. -/
def toWkpSpace (φ : 𝓢(ℝ^n, ℝ)) (k : ℕ) : W^{k,2}(ℝ^n) :=
  mkWkpSpaceOnOfContDiffMemLp φ (φ.smooth ⊤)
    (fun a ↦ by simpa only [domainMeasure, Measure.restrict_univ] using
      φ.memLp_iteratedPartialDeriv a.toList)

/-- The Sobolev rows of a Schwartz function represent its classical derivatives. -/
theorem toWkpSpace_coordinate_ae (φ : 𝓢(ℝ^n, ℝ)) (a : DerivIndex n k) :
    (φ.toWkpSpace k).val a =ᵐ[volume] iteratedPartialDeriv a.toList φ := by
  simpa only [toWkpSpace, domainMeasure, Measure.restrict_univ] using
    mkWkpSpaceOnOfContDiffMemLp_apply_ae (k := k) (p := 2) (Ω := univ) φ (φ.smooth ⊤)
      (fun a ↦ by simpa only [domainMeasure, Measure.restrict_univ] using
        φ.memLp_iteratedPartialDeriv a.toList) a

/-- The Laplacian row of a Schwartz bundle represents its classical Laplacian. -/
theorem laplacian_toWkpSpace_ae (φ : 𝓢(ℝ^n, ℝ)) :
    (Δ (φ.toWkpSpace 2) : DerivLp n 2 univ) =ᵐ[volume] laplacian (φ : ℝ^n → ℝ) := by
  classical
  filter_upwards [show (Δ (φ.toWkpSpace 2) : DerivLp n 2 univ) =ᵐ[volume]
        fun x ↦ ∑ i : Fin n, (φ.toWkpSpace 2).val (pairDerivIndex n i i) x from
      by simpa only [domainMeasure, Measure.restrict_univ,
        laplacian_eq_wkpLaplacianCLM] using wkpLaplacianCLM_coeFn (φ.toWkpSpace 2),
      ae_all_iff.mpr (fun i : Fin n ↦ φ.toWkpSpace_coordinate_ae (pairDerivIndex n i i))]
    with x hx hd
  rw [hx]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hlist : (pairDerivIndex n i i).toList = [i, i] := by
    apply (List.perm_replicate (n := 2) (a := i)).mp
    simpa using pairDerivIndex_toList_perm i i
  simpa only [hlist, iteratedPartialDeriv] using hd i

end SchwartzMap

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ}

/-- The H¹ variational Laplacian agrees with distributional testing on every
real Schwartz function. -/
theorem gradientForm_schwartz (u : H¹(ℝ^n)) (φ : 𝓢(ℝ^n, ℝ)) :
    gradientForm n u (lowerOrderCLM (by decide : 1 ≤ 2) (φ.toWkpSpace 2)) =
      -(∫ x, (energyTriple n).inclusion u x * laplacian (φ : ℝ^n → ℝ) x) := by
  have hsymm (v : H¹(ℝ^n)) : gradientForm n u v = gradientForm n v u := by
    simp only [gradientForm_apply]
    exact Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _
  rw [hsymm, gradientForm_h2, L2.inner_def]
  congr 1
  simp only [domainMeasure, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [φ.laplacian_toWkpSpace_ae] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial]

end PDE.Hyperbolic.NonlinearWave.Cauchy
