/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Sobolev
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.Spaces.Sobolev.Fractional.WholeSpace.IntegrationByParts

/-!
# Real Sobolev representatives of complex H² functions

The real part of a complex H² function belongs to the real weak-derivative
space W²,². The complex function need not be real-valued away from the region
where it represents given real data.

Directional derivatives come from Mathlib's Bessel space. Taking real parts
of their distributional test identities gives real weak derivatives.
The graph-space constructor then assembles their L² representatives.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

open MeasureTheory TopologicalSpace TemperedDistribution
open scoped ENNReal SchwartzMap LineDeriv Distributions

namespace SobolevSpace.Fractional

open GraphSpace

variable {n : ℕ}

/-- If two complex L² functions represent a distribution and its coordinate
derivative, their real parts satisfy the real weak-derivative identity.
Neither function is required to be real-valued. -/
theorem hasWeakDerivativeOn_re_of_lineDeriv_eq
    (i : Fin n) (u g : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hg : (g : 𝓢'(ℝ^n, ℂ)) =
      ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(ℝ^n, ℂ))) :
    HasWeakDerivativeOn Set.univ [i] (fun x ↦ (u x).re) (fun x ↦ (g x).re) := by
  refine ⟨((Lp.memLp u).re.locallyIntegrable (by norm_num)).locallyIntegrableOn _,
    ((Lp.memLp g).re.locallyIntegrable (by norm_num)).locallyIntegrableOn _, ?_⟩
  intro φ _
  let ψ : 𝓢(ℝ^n, ℂ) := testFunctionToSchwartz φ
  let e : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  have hpair := congrArg (fun T : 𝓢'(ℝ^n, ℂ) ↦ T ψ) hg
  change (g : 𝓢'(ℝ^n, ℂ)) ψ = (∂_{e} (u : 𝓢'(ℝ^n, ℂ))) ψ at hpair
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    Lp.toTemperedDistribution_apply, smul_eq_mul] at hpair
  have hL : Integrable (fun x ↦ (∂_{e} ψ) x * u x) volume :=
    ((∂_{e} ψ).memLp 2 volume).integrable_mul (Lp.memLp u)
  have hR : Integrable (fun x ↦ ψ x * g x) volume :=
    (ψ.memLp 2 volume).integrable_mul (Lp.memLp g)
  have hreal := congrArg Complex.reCLM hpair
  rw [map_neg, ← Complex.reCLM.integral_comp_comm hR,
    ← Complex.reCLM.integral_comp_comm hL] at hreal
  have hid :
      (∫ x, (g x).re * φ x) = -(∫ x, (u x).re * (∂[i] (φ : ℝ^n → ℝ)) x) := by
    simpa [ψ, e, lineDerivOp_testFunctionToSchwartz, Complex.mul_re, mul_comm] using hreal
  have hidentity :
      (∫ x, (u x).re * (∂[i] (φ : ℝ^n → ℝ)) x) = -(∫ x, (g x).re * φ x) := by
    linarith
  simpa [domainMeasure, iteratedPartialDeriv] using hidentity

/-- The real part of an H² distribution represented by a complex L² function
has a real W²,² bundle. All first and second rows are derived from Bessel
regularity; the base row agrees almost everywhere with the real part. -/
theorem exists_wkpSpaceOn_two_re_of_memSobolev
    (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hu : MemSobolev 2 2 (u : 𝓢'(ℝ^n, ℂ))) :
    ∃ U : W^{2,2}((Set.univ : Set (ℝ^n))),
      (((U : WkpAmbientOn n 2 2 Set.univ) (baseIndex n 2) :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ (u x).re := by
  classical
  have hfirst (i : Fin n) :
      ∃ g : Lp ℂ 2 (volume : Measure (ℝ^n)),
        MemSobolev 1 2 (g : 𝓢'(ℝ^n, ℂ)) ∧
          (g : 𝓢'(ℝ^n, ℂ)) =
            ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(ℝ^n, ℂ)) := by
    have h1 : MemSobolev 1 2
        (∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(ℝ^n, ℂ))) := by
      convert hu.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ)) using 1
      norm_num
    obtain ⟨g, hg⟩ := memSobolev_zero_iff.mp (h1.mono (by norm_num))
    exact ⟨g, hg ▸ h1, hg.symm⟩
  choose g hg hgeq using hfirst
  have hsecond (i j : Fin n) :
      ∃ h : Lp ℂ 2 (volume : Measure (ℝ^n)),
        (h : 𝓢'(ℝ^n, ℂ)) =
          ∂_{EuclideanSpace.single j (1 : ℝ)} (g i : 𝓢'(ℝ^n, ℂ)) := by
    have h0 : MemSobolev 0 2
        (∂_{EuclideanSpace.single j (1 : ℝ)} (g i : 𝓢'(ℝ^n, ℂ))) := by
      convert (hg i).lineDerivOp (m := EuclideanSpace.single j (1 : ℝ)) using 1
      norm_num
    obtain ⟨h, hh⟩ := memSobolev_zero_iff.mp h0
    exact ⟨h, hh.symm⟩
  choose h heq using hsecond
  let d : DerivIndex n 2 → ℝ^n → ℝ :=
    secondOrderRows (fun x ↦ (u x).re)
      (fun i x ↦ (g i x).re) (fun i j x ↦ (h i j x).re)
  have hbase : d (baseIndex n 2) = fun x ↦ (u x).re := by
    simp [d]
  have hmem (a : DerivIndex n 2) : MemLp (d a) 2 (domainMeasure n Set.univ) := by
    refine DerivIndex.inductionOnOrderTwo (motive := fun a ↦
      MemLp (d a) 2 (domainMeasure n Set.univ)) ?_ ?_ ?_ a
    · simpa [d, domainMeasure] using (Lp.memLp u).re
    · intro i
      simpa [d, domainMeasure] using (Lp.memLp (g i)).re
    · intro a i j ha
      simpa [d, secondOrderRows, ha, domainMeasure] using (Lp.memLp (h i j)).re
  have hweak (a : DerivIndex n 2) :
      HasWeakDerivativeOn Set.univ a.toList (fun x ↦ (u x).re) (d a) := by
    refine DerivIndex.inductionOnOrderTwo (motive := fun a ↦
      HasWeakDerivativeOn Set.univ a.toList (fun x ↦ (u x).re) (d a)) ?_ ?_ ?_ a
    · simpa [d] using SobolevSpace.hasWeakDerivativeOn_nil
        (((Lp.memLp u).re.locallyIntegrable (by norm_num)).locallyIntegrableOn Set.univ)
    · intro i
      simpa [d] using hasWeakDerivativeOn_re_of_lineDeriv_eq i u (g i) (hgeq i)
    · intro a i j ha
      have hi := hasWeakDerivativeOn_re_of_lineDeriv_eq i u (g i) (hgeq i)
      have hij := hasWeakDerivativeOn_re_of_lineDeriv_eq j (g i) (h i j) (heq i j)
      simpa [d, secondOrderRows, ha] using hi.append_single j hij
  refine ⟨mkWkpSpaceOnOfWeakDerivatives (fun x ↦ (u x).re) d hbase hmem hweak, ?_⟩
  simpa [domainMeasure, hbase] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (fun x ↦ (u x).re) d hbase hmem hweak (baseIndex n 2)

end SobolevSpace.Fractional
