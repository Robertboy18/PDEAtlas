/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.VectorValued.Classical
public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.OpenDomain
public import PDE.Spaces.Sobolev.Calculus.Product.VectorValued.Closure

/-!
# Banach-valued weak Leibniz rule at finite exponents

Smooth density in each input and Mathlib's continuous bilinear Hölder map on `Lp`
pass the classical product identity to the closed weak-derivative graph. The codomains
are arbitrary complete real Banach spaces, and the domain may be any open Euclidean set.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
  [ENNReal.HolderTriple p q r]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
private theorem weak_bilinear_smooth
    (B : F →L[ℝ] G →L[ℝ] H) (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G))
    {f : ℝ^n → F} {g : ℝ^n → G}
    (hf : ContDiffOn ℝ 1 f Ω) (hg : ContDiffOn ℝ 1 g Ω)
    (hU : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f)
    (hV : (V.val (baseIndex n 1) : ℝ^n → G) =ᵐ[domainMeasure n Ω] g)
    (i : Fin n) :
    HasWeakDerivativeOn Ω [i]
      (fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x))
      (fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x)) := by
  apply (hasWeakDerivativeOn_bilinear_of_contDiffOn B hf hg i).congr_ae
  · filter_upwards [hU, hV] with x hu hv
    simp only [hu, hv]
  · filter_upwards [coordinate_ae_partialDeriv_of_contDiffOn U hf hU i,
      coordinate_ae_partialDeriv_of_contDiffOn V hg hV i, hU, hV] with x hdu hdv hu hv
    simp only [hdu, hdv, hu, hv]

include r in
/-- At finite input exponents, the continuous bilinear Hölder product has the expected
first weak derivative. The output exponent may be `1`; no finite-volume hypothesis is used. -/
theorem hasWeakDerivativeOn_bilinear_finite
    (B : F →L[ℝ] G →L[ℝ] H) (hp : p ≠ ∞) (hq : q ≠ ∞)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) (i : Fin n) :
    HasWeakDerivativeOn Ω [i]
      (fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x))
      (fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x)) := by
  obtain ⟨Us, f, hf, hUf, hUs⟩ := meyers_serrin hp U
  obtain ⟨Vs, g, hg, hVg, hVs⟩ := meyers_serrin hq V
  have hUt : Tendsto Us atTop (𝓝 U) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_eq_norm] using hUs
  have hVt : Tendsto Vs atTop (𝓝 V) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_eq_norm] using hVs
  exact hasWeakDerivativeOn_bilinear_of_tendsto (r := r) B hUt hVt i fun j ↦
    weak_bilinear_smooth B (Us j) (Vs j)
      ((hf j).of_le (by simp)) ((hg j).of_le (by simp)) (hUf j) (hVg j) i

end SobolevSpace.VectorValued
