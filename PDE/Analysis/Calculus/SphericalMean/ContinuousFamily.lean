/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.SphericalMean.Regularity
public import PDE.Analysis.Calculus.CompactParametricIntegral.IteratedDerivative
public import PDE.Analysis.Calculus.ContinuousFamily.IteratedDerivative

/-!
# Continuously indexed spherical means

Finite spatial jets of the data give jointly continuous actual center and signed
radius jets of their spherical means, including radius zero.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace PDE.Analysis

variable {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]
  {n k : ℕ} {f : A → ℝ^n → ℝ}

/-- A continuous family of spatial jets remains continuous after spherical averaging
and differentiation in the center and signed radius. -/
theorem continuous_iteratedFDeriv_unitSphereAverage_family
    (hf : ∀ a, ContDiff ℝ k (f a))
    (hjet : ∀ j ≤ k, Continuous
      (fun p : A × ℝ^n ↦ iteratedFDeriv ℝ j (f p.1) p.2))
    {j : ℕ} (hj : j ≤ k) :
    Continuous (fun p : A × (ℝ^n × ℝ) ↦ iteratedFDeriv ℝ j
      (fun q : ℝ^n × ℝ ↦ unitSphereAverage n (f p.1) q.1 q.2) p.2) := by
  let S := Metric.sphere (0 : ℝ^n) 1
  let μ := (volume : Measure (ℝ^n)).toSphere
  let L (a : A × S) : ℝ^n × ℝ →L[ℝ] ℝ^n :=
    ContinuousLinearMap.fst ℝ (ℝ^n) ℝ +
      (ContinuousLinearMap.snd ℝ (ℝ^n) ℝ).smulRight (a.2 : ℝ^n)
  have hL : Continuous L :=
    continuous_const.add
      (((ContinuousLinearMap.smulRightL ℝ (ℝ^n × ℝ) (ℝ^n))
        (ContinuousLinearMap.snd ℝ (ℝ^n) ℝ)).continuous.comp
          (continuous_subtype_val.comp continuous_snd))
  let F (a : A) (p : ℝ^n × ℝ) (ω : S) := f a (p.1 + p.2 • (ω : ℝ^n))
  have hF (a : A) (ω : S) : ContDiff ℝ k (fun p ↦ F a p ω) :=
    (hf a).comp (contDiff_fst.add (contDiff_snd.smul contDiff_const))
  have hFj (i : ℕ) (hi : i ≤ k) : Continuous
      (fun p : (A × (ℝ^n × ℝ)) × S ↦
        iteratedFDeriv ℝ i (fun x ↦ F p.1.1 x p.2) p.1.2) := by
    have h := continuous_iteratedFDeriv_comp_linear_family
      (L := L) (fun a ↦ (hf a.1).of_le (by exact_mod_cast hi))
      ((hjet i hi).comp (continuous_fst.fst.prodMk continuous_snd)) hL
    exact h.comp ((continuous_fst.fst.prodMk continuous_snd).prodMk continuous_fst.snd)
  have hI (a : A) : ContDiff ℝ k (fun p ↦ ∫ ω, F a p ω ∂μ) :=
    contDiff_integral_of_compact (hF a) (fun i hi ↦ (hFj i hi).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd))
  have hIj := continuous_iteratedFDeriv_integral_family (μ := μ) hF hFj hj
  let N : ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (unitSphereArea n)⁻¹
  simpa only [N, F, unitSphereAverage, Function.comp_def,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, div_eq_mul_inv] using
    N.continuous_iteratedFDeriv_comp_family
      (fun a ↦ (hI a).of_le (by exact_mod_cast hj)) hIj

end PDE.Analysis
