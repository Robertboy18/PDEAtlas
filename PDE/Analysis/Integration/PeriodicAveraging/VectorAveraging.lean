/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.WeakAveraging
public import PDE.Analysis.MeasureTheory.Lp.RealL2
public import PDE.Analysis.MeasureTheory.Lp.EuclideanCoordinates
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Weak averaging of real and vector-valued periodic fields

Complex Fourier averaging gives real L² pairing convergence by taking real parts.
Pairing coordinatewise through `EuclideanSpace.proj` then gives averaging of vector
fields.
The weak limits are the actual normalized cell integrals.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace PDE.Analysis.PeriodicAveraging

variable {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0))

include hΩm ht

/-- Periodic real L² functions converge to their cell mean against every local L² test. -/
theorem tendsto_inner_rescaleLp_real (u : Lp ℝ 2 (cellMeasure n))
    (g : Lp ℝ 2 (volume.restrict Ω)) :
    Tendsto (fun j ↦ ⟪g, rescaleLp hΩ (ε j) (hε j) (hε1 j) u⟫_ℝ)
      l (𝓝 ⟪g, Lp.const 2 (volume.restrict Ω) (∫ x, u x ∂cellMeasure n)⟫_ℝ) := by
  have hinner {X : Type} [MeasurableSpace X] (μ : Measure X) (v w : Lp ℝ 2 μ) :
      (⟪Complex.ofRealCLM.compLp v, Complex.ofRealCLM.compLp w⟫_ℂ).re =
        ⟪v, w⟫_ℝ := by
    symm
    simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm] using
      integral_mul_eq_re_inner (f := v) (g := w)
        (Filter.EventuallyEq.symm (Complex.ofRealCLM.coeFn_compLp v))
        (Filter.EventuallyEq.symm (Complex.ofRealCLM.coeFn_compLp w))
  have hmean : (∫ x, Complex.ofRealCLM.compLp u x ∂cellMeasure n) =
      Complex.ofReal (∫ x, u x ∂cellMeasure n) := by
    exact (integral_congr_ae (Complex.ofRealCLM.coeFn_compLp u)).trans integral_complex_ofReal
  have hconst (c : ℝ) :
      Lp.const 2 (volume.restrict Ω) (c : ℂ) =
        Complex.ofRealCLM.compLp (Lp.const 2 (volume.restrict Ω) c) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_const 2 (volume.restrict Ω) (c : ℂ),
      Complex.ofRealCLM.coeFn_compLp (Lp.const 2 (volume.restrict Ω) c),
      Lp.coeFn_const 2 (volume.restrict Ω) c] with x hx hy hz
    simp only [hx, hy, hz, Complex.ofRealCLM_apply, Function.const_apply]
  have h := tendsto_inner_rescaleLp_complex hΩ hΩm ε hε hε1 ht
    (Complex.ofRealCLM.compLp u) (Complex.ofRealCLM.compLp g)
  simp_rw [rescaleLp_compLp, hmean, hconst] at h
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  change Tendsto (fun j ↦
    (⟪Complex.ofRealCLM.compLp g,
      Complex.ofRealCLM.compLp (rescaleLp hΩ (ε j) (hε j) (hε1 j) u)⟫_ℂ).re)
    l (𝓝 (⟪Complex.ofRealCLM.compLp g,
      Complex.ofRealCLM.compLp
        (Lp.const 2 (volume.restrict Ω) (∫ x, u x ∂cellMeasure n))⟫_ℂ).re) at hr
  simpa only [hinner] using hr

/-- Periodic real L² functions converge weakly in local L² to their cell mean. -/
theorem tendsto_weak_rescaleLp_real (u : Lp ℝ 2 (cellMeasure n)) :
    Tendsto (fun j ↦ toWeakSpace ℝ (Lp ℝ 2 (volume.restrict Ω))
      (rescaleLp hΩ (ε j) (hε j) (hε1 j) u)) l
      (𝓝 (toWeakSpace ℝ (Lp ℝ 2 (volume.restrict Ω))
        (Lp.const 2 (volume.restrict Ω) (∫ x, u x ∂cellMeasure n)))) := by
  have hinj : Function.Injective (topDualPairing ℝ (Lp ℝ 2 (volume.restrict Ω))).flip := by
    intro x y h
    apply ext_inner_left ℝ
    intro v
    exact DFunLike.congr_fun h (innerSL ℝ v)
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hinj).mpr
  intro φ
  let v := (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume.restrict Ω))).symm φ
  change Tendsto (fun j ↦ φ (rescaleLp hΩ (ε j) (hε j) (hε1 j) u)) l
    (𝓝 (φ (Lp.const 2 (volume.restrict Ω) (∫ x, u x ∂cellMeasure n))))
  simpa only [v, InnerProductSpace.toDual_symm_apply] using
    tendsto_inner_rescaleLp_real hΩ hΩm ε hε hε1 ht u v

/-- Periodic Euclidean L² fields converge to their vector cell mean in every local pairing. -/
theorem tendsto_inner_rescaleLp_euclidean {m : ℕ} (u : Lp (ℝ^m) 2 (cellMeasure n))
    (g : Lp (ℝ^m) 2 (volume.restrict Ω)) :
    Tendsto (fun j ↦ ⟪g, rescaleLp hΩ (ε j) (hε j) (hε1 j) u⟫_ℝ)
      l (𝓝 ⟪g, Lp.const 2 (volume.restrict Ω) (∫ x, u x ∂cellMeasure n)⟫_ℝ) := by
  let P (i : Fin m) : (ℝ^m) →L[ℝ] ℝ := EuclideanSpace.proj i
  have hpair (v w : Lp (ℝ^m) 2 (volume.restrict Ω)) :
      ⟪v, w⟫_ℝ = ∑ i, ⟪(P i).compLp v, (P i).compLp w⟫_ℝ := by
    calc
      _ = ⟪Lp.euclideanTuple (fun i ↦ (P i).compLp v),
          Lp.euclideanTuple (fun i ↦ (P i).compLp w)⟫_ℝ := by
        have hv : Lp.euclideanTuple (fun i ↦ (P i).compLp v) = v :=
          Lp.euclideanTuple_coordinates v
        have hw : Lp.euclideanTuple (fun i ↦ (P i).compLp w) = w :=
          Lp.euclideanTuple_coordinates w
        rw [hv, hw]
      _ = _ := Lp.inner_euclideanTuple _ _
  have hmean (i : Fin m) :
      (∫ x, (P i).compLp u x ∂cellMeasure n) = P i (∫ x, u x ∂cellMeasure n) := by
    rw [integral_congr_ae ((P i).coeFn_compLp u)]
    exact (P i).integral_comp_comm ((Lp.memLp u).integrable (by norm_num))
  have hconst (v : ℝ^m) (i : Fin m) :
      (P i).compLp (Lp.const 2 (volume.restrict Ω) v) =
        Lp.const 2 (volume.restrict Ω) (P i v) := by
    apply Lp.ext
    filter_upwards [(P i).coeFn_compLp (Lp.const 2 (volume.restrict Ω) v),
      Lp.coeFn_const 2 (volume.restrict Ω) v,
      Lp.coeFn_const 2 (volume.restrict Ω) (P i v)] with x hx hy hz
    exact hx.trans ((congrArg (P i) hy).trans hz.symm)
  simp_rw [hpair, ← rescaleLp_compLp, hconst, ← hmean]
  exact tendsto_finsetSum _ fun i _ ↦
    tendsto_inner_rescaleLp_real hΩ hΩm ε hε hε1 ht ((P i).compLp u) ((P i).compLp g)

/-- Periodic Euclidean L² fields converge weakly to their actual normalized cell integral. -/
theorem tendsto_weak_rescaleLp_euclidean {m : ℕ} (u : Lp (ℝ^m) 2 (cellMeasure n)) :
    Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^m) 2 (volume.restrict Ω))
      (rescaleLp hΩ (ε j) (hε j) (hε1 j) u)) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^m) 2 (volume.restrict Ω))
        (Lp.const 2 (volume.restrict Ω) (∫ x, u x ∂cellMeasure n)))) := by
  have hinj : Function.Injective
      (topDualPairing ℝ (Lp (ℝ^m) 2 (volume.restrict Ω))).flip := by
    intro x y h
    apply ext_inner_left ℝ
    intro v
    exact DFunLike.congr_fun h (innerSL ℝ v)
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hinj).mpr
  intro φ
  let v := (InnerProductSpace.toDual ℝ (Lp (ℝ^m) 2 (volume.restrict Ω))).symm φ
  change Tendsto (fun j ↦ φ (rescaleLp hΩ (ε j) (hε j) (hε1 j) u)) l
    (𝓝 (φ (Lp.const 2 (volume.restrict Ω) (∫ x, u x ∂cellMeasure n))))
  simpa only [v, InnerProductSpace.toDual_symm_apply] using
    tendsto_inner_rescaleLp_euclidean hΩ hΩm ε hε hε1 ht u v

end PDE.Analysis.PeriodicAveraging
