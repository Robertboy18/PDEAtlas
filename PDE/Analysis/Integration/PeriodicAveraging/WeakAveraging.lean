/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.FourierRescaling
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Weak averaging in local L²

Fourier modes average to their constant mode after periodic rescaling.
The uniform operator bound extends this convergence by density to every
periodic square-integrable function, tested against every local L² function.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter UnitAddTorus
open scoped ENNReal NNReal Topology InnerProductSpace ComplexConjugate

namespace PDE.Analysis.PeriodicAveraging

/-- The zero Fourier mode is the constant function one in the periodic L² space. -/
theorem mFourierLp_zero_eq_const {n : ℕ} :
    mFourierLp 2 (0 : Fin n → ℤ) = Lp.const 2 (cellMeasure n) (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [coeFn_mFourierLp 2 (0 : Fin n → ℤ),
    Lp.coeFn_const 2 (cellMeasure n) (1 : ℂ)] with x hx hy
  simp only [mFourier_zero, ContinuousMap.one_apply] at hx
  exact hx.trans hy.symm

/-- Pairing with the zero Fourier mode computes the normalized cell integral. -/
theorem inner_mFourierLp_zero {n : ℕ} (u : Lp ℂ 2 (cellMeasure n)) :
    ⟪mFourierLp 2 (0 : Fin n → ℤ), u⟫_ℂ = ∫ x, u x ∂cellMeasure n := by
  change (∫ x, ⟪mFourierLp 2 (0 : Fin n → ℤ) x, u x⟫_ℂ ∂cellMeasure n) = _
  apply integral_congr_ae
  filter_upwards [coeFn_mFourierLp 2 (0 : Fin n → ℤ)] with x hx
  have hz : mFourierLp 2 (0 : Fin n → ℤ) x = 1 := by
    simpa only [mFourier_zero, ContinuousMap.one_apply] using hx
  change u x * conj (mFourierLp 2 (0 : Fin n → ℤ) x) = u x
  calc
    _ = u x * conj (1 : ℂ) := congrArg (fun z : ℂ ↦ u x * conj z) hz
    _ = _ := by simp

variable {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω)

include hΩm

/-- Pairing a rescaled Fourier mode with a local L² function is a plane-wave integral. -/
theorem inner_rescaleLp_mFourier (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (k : Fin n → ℤ) (g : Lp ℂ 2 (volume.restrict Ω)) :
    ⟪g, rescaleLp hΩ ε hε hε1 (mFourierLp 2 k)⟫_ℂ =
      ∫ x : ℝ^n, mFourier k (toTorus n (ε⁻¹ • x)) *
        Ω.indicator (fun x ↦ conj (g x)) x := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in Ω, mFourier k (toTorus n (ε⁻¹ • x)) * conj (g x) := by
      apply integral_congr_ae
      filter_upwards [rescaleLp_ae hΩ ε hε hε1 (mFourierLp 2 k),
        ae_restrict_of_ae ((quasiMeasurePreserving_toTorus_smul n ε⁻¹
          (inv_ne_zero hε.ne')).ae_eq_comp (coeFn_mFourierLp 2 k))] with x hx hy
      change mFourierLp 2 k (toTorus n (ε⁻¹ • x)) =
        mFourier k (toTorus n (ε⁻¹ • x)) at hy
      exact congrArg (fun z : ℂ ↦ z * conj (g x)) (hx.trans hy)
    _ = _ := by
      rw [← integral_indicator hΩm]
      congr 1
      funext x
      by_cases hx : x ∈ Ω <;> simp [hx]

/-- Every periodic complex L² function averages to its cell mean against all local L² tests. -/
theorem tendsto_inner_rescaleLp_complex [IsFiniteMeasure (volume.restrict Ω)]
    {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (u : Lp ℂ 2 (cellMeasure n))
    (g : Lp ℂ 2 (volume.restrict Ω)) :
    Tendsto (fun j ↦ ⟪g, rescaleLp hΩ (ε j) (hε j) (hε1 j) u⟫_ℂ)
      l (𝓝 ⟪g, Lp.const 2 (volume.restrict Ω) (∫ x, u x ∂cellMeasure n)⟫_ℂ) := by
  classical
  let R (j : ι) : Lp ℂ 2 (cellMeasure n) →L[ℂ] Lp ℂ 2 (volume.restrict Ω) :=
    { toFun := rescaleLp hΩ (ε j) (hε j) (hε1 j)
      map_add' := map_add _
      map_smul' := fun c v ↦ rescaleLp_smul hΩ (ε j) (hε j) (hε1 j) c v
      cont := (rescaleLp hΩ (ε j) (hε j) (hε1 j)).continuous }
  let F (j : ι) := (innerSL ℂ g).comp (R j)
  let M : Lp ℂ 2 (cellMeasure n) →L[ℂ] ℂ :=
    innerSL ℂ (mFourierLp 2 (0 : Fin n → ℤ))
  let T := (innerSL ℂ g).comp ((Lp.constL 2 (volume.restrict Ω) ℂ).comp M)
  let S : Submodule ℂ (Lp ℂ 2 (cellMeasure n)) :=
    { carrier := {v | Tendsto (fun j ↦ F j v) l (𝓝 (T v))}
      zero_mem' := by
        change Tendsto (fun j ↦ F j 0) l (𝓝 (T 0))
        simpa only [map_zero] using (tendsto_const_nhds (x := (0 : ℂ)))
      add_mem' := by
        intro v w hv hw
        change Tendsto (fun j ↦ F j (v + w)) l (𝓝 (T (v + w)))
        simpa only [map_add] using hv.add hw
      smul_mem' := by
        intro c v hv
        change Tendsto (fun j ↦ F j (c • v)) l (𝓝 (T (c • v)))
        simpa only [map_smul] using hv.const_smul c }
  obtain ⟨C, hC, hbound⟩ := exists_norm_rescaleLp_le (E := ℂ) (p := 2) hΩ
  let K : ℝ≥0 := ⟨‖g‖ * C, mul_nonneg (norm_nonneg _) hC⟩
  have hLip (j : ι) : LipschitzWith K (F j) := by
    apply ContinuousLinearMap.lipschitzWith_of_opNorm_le
    apply (F j).opNorm_le_bound K.property
    intro v
    calc
      ‖F j v‖ ≤ ‖g‖ * ‖rescaleLp hΩ (ε j) (hε j) (hε1 j) v‖ :=
        norm_inner_le_norm g (rescaleLp hΩ (ε j) (hε j) (hε1 j) v)
      _ ≤ ‖g‖ * (C * ‖v‖) :=
        mul_le_mul_of_nonneg_left (hbound _ _ _ v) (norm_nonneg _)
      _ = (K : ℝ) * ‖v‖ := (mul_assoc _ _ _).symm
  have hclosed : IsClosed (S : Set (Lp ℂ 2 (cellMeasure n))) :=
    (LipschitzWith.uniformEquicontinuous (fun j ↦ F j) K hLip).equicontinuous
      |>.isClosed_setOfPred_tendsto T.continuous
  have hmodes : Submodule.span ℂ (range (mFourierLp (d := Fin n) 2)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change Tendsto (fun j ↦ ⟪g, rescaleLp hΩ (ε j) (hε j) (hε1 j)
      (mFourierLp 2 k)⟫_ℂ) l
      (𝓝 ⟪g, Lp.const 2 (volume.restrict Ω)
        ⟪mFourierLp 2 (0 : Fin n → ℤ), mFourierLp 2 k⟫_ℂ⟫_ℂ)
    by_cases hk : k = 0
    · subst k
      have hz : ⟪mFourierLp 2 (0 : Fin n → ℤ), mFourierLp 2 (0 : Fin n → ℤ)⟫_ℂ = 1 :=
        by simpa using (orthonormal_iff_ite.mp orthonormal_mFourier
          (0 : Fin n → ℤ) (0 : Fin n → ℤ))
      rw [hz]
      simp only [mFourierLp_zero_eq_const, rescaleLp_const]
      exact tendsto_const_nhds
    · rw [orthonormal_mFourier.inner_eq_zero (Ne.symm hk), map_zero, inner_zero_right]
      simp_rw [inner_rescaleLp_mFourier hΩ hΩm]
      exact tendsto_integral_mFourier_rescale_mul k hk
        (Ω.indicator (fun x ↦ conj (g x))) ε hε ht
  have hall : (⊤ : Submodule ℂ (Lp ℂ 2 (cellMeasure n))) ≤ S := by
    have hdense : (Submodule.span ℂ
        (range (mFourierLp (d := Fin n) 2) : Set (Lp ℂ 2 (cellMeasure n)))).topologicalClosure =
        ⊤ := span_mFourierLp_closure_eq_top (p := 2) (by simp)
    rw [← hdense]
    exact Submodule.topologicalClosure_minimal _ hmodes hclosed
  have hu := hall (Submodule.mem_top (x := u))
  change Tendsto (fun j ↦ ⟪g, rescaleLp hΩ (ε j) (hε j) (hε1 j) u⟫_ℂ)
    l (𝓝 ⟪g, Lp.const 2 (volume.restrict Ω)
      ⟪mFourierLp 2 (0 : Fin n → ℤ), u⟫_ℂ⟫_ℂ) at hu
  rwa [inner_mFourierLp_zero] at hu

end PDE.Analysis.PeriodicAveraging
