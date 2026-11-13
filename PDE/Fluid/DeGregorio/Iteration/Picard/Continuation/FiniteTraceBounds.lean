/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.FiniteTrace

/-!
# Terminal traces under velocity bounds on the support

A uniform supported H² bound controls vorticity and its first spatial derivative.
Uniform bounds on velocity and its derivative on that compact support therefore
give a common L² majorant for the coupled transport production. Outside the support
both vorticity factors vanish, so no velocity bound at spatial infinity is needed.

These estimates construct the strong terminal L² limit and its supported H² graph.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- Bounds on velocity and its spatial derivative are needed only on the fixed
compact support. Together with H² control they construct an L² majorant for the
transport production, uniform throughout the half-open time interval. -/
theorem exists_transport_majorant_of_supported_h2
    {a T : ℝ} {B C V : NNReal} {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ} {w u : ℝ → ℝ → ℝ}
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hw : ∀ t ∈ Ioo a T, Continuous (fun x ↦ w x t))
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume] fun x ↦ w x t)
    (hvelocity : ∀ t ∈ Ioo a T, ∀ x ∈ K,
      ‖u x t‖ ≤ V ∧ ‖deriv (fun y ↦ u y t) x‖ ≤ C) :
    ∃ M : ℝ → ℝ, MemLp M 2 volume ∧
      ∀ x, ∀ t ∈ Ioo a T,
        ‖deriv (fun y ↦ u y t) x * w x t - u x t * deriv (fun y ↦ w y t) x‖ ≤ M x := by
  classical
  let M := K.indicator (fun _ : ℝ ↦ ((C : ℝ) + V) * (2 * B))
  refine ⟨M, memLp_indicator_const 2 hK.measurableSet.nullMeasurableSet _
    (Or.inr hK.measure_lt_top.ne), ?_⟩
  intro x t ht
  by_cases hx : x ∈ K
  · rw [show M x = ((C : ℝ) + V) * (2 * B) from indicator_of_mem hx _]
    have hb := (contDiff_and_bounds_of_hkBaseBall (hbound t ht).1
      (hw t ht) (hrep t ht)).2 x
    calc
      _ ≤ ‖deriv (fun y ↦ u y t) x * w x t‖ +
          ‖u x t * deriv (fun y ↦ w y t) x‖ := norm_sub_le _ _
      _ = ‖deriv (fun y ↦ u y t) x‖ * ‖w x t‖ +
          ‖u x t‖ * ‖deriv (fun y ↦ w y t) x‖ := by rw [norm_mul, norm_mul]
      _ ≤ (C : ℝ) * (2 * B) + V * (2 * B) :=
        add_le_add (mul_le_mul (hvelocity t ht x hx).2 hb.1 (norm_nonneg _) C.coe_nonneg)
          (mul_le_mul (hvelocity t ht x hx).1 hb.2 (norm_nonneg _) V.coe_nonneg)
      _ = _ := (add_mul _ _ _).symm
  · have hs := tsupport_subset_of_mem_supportedHkBaseBall hK.isClosed
      (hbound t ht) (hw t ht) (hrep t ht)
    have hxw : x ∉ tsupport (fun y ↦ w y t) := fun h ↦ hx (hs h)
    have hwzero : w x t = 0 := by
      by_contra hne
      exact hxw (subset_tsupport _ hne)
    rw [hwzero, deriv_of_notMem_tsupport hxw, mul_zero, mul_zero, sub_self, norm_zero]
    exact le_of_eq (indicator_of_notMem hx _).symm

/-- A coupled trajectory with uniform supported H² control and uniform bounds
on velocity and its derivative on that support has a constructed terminal H²
state. Its continuous representative is the compact C¹ limit of the trajectory. -/
theorem _root_.DeGregorio.IsClassicalSolutionOn.exists_h2_terminal_of_velocity_bounds
    {a T : ℝ} (haT : a < T) {B C V : NNReal} {K : Set ℝ} (hK : IsCompact K)
    {F : ℝ → DerivLp 1 2 univ} {w u : ℝ → ℝ → ℝ}
    (hsol : IsClassicalSolutionOn 1 ⟨w, u⟩ (Ioo a T))
    (hbound : ∀ t ∈ Ioo a T, F t ∈ supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B)
    (hrep : ∀ t ∈ Ioo a T,
      (oneDimensionalPushforwardL2 (F t) : ℝ → ℝ) =ᵐ[volume] fun x ↦ w x t)
    (hvelocity : ∀ t ∈ Ioo a T, ∀ x ∈ K,
      ‖u x t‖ ≤ V ∧ ‖deriv (fun y ↦ u y t) x‖ ≤ C) :
    ∃ (U : W^{2,2}(ℝ^1)) (v : ℝ → ℝ) (L : NNReal),
      ‖U‖ ≤ B ∧
      wkpBaseCoordinateCLM U ∈ supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B ∧
      ContDiff ℝ 1 v ∧ tsupport v ⊆ K ∧
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) : ℝ → ℝ) =ᵐ[volume] v ∧
      Tendsto F (𝓝[<] T) (𝓝 (wkpBaseCoordinateCLM U)) ∧
      (∀ t ∈ Ioo a T, ‖F t - wkpBaseCoordinateCLM U‖ ≤ L * (T - t)) ∧
      ∀ A : Set ℝ, IsCompact A →
        TendstoUniformlyOn (fun t x ↦ w x t) v (𝓝[<] T) A ∧
        TendstoUniformlyOn (fun t ↦ deriv (fun x ↦ w x t)) (deriv v) (𝓝[<] T) A := by
  have hw (t : ℝ) (ht : t ∈ Ioo a T) : Continuous (fun x ↦ w x t) :=
    continuous_iff_continuousAt.mpr fun _ ↦
      (hsol.regularity.vorticity_spatial_differentiableAt ht).continuousAt
  obtain ⟨M, hM, hmajorant⟩ :=
    exists_transport_majorant_of_supported_h2 hK hbound hw hrep hvelocity
  obtain ⟨U, v, hU, hUb, hv, hs, hr, hlim, hrate, hspatial⟩ :=
    hsol.exists_h2_terminal_of_majorant haT hK.isClosed hbound hrep hM
      (Eventually.of_forall hmajorant)
  exact ⟨U, v, ‖hM.toLp M‖₊, hU, hUb, hv, hs, hr, hlim, hrate, hspatial⟩

end DeGregorio.Iteration
