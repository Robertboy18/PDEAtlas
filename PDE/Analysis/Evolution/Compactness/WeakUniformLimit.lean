/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Passing bounded spatial tests through a uniform limit

The time-dependent functionals below need not be strongly measurable as operator-valued
maps. Measurability of their scalar evaluations on the approximating states suffices.
The limit evaluation is measurable by sequential convergence, and the uniform bounds
then give integrability and convergence of its time integral.

The second lemma obtains those measurable evaluations from a.e. evolution equations.
The forcing term passes through the continuous functional on Bochner L2.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace PDE.Analysis.Evolution

section Normed

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {μ : Measure α}

/-- Bounded linear spatial tests pass to a pointwise a.e. limit of uniformly bounded states.
Only their evaluations on the approximants are assumed measurable. The conclusion includes
integrability of the limiting evaluation; a norm bound alone would not imply it. -/
theorem integrable_and_tendsto_integral_linear_tests
    (B : α → H →L[ℝ] ℝ) {u : ℕ → α → H} {v : α → H}
    {M K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ᵐ t ∂μ, ‖B t‖ ≤ K)
    (hu : ∀ k, ∀ᵐ t ∂μ, ‖u k t‖ ≤ M)
    (hmeas : ∀ k, AEStronglyMeasurable (fun t ↦ B t (u k t)) μ)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun k ↦ u k t) atTop (𝓝 (v t)))
    {τ : α → ℝ} (hτ : Integrable τ μ) :
    Integrable (fun t ↦ B t (v t) * τ t) μ ∧
      Tendsto (fun k ↦ ∫ t, B t (u k t) * τ t ∂μ) atTop
        (𝓝 (∫ t, B t (v t) * τ t ∂μ)) := by
  have hmeas' (k : ℕ) :
      AEStronglyMeasurable (fun t ↦ B t (u k t) * τ t) μ :=
    (hmeas k).mul hτ.aestronglyMeasurable
  have htendsto : ∀ᵐ t ∂μ, Tendsto (fun k ↦ B t (u k t) * τ t) atTop
      (𝓝 (B t (v t) * τ t)) := by
    filter_upwards [hlim] with t ht
    exact ((B t).continuous.continuousAt.tendsto.comp ht).mul tendsto_const_nhds
  have hbound (k : ℕ) : ∀ᵐ t ∂μ,
      ‖B t (u k t) * τ t‖ ≤ (K * M) * ‖τ t‖ := by
    filter_upwards [hB, hu k] with t hBt hut
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (((B t).le_opNorm _).trans
        (mul_le_mul hBt hut (norm_nonneg _) hK)) (norm_nonneg _)
  have hboundInt : Integrable (fun t ↦ (K * M) * ‖τ t‖) μ :=
    hτ.norm.const_mul _
  have hboundLimit : ∀ᵐ t ∂μ, ‖B t (v t) * τ t‖ ≤ (K * M) * ‖τ t‖ := by
    filter_upwards [htendsto, ae_all_iff.mpr hbound] with t ht hbt
    exact le_of_tendsto ht.norm (Eventually.of_forall hbt)
  exact ⟨hboundInt.mono' (aestronglyMeasurable_of_tendsto_ae atTop hmeas' htendsto)
      hboundLimit,
    tendsto_integral_of_dominated_convergence _ hmeas' hboundInt hbound htendsto⟩

end Normed

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {a b : ℝ}

omit [CompleteSpace H] in
/-- Testing an absolutely continuous evolution gives its initial-value weak
identity. The scalar spatial term is measurable and integrable because it equals the
pairing of the L2 velocity minus the L2 forcing with the fixed test. -/
theorem weak_identity_of_ac_velocity
    (hab : a ≤ b) {z g f : ℝ → H} (v : H) (B : ℝ → H →L[ℝ] ℝ)
    (hz : AbsolutelyContinuousOnInterval z a b)
    (hg : MemLp g 2 (volume.restrict (Ioc a b)))
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt z (g t) t)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ⟪g t, v⟫_ℝ = B t (z t) + ⟪f t, v⟫_ℝ)
    (τ : TimeTest a b) :
    AEStronglyMeasurable (fun t ↦ B t (z t)) (volume.restrict (Ioc a b)) ∧
      Integrable (fun t ↦ B t (z t) * τ.toFun t) (volume.restrict (Ioc a b)) ∧
      -(∫ t in Ioc a b, ⟪z t, v⟫_ℝ * τ.derivFun t) =
        (∫ t in Ioc a b, B t (z t) * τ.toFun t) +
          (∫ t in Ioc a b, ⟪f t, v⟫_ℝ * τ.toFun t) +
            ⟪z a, v⟫_ℝ * τ.toFun a := by
  have hpair : (fun t ↦ B t (z t)) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ ⟪g t, v⟫_ℝ - ⟪f t, v⟫_ℝ := by
    filter_upwards [heq] with t ht
    exact eq_sub_iff_add_eq.mpr ht.symm
  have hBp : MemLp (fun t ↦ B t (z t)) 2 (volume.restrict (Ioc a b)) :=
    MemLp.ae_eq hpair.symm ((hg.inner_const v).sub (hf.inner_const v))
  have hBi : Integrable (fun t ↦ B t (z t) * τ.toFun t)
      (volume.restrict (Ioc a b)) := hBp.integrable_mul τ.memLp
  have hFi : Integrable (fun t ↦ ⟪f t, v⟫_ℝ * τ.toFun t)
      (volume.restrict (Ioc a b)) := (hf.inner_const v).integrable_mul τ.memLp
  refine ⟨hBp.aestronglyMeasurable, hBi, ?_⟩
  have hparts := τ.integrationByParts_inner hab v hz hderiv
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab] at hparts
  have hsplit :
      (∫ t in Ioc a b, ⟪g t, v⟫_ℝ * τ.toFun t) =
        (∫ t in Ioc a b, B t (z t) * τ.toFun t) +
          ∫ t in Ioc a b, ⟪f t, v⟫_ℝ * τ.toFun t := by
    rw [← integral_add hBi hFi]
    apply integral_congr_ae
    filter_upwards [heq] with t ht
    rw [ht, add_mul]
  rwa [hsplit] at hparts

omit [CompleteSpace H] in
/-- Strong Bochner L2 convergence passes the forcing term against an endpoint time test.
Continuity comes from the time-test functional; no a.e. subsequence is chosen. -/
theorem tendsto_forcing_timeTest
    {f : ℕ → Lp H 2 (volume.restrict (Ioc a b))}
    {f₀ : Lp H 2 (volume.restrict (Ioc a b))}
    (hf : Tendsto f atTop (𝓝 f₀)) (v : H) (τ : TimeTest a b) :
    Tendsto (fun k ↦ ∫ t in Ioc a b, ⟪f k t, v⟫_ℝ * τ.toFun t) atTop
      (𝓝 (∫ t in Ioc a b, ⟪f₀ t, v⟫_ℝ * τ.toFun t)) := by
  have heq (w : Lp H 2 (volume.restrict (Ioc a b))) :
      timeTestFunctional v τ.toLp w =
        ∫ t in Ioc a b, ⟪w t, v⟫_ℝ * τ.toFun t := by
    rw [timeTestFunctional_apply]
    apply integral_congr_ae
    filter_upwards [τ.memLp.coeFn_toLp] with t ht
    rw [show τ.toLp t = τ.toFun t from ht]
  simpa only [Function.comp_def, heq] using
    (timeTestFunctional v τ.toLp).continuous.continuousAt.tendsto.comp hf

end Hilbert

end PDE.Analysis.Evolution
