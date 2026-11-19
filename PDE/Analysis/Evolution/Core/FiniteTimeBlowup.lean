/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Finite-time blowup as an obstruction to continuation

If `‖u‖ → ∞` along a nontrivial filter, then `u` converges to no point along
it. In particular, if `‖u(t)‖ → ∞` as `t → T⁻`, then no function agreeing with
`u` on `t < T` is left-continuous at `T`. The same conclusion holds when the
blowup is observed along a reparametrized time `clock s → T⁻`. A monotone clock
mapping `[t₀, ∞)` onto `[clock t₀, T)` transfers limits as `s → ∞` to left
limits at `T`. Nonvanishing rescaled values supply uniform norm blowup
for scalar or vector-valued bounded continuous states.
-/

@[expose] public section

open Filter Set
open scoped Topology BoundedContinuousFunction

namespace PDE.Analysis.Evolution

/-- A nonzero rescaled value bounds the uniform norm of the original state.
The point may depend on the scale or on time. -/
theorem div_le_norm_of_le_norm_smul_apply
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {state : X →ᵇ E} {A κ : ℝ} {x : X} (hA : 0 < A)
    (hvalue : κ ≤ ‖A • state x‖) : κ / A ≤ ‖state‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA] at hvalue
  rw [div_le_iff₀ hA, mul_comm _ A]
  exact hvalue.trans (mul_le_mul_of_nonneg_left (state.norm_coe_le_norm x) hA.le)

/-- Nonvanishing rescaled values force uniform norm blowup when the inverse
amplitude multiplier grows. No spatial point needs to stay fixed, and the
statement applies to vector-valued states along any sampling filter. -/
theorem norm_tendsto_atTop_of_nonvanishing_rescaling
    {ι X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} {states : ι → X →ᵇ E} {A : ι → ℝ} {κ : ℝ}
    (hA : ∀ᶠ i in l, 0 < A i)
    (hinverse : Tendsto (fun i ↦ (A i)⁻¹) l atTop) (hκ : 0 < κ)
    (hvalue : ∀ᶠ i in l, ∃ x, κ ≤ ‖A i • states i x‖) :
    Tendsto (fun i ↦ ‖states i‖) l atTop := by
  refine tendsto_atTop_mono' l ?_ (hinverse.const_mul_atTop hκ)
  filter_upwards [hA, hvalue] with i hAi hi
  obtain ⟨x, hx⟩ := hi
  simpa only [div_eq_mul_inv] using div_le_norm_of_le_norm_smul_apply hAi hx

/-- A monotone clock covering the whole interval before its lifetime transfers limits
from rescaled time to physical time: if `clock` is monotone on `[t₀, ∞)` with image
`[clock t₀, T)` and `u (clock s) → l` as `s → ∞`, then `u t → l` as `t → T⁻`.
The surjectivity onto `[clock t₀, T)` is needed, since convergence along a single
path approaching `T` does not give a left limit. -/
theorem tendsto_nhdsWithin_of_monotone_clock
    {E : Type*} {l : Filter E} {u : ℝ → E} {clock : ℝ → ℝ}
    {initialTime lifetime : ℝ}
    (hmono : MonotoneOn clock (Ici initialTime))
    (himage : clock '' Ici initialTime = Ico (clock initialTime) lifetime)
    (hu : Tendsto (fun s ↦ u (clock s)) atTop l) :
    Tendsto u (𝓝[<] lifetime) l := by
  rw [Filter.tendsto_def] at hu ⊢
  intro s hs
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hu s hs)
  let b := max initialTime a
  have hb : b ∈ Ici initialTime := show initialTime ≤ max initialTime a from le_max_left _ _
  have hblifetime : clock b < lifetime := by
    have hmem : clock b ∈ clock '' Ici initialTime := ⟨b, hb, rfl⟩
    rw [himage] at hmem
    exact hmem.2
  filter_upwards [Ioo_mem_nhdsLT hblifetime] with t ht
  have htimage : t ∈ clock '' Ici initialTime := by
    rw [himage]
    exact ⟨(hmono (by simp) hb hb).trans ht.1.le, ht.2⟩
  obtain ⟨r, hr, rfl⟩ := htimage
  have hbr : b ≤ r := by
    by_contra h
    exact (not_le_of_gt ht.1) (hmono hr hb (le_of_not_ge h))
  exact ha r ((le_max_right _ _).trans hbr)

/-- A trajectory whose norm tends to infinity cannot converge to a point of
its normed state space. -/
theorem not_tendsto_nhds_of_norm_tendsto_atTop
    {α E : Type*} [NormedAddCommGroup E] {l : Filter α} [l.NeBot]
    {u : α → E} (hu : Tendsto (fun x ↦ ‖u x‖) l atTop) (y : E) :
    ¬Tendsto u l (𝓝 y) := by
  intro huy
  exact not_tendsto_atTop_of_tendsto_nhds huy.norm hu

/-- If a trajectory's norm diverges as time approaches `T` from below, then
no trajectory agreeing with it before `T` can be continuous from the left at
`T`. -/
theorem not_exists_continuous_extension_Iic_of_norm_tendsto_atTop
    {E : Type*} [NormedAddCommGroup E] {u : ℝ → E} {T : ℝ}
    (hu : Tendsto (fun t ↦ ‖u t‖) (𝓝[<] T) atTop) :
    ¬∃ v : ℝ → E, (∀ t < T, v t = u t) ∧ ContinuousWithinAt v (Iic T) T := by
  rintro ⟨v, hvu, hvcont⟩
  apply not_tendsto_nhds_of_norm_tendsto_atTop hu (v T)
  have hvlim : Tendsto v (𝓝[<] T) (𝓝 (v T)) :=
    hvcont.tendsto.mono_left (nhdsWithin_mono T Iio_subset_Iic_self)
  apply hvlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hvu t ht

/-- Norm blowup along any nontrivial path approaching `T` from below rules
out a left-continuous extension at `T`.

This form is useful after a time reparametrization: `clock` may be a physical
time map defined on an auxiliary rescaled-time filter. -/
theorem not_exists_continuous_extension_Iic_of_norm_tendsto_atTop_along
    {α E : Type*} [NormedAddCommGroup E] {l : Filter α} [l.NeBot]
    {u : ℝ → E} {clock : α → ℝ} {T : ℝ}
    (hclock : Tendsto clock l (𝓝[<] T))
    (hu : Tendsto (fun s ↦ ‖u (clock s)‖) l atTop) :
    ¬∃ v : ℝ → E, (∀ t < T, v t = u t) ∧ ContinuousWithinAt v (Iic T) T := by
  rintro ⟨v, hvu, hvcont⟩
  apply not_tendsto_nhds_of_norm_tendsto_atTop hu (v T)
  have hvlim : Tendsto v (𝓝[<] T) (𝓝 (v T)) :=
    hvcont.tendsto.mono_left (nhdsWithin_mono T Iio_subset_Iic_self)
  apply (hvlim.comp hclock).congr'
  filter_upwards [hclock.eventually self_mem_nhdsWithin] with s hs
  exact hvu (clock s) hs

end PDE.Analysis.Evolution
