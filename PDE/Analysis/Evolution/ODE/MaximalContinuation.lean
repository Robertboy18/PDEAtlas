/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Continuation past a finite endpoint

An integral curve of an autonomous `C¹` vector field can be continued past a
finite right endpoint whenever the curve has a limit in the Banach state
space.  The proof first recovers the missing left derivative at the endpoint,
uses Picard–Lindelöf to start a local solution there, and then glues the two
curves.

The Cauchy formulation is convenient in PDE applications: an a priori estimate
often proves that the trajectory is Cauchy as time approaches the endpoint.
Completeness of the state space supplies the limiting state required by the
continuation theorem.

Integrability of the velocity also suffices. The fundamental theorem of
calculus identifies each compact prefix with a Bochner integral; continuity
of the integral at the terminal time supplies the limit without a separate
Cauchy hypothesis.
-/

@[expose] public section

noncomputable section


open Filter Set
open scoped Topology

namespace PDE.Analysis.Evolution

section AutonomousContinuation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
Continue an integral curve past a finite right endpoint at which it has a
state-space limit and a local solution can be started.

The returned curve agrees with the original one on `(a, b)` and solves the ODE
on a strictly larger interval `(a, c)`.
-/
theorem exists_right_extension_of_tendsto_of_local
    {f : E → E} {u localCurve : ℝ → E} {a b ε : ℝ} {x : E}
    (hab : a < b)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (f (u t)) t)
    (hulim : Tendsto u (𝓝[<] b) (𝓝 x))
    (hf : ContinuousAt f x)
    (hε : 0 < ε)
    (hlocal_b : localCurve b = x)
    (hlocal : ∀ t ∈ Ioo (b - ε) (b + ε),
      HasDerivAt localCurve (f (localCurve t)) t) :
    ∃ c > b, ∃ v : ℝ → E,
      (∀ t ∈ Ioo a b, v t = u t) ∧
      ∀ t ∈ Ioo a c, HasDerivAt v (f (v t)) t := by
  let uLeft : ℝ → E := fun t ↦ if t < b then u t else x
  have huLeft_eq (t : ℝ) (ht : t < b) : uLeft t = u t := by
    simp [uLeft, ht]
  have huLeft_b : uLeft b = x := by
    simp [uLeft]
  have huLeft_deriv (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt uLeft (f (u t)) t := by
    have heq : uLeft =ᶠ[𝓝 t] u := by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      exact huLeft_eq s hs
    exact (hu t ht).congr_of_eventuallyEq heq
  have huLeft_diff : DifferentiableOn ℝ uLeft (Ioo a b) := by
    intro t ht
    exact (huLeft_deriv t ht).differentiableAt.differentiableWithinAt
  have huLeft_cont : ContinuousWithinAt uLeft (Ioo a b) b := by
    change Tendsto uLeft (𝓝[Ioo a b] b) (𝓝 (uLeft b))
    rw [huLeft_b]
    apply (hulim.mono_left (nhdsWithin_mono b Ioo_subset_Iio_self)).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (huLeft_eq t ht.2).symm
  have hderiv_lim : Tendsto (fun t ↦ deriv uLeft t) (𝓝[<] b) (𝓝 (f x)) := by
    have hfield_lim : Tendsto (fun t ↦ f (u t)) (𝓝[<] b) (𝓝 (f x)) :=
      hf.tendsto.comp hulim
    apply hfield_lim.congr'
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hab),
      self_mem_nhdsWithin] with t hat htb
    exact (huLeft_deriv t ⟨hat, htb⟩).deriv.symm
  have hleft : HasDerivWithinAt uLeft (f x) (Iic b) b :=
    hasDerivWithinAt_Iic_of_tendsto_deriv huLeft_diff huLeft_cont
      (Ioo_mem_nhdsLT hab) hderiv_lim
  let v : ℝ → E := fun t ↦ if t ≤ b then uLeft t else localCurve t
  have hv_left (t : ℝ) (ht : t ≤ b) : v t = uLeft t := by
    simp [v, ht]
  have hv_right (t : ℝ) (ht : b ≤ t) : v t = localCurve t := by
    rcases ht.eq_or_lt with rfl | hbt
    · simp [v, huLeft_b, hlocal_b]
    · simp [v, not_le_of_gt hbt]
  refine ⟨b + ε, by linarith, v, ?_, ?_⟩
  · intro t ht
    rw [hv_left t ht.2.le, huLeft_eq t ht.2]
  · intro t ht
    rcases lt_trichotomy t b with htb | htb | hbt
    · have heq : v =ᶠ[𝓝 t] uLeft := by
        filter_upwards [Iio_mem_nhds htb] with s hs
        exact hv_left s hs.le
      rw [hv_left t htb.le, huLeft_eq t htb]
      exact (huLeft_deriv t ⟨ht.1, htb⟩).congr_of_eventuallyEq heq
    · subst t
      have hleft' : HasDerivWithinAt v (f (v b)) (Iic b) b := by
        rw [hv_left b le_rfl, huLeft_b]
        exact hleft.congr_of_mem (fun t ht ↦ hv_left t ht) (mem_Iic.mpr le_rfl)
      have hlocal_deriv : HasDerivAt localCurve (f (localCurve b)) b :=
        hlocal b (by constructor <;> linarith)
      have hright : HasDerivWithinAt v (f (v b)) (Ici b) b := by
        rw [hv_right b le_rfl]
        exact hlocal_deriv.hasDerivWithinAt.congr_of_mem
          (fun t ht ↦ hv_right t ht) (mem_Ici.mpr le_rfl)
      rw [← hasDerivWithinAt_univ, ← Iic_union_Ici]
      exact hleft'.union hright
    · have heq : v =ᶠ[𝓝 t] localCurve := by
        filter_upwards [Ioi_mem_nhds hbt] with s hs
        exact hv_right s hs.le
      have htlocal : t ∈ Ioo (b - ε) (b + ε) := ⟨by linarith, ht.2⟩
      rw [hv_right t hbt.le]
      exact (hlocal t htlocal).congr_of_eventuallyEq heq

/--
Continue an integral curve of an autonomous `C¹` vector field past a finite
right endpoint at which the curve has a state-space limit.

Local existence is supplied by Mathlib's Picard–Lindelöf theorem; the gluing
argument is `exists_right_extension_of_tendsto_of_local`.
-/
theorem exists_right_extension_of_tendsto
    [CompleteSpace E]
    {f : E → E} {u : ℝ → E} {a b : ℝ} {x : E}
    (hab : a < b)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (f (u t)) t)
    (hulim : Tendsto u (𝓝[<] b) (𝓝 x))
    (hf : ContDiffAt ℝ 1 f x) :
    ∃ c > b, ∃ v : ℝ → E,
      (∀ t ∈ Ioo a b, v t = u t) ∧
      ∀ t ∈ Ioo a c, HasDerivAt v (f (v t)) t := by
  obtain ⟨localCurve, hlocal_b, ε, hε, hlocal⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ b
  exact exists_right_extension_of_tendsto_of_local hab hu hulim hf.continuousAt hε
    hlocal_b hlocal

/--
A Cauchy trajectory approaching a finite right endpoint admits a strict right
extension for an autonomous `C¹` vector field. Completeness of `E` supplies the
limit at the endpoint.
-/
theorem exists_right_extension_of_cauchy
    [CompleteSpace E]
    {f : E → E} {u : ℝ → E} {a b : ℝ}
    (hab : a < b)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (f (u t)) t)
    (huc : Cauchy (map u (𝓝[<] b)))
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∃ c > b, ∃ v : ℝ → E,
      (∀ t ∈ Ioo a b, v t = u t) ∧
      ∀ t ∈ Ioo a c, HasDerivAt v (f (v t)) t := by
  obtain ⟨x, hx⟩ := cauchy_map_iff_exists_tendsto.mp huc
  exact exists_right_extension_of_tendsto hab hu hx (hf x)

/-- Integrable velocity prevents a finite endpoint of an autonomous `C¹` ODE
from being maximal. The extension agrees with the whole original trajectory
on `(a, b)` and solves the equation past `b`.

No value or continuity of the supplied curve at `b` is required. Its limiting
state is obtained from an interior state and the integral of the velocity
up to `b`, and Picard–Lindelöf starts a new solution from that limit. -/
theorem exists_right_extension_of_integrableOn
    [CompleteSpace E]
    {f : E → E} {u : ℝ → E} {a b : ℝ}
    (hab : a < b)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (f (u t)) t)
    (hint : MeasureTheory.IntegrableOn (fun t ↦ f (u t)) (Ioo a b))
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∃ c > b, ∃ v : ℝ → E,
      (∀ t ∈ Ioo a b, v t = u t) ∧
      ∀ t ∈ Ioo a c, HasDerivAt v (f (v t)) t := by
  obtain ⟨s, has, hsb⟩ := exists_between hab
  have hint_sb : IntervalIntegrable (fun t ↦ f (u t)) MeasureTheory.volume s b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hsb.le).mpr
      (hint.mono_set (Ioo_subset_Ioo has.le le_rfl))
  have hprimitive : ContinuousOn (fun t ↦ u s + ∫ r in s..t, f (u r)) (Icc s b) := by
    have hcont : ContinuousOn (fun t ↦ ∫ r in s..t, f (u r)) (Icc s b) := by
      simpa only [uIcc_of_le hsb.le] using
        intervalIntegral.continuousOn_primitive_interval' hint_sb left_mem_uIcc
    exact hcont.const_add (u s)
  have hlim : Tendsto (fun t ↦ u s + ∫ r in s..t, f (u r))
      (𝓝[<] b) (𝓝 (u s + ∫ r in s..b, f (u r))) := by
    apply (hprimitive b ⟨hsb.le, le_rfl⟩).mono_of_mem_nhdsWithin
    filter_upwards [Ioo_mem_nhdsLT hsb] with t ht
    exact ⟨ht.1.le, ht.2.le⟩
  have hulim : Tendsto u (𝓝[<] b) (𝓝 (u s + ∫ r in s..b, f (u r))) := by
    apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsLT hsb] with t ht
    have hsub : uIcc s t ⊆ Ioo a b := by
      rw [uIcc_of_le ht.1.le]
      intro r hr
      exact ⟨has.trans_le hr.1, hr.2.trans_lt ht.2⟩
    have hint_st : IntervalIntegrable (fun r ↦ f (u r)) MeasureTheory.volume s t :=
      hint_sb.mono_set (uIcc_subset_uIcc left_mem_uIcc
        (by simpa only [uIcc_of_le hsb.le] using ⟨ht.1.le, ht.2.le⟩))
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr ↦ hu r (hsub hr)) hint_st
    rw [heq, add_sub_cancel]
  exact exists_right_extension_of_tendsto hab hu hulim (hf _)

end AutonomousContinuation

end PDE.Analysis.Evolution
