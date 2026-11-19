/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import PDE.Analysis.Calculus.LocalExtrema
import CAS.ExactTactic

/-!
# A minimum principle for a transport inequality on an interval

Let `z` be continuous on `[a, b] × [0, T]` and differentiable in time for `0 < t < T`, and let
`z_t + u z_x + c z ≥ 0` on `[a, b]` for `0 < t < T`, where the velocity `u` vanishes at the two
ends `a` and `b` and `c` is bounded below. If `z ≥ 0` at time `0`, then `z ≥ 0` on
`[a, b] × [0, T]` (`PDE.Analysis.Transport.nonneg_of_transport_ineq`). The theorem holds for all
such `z`, `u` and `c`. Nothing is asked of `z` at the two ends: they are characteristic, because
`u` vanishes there. No differentiability in space is asked either: `z_x` is Mathlib's `deriv`,
which is zero where the derivative does not exist, and at an interior minimum it is zero in both
cases. Fields take space first, then time.

`PDE.Analysis.Transport.strict_invariant_of_first_contact` and
`PDE.Analysis.Transport.rectangle_on_timeSlab` treat transport without a zeroth-order term on the
whole space, with strict barriers and Fréchet derivatives. The statement here is on an interval
with characteristic end points and allows the term `c z` and a source of one sign.

An example is the one-dimensional model of Choi, Hou, Kiselev, Luo, Šverák and Yao for the
axisymmetric Euler equations, `ω_t + u ω_x = θ_x`, `θ_t + u θ_x = 0`, their (1.7). At the start
of their Section 4 the signs `θ_x ≥ 0` and `ω ≥ 0` on the half period `[0, L / 2]` are preserved
by the transport structure of the model. There the velocity of an odd vorticity of period `L`
vanishes at `0` and at `L / 2`, the derivative `z = θ_x` solves `z_t + u z_x + u_x z = 0`, and
the vorticity solves `ω_t + u ω_x = θ_x ≥ 0`.

## How it works

Let `c ≥ -M`. If `z` were negative at a time `t₁ < T`, then `exp (-(M + 1) t) z` would have a
negative minimum over `[a, b] × [0, t₁]`, at a point `(x, t)` with `t > 0`. The minimum in time
gives `z_t ≤ (M + 1) z` there (`IsMinOn.deriv_nonpos_of_left_lt`). The term `u z_x` vanishes
there: by Fermat's theorem if `a < x < b`, and because `u` vanishes if `x` is an end. The
inequality then reads `0 ≤ (M + 1 + c) z < 0`. The time `T` follows by continuity.

## References

* K. Choi, T. Y. Hou, A. Kiselev, G. Luo, V. Šverák, and Y. Yao, "On the finite-time blowup of a
  one-dimensional model for the three-dimensional axisymmetric Euler equations", *Comm. Pure
  Appl. Math.* 70 (2017), no. 11, 2218-2243; numbering of arXiv:1407.4776v2, (1.7) and Section 4,
  the paragraph before Lemma 4.1. <https://doi.org/10.1002/cpa.21697>
  <https://arxiv.org/abs/1407.4776v2>
-/

@[expose] public noncomputable section

open Set Real

namespace PDE.Analysis.Transport

/-- **Minimum principle for a transport inequality.** Let `z` be continuous on
`[a, b] × [0, T]` and differentiable in time for `0 < t < T`. If
`z_t + u z_x + c z ≥ 0` on `[a, b]` for `0 < t < T`, where `u` vanishes at `a` and at `b` and
`c ≥ -M`, and if `z ≥ 0` at time `0`, then `z ≥ 0` on `[a, b] × [0, T]`. -/
theorem nonneg_of_transport_ineq {z u c : ℝ → ℝ → ℝ} {a b T M : ℝ}
    (hz : ContinuousOn (Function.uncurry z) (Icc a b ×ˢ Icc 0 T))
    (hzt : ∀ x ∈ Icc a b, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (z x) t)
    (hua : ∀ t ∈ Ioo 0 T, u a t = 0) (hub : ∀ t ∈ Ioo 0 T, u b t = 0)
    (hc : ∀ x ∈ Icc a b, ∀ t ∈ Ioo 0 T, -M ≤ c x t)
    (hineq : ∀ x ∈ Icc a b, ∀ t ∈ Ioo 0 T,
      0 ≤ deriv (z x) t + u x t * deriv (z · t) x + c x t * z x t)
    (h₀ : ∀ x ∈ Icc a b, 0 ≤ z x 0) :
    ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, 0 ≤ z x t := by
  -- Times before `T` suffice: the value at `T` is a limit of earlier values.
  suffices key : ∀ x ∈ Icc a b, ∀ t ∈ Ico 0 T, 0 ≤ z x t by
    intro x hx t ht
    rcases ht.1.eq_or_lt with rfl | h0
    · exact h₀ x hx
    have hcont : ContinuousOn (z x) (Icc 0 T) :=
      hz.comp (Continuous.prodMk_right x).continuousOn fun s hs ↦ mk_mem_prod hx hs
    refine ContinuousWithinAt.closure_le (f := fun _ ↦ (0 : ℝ)) ?_ continuousWithinAt_const
      ((hcont t ht).mono Ico_subset_Icc_self) (key x hx)
    rw [closure_Ico (h0.trans_le ht.2).ne]
    exact ht
  intro x₁ hx₁ t₁ ht₁
  by_contra hneg
  -- A minimum point `(x', t')` of `exp (-(M + 1) t) z` on `[a, b] × [0, t₁]`.
  have hK : IsCompact (Icc a b ×ˢ Icc 0 t₁) := isCompact_Icc.prod isCompact_Icc
  have hw : ContinuousOn (fun p : ℝ × ℝ ↦ exp (-(M + 1) * p.2) * z p.1 p.2)
      (Icc a b ×ˢ Icc 0 t₁) :=
    (Continuous.continuousOn (by fun_prop)).fun_mul
      (hz.mono (prod_mono_right (Icc_subset_Icc_right ht₁.2.le)))
  obtain ⟨⟨x', t'⟩, hp, hmin⟩ :=
    hK.exists_isMinOn ⟨(x₁, t₁), mk_mem_prod hx₁ (right_mem_Icc.2 ht₁.1)⟩ hw
  have hx' : x' ∈ Icc a b := hp.1
  have ht' : t' ∈ Icc 0 t₁ := hp.2
  have hmin' : ∀ x ∈ Icc a b, ∀ s ∈ Icc 0 t₁,
      exp (-(M + 1) * t') * z x' t' ≤ exp (-(M + 1) * s) * z x s :=
    fun x hx s hs ↦ isMinOn_iff.1 hmin (x, s) (mk_mem_prod hx hs)
  -- There `z < 0`, so the time `t'` is positive.
  have hz' : z x' t' < 0 :=
    neg_of_mul_neg_right ((hmin' x₁ hx₁ t₁ (right_mem_Icc.2 ht₁.1)).trans_lt
      (mul_neg_of_pos_of_neg (Real.exp_pos _) (not_le.1 hneg))) (Real.exp_pos _).le
  have ht'0 : 0 < t' := by
    refine lt_of_le_of_ne ht'.1 fun h ↦ ?_
    rw [← h] at hz'
    exact not_le.2 hz' (h₀ x' hx')
  have ht'T : t' ∈ Ioo 0 T := ⟨ht'0, ht'.2.trans_lt ht₁.2⟩
  -- The minimum in time gives `z_t ≤ (M + 1) z`.
  have htime : deriv (z x') t' ≤ (M + 1) * z x' t' := by
    have hg : HasDerivAt (fun s ↦ exp (-(M + 1) * s) * z x' s)
        (exp (-(M + 1) * t') * (deriv (z x') t' - (M + 1) * z x' t')) t' := by
      cas using [(hzt x' hx' t' ht'T).hasDerivAt]
    have hmin_t : IsMinOn (fun s ↦ exp (-(M + 1) * s) * z x' s) (Icc 0 t') t' :=
      isMinOn_iff.2 fun s hs ↦ hmin' x' hx' s ⟨hs.1, hs.2.trans ht'.2⟩
    have h := hmin_t.deriv_nonpos_of_left_lt ht'0 le_rfl hg.differentiableAt
    rw [hg.deriv] at h
    exact sub_nonpos.1 (nonpos_of_mul_nonpos_right h (Real.exp_pos _))
  -- The transport term vanishes: by Fermat's theorem inside, and because `u = 0` at the ends.
  have hspace : u x' t' * deriv (z · t') x' = 0 := by
    rcases hx'.1.eq_or_lt with rfl | hax
    · rw [hua t' ht'T, zero_mul]
    rcases hx'.2.eq_or_lt with rfl | hxb
    · rw [hub t' ht'T, zero_mul]
    have hmin_x : IsMinOn (z · t') (Icc a b) x' :=
      isMinOn_iff.2 fun x hx ↦ le_of_mul_le_mul_left (hmin' x hx t' ht') (Real.exp_pos _)
    rw [(hmin_x.isLocalMin (Icc_mem_nhds hax hxb)).deriv_eq_zero, mul_zero]
  have hM : 0 < M + 1 + c x' t' := by cas using [hc x' hx' t' ht'T]
  cas using [hineq x' hx' t' ht'T, mul_neg_of_pos_of_neg hM hz']

end PDE.Analysis.Transport
