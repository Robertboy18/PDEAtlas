/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Convergence
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# Comparison of the flows of two fields on the closed half-plane

Two `C²` fields `v, v'` on `[-T, T]` that preserve the closed half-plane, with derivatives at most
`K₁` there, form an `IsFieldPair` when their values differ at time `r` on the closed half-plane by
at most `c₀ Dm |r|` and their derivatives differ there by at most `c₁ φ_A(Dm |r|)`, where
`φ_A(r) = r (1 + log (A / r))` and `Dm` is a nondecreasing majorant with values in `[0, A]`. The
fields are close in the sup norm, but their derivatives only up to a logarithm. Their flow lines and
first variations from the base time `0` then differ by at most `pairFlowConst T K₁ c₀ ∫₀^{|s|} Dm`
and `pairVariationConst T K₂ K₁ c₀ c₁ ∫₀^{|s|} φ_A(Dm)`, forward and backward in time.

The difference of two flow lines solves a linear differential inequality with the coefficient `K₁`
and the forcing `c₀ Dm`, and Grönwall's inequality gives the first bound. The difference of the
first variations has the forcing `K₂ ‖X - X'‖ + c₁ φ_A(Dm)`, where the first term comes from the
second derivative of one field along two different flow lines.

## Main results

* `IsFieldPair`: the class of pairs of fields.
* `IsFieldPair.norm_flowOn_sub_le`: the flow lines from the base time `0` differ by at most
  `pairFlowConst T K₁ c₀ · ∫₀^{|s|} Dm`; `IsFieldPair.norm_flowOn_sub_le_forward` and
  `IsFieldPair.norm_flowOn_sub_le_backward` are the two directions of time.
* `IsFieldPair.norm_flowOn_sub_le_majorant`, `IsFieldPair.norm_flowOn_sub_le_osgood`: the same
  difference is at most `pairFlowConst T K₁ c₀ · T · Dm |s|` and at most
  `pairFlowConst T K₁ c₀ · ∫₀^{|s|} φ_A(Dm)`.
* `IsFieldPair.norm_variationOn_sub_le`: the first variations differ by at most
  `pairVariationConst T K₂ K₁ c₀ c₁ · ∫₀^{|s|} φ_A(Dm)`.
* `pairFlowConst`, `pairVariationConst`: the constants `e^{K₁ T} c₀` and
  `e^{2 K₁ T} (K₂ e^{K₁ T} c₀ T + c₁)`.

The fields of two vorticity histories under a velocity law form such a pair, with `c₀ = C 0 0` and
`c₁ = 2 C 0 α`: `Convergence.lean` proves this (`isFieldPair_lawField`) and derives the difference
estimate of the iteration map, and `LocalExistence.lean` uses the two constants. The comparison is
the core of the convergence of the iteration and of the uniqueness of solutions.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal Topology
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport Boussinesq.HalfPlane
open PDE.Analysis (monotoneOn_osgoodModulus_comp)

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- Two `C²` fields on `[-T, T]` preserving the closed half-plane, with derivatives at most `K₁`
there, whose values and derivatives at time `r` differ on the closed half-plane by at most
`c₀ Dm |r|` and `c₁ φ_A(Dm |r|)`, for a nondecreasing majorant `Dm` with values in `[0, A]`. -/
structure IsFieldPair (v v' : ℝ → ℝ^2 → ℝ^2) (Dv Dv' : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2)
    (D2v D2v' : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2) (T : ℝ) (K K₂ : ℝ≥0) (K₁ c₀ c₁ A : ℝ)
    (Dm : ℝ → ℝ) : Prop where
  /-- The time interval is nonempty. -/
  nonneg : 0 ≤ T
  /-- The first field is a `C²` field. -/
  left : IsC2FieldOn v Dv D2v (-T) T K K₂
  /-- The second field is a `C²` field. -/
  right : IsC2FieldOn v' Dv' D2v' (-T) T K K₂
  /-- The flow of the first field preserves the closed half-plane. -/
  mapsTo_left : ∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T, MapsTo (flowOn v (-T) T s t) H̄ H̄
  /-- The flow of the second field preserves the closed half-plane. -/
  mapsTo_right : ∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T, MapsTo (flowOn v' (-T) T s t) H̄ H̄
  /-- The derivative of the first field is at most `K₁` on the closed half-plane. -/
  norm_deriv_left : ∀ r ∈ Icc (-T) T, ∀ y ∈ H̄, ‖Dv r y‖ ≤ K₁
  /-- The derivative of the second field is at most `K₁` on the closed half-plane. -/
  norm_deriv_right : ∀ r ∈ Icc (-T) T, ∀ y ∈ H̄, ‖Dv' r y‖ ≤ K₁
  /-- The constant of the difference of the values is nonnegative. -/
  const_nonneg : 0 ≤ c₀
  /-- The constant of the difference of the derivatives is nonnegative. -/
  deriv_const_nonneg : 0 ≤ c₁
  /-- The Osgood parameter is positive. -/
  modulus_pos : 0 < A
  /-- The majorant is monotone. -/
  monotoneOn : MonotoneOn Dm (Icc 0 T)
  /-- The majorant is nonnegative. -/
  nonneg_majorant : ∀ s ∈ Icc 0 T, 0 ≤ Dm s
  /-- The majorant is at most the Osgood parameter. -/
  le_modulus : ∀ s ∈ Icc 0 T, Dm s ≤ A
  /-- The values of the fields differ by at most `c₀ Dm |r|`. -/
  norm_sub_le : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → ‖v r y - v' r y‖ ≤ c₀ * Dm |r|
  /-- The derivatives of the fields differ by at most `c₁ φ_A(Dm |r|)`. -/
  norm_deriv_sub_le : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 →
    ‖Dv r y - Dv' r y‖ ≤ c₁ * PDE.Analysis.osgoodModulus A (Dm |r|)

/-- The constant `e^{K₁ T} c₀` of the flow comparison. -/
def pairFlowConst (T K₁ c₀ : ℝ) : ℝ :=
  Real.exp (K₁ * T) * c₀

/-- The constant `e^{2 K₁ T} (K₂ e^{K₁ T} c₀ T + c₁)` of the variation comparison. -/
def pairVariationConst (T K₂ K₁ c₀ c₁ : ℝ) : ℝ :=
  Real.exp (2 * K₁ * T) * (K₂ * pairFlowConst T K₁ c₀ * T + c₁)

namespace IsFieldPair

variable {v v' : ℝ → ℝ^2 → ℝ^2} {Dv Dv' : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2}
  {D2v D2v' : ℝ → ℝ^2 → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2} {T : ℝ} {K K₂ : ℝ≥0} {K₁ c₀ c₁ A : ℝ}
  {Dm : ℝ → ℝ}
variable (hp : IsFieldPair v v' Dv Dv' D2v D2v' T K K₂ K₁ c₀ c₁ A Dm)
include hp

/-- The time `0` lies in `[-T, T]`. -/
theorem zero_mem : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith [hp.nonneg], hp.nonneg⟩

/-- The bound of the derivatives is nonnegative. -/
theorem deriv_bound_nonneg : 0 ≤ K₁ :=
  (norm_nonneg _).trans (hp.norm_deriv_left 0 hp.zero_mem 0 (by simp))

/-- The constant of the flow comparison is nonnegative. -/
theorem pairFlowConst_nonneg : 0 ≤ pairFlowConst T K₁ c₀ := by
  have := hp.const_nonneg
  unfold pairFlowConst; positivity

/-- The constant of the variation comparison is nonnegative. -/
theorem pairVariationConst_nonneg : 0 ≤ pairVariationConst T K₂ K₁ c₀ c₁ := by
  have := hp.pairFlowConst_nonneg
  have := hp.nonneg
  have := hp.deriv_const_nonneg
  unfold pairVariationConst; positivity

/-- **Forward comparison of the flow lines** from the base time `0`. -/
theorem norm_flowOn_sub_le_forward {s : ℝ} (hs : s ∈ Icc 0 T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn v (-T) T s 0 x - flowOn v' (-T) T s 0 x‖ ≤
      pairFlowConst T K₁ c₀ * ∫ r in (0)..s, Dm r := by
  have hK₁ := hp.deriv_bound_nonneg
  have hR := hp.const_nonneg
  have hmono : MonotoneOn (fun r ↦ c₀ * Dm r) (Icc 0 T) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left (hp.monotoneOn hr hr' hrr') hR
  have h := hp.left.toIsC1FieldOn.norm_flowOn_sub_flowOn_le_of_invariant hp.right.toIsC1FieldOn
    PDE.Analysis.convex_closedUpperHalfPlane hp.mapsTo_left hp.mapsTo_right hp.norm_deriv_left
    hp.zero_mem hmono (fun r hr ↦ mul_nonneg hR (hp.nonneg_majorant r hr))
    (fun r hr y hy ↦ by
      have h1 := hp.norm_sub_le r ⟨by linarith [hr.1, hp.nonneg], hr.2⟩ y hy
      rwa [abs_of_nonneg hr.1] at h1) hx hs
  rw [intervalIntegral.integral_const_mul] at h
  have hI0 : 0 ≤ ∫ r in (0)..s, Dm r :=
    intervalIntegral.integral_nonneg hs.1 fun r hr ↦ hp.nonneg_majorant r ⟨hr.1, hr.2.trans hs.2⟩
  have he : Real.exp (K₁ * (s - 0)) ≤ Real.exp (K₁ * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hK₁)
  calc _ ≤ Real.exp (K₁ * (s - 0)) * (c₀ * ∫ r in (0)..s, Dm r) := h
    _ ≤ Real.exp (K₁ * T) * (c₀ * ∫ r in (0)..s, Dm r) :=
        mul_le_mul_of_nonneg_right he (mul_nonneg hR hI0)
    _ = pairFlowConst T K₁ c₀ * ∫ r in (0)..s, Dm r := by unfold pairFlowConst; ring

/-- **Backward comparison of the flow lines** from the base time `0`. -/
theorem norm_flowOn_sub_le_backward {s : ℝ} (hs : s ∈ Icc (-T) 0) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn v (-T) T s 0 x - flowOn v' (-T) T s 0 x‖ ≤
      pairFlowConst T K₁ c₀ * ∫ r in (0)..(-s), Dm r := by
  have hK₁ := hp.deriv_bound_nonneg
  have hR := hp.const_nonneg
  have hneg {r : ℝ} (hr : r ∈ Icc (-T) 0) : -r ∈ Icc 0 T :=
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hanti : AntitoneOn (fun r ↦ c₀ * Dm (-r)) (Icc (-T) 0) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left
      (hp.monotoneOn (hneg hr') (hneg hr) (neg_le_neg hrr')) hR
  have h := hp.left.toIsC1FieldOn.norm_flowOn_sub_flowOn_le_of_invariant_left
    hp.right.toIsC1FieldOn PDE.Analysis.convex_closedUpperHalfPlane hp.mapsTo_left
    hp.mapsTo_right hp.norm_deriv_left hp.zero_mem hanti
    (fun r hr ↦ mul_nonneg hR (hp.nonneg_majorant _ (hneg hr)))
    (fun r hr y hy ↦ by
      have h1 := hp.norm_sub_le r ⟨hr.1, by linarith [hr.2, hp.nonneg]⟩ y hy
      rwa [abs_of_nonpos hr.2] at h1) hx hs
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_neg (fun r ↦ Dm r), neg_zero] at h
  have hs' := hneg hs
  have hI0 : 0 ≤ ∫ r in (0)..(-s), Dm r :=
    intervalIntegral.integral_nonneg hs'.1 fun r hr ↦
      hp.nonneg_majorant r ⟨hr.1, hr.2.trans hs'.2⟩
  have he : Real.exp (K₁ * (0 - s)) ≤ Real.exp (K₁ * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hs.1]) hK₁)
  calc _ ≤ Real.exp (K₁ * (0 - s)) * (c₀ * ∫ r in (0)..(-s), Dm r) := h
    _ ≤ Real.exp (K₁ * T) * (c₀ * ∫ r in (0)..(-s), Dm r) :=
        mul_le_mul_of_nonneg_right he (mul_nonneg hR hI0)
    _ = pairFlowConst T K₁ c₀ * ∫ r in (0)..(-s), Dm r := by unfold pairFlowConst; ring

/-- **Comparison of the flow lines** at any time `s ∈ [-T, T]`: on the closed half-plane the flow
lines of the two fields from the base time `0` differ by at most
`pairFlowConst T K₁ c₀ · ∫₀^{|s|} Dm`. It bounds the distance of the particles of two histories
by the distance of the histories. Proof: the forward and the backward comparison,
each by Grönwall's inequality for the difference of the two flow lines. -/
theorem norm_flowOn_sub_le {s : ℝ} (hs : s ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn v (-T) T s 0 x - flowOn v' (-T) T s 0 x‖ ≤
      pairFlowConst T K₁ c₀ * ∫ r in (0)..|s|, Dm r := by
  rcases le_total 0 s with h0 | h0
  · rw [abs_of_nonneg h0]
    exact hp.norm_flowOn_sub_le_forward ⟨h0, hs.2⟩ hx
  · rw [abs_of_nonpos h0]
    exact hp.norm_flowOn_sub_le_backward ⟨hs.1, h0⟩ hx

/-- The flow lines differ at time `s` by at most `pairFlowConst T K₁ c₀ T Dm |s|`. -/
theorem norm_flowOn_sub_le_majorant {s : ℝ} (hs : s ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn v (-T) T s 0 x - flowOn v' (-T) T s 0 x‖ ≤
      pairFlowConst T K₁ c₀ * T * Dm |s| := by
  have hsT : |s| ∈ Icc 0 T := ⟨abs_nonneg s, abs_le.mpr ⟨hs.1, hs.2⟩⟩
  have hI : ∫ r in (0)..|s|, Dm r ≤ Dm |s| * |s| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := |s|)
      (f := Dm) (C := Dm |s|) fun r hr ↦ by
        rw [uIoc_of_le hsT.1] at hr
        have hrT : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.trans hsT.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (hp.nonneg_majorant r hrT)]
        exact hp.monotoneOn hrT hsT hr.2
    rw [sub_zero, abs_abs] at h
    exact (le_abs_self _).trans (by simpa using h)
  have hD := hp.nonneg_majorant _ hsT
  calc _ ≤ pairFlowConst T K₁ c₀ * ∫ r in (0)..|s|, Dm r := hp.norm_flowOn_sub_le hs hx
    _ ≤ pairFlowConst T K₁ c₀ * (Dm |s| * T) :=
        mul_le_mul_of_nonneg_left (hI.trans (mul_le_mul_of_nonneg_left hsT.2 hD))
          hp.pairFlowConst_nonneg
    _ = pairFlowConst T K₁ c₀ * T * Dm |s| := by ring

/-- The integrand of the variation comparison is bounded by the Osgood modulus of the
majorant. -/
theorem forcing_le {q : ℝ} (hq : q ∈ Icc 0 T) :
    (K₂ : ℝ) * (pairFlowConst T K₁ c₀ * T * Dm q) +
        c₁ * PDE.Analysis.osgoodModulus A (Dm q) ≤
      ((K₂ : ℝ) * pairFlowConst T K₁ c₀ * T + c₁) * PDE.Analysis.osgoodModulus A (Dm q) := by
  have hle := PDE.Analysis.le_osgoodModulus (hp.nonneg_majorant q hq) (hp.le_modulus q hq)
  have hc : 0 ≤ (K₂ : ℝ) * pairFlowConst T K₁ c₀ * T :=
    mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) hp.pairFlowConst_nonneg) hp.nonneg
  calc _ = (K₂ : ℝ) * pairFlowConst T K₁ c₀ * T * Dm q +
        c₁ * PDE.Analysis.osgoodModulus A (Dm q) := by ring
    _ ≤ _ := by
        rw [add_mul]
        exact add_le_add_left (mul_le_mul_of_nonneg_left hle hc) _

/-- **Forward comparison of the first variations** from the base time `0`. -/
theorem norm_variationOn_sub_le_forward {s : ℝ} (hs : s ∈ Icc 0 T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖variationOn v Dv (-T) T s 0 x - variationOn v' Dv' (-T) T s 0 x‖ ≤
      pairVariationConst T K₂ K₁ c₀ c₁ *
        ∫ r in (0)..s, PDE.Analysis.osgoodModulus A (Dm r) := by
  have hv := hp.left
  have hv' := hp.right
  have hK₁ := hp.deriv_bound_nonneg
  have hCκ := hp.deriv_const_nonneg
  have hA := hp.modulus_pos
  have hφmono := monotoneOn_osgoodModulus_comp hA hp.monotoneOn hp.nonneg_majorant hp.le_modulus
  have hψ : MonotoneOn (fun q : ℝ ↦ (K₂ : ℝ) * q) (Ici 0) :=
    fun q _ q' _ h ↦ mul_le_mul_of_nonneg_left h K₂.2
  have hDvψ : ∀ r ∈ Icc (-T) T, ∀ y ∈ H̄, ∀ z ∈ H̄,
      ‖Dv r y - Dv r z‖ ≤ (K₂ : ℝ) * ‖y - z‖ :=
    fun r hr y _ z _ ↦ (hv.lipschitzWith_deriv hr).norm_sub_le y z
  have hε₁ : MonotoneOn (fun r ↦ c₁ * PDE.Analysis.osgoodModulus A (Dm r)) (Icc 0 T) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left (hφmono hr hr' hrr') hCκ
  have hDmono : MonotoneOn (fun r ↦ pairFlowConst T K₁ c₀ * T * Dm r) (Icc 0 T) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left (hp.monotoneOn hr hr' hrr')
      (mul_nonneg hp.pairFlowConst_nonneg hp.nonneg)
  have h := hv.toIsC1FieldOn.norm_variationOn_sub_variationOn_le_of_invariant
    hv'.toIsC1FieldOn hp.mapsTo_left hp.mapsTo_right hp.norm_deriv_left hp.norm_deriv_right hψ
    (fun q hq ↦ mul_nonneg K₂.2 hq) hDvψ hp.zero_mem hε₁
    (fun r hr ↦ mul_nonneg hCκ (PDE.Analysis.osgoodModulus_nonneg (hp.nonneg_majorant r hr)
      (hp.le_modulus r hr)))
    (fun r hr y hy ↦ by
      have h1 := hp.norm_deriv_sub_le r ⟨by linarith [hr.1, hp.nonneg], hr.2⟩ y hy
      rwa [abs_of_nonneg hr.1] at h1) hx hDmono
    (fun r hr ↦ by
      have h1 := hp.norm_flowOn_sub_le_majorant (s := r)
        ⟨by linarith [hr.1, hp.nonneg], hr.2⟩ hx
      rwa [abs_of_nonneg hr.1] at h1) hs
  have hint : ∫ r in (0)..s, ((K₂ : ℝ) * (pairFlowConst T K₁ c₀ * T * Dm r) +
        c₁ * PDE.Analysis.osgoodModulus A (Dm r)) ≤
      ((K₂ : ℝ) * pairFlowConst T K₁ c₀ * T + c₁) *
        ∫ r in (0)..s, PDE.Analysis.osgoodModulus A (Dm r) := by
    rw [← intervalIntegral.integral_const_mul]
    have hm2 : MonotoneOn (fun r ↦ (K₂ : ℝ) * (pairFlowConst T K₁ c₀ * T * Dm r) +
        c₁ * PDE.Analysis.osgoodModulus A (Dm r)) (Icc 0 T) :=
      fun r hr r' hr' hrr' ↦ add_le_add (mul_le_mul_of_nonneg_left (hDmono hr hr' hrr') K₂.2)
        (hε₁ hr hr' hrr')
    refine intervalIntegral.integral_mono_on hs.1 (intervalIntegrable_of_monotoneOn hm2 hs)
      ((intervalIntegrable_of_monotoneOn hφmono hs).const_mul _) fun r hr ↦ ?_
    exact hp.forcing_le ⟨hr.1, hr.2.trans hs.2⟩
  have he : Real.exp ((K₁ + K₁) * (s - 0)) ≤ Real.exp (2 * K₁ * T) :=
    Real.exp_le_exp.mpr (by nlinarith [hs.2, hs.1])
  calc _ ≤ _ := h
    _ ≤ Real.exp (2 * K₁ * T) * (((K₂ : ℝ) * pairFlowConst T K₁ c₀ * T + c₁) *
          ∫ r in (0)..s, PDE.Analysis.osgoodModulus A (Dm r)) :=
        mul_le_mul he hint (intervalIntegral.integral_nonneg hs.1 fun r hr ↦
          add_nonneg (mul_nonneg K₂.2 (mul_nonneg (mul_nonneg hp.pairFlowConst_nonneg hp.nonneg)
            (hp.nonneg_majorant r ⟨hr.1, hr.2.trans hs.2⟩)))
            (mul_nonneg hCκ (PDE.Analysis.osgoodModulus_nonneg
              (hp.nonneg_majorant r ⟨hr.1, hr.2.trans hs.2⟩)
              (hp.le_modulus r ⟨hr.1, hr.2.trans hs.2⟩)))) (Real.exp_pos _).le
    _ = _ := by unfold pairVariationConst; ring

/-- **Backward comparison of the first variations** from the base time `0`. -/
theorem norm_variationOn_sub_le_backward {s : ℝ} (hs : s ∈ Icc (-T) 0) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    ‖variationOn v Dv (-T) T s 0 x - variationOn v' Dv' (-T) T s 0 x‖ ≤
      pairVariationConst T K₂ K₁ c₀ c₁ *
        ∫ r in (0)..(-s), PDE.Analysis.osgoodModulus A (Dm r) := by
  have hv := hp.left
  have hv' := hp.right
  have hK₁ := hp.deriv_bound_nonneg
  have hCκ := hp.deriv_const_nonneg
  have hA := hp.modulus_pos
  have hφmono := monotoneOn_osgoodModulus_comp hA hp.monotoneOn hp.nonneg_majorant hp.le_modulus
  have hneg {r : ℝ} (hr : r ∈ Icc (-T) 0) : -r ∈ Icc 0 T :=
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hψ : MonotoneOn (fun q : ℝ ↦ (K₂ : ℝ) * q) (Ici 0) :=
    fun q _ q' _ h ↦ mul_le_mul_of_nonneg_left h K₂.2
  have hDvψ : ∀ r ∈ Icc (-T) T, ∀ y ∈ H̄, ∀ z ∈ H̄,
      ‖Dv r y - Dv r z‖ ≤ (K₂ : ℝ) * ‖y - z‖ :=
    fun r hr y _ z _ ↦ (hv.lipschitzWith_deriv hr).norm_sub_le y z
  have hε₁ : AntitoneOn (fun r ↦ c₁ * PDE.Analysis.osgoodModulus A (Dm (-r))) (Icc (-T) 0) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left
      (hφmono (hneg hr') (hneg hr) (neg_le_neg hrr')) hCκ
  have hDanti : AntitoneOn (fun r ↦ pairFlowConst T K₁ c₀ * T * Dm (-r)) (Icc (-T) 0) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left
      (hp.monotoneOn (hneg hr') (hneg hr) (neg_le_neg hrr'))
      (mul_nonneg hp.pairFlowConst_nonneg hp.nonneg)
  have h := hv.toIsC1FieldOn.norm_variationOn_sub_variationOn_le_of_invariant_left
    hv'.toIsC1FieldOn hp.mapsTo_left hp.mapsTo_right hp.norm_deriv_left hp.norm_deriv_right hψ
    (fun q hq ↦ mul_nonneg K₂.2 hq) hDvψ hp.zero_mem hε₁
    (fun r hr ↦ mul_nonneg hCκ (PDE.Analysis.osgoodModulus_nonneg
      (hp.nonneg_majorant _ (hneg hr)) (hp.le_modulus _ (hneg hr))))
    (fun r hr y hy ↦ by
      have h1 := hp.norm_deriv_sub_le r ⟨hr.1, by linarith [hr.2, hp.nonneg]⟩ y hy
      rwa [abs_of_nonpos hr.2] at h1) hx hDanti
    (fun r hr ↦ by
      have h1 := hp.norm_flowOn_sub_le_majorant (s := r)
        ⟨hr.1, by linarith [hr.2, hp.nonneg]⟩ hx
      rwa [abs_of_nonpos hr.2] at h1) hs
  have hs' := hneg hs
  rw [intervalIntegral.integral_comp_neg (fun r ↦ (K₂ : ℝ) * (pairFlowConst T K₁ c₀ * T *
    Dm r) + c₁ * PDE.Analysis.osgoodModulus A (Dm r)), neg_zero] at h
  have hint : ∫ r in (0)..(-s), ((K₂ : ℝ) * (pairFlowConst T K₁ c₀ * T * Dm r) +
        c₁ * PDE.Analysis.osgoodModulus A (Dm r)) ≤
      ((K₂ : ℝ) * pairFlowConst T K₁ c₀ * T + c₁) *
        ∫ r in (0)..(-s), PDE.Analysis.osgoodModulus A (Dm r) := by
    rw [← intervalIntegral.integral_const_mul]
    have hm2 : MonotoneOn (fun r ↦ (K₂ : ℝ) * (pairFlowConst T K₁ c₀ * T * Dm r) +
        c₁ * PDE.Analysis.osgoodModulus A (Dm r)) (Icc 0 T) :=
      fun r hr r' hr' hrr' ↦ add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hp.monotoneOn hr hr' hrr')
          (mul_nonneg hp.pairFlowConst_nonneg hp.nonneg)) K₂.2)
        (mul_le_mul_of_nonneg_left (hφmono hr hr' hrr') hCκ)
    refine intervalIntegral.integral_mono_on hs'.1 (intervalIntegrable_of_monotoneOn hm2 hs')
      ((intervalIntegrable_of_monotoneOn hφmono hs').const_mul _) fun r hr ↦ ?_
    exact hp.forcing_le ⟨hr.1, hr.2.trans hs'.2⟩
  have he : Real.exp ((K₁ + K₁) * (0 - s)) ≤ Real.exp (2 * K₁ * T) :=
    Real.exp_le_exp.mpr (by nlinarith [hs.2, hs.1])
  calc _ ≤ _ := h
    _ ≤ Real.exp (2 * K₁ * T) * (((K₂ : ℝ) * pairFlowConst T K₁ c₀ * T + c₁) *
          ∫ r in (0)..(-s), PDE.Analysis.osgoodModulus A (Dm r)) :=
        mul_le_mul he hint (intervalIntegral.integral_nonneg hs'.1 fun r hr ↦
          add_nonneg (mul_nonneg K₂.2 (mul_nonneg (mul_nonneg hp.pairFlowConst_nonneg hp.nonneg)
            (hp.nonneg_majorant r ⟨hr.1, hr.2.trans hs'.2⟩)))
            (mul_nonneg hCκ (PDE.Analysis.osgoodModulus_nonneg
              (hp.nonneg_majorant r ⟨hr.1, hr.2.trans hs'.2⟩)
              (hp.le_modulus r ⟨hr.1, hr.2.trans hs'.2⟩)))) (Real.exp_pos _).le
    _ = _ := by unfold pairVariationConst; ring

/-- **Comparison of the first variations** at any time `s ∈ [-T, T]`: on the closed half-plane
the first variations of the two flows from the base time `0` differ by at most
`pairVariationConst T K₂ K₁ c₀ c₁ · ∫₀^{|s|} φ_A(Dm)`. The forcing of the carried vorticity
contains the first variation, so this bound is needed for the difference of two carried
vorticities. Proof: the forward and the backward comparison; the difference of the variations
solves a linear equation whose forcing is bounded by the difference of the flow lines and by
the difference of the derivatives of the fields. -/
theorem norm_variationOn_sub_le {s : ℝ} (hs : s ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖variationOn v Dv (-T) T s 0 x - variationOn v' Dv' (-T) T s 0 x‖ ≤
      pairVariationConst T K₂ K₁ c₀ c₁ *
        ∫ r in (0)..|s|, PDE.Analysis.osgoodModulus A (Dm r) := by
  rcases le_total 0 s with h0 | h0
  · rw [abs_of_nonneg h0]
    exact hp.norm_variationOn_sub_le_forward ⟨h0, hs.2⟩ hx
  · rw [abs_of_nonpos h0]
    exact hp.norm_variationOn_sub_le_backward ⟨hs.1, h0⟩ hx

/-- **Comparison of the flow lines** with the Osgood modulus at any time `s ∈ [-T, T]`. -/
theorem norm_flowOn_sub_le_osgood {s : ℝ} (hs : s ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn v (-T) T s 0 x - flowOn v' (-T) T s 0 x‖ ≤
      pairFlowConst T K₁ c₀ * ∫ r in (0)..|s|, PDE.Analysis.osgoodModulus A (Dm r) := by
  have hsT : |s| ∈ Icc 0 T := ⟨abs_nonneg s, abs_le.mpr ⟨hs.1, hs.2⟩⟩
  have h := integral_const_mul_le_integral_osgoodModulus hp.modulus_pos
    hp.monotoneOn hp.nonneg_majorant hp.le_modulus (c := 1) zero_le_one hsT
  simp only [one_mul] at h
  exact (hp.norm_flowOn_sub_le hs hx).trans
    (mul_le_mul_of_nonneg_left h hp.pairFlowConst_nonneg)

end IsFieldPair

end HalfPlaneSystem
