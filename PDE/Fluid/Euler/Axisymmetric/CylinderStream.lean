/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderMeridian
import PDE.Elliptic.Classical.Harmonic.WeakMaximumPrinciple
import PDE.FDeriv.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import PDE.FDeriv.Reflection.Coordinate

/-!
# The stream function problem in the cylinder

For an angular vorticity `ω` on the meridian plane, the angular stream function `φ` of the
cylinder `{r ≤ 1} × ℝ/Lℤ` solves

```text
-(∂_rr + r⁻¹ ∂_r + ∂_zz) φ + r⁻² φ = ω   on 0 < r < 1,     φ(1, z) = 0,     φ(0, z) = 0,
```

and is `L`-periodic in `z` (Chen and Hou, Part I (6.3)-(6.4)). The value at the axis is part of
axis regularity: the angular component of a regular vector potential vanishes on the axis (for
`φ = r Ψ(r², z)` with `Ψ` continuous it is automatic). `IsStreamFunction L ω φ` is this
problem, with `φ` of class `C²` in the open strip and continuous up to the axis and the wall.

The zero-order coefficient `r⁻²` of the operator is strictly positive. So at a negative interior
minimum the operator is negative (`streamOperator_neg_of_isLocalMin`), and a supersolution that
is nonnegative on the axis and the wall is nonnegative, without any barrier. This gives the
comparison principles `nonneg_of_streamOperator_nonneg` (periodic strip) and
`nonneg_of_streamOperator_nonneg_of_isCompact` (compact sets), and uniqueness
of the stream function (`IsStreamFunction.eqOn`).

## Main definitions

* `closedMeridianStrip`: the closed strip `0 ≤ r ≤ 1`.
* `IsStreamFunction`: the stream function problem with period `L`.

## Main results

* `streamOperator_neg_of_isLocalMin`: the operator at a negative local minimum off the axis.
* `nonneg_of_streamOperator_nonneg`: comparison on the periodic strip.
* `nonneg_of_streamOperator_nonneg_of_isCompact`: comparison on compact sets.
* `IsStreamFunction.eqOn`: uniqueness of the stream function on the closed strip.
* `IsStreamFunction.satisfiesStreamFunctionEquationOn`,
  `IsStreamFunction.hasZeroWallStreamFunctionOn`: the meridian system's elliptic part.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6, (6.3)-(6.5).
  <https://arxiv.org/abs/2210.07191v4>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 3, for the maximum principle with a positive
  zero-order term.
  <https://doi.org/10.1007/978-3-642-61798-0>
-/

@[expose] public section

open PDE (laplacian partialDeriv)

namespace Euler.Cylinder

open EuclideanSpace
open PDE.Common

set_option linter.missingDocs true

noncomputable section

/-- The closed meridian strip `{(r, z) | 0 ≤ r ≤ 1}`, the meridian section of the closed
cylinder including the axis. -/
def closedMeridianStrip : Set (ℝ^2) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ 1}

/-- The open strip lies in the closed one. -/
theorem meridianDomain_subset_closedMeridianStrip : meridianDomain ⊆ closedMeridianStrip :=
  fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩

/-- The open meridian strip is open. -/
theorem isOpen_meridianDomain : IsOpen meridianDomain := by
  have h : Continuous (fun x : ℝ^2 ↦ x 0) := by fun_prop
  exact (isOpen_lt continuous_const h).inter (isOpen_lt h continuous_const)

/-- The closed meridian strip is closed. -/
theorem isClosed_closedMeridianStrip : IsClosed closedMeridianStrip := by
  have h : Continuous (fun x : ℝ^2 ↦ x 0) := by fun_prop
  exact (isClosed_le continuous_const h).inter (isClosed_le h continuous_const)

/-- Every point is the meridian point of its coordinates. -/
theorem meridianPoint_coords (x : ℝ^2) : meridianPoint (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> simp [meridianPoint]

/-- `φ` is the angular stream function of `ω` in the cylinder of radius one with period `L`:
`φ` is `C²` in the open strip `0 < r < 1` and continuous on the closed strip `0 ≤ r ≤ 1`, solves
`-(∂_rr + r⁻¹ ∂_r + ∂_zz) φ + r⁻² φ = ω` there, vanishes on the axis `r = 0` and on the wall
`r = 1`, and is `L`-periodic in `z` (Chen and Hou, Part I (6.3)-(6.4)). -/
structure IsStreamFunction (L : ℝ) (ω φ : ℝ^2 → ℝ) : Prop where
  /-- `C²` regularity in the open strip. -/
  contDiffAt : ∀ ⦃x : ℝ^2⦄, x ∈ meridianDomain → ContDiffAt ℝ 2 φ x
  /-- Continuity up to the axis and the wall. -/
  continuousOn : ContinuousOn φ closedMeridianStrip
  /-- The stream function equation (6.3). -/
  equation : ∀ ⦃x : ℝ^2⦄, x ∈ meridianDomain → streamOperator φ x = ω x
  /-- The value at the axis. -/
  axis : ∀ z, φ (meridianPoint 0 z) = 0
  /-- The wall condition (6.4). -/
  wall : ∀ z, φ (meridianPoint 1 z) = 0
  /-- Periodicity in `z`. -/
  periodic : ∀ x, φ (axialTranslate L x) = φ x

/-- At a local minimum off the axis where a `C²` function is negative, the stream operator is
negative: the Laplacian is nonnegative, the radial derivative vanishes and the zero-order term
`φ / r²` is negative. -/
theorem streamOperator_neg_of_isLocalMin {v : ℝ^2 → ℝ} {p : ℝ^2} (hmin : IsLocalMin v p)
    (hp : 0 < p 0) (hv : ContDiffAt ℝ 2 v p) (hneg : v p < 0) : streamOperator v p < 0 := by
  have hmax : IsLocalMax (-v) p := hmin.neg
  have hlap : laplacian (-v) p ≤ 0 :=
    LaplacianEquation.laplacian_nonpos_at_localMax hmax hv.neg
  rw [PDE.laplacian_neg] at hlap
  have hderiv : (∂[(0 : Fin 2)] v) p = 0 := by
    rw [partialDeriv, IsLocalMin.fderiv_eq_zero hmin]
    rfl
  have hpos : 0 < p 0 ^ 2 := by positivity
  rw [streamOperator, hderiv, zero_div, sub_zero]
  have : v p / p 0 ^ 2 < 0 := div_neg_of_neg_of_pos hneg hpos
  linarith

/-- A periodic function of `z` on the strip takes each of its values in the fundamental cell
`0 ≤ z ≤ L`. -/
theorem exists_mem_cell_eq {L : ℝ} (hL : 0 < L) {v : ℝ^2 → ℝ}
    (hper : ∀ x, v (axialTranslate L x) = v x) (x : ℝ^2) :
    ∃ y : ℝ^2, y 0 = x 0 ∧ 0 ≤ y 1 ∧ y 1 ≤ L ∧ v y = v x := by
  set g : ℝ → ℝ := fun z ↦ v (meridianPoint (x 0) z)
  have hg : Function.Periodic g L := by
    intro z
    simp only [g]
    rw [← axialTranslate_meridianPoint, hper]
  obtain ⟨w, hw, hgw⟩ := hg.exists_mem_Ico₀ hL (x 1)
  refine ⟨meridianPoint (x 0) w, by simp, by simpa using hw.1, by simpa using hw.2.le, ?_⟩
  change g w = v x
  rw [← hgw]
  simp [g, meridianPoint_coords]

/-- **Comparison on the periodic strip.** A function that is `C²` in the open strip, continuous
on the closed strip, `L`-periodic in `z`, nonnegative on the axis and on the wall, with
nonnegative stream operator in the open strip, is nonnegative on the closed strip. -/
theorem nonneg_of_streamOperator_nonneg {L : ℝ} (hL : 0 < L) {v : ℝ^2 → ℝ}
    (hcont : ContinuousOn v closedMeridianStrip)
    (hreg : ∀ ⦃x : ℝ^2⦄, x ∈ meridianDomain → ContDiffAt ℝ 2 v x)
    (hop : ∀ ⦃x : ℝ^2⦄, x ∈ meridianDomain → 0 ≤ streamOperator v x)
    (haxis : ∀ z, 0 ≤ v (meridianPoint 0 z)) (hwall : ∀ z, 0 ≤ v (meridianPoint 1 z))
    (hper : ∀ x, v (axialTranslate L x) = v x) :
    ∀ ⦃x : ℝ^2⦄, x ∈ closedMeridianStrip → 0 ≤ v x := by
  set K : Set (ℝ^2) := {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ 0 ≤ x 1 ∧ x 1 ≤ L}
  have hKsub : K ⊆ closedMeridianStrip := fun x hx ↦ ⟨hx.1, hx.2.1⟩
  have hKc : IsCompact K := by
    have hb : Bornology.IsBounded K := by
      refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ^2)).2 ⟨1 + L, fun x hx ↦ ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_two]
      rw [Real.sqrt_le_left (by positivity)]
      have h0 : x 0 ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2.1]
      have h1 : x 1 ^ 2 ≤ L ^ 2 := by nlinarith [hx.2.2.1, hx.2.2.2]
      simp only [Real.norm_eq_abs, sq_abs]
      nlinarith
    have hcl : IsClosed K := by
      have h0 : Continuous (fun x : ℝ^2 ↦ x 0) := by fun_prop
      have h1 : Continuous (fun x : ℝ^2 ↦ x 1) := by fun_prop
      exact (isClosed_le continuous_const h0).inter ((isClosed_le h0 continuous_const).inter
        ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const)))
    exact Metric.isCompact_of_isClosed_isBounded hcl hb
  have hKne : K.Nonempty := ⟨meridianPoint 0 0, by simp [K, hL.le]⟩
  obtain ⟨p, hpK, hpmin⟩ := hKc.exists_isMinOn hKne (hcont.mono hKsub)
  have hglobal : ∀ ⦃x : ℝ^2⦄, x ∈ closedMeridianStrip → v p ≤ v x := by
    intro x hx
    obtain ⟨y, hy0, hy1, hy2, hyx⟩ := exists_mem_cell_eq hL hper x
    rw [← hyx]
    exact hpmin ⟨hy0 ▸ hx.1, hy0 ▸ hx.2, hy1, hy2⟩
  intro x hx
  refine le_trans ?_ (hglobal hx)
  by_contra hneg
  rw [not_le] at hneg
  have hp0 : 0 < p 0 := by
    rcases hpK.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := haxis (p 1)
      rw [h, meridianPoint_coords] at this
      linarith
  have hp1 : p 0 < 1 := by
    rcases hpK.2.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hwall (p 1)
      rw [← h, meridianPoint_coords] at this
      linarith
  have hpD : p ∈ meridianDomain := ⟨hp0, hp1⟩
  have hlocal : IsLocalMin v p := by
    filter_upwards [isOpen_meridianDomain.mem_nhds hpD] with y hy
    exact hglobal (meridianDomain_subset_closedMeridianStrip hy)
  have := streamOperator_neg_of_isLocalMin hlocal hp0 (hreg hpD) hneg
  linarith [hop hpD]

/-- **Comparison on compact sets.** Let `U ⊆ K` with `U` open, `K` compact and `r > 0` on `U`.
A function continuous on `K`, `C²` in `U`, with nonnegative stream operator in `U` and
nonnegative on `K \ U`, is nonnegative on `K`. The set `K \ U` may contain axis points. -/
theorem nonneg_of_streamOperator_nonneg_of_isCompact {U K : Set (ℝ^2)} (hU : IsOpen U)
    (hK : IsCompact K) (hUK : U ⊆ K) (hpos : ∀ ⦃x : ℝ^2⦄, x ∈ U → 0 < x 0) {v : ℝ^2 → ℝ}
    (hcont : ContinuousOn v K)
    (hreg : ∀ ⦃x : ℝ^2⦄, x ∈ U → ContDiffAt ℝ 2 v x)
    (hop : ∀ ⦃x : ℝ^2⦄, x ∈ U → 0 ≤ streamOperator v x)
    (hbd : ∀ ⦃x : ℝ^2⦄, x ∈ K → x ∉ U → 0 ≤ v x) :
    ∀ ⦃x : ℝ^2⦄, x ∈ K → 0 ≤ v x := by
  intro x hx
  obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hcont
  refine le_trans ?_ (hpmin hx)
  by_contra hneg
  rw [not_le] at hneg
  have hpU : p ∈ U := by
    by_contra hpU
    linarith [hbd hpK hpU]
  have hlocal : IsLocalMin v p := by
    filter_upwards [hU.mem_nhds hpU] with y hy
    exact hpmin (hUK hy)
  have := streamOperator_neg_of_isLocalMin hlocal (hpos hpU) (hreg hpU) hneg
  linarith [hop hpU]

/-- The stream operator of a difference of `C²` functions is the difference of their stream
operators. -/
theorem streamOperator_sub {f g : ℝ^2 → ℝ} {x : ℝ^2} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    streamOperator (fun y ↦ f y - g y) x = streamOperator f x - streamOperator g x := by
  rw [streamOperator, streamOperator, streamOperator, PDE.laplacian_sub f g x hf hg,
    PDE.partialDeriv_sub (hf.differentiableAt two_ne_zero) (hg.differentiableAt two_ne_zero)]
  ring

/-- The stream operator of a sum of `C²` functions is the sum of their stream operators. -/
theorem streamOperator_add {f g : ℝ^2 → ℝ} {x : ℝ^2} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    streamOperator (fun y ↦ f y + g y) x = streamOperator f x + streamOperator g x := by
  rw [streamOperator, streamOperator, streamOperator, PDE.laplacian_add f g x hf hg,
    PDE.partialDeriv_add (hf.differentiableAt two_ne_zero) (hg.differentiableAt two_ne_zero)]
  ring

namespace IsStreamFunction

variable {L : ℝ} {ω φ φ₁ φ₂ : ℝ^2 → ℝ}

/-- **Uniqueness of the stream function.** Two stream functions of the same vorticity with the
same positive period agree on the closed strip. -/
theorem eqOn (hL : 0 < L) (h₁ : IsStreamFunction L ω φ₁) (h₂ : IsStreamFunction L ω φ₂) :
    Set.EqOn φ₁ φ₂ closedMeridianStrip := by
  have key : ∀ {a b : ℝ^2 → ℝ}, IsStreamFunction L ω a → IsStreamFunction L ω b →
      ∀ ⦃x : ℝ^2⦄, x ∈ closedMeridianStrip → 0 ≤ a x - b x := by
    intro a b ha hb
    refine nonneg_of_streamOperator_nonneg (v := fun y ↦ a y - b y) hL
      (ha.continuousOn.sub hb.continuousOn) (fun x hx ↦ (ha.contDiffAt hx).sub (hb.contDiffAt hx))
      (fun x hx ↦ ?_) (fun z ↦ by simp [ha.axis, hb.axis])
      (fun z ↦ by simp [ha.wall, hb.wall]) (fun x ↦ by simp [ha.periodic, hb.periodic])
    rw [streamOperator_sub (ha.contDiffAt hx) (hb.contDiffAt hx), ha.equation hx,
      hb.equation hx, sub_self]
  intro x hx
  have h₁₂ := key h₁ h₂ hx
  have h₂₁ := key h₂ h₁ hx
  linarith

/-- A stream function of `ω` is a stream function of every `ω'` agreeing with `ω` on the open
strip. -/
theorem congr_vorticity {ω' : ℝ^2 → ℝ} (h : IsStreamFunction L ω φ)
    (hω : Set.EqOn ω ω' meridianDomain) : IsStreamFunction L ω' φ :=
  { h with equation := fun _ hx ↦ (h.equation hx).trans (hω hx) }

/-- The time slices of meridian fields whose stream functions solve the stream function problem
satisfy the stream function equation (6.3) of the meridian system. -/
theorem satisfiesStreamFunctionEquationOn {f : MeridianFields} {times : Set ℝ}
    (h : ∀ t ∈ times, IsStreamFunction L (fun x ↦ f.vorticity x t)
      (fun x ↦ f.streamFunction x t)) :
    SatisfiesStreamFunctionEquationOn f times :=
  fun _ _ hx ht ↦ (h _ ht).equation hx

/-- The time slices of meridian fields whose stream functions solve the stream function problem
satisfy the wall condition (6.4) of the meridian system. -/
theorem hasZeroWallStreamFunctionOn {f : MeridianFields} {times : Set ℝ}
    (h : ∀ t ∈ times, IsStreamFunction L (fun x ↦ f.vorticity x t)
      (fun x ↦ f.streamFunction x t)) :
    HasZeroWallStreamFunctionOn f times :=
  fun z _ ht ↦ (h _ ht).wall z

end IsStreamFunction

/-- The stream operator commutes with negation. -/
theorem streamOperator_neg (f : ℝ^2 → ℝ) (x : ℝ^2) :
    streamOperator (fun y ↦ -f y) x = -streamOperator f x := by
  have hlap : laplacian (fun y ↦ -f y) x = -laplacian f x := PDE.laplacian_neg f x
  have hd : (∂[(0 : Fin 2)] (fun y ↦ -f y)) x = -(∂[(0 : Fin 2)] f) x :=
    PDE.partialDeriv_neg (f := f)
  rw [streamOperator, streamOperator, hlap, hd]
  ring

/-- The stream operator commutes with the axial reflection `z ↦ -z`. -/
theorem streamOperator_comp_axialReflection {φ : ℝ^2 → ℝ} {x : ℝ^2}
    (hφ : ContDiffAt ℝ 2 φ (axialReflection x)) :
    streamOperator (fun y ↦ φ (axialReflection y)) x = streamOperator φ (axialReflection x) := by
  have hlap := laplacian_comp_coordinateReflection_at (1 : Fin 2) φ x hφ
  have hd := partialDeriv_comp_coordinateReflection_of_ne (1 : Fin 2) 0 (by decide) φ x
    (hφ.differentiableAt (by norm_num))
  simp only [axialReflection] at hlap hd ⊢
  rw [streamOperator, streamOperator, hlap, hd]
  have h0 : coordinateReflection (1 : Fin 2) x 0 = x 0 :=
    coordinateReflection_apply_of_ne (1 : Fin 2) 0 (by decide) x
  rw [h0]

/-- The axial reflection commutes with the axial translation up to the sign of the shift. -/
theorem axialReflection_axialTranslate (L : ℝ) (x : ℝ^2) :
    axialReflection (axialTranslate L x) = axialTranslate (-L) (axialReflection x) := by
  ext i
  fin_cases i <;> simp [axialTranslate]
  ring

namespace IsStreamFunction

variable {L : ℝ} {ω φ : ℝ^2 → ℝ}

/-- The reflection `φ ↦ -φ(r, -z)` maps stream functions of `ω` to stream functions of
`-ω(r, -z)`. -/
theorem reflect (h : IsStreamFunction L ω φ) :
    IsStreamFunction L (fun x ↦ -ω (axialReflection x)) (fun x ↦ -φ (axialReflection x)) where
  contDiffAt x hx := by
    have hR : axialReflection x ∈ meridianDomain := axialReflection_mem_meridianDomain_iff.2 hx
    exact ((h.contDiffAt hR).comp x
      ((contDiff_coordinateReflection (1 : Fin 2) 2).contDiffAt)).neg
  continuousOn := by
    refine (h.continuousOn.comp
      (contDiff_coordinateReflection (1 : Fin 2) 0).continuous.continuousOn ?_).neg
    intro x hx
    simpa [closedMeridianStrip] using hx
  equation x hx := by
    have hR : axialReflection x ∈ meridianDomain := axialReflection_mem_meridianDomain_iff.2 hx
    rw [streamOperator_neg, streamOperator_comp_axialReflection (h.contDiffAt hR),
      h.equation hR]
  axis z := by simp [h.axis]
  wall z := by simp [h.wall]
  periodic x := by
    have h' := h.periodic (axialTranslate (-L) (axialReflection x))
    have hcancel : axialTranslate L (axialTranslate (-L) (axialReflection x)) =
        axialReflection x := by
      ext i
      fin_cases i <;> simp [axialTranslate]
    rw [hcancel] at h'
    simp only [axialReflection_axialTranslate, h']

/-- A stream function of a vorticity that is odd in `z` on the open strip is odd in `z` on the
closed strip. -/
theorem odd (hL : 0 < L) (h : IsStreamFunction L ω φ)
    (hω : ∀ ⦃x : ℝ^2⦄, x ∈ meridianDomain → ω (axialReflection x) = -ω x) :
    ∀ ⦃x : ℝ^2⦄, x ∈ closedMeridianStrip → φ (axialReflection x) = -φ x := by
  have hr := h.reflect
  have h' : IsStreamFunction L ω (fun x ↦ -φ (axialReflection x)) :=
    { hr with
      equation := fun x hx ↦ by rw [hr.equation hx, hω hx, neg_neg] }
  intro x hx
  have := eqOn hL h' h hx
  simp only at this
  linarith

/-- An odd stream function vanishes on the lines `z = ±L/2` (Part I (6.5) for `L = 2`). -/
theorem eq_zero_of_odd (h : IsStreamFunction L ω φ)
    (hodd : ∀ ⦃x : ℝ^2⦄, x ∈ closedMeridianStrip → φ (axialReflection x) = -φ x) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    φ (meridianPoint r (L / 2)) = 0 ∧ φ (meridianPoint r (-(L / 2))) = 0 := by
  have hmem : ∀ z, meridianPoint r z ∈ closedMeridianStrip := fun z ↦ by
    simp [closedMeridianStrip, hr0, hr1]
  have hper : φ (meridianPoint r (L / 2)) = φ (meridianPoint r (-(L / 2))) := by
    have := h.periodic (meridianPoint r (-(L / 2)))
    rw [axialTranslate_meridianPoint] at this
    rw [← this]
    congr 2
    ring
  have hodd' := hodd (hmem (L / 2))
  rw [axialReflection_meridianPoint] at hodd'
  constructor <;> linarith

end IsStreamFunction

end

end Euler.Cylinder
