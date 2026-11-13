/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Construction
public import PDE.Analysis.ODE.Flow.Inverse
public import PDE.Analysis.ODE.Flow.Comparison
import PDE.Analysis.Calculus.HolderInterpolation

/-!
# Convergence of the Picard iteration for half-plane Boussinesq

The iteration map `carriedHistory ω₀ θ₀ (-T) T` sends a vorticity history to the vorticity carried
by the flow of its velocity field. On the class of `C^{1,α}` histories with fixed bounds,
`IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁`, the map satisfies a difference estimate of Osgood
type: if `|ω - ω'| ≤ D(|r|)` on the closed half-plane at time `r`, with `D` nondecreasing, then
at time `t` the images differ by at most `C ∫₀^{|t|} φ_A(D)`, where `φ_A(r) = r (1 + log (A / r))`
(`abs_carriedHistory_sub_le`). The constants depend only on the bounds of the class, on the
data and on a Lipschitz constant `L` of the carried amplitude in the label.

## Main definitions

* `IsHistoryPair`: two histories of the class on `[-T, T]` that differ on the closed half-plane
  at time `r` by at most `Dm |r|`.
* `carriedSubConst`: the constant `L e^{K T} c_X + T N e^{2 K₁ T} c_J` of the difference
  estimate of the iteration map.

## Main results

* `abs_carriedHistory_sub_le`: the Osgood-type difference estimate of the iteration map.
* `norm_historyField_sub_le`: the fields of two histories that differ by `β` differ by
  `(1 + R₀²) β` on the closed half-plane.
* `norm_historyFieldDeriv_sub_le`: their derivatives differ by `Cκ φ_A(β)` there, with
  `Cκ = 4 (50/α + 8 + 10 π R₀²)`.
* `IsHistoryPair.norm_flowOn_sub_le`: the comparison of the flow lines at any time of `[-T, T]`.
* `IsHistoryPair.norm_flowOn_sub_le_osgood`: the same comparison with the Osgood modulus.
* `IsHistoryPair.norm_variationOn_sub_le`: the comparison of the first variations at any time of
  `[-T, T]`.

## How it works

We combine five estimates. The velocity fields of `ω, ω'` differ by `(1 + R₀²) D` and their
derivatives by `C φ_A(D)` on the closed half-plane (`norm_historyField_sub_le`,
`norm_historyFieldDeriv_sub_le`), by the size bound and the homogeneous Kato bound of a difference
(`norm_sub_fderivWithin_halfPlaneVelocity_le`). The derivative of the first field is Lipschitz,
since its second derivative is bounded. The flows and the first variations are compared from the
base time `0`, forward and backward (`IsHistoryPair.norm_flowOn_sub_le`,
`IsHistoryPair.norm_variationOn_sub_le`), and then the labels and the inverse variations. Finally
the Lagrangian formula of the carried vorticity, whose forcing `Dθ₀(Y)(W e₀)` has `‖Dθ₀‖ ≤ N`, gives
the estimate `abs_carriedHistory_sub_le`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace Boussinesq.HalfPlane

open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport
open SobolevSpace.GraphSpace.HigherOrderReflection

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-! ### The velocity field of a history in the class -/

section Field

variable {ω ω' : ℝ → ℝ^2 → ℝ} {a b α R₁ B M B₁ M₁ : ℝ}

/-- The flow of the field of a history preserves the closed half-plane. -/
theorem mapsTo_flowOn_historyField {K : ℝ≥0}
    (hω : IsVorticityHistory ω a b α R₁ B M) (hv : IsLipschitzFieldOn (historyField ω) a b K)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    MapsTo (flowOn (historyField ω) a b s t) H̄ H̄ :=
  (hv.bijOn_flowOn_nonneg (j := 1) (fun _ hr _ hx ↦ historyField_normal_eq_zero hω hr hx)
    hs ht).mapsTo

/-- On the closed half-plane the derivative of the field of a `C^{1,α}` history is bounded by the
Kato bound. -/
theorem norm_historyFieldDeriv_le
    (hω : IsC1VorticityHistory ω a b α R₁ B M B₁ M₁) (hα : 0 < α) (hα1 : α < 1) {r : ℝ}
    (hr : r ∈ Icc a b) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖historyFieldDeriv ω r y‖ ≤ katoBound α (max R₁ 0) B M := by
  rw [IsC1VorticityHistory.historyFieldDeriv_eq hω hα hα1 hr hy]
  exact hω.toIsVorticityHistory.norm_fderivWithin_le hα hα1 hr hy

/-- On the closed half-plane the fields of two histories differ by `(1 + R₀²) β` when the
histories differ by `β`. -/
theorem norm_historyField_sub_le (hω : IsVorticityHistory ω a b α R₁ B M)
    (hω' : IsVorticityHistory ω' a b α R₁ B M) {r β : ℝ} (hr : r ∈ Icc a b)
    (hβ : ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y - ω' r y| ≤ β) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖historyField ω r y - historyField ω' r y‖ ≤ (1 + max R₁ 0 ^ 2) * β := by
  rw [historyField_of_nonneg ω r hy, historyField_of_nonneg ω' r hy]
  exact norm_halfPlaneVelocity_sub_le_of_abs_sub_le (hω.continuousOn r hr) (hω.eq_zero_max hr)
    (hω'.continuousOn r hr) (hω'.eq_zero_max hr) (le_max_right R₁ 0) hβ y

/-- On the closed half-plane the derivatives of the fields of two `C^{1,α}` histories differ by
`Cκ φ_A(β)` when the histories differ by `β ≤ A'`, with `Cκ = 4 (50/α + 8 + 10 π R₀²)` and any
`A ≥ max (2 A' + 2 M) A'`, `A' > 0`. -/
theorem norm_historyFieldDeriv_sub_le
    (hω : IsC1VorticityHistory ω a b α R₁ B M B₁ M₁)
    (hω' : IsC1VorticityHistory ω' a b α R₁ B M B₁ M₁) (hα : 0 < α) (hα1 : α < 1)
    {A' A : ℝ} (hA' : 0 < A') (hA₁ : 2 * A' + (M + M) ≤ A) (hA'A : A' ≤ A) {r β : ℝ}
    (hr : r ∈ Icc a b) (hβ0 : 0 ≤ β) (hβA : β ≤ A')
    (hβ : ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y - ω' r y| ≤ β) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖historyFieldDeriv ω r y - historyFieldDeriv ω' r y‖ ≤
      4 * (50 / α + 8 + 10 * (Real.pi * max R₁ 0 ^ 2)) * PDE.Analysis.osgoodModulus A β := by
  rw [IsC1VorticityHistory.historyFieldDeriv_eq hω hα hα1 hr hy,
    IsC1VorticityHistory.historyFieldDeriv_eq hω' hα hα1 hr hy]
  have hM0 : 0 ≤ M := hω.holder_nonneg hr
  have h1 := norm_sub_fderivWithin_halfPlaneVelocity_le (hω.continuousOn r hr)
    (hω.eq_zero_max hr) (hω'.continuousOn r hr) (hω'.eq_zero_max hr) (le_max_right R₁ 0) hα
    hα1 (hω.holder r hr) (hω'.holder r hr) hM0 hM0 hβ hβA hy
  have hA₁0 : 0 < 2 * A' + (M + M) := by linarith
  have hβA'' : β ≤ A := hβA.trans hA'A
  have h2 := PDE.Analysis.osgoodModulus_le_osgoodModulus (r := β) hA₁0 hA₁ hβ0
  have h3 := PDE.Analysis.le_osgoodModulus hβ0 hβA''
  have hR2 : 0 ≤ Real.pi * max R₁ 0 ^ 2 := by positivity
  refine h1.trans ?_
  calc 4 * (50 / α * PDE.Analysis.osgoodModulus (2 * A' + (M + M)) β + 8 * β +
        10 * (Real.pi * max R₁ 0 ^ 2 * β)) ≤
      4 * (50 / α * PDE.Analysis.osgoodModulus A β + 8 * PDE.Analysis.osgoodModulus A β +
        10 * (Real.pi * max R₁ 0 ^ 2 * PDE.Analysis.osgoodModulus A β)) := by
        have hα0 : 0 ≤ 50 / α := by positivity
        gcongr
    _ = 4 * (50 / α + 8 + 10 * (Real.pi * max R₁ 0 ^ 2)) * PDE.Analysis.osgoodModulus A β := by
        ring

end Field

/-! ### Integrals of a monotone majorant -/

section Majorant

variable {Dm : ℝ → ℝ} {T A : ℝ}

/-- The Osgood modulus of a monotone majorant with values in `[0, A]` is monotone. -/
theorem monotoneOn_osgoodModulus_comp (hA : 0 < A) (hDm : MonotoneOn Dm (Icc 0 T))
    (hDm0 : ∀ s ∈ Icc 0 T, 0 ≤ Dm s) (hDmA : ∀ s ∈ Icc 0 T, Dm s ≤ A) :
    MonotoneOn (fun s ↦ PDE.Analysis.osgoodModulus A (Dm s)) (Icc 0 T) :=
  fun s hs s' hs' hss' ↦ PDE.Analysis.monotoneOn_osgoodModulus hA ⟨hDm0 s hs, hDmA s hs⟩
    ⟨hDm0 s' hs', hDmA s' hs'⟩ (hDm hs hs' hss')

/-- Monotone functions on `[0, T]` are interval integrable on `[0, q]`, `q ∈ [0, T]`. -/
theorem intervalIntegrable_of_monotoneOn {g : ℝ → ℝ} (hg : MonotoneOn g (Icc 0 T)) {q : ℝ}
    (hq : q ∈ Icc 0 T) : IntervalIntegrable g volume 0 q := by
  refine MonotoneOn.intervalIntegrable (hg.mono ?_)
  rw [uIcc_of_le hq.1]
  exact Icc_subset_Icc_right hq.2

/-- `∫₀^q c D ≤ c ∫₀^q φ_A(D)` for a monotone majorant `D` with values in `[0, A]`. -/
theorem integral_const_mul_le_integral_osgoodModulus (hA : 0 < A) (hDm : MonotoneOn Dm (Icc 0 T))
    (hDm0 : ∀ s ∈ Icc 0 T, 0 ≤ Dm s) (hDmA : ∀ s ∈ Icc 0 T, Dm s ≤ A) {c : ℝ} (hc : 0 ≤ c)
    {q : ℝ} (hq : q ∈ Icc 0 T) :
    ∫ r in (0)..q, c * Dm r ≤ c * ∫ r in (0)..q, PDE.Analysis.osgoodModulus A (Dm r) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hq.1
    ((intervalIntegrable_of_monotoneOn hDm hq).const_mul c)
    ((intervalIntegrable_of_monotoneOn (monotoneOn_osgoodModulus_comp hA hDm hDm0 hDmA)
      hq).const_mul c) fun r hr ↦ ?_
  have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans hq.2⟩
  exact mul_le_mul_of_nonneg_left (PDE.Analysis.le_osgoodModulus (hDm0 r hrT) (hDmA r hrT)) hc

/-- The integral of a nonnegative monotone majorant grows with the upper limit. -/
theorem integral_osgoodModulus_mono (hA : 0 < A) (hDm : MonotoneOn Dm (Icc 0 T))
    (hDm0 : ∀ s ∈ Icc 0 T, 0 ≤ Dm s) (hDmA : ∀ s ∈ Icc 0 T, Dm s ≤ A) {q q' : ℝ}
    (hq : 0 ≤ q) (hqq' : q ≤ q') (hq' : q' ≤ T) :
    ∫ r in (0)..q, PDE.Analysis.osgoodModulus A (Dm r) ≤
      ∫ r in (0)..q', PDE.Analysis.osgoodModulus A (Dm r) :=
  intervalIntegral.integral_mono_interval le_rfl hq hqq'
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact PDE.Analysis.osgoodModulus_nonneg (hDm0 r ⟨hr.1.le, hr.2.trans hq'⟩)
        (hDmA r ⟨hr.1.le, hr.2.trans hq'⟩))
    (intervalIntegrable_of_monotoneOn (monotoneOn_osgoodModulus_comp hA hDm hDm0 hDmA)
      ⟨hq.trans hqq', hq'⟩)

/-- The integral of the Osgood modulus of a majorant is nonnegative. -/
theorem integral_osgoodModulus_nonneg {q : ℝ} (hDm0 : ∀ s ∈ Icc 0 T, 0 ≤ Dm s)
    (hDmA : ∀ s ∈ Icc 0 T, Dm s ≤ A) (hq : q ∈ Icc 0 T) :
    0 ≤ ∫ r in (0)..q, PDE.Analysis.osgoodModulus A (Dm r) :=
  intervalIntegral.integral_nonneg hq.1 fun r hr ↦
    PDE.Analysis.osgoodModulus_nonneg (hDm0 r ⟨hr.1, hr.2.trans hq.2⟩)
      (hDmA r ⟨hr.1, hr.2.trans hq.2⟩)

end Majorant

/-! ### Flows and variations of two histories -/

section Comparison

variable {ω ω' : ℝ → ℝ^2 → ℝ} {T α R₁ B M B₁ M₁ : ℝ} {Dm : ℝ → ℝ} {A' : ℝ}

/-- The common setting of the comparison of the fields of two histories `ω, ω'` of the class on
`[-T, T]` that differ on the closed half-plane at time `r` by at most `Dm |r|`. -/
structure IsHistoryPair (ω ω' : ℝ → ℝ^2 → ℝ) (T α R₁ B M B₁ M₁ : ℝ) (Dm : ℝ → ℝ) (A' : ℝ) :
    Prop where
  /-- The time interval is nonempty. -/
  nonneg : 0 ≤ T
  /-- The Hölder exponent is positive. -/
  pos : 0 < α
  /-- The Hölder exponent is less than one. -/
  lt_one : α < 1
  /-- The first history is in the class. -/
  left : IsC1VorticityHistory ω (-T) T α R₁ B M B₁ M₁
  /-- The second history is in the class. -/
  right : IsC1VorticityHistory ω' (-T) T α R₁ B M B₁ M₁
  /-- The a priori bound of the majorant is positive. -/
  bound_pos : 0 < A'
  /-- The majorant is monotone. -/
  monotoneOn : MonotoneOn Dm (Icc 0 T)
  /-- The majorant is nonnegative. -/
  nonneg_majorant : ∀ s ∈ Icc 0 T, 0 ≤ Dm s
  /-- The majorant is at most `A'`. -/
  le_bound : ∀ s ∈ Icc 0 T, Dm s ≤ A'
  /-- The majorant bounds the difference of the histories. -/
  abs_sub_le : ∀ r ∈ Icc (-T) T, ∀ y : ℝ^2, 0 ≤ y 1 → |ω r y - ω' r y| ≤ Dm |r|

/-- The Osgood parameter `A = max (2 A' + 2 M) (max A' 1)` of the comparison. -/
def pairModulusBound (A' M : ℝ) : ℝ :=
  max (2 * A' + (M + M)) (max A' 1)

/-- The constant of the flow comparison, `e^{K₁ T} (1 + R₀²)`. -/
def flowSubConst (T α R₁ B M : ℝ) : ℝ :=
  Real.exp (katoBound α (max R₁ 0) B M * T) * (1 + max R₁ 0 ^ 2)

/-- The constant of the variation comparison,
`e^{2 K₁ T} (K₂ e^{K₁ T} (1 + R₀²) T + 4 (50/α + 8 + 10 π R₀²))`. -/
def variationSubConst (T α R₁ B M B₁ M₁ : ℝ) : ℝ :=
  Real.exp (2 * katoBound α (max R₁ 0) B M * T) *
    ((Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
      secondDerivBound α (max R₁ 0) B B₁ M₁) : ℝ) * flowSubConst T α R₁ B M * T +
      4 * (50 / α + 8 + 10 * (Real.pi * max R₁ 0 ^ 2)))

namespace IsHistoryPair

variable (hp : IsHistoryPair ω ω' T α R₁ B M B₁ M₁ Dm A')
include hp

/-- The base time `0` lies in `[-T, T]`. -/
theorem zero_mem : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith [hp.nonneg], hp.nonneg⟩

omit hp in
/-- The Osgood parameter `pairModulusBound A' M` is positive. -/
theorem modulus_pos : 0 < pairModulusBound A' M :=
  zero_lt_one.trans_le ((le_max_right A' 1).trans (le_max_right _ _))

/-- On `[0, T]` the majorant is at most the Osgood parameter `pairModulusBound A' M`. -/
theorem le_modulus : ∀ s ∈ Icc 0 T, Dm s ≤ pairModulusBound A' M := fun s hs ↦
  (hp.le_bound s hs).trans ((le_max_left A' 1).trans (le_max_right _ _))

/-- The Kato bound `katoBound α R₀ B M`, `R₀ = max R₁ 0`, of the pair is nonnegative. -/
theorem katoBound_nonneg : 0 ≤ katoBound α (max R₁ 0) B M :=
  (norm_nonneg _).trans (norm_historyFieldDeriv_le hp.left hp.pos hp.lt_one hp.zero_mem
    (y := 0) (by simp))

omit hp in
/-- The constant `flowSubConst` of the flow comparison is nonnegative. -/
theorem flowSubConst_nonneg : 0 ≤ flowSubConst T α R₁ B M := by
  unfold flowSubConst; positivity

/-- The constant `variationSubConst` of the variation comparison is nonnegative. -/
theorem variationSubConst_nonneg : 0 ≤ variationSubConst T α R₁ B M B₁ M₁ := by
  have := flowSubConst_nonneg (T := T) (α := α) (R₁ := R₁) (B := B) (M := M)
  have := hp.nonneg
  have := hp.pos
  unfold variationSubConst; positivity

/-- The difference of the fields at a time `r` is bounded by `(1 + R₀²) Dm |r|`. -/
theorem norm_historyField_sub_le {r : ℝ} (hr : r ∈ Icc (-T) T) {y : ℝ^2} (hy : 0 ≤ y 1) :
    ‖historyField ω r y - historyField ω' r y‖ ≤ (1 + max R₁ 0 ^ 2) * Dm |r| :=
  Boussinesq.HalfPlane.norm_historyField_sub_le hp.left.toIsVorticityHistory
    hp.right.toIsVorticityHistory hr (hp.abs_sub_le r hr) hy

/-- The difference of the derivatives of the fields at a time `r` is bounded by
`Cκ φ_A(Dm |r|)`. -/
theorem norm_historyFieldDeriv_sub_le {r : ℝ} (hr : r ∈ Icc (-T) T) {y : ℝ^2}
    (hy : 0 ≤ y 1) :
    ‖historyFieldDeriv ω r y - historyFieldDeriv ω' r y‖ ≤
      4 * (50 / α + 8 + 10 * (Real.pi * max R₁ 0 ^ 2)) *
        PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm |r|) := by
  have hrT : |r| ∈ Icc 0 T := ⟨abs_nonneg r, abs_le.mpr ⟨hr.1, hr.2⟩⟩
  exact Boussinesq.HalfPlane.norm_historyFieldDeriv_sub_le hp.left hp.right hp.pos hp.lt_one
    hp.bound_pos (le_max_left _ _) ((le_max_left A' 1).trans (le_max_right _ _)) hr
    (hp.nonneg_majorant _ hrT) (hp.le_bound _ hrT) (hp.abs_sub_le r hr) hy

/-- The common facts on the two fields: `C²` fields preserving the closed half-plane, with
derivative bounded by `K₁` on it. -/
theorem fields :
    IsC2FieldOn (historyField ω) (historyFieldDeriv ω) (historyFieldDeriv₂ ω) (-T) T
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 * katoBound α (max R₁ 0) B M))
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
        secondDerivBound α (max R₁ 0) B B₁ M₁)) ∧
    IsC2FieldOn (historyField ω') (historyFieldDeriv ω') (historyFieldDeriv₂ ω') (-T) T
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 * katoBound α (max R₁ 0) B M))
      (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
        secondDerivBound α (max R₁ 0) B B₁ M₁)) ∧
    (∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T, MapsTo (flowOn (historyField ω) (-T) T s t) H̄ H̄) ∧
    (∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T, MapsTo (flowOn (historyField ω') (-T) T s t) H̄ H̄) ∧
    (∀ r ∈ Icc (-T) T, ∀ y ∈ H̄, ‖historyFieldDeriv ω r y‖ ≤ katoBound α (max R₁ 0) B M) ∧
    (∀ r ∈ Icc (-T) T, ∀ y ∈ H̄, ‖historyFieldDeriv ω' r y‖ ≤ katoBound α (max R₁ 0) B M) := by
  have hv := IsC1VorticityHistory.isC2FieldOn_historyField hp.left hp.pos hp.lt_one
  have hv' := IsC1VorticityHistory.isC2FieldOn_historyField hp.right hp.pos hp.lt_one
  exact ⟨hv, hv', fun s hs t ht ↦ mapsTo_flowOn_historyField hp.left.toIsVorticityHistory
    hv.isLipschitzFieldOn hs ht, fun s hs t ht ↦ mapsTo_flowOn_historyField
    hp.right.toIsVorticityHistory hv'.isLipschitzFieldOn hs ht,
    fun r hr y hy ↦ norm_historyFieldDeriv_le hp.left hp.pos hp.lt_one hr hy,
    fun r hr y hy ↦ norm_historyFieldDeriv_le hp.right hp.pos hp.lt_one hr hy⟩

/-- **Forward comparison of the flow lines** from the base time `0`. -/
theorem norm_flowOn_sub_le_forward {s : ℝ} (hs : s ∈ Icc 0 T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn (historyField ω) (-T) T s 0 x - flowOn (historyField ω') (-T) T s 0 x‖ ≤
      flowSubConst T α R₁ B M * ∫ r in (0)..s, Dm r := by
  obtain ⟨hv, hv', hS, hS', hDv, -⟩ := hp.fields
  have hK₁ := hp.katoBound_nonneg
  have hR : 0 ≤ 1 + max R₁ 0 ^ 2 := by positivity
  have hmono : MonotoneOn (fun r ↦ (1 + max R₁ 0 ^ 2) * Dm r) (Icc 0 T) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left (hp.monotoneOn hr hr' hrr') hR
  have h := hv.toIsC1FieldOn.norm_flowOn_sub_flowOn_le_of_invariant hv'.toIsC1FieldOn
    PDE.Analysis.convex_closedUpperHalfPlane hS hS' hDv hp.zero_mem hmono
    (fun r hr ↦ mul_nonneg hR (hp.nonneg_majorant r hr))
    (fun r hr y hy ↦ by
      simpa only [abs_of_nonneg hr.1] using
        hp.norm_historyField_sub_le (r := r) ⟨by linarith [hr.1, hp.nonneg], hr.2⟩ hy) hx hs
  rw [intervalIntegral.integral_const_mul] at h
  have hI0 : 0 ≤ ∫ r in (0)..s, Dm r :=
    intervalIntegral.integral_nonneg hs.1 fun r hr ↦ hp.nonneg_majorant r ⟨hr.1, hr.2.trans hs.2⟩
  have he : Real.exp (katoBound α (max R₁ 0) B M * (s - 0)) ≤
      Real.exp (katoBound α (max R₁ 0) B M * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hs.2]) hK₁)
  exact h.trans ((mul_le_mul_of_nonneg_right he (mul_nonneg hR hI0)).trans_eq
    (by unfold flowSubConst; ring))

/-- **Backward comparison of the flow lines** from the base time `0`. -/
theorem norm_flowOn_sub_le_backward {s : ℝ} (hs : s ∈ Icc (-T) 0) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn (historyField ω) (-T) T s 0 x - flowOn (historyField ω') (-T) T s 0 x‖ ≤
      flowSubConst T α R₁ B M * ∫ r in (0)..(-s), Dm r := by
  obtain ⟨hv, hv', hS, hS', hDv, -⟩ := hp.fields
  have hK₁ := hp.katoBound_nonneg
  have hR : 0 ≤ 1 + max R₁ 0 ^ 2 := by positivity
  have hneg {r : ℝ} (hr : r ∈ Icc (-T) 0) : -r ∈ Icc 0 T :=
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hanti : AntitoneOn (fun r ↦ (1 + max R₁ 0 ^ 2) * Dm (-r)) (Icc (-T) 0) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left
      (hp.monotoneOn (hneg hr') (hneg hr) (neg_le_neg hrr')) hR
  have h := hv.toIsC1FieldOn.norm_flowOn_sub_flowOn_le_of_invariant_left hv'.toIsC1FieldOn
    PDE.Analysis.convex_closedUpperHalfPlane hS hS' hDv hp.zero_mem hanti
    (fun r hr ↦ mul_nonneg hR (hp.nonneg_majorant _ (hneg hr)))
    (fun r hr y hy ↦ by
      simpa only [abs_of_nonpos hr.2] using
        hp.norm_historyField_sub_le (r := r) ⟨hr.1, by linarith [hr.2, hp.nonneg]⟩ hy) hx hs
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_neg (fun r ↦ Dm r), neg_zero] at h
  have hs' := hneg hs
  have hI0 : 0 ≤ ∫ r in (0)..(-s), Dm r :=
    intervalIntegral.integral_nonneg hs'.1 fun r hr ↦
      hp.nonneg_majorant r ⟨hr.1, hr.2.trans hs'.2⟩
  have he : Real.exp (katoBound α (max R₁ 0) B M * (0 - s)) ≤
      Real.exp (katoBound α (max R₁ 0) B M * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hs.1]) hK₁)
  exact h.trans ((mul_le_mul_of_nonneg_right he (mul_nonneg hR hI0)).trans_eq
    (by unfold flowSubConst; ring))

/-- **Comparison of the flow lines** at any time `s ∈ [-T, T]`. -/
theorem norm_flowOn_sub_le {s : ℝ} (hs : s ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn (historyField ω) (-T) T s 0 x - flowOn (historyField ω') (-T) T s 0 x‖ ≤
      flowSubConst T α R₁ B M * ∫ r in (0)..|s|, Dm r := by
  rcases le_total 0 s with h0 | h0
  · rw [abs_of_nonneg h0]
    exact hp.norm_flowOn_sub_le_forward ⟨h0, hs.2⟩ hx
  · rw [abs_of_nonpos h0]
    exact hp.norm_flowOn_sub_le_backward ⟨hs.1, h0⟩ hx

/-- The flow lines differ at time `s` by at most `flowSubConst T α R₁ B M * T * Dm |s|`. -/
theorem norm_flowOn_sub_le_majorant {s : ℝ} (hs : s ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn (historyField ω) (-T) T s 0 x - flowOn (historyField ω') (-T) T s 0 x‖ ≤
      flowSubConst T α R₁ B M * T * Dm |s| := by
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
  calc _ ≤ flowSubConst T α R₁ B M * ∫ r in (0)..|s|, Dm r := hp.norm_flowOn_sub_le hs hx
    _ ≤ flowSubConst T α R₁ B M * (Dm |s| * T) :=
        mul_le_mul_of_nonneg_left (hI.trans (mul_le_mul_of_nonneg_left hsT.2 hD))
          flowSubConst_nonneg
    _ = flowSubConst T α R₁ B M * T * Dm |s| := by ring

/-- The integrand of the variation comparison is bounded by the Osgood modulus of the
majorant. -/
theorem forcing_le {q : ℝ} (hq : q ∈ Icc 0 T) :
    (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
        secondDerivBound α (max R₁ 0) B B₁ M₁) : ℝ) * (flowSubConst T α R₁ B M * T * Dm q) +
      4 * (50 / α + 8 + 10 * (Real.pi * max R₁ 0 ^ 2)) *
        PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm q) ≤
    ((Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
        secondDerivBound α (max R₁ 0) B B₁ M₁) : ℝ) * flowSubConst T α R₁ B M * T +
      4 * (50 / α + 8 + 10 * (Real.pi * max R₁ 0 ^ 2))) *
        PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm q) := by
  have hle := PDE.Analysis.le_osgoodModulus (hp.nonneg_majorant q hq) (hp.le_modulus q hq)
  have hc : 0 ≤ (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
      secondDerivBound α (max R₁ 0) B B₁ M₁) : ℝ) * flowSubConst T α R₁ B M * T :=
    mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) flowSubConst_nonneg) hp.nonneg
  calc _ = (Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
        secondDerivBound α (max R₁ 0) B B₁ M₁) : ℝ) * flowSubConst T α R₁ B M * T * Dm q +
      4 * (50 / α + 8 + 10 * (Real.pi * max R₁ 0 ^ 2)) *
        PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm q) := by ring
    _ ≤ _ := by
        rw [add_mul]
        exact add_le_add_left (mul_le_mul_of_nonneg_left hle hc) _

/-- **Forward comparison of the first variations** from the base time `0`. -/
theorem norm_variationOn_sub_le_forward {s : ℝ} (hs : s ∈ Icc 0 T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖variationOn (historyField ω) (historyFieldDeriv ω) (-T) T s 0 x -
        variationOn (historyField ω') (historyFieldDeriv ω') (-T) T s 0 x‖ ≤
      variationSubConst T α R₁ B M B₁ M₁ *
        ∫ r in (0)..s, PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm r) := by
  obtain ⟨hv, hv', hS, hS', hDv, hDv'⟩ := hp.fields
  have hK₁ := hp.katoBound_nonneg
  set K₂ : ℝ≥0 := Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
    secondDerivBound α (max R₁ 0) B B₁ M₁)
  set Cκ := 4 * (50 / α + 8 + 10 * (Real.pi * max R₁ 0 ^ 2))
  have hCκ : 0 ≤ Cκ := by have := hp.pos; positivity
  set A := pairModulusBound A' M
  have hA := modulus_pos (A' := A') (M := M)
  have hφmono := monotoneOn_osgoodModulus_comp hA hp.monotoneOn hp.nonneg_majorant hp.le_modulus
  have hψ : MonotoneOn (fun q : ℝ ↦ (K₂ : ℝ) * q) (Ici 0) :=
    fun q _ q' _ h ↦ mul_le_mul_of_nonneg_left h K₂.2
  have hDvψ : ∀ r ∈ Icc (-T) T, ∀ y ∈ H̄, ∀ z ∈ H̄,
      ‖historyFieldDeriv ω r y - historyFieldDeriv ω r z‖ ≤ (K₂ : ℝ) * ‖y - z‖ :=
    fun r hr y _ z _ ↦ (hv.lipschitzWith_deriv hr).norm_sub_le y z
  have hε₁ : MonotoneOn (fun r ↦ Cκ * PDE.Analysis.osgoodModulus A (Dm r)) (Icc 0 T) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left (hφmono hr hr' hrr') hCκ
  have hDmono : MonotoneOn (fun r ↦ flowSubConst T α R₁ B M * T * Dm r) (Icc 0 T) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left (hp.monotoneOn hr hr' hrr')
      (mul_nonneg flowSubConst_nonneg hp.nonneg)
  have h := hv.toIsC1FieldOn.norm_variationOn_sub_variationOn_le_of_invariant
    hv'.toIsC1FieldOn hS hS' hDv hDv' hψ (fun q hq ↦ mul_nonneg K₂.2 hq) hDvψ hp.zero_mem hε₁
    (fun r hr ↦ mul_nonneg hCκ (PDE.Analysis.osgoodModulus_nonneg (hp.nonneg_majorant r hr)
      (hp.le_modulus r hr)))
    (fun r hr y hy ↦ by
      simpa only [abs_of_nonneg hr.1] using
        hp.norm_historyFieldDeriv_sub_le (r := r) ⟨by linarith [hr.1, hp.nonneg], hr.2⟩ hy)
    hx hDmono (fun r hr ↦ by
      simpa only [abs_of_nonneg hr.1] using
        hp.norm_flowOn_sub_le_majorant (s := r) ⟨by linarith [hr.1, hp.nonneg], hr.2⟩ hx) hs
  have hint : ∫ r in (0)..s, ((K₂ : ℝ) * (flowSubConst T α R₁ B M * T * Dm r) +
        Cκ * PDE.Analysis.osgoodModulus A (Dm r)) ≤
      ((K₂ : ℝ) * flowSubConst T α R₁ B M * T + Cκ) *
        ∫ r in (0)..s, PDE.Analysis.osgoodModulus A (Dm r) := by
    rw [← intervalIntegral.integral_const_mul]
    have hm2 : MonotoneOn (fun r ↦ (K₂ : ℝ) * (flowSubConst T α R₁ B M * T * Dm r) +
        Cκ * PDE.Analysis.osgoodModulus A (Dm r)) (Icc 0 T) :=
      fun r hr r' hr' hrr' ↦ add_le_add (mul_le_mul_of_nonneg_left (hDmono hr hr' hrr') K₂.2)
        (hε₁ hr hr' hrr')
    exact intervalIntegral.integral_mono_on hs.1 (intervalIntegrable_of_monotoneOn hm2 hs)
      ((intervalIntegrable_of_monotoneOn hφmono hs).const_mul _) fun r hr ↦
        hp.forcing_le ⟨hr.1, hr.2.trans hs.2⟩
  have hI0 := integral_osgoodModulus_nonneg hp.nonneg_majorant hp.le_modulus hs
  have he : Real.exp ((katoBound α (max R₁ 0) B M + katoBound α (max R₁ 0) B M) * (s - 0)) ≤
      Real.exp (2 * katoBound α (max R₁ 0) B M * T) :=
    Real.exp_le_exp.mpr (by nlinarith [hs.2, hs.1])
  have hc0 : 0 ≤ (K₂ : ℝ) * flowSubConst T α R₁ B M * T + Cκ :=
    add_nonneg (mul_nonneg (mul_nonneg K₂.2 flowSubConst_nonneg) hp.nonneg) hCκ
  exact h.trans ((mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le).trans
    ((mul_le_mul_of_nonneg_right he (mul_nonneg hc0 hI0)).trans_eq
      (by unfold variationSubConst; ring)))

/-- **Backward comparison of the first variations** from the base time `0`. -/
theorem norm_variationOn_sub_le_backward {s : ℝ} (hs : s ∈ Icc (-T) 0) {x : ℝ^2}
    (hx : 0 ≤ x 1) :
    ‖variationOn (historyField ω) (historyFieldDeriv ω) (-T) T s 0 x -
        variationOn (historyField ω') (historyFieldDeriv ω') (-T) T s 0 x‖ ≤
      variationSubConst T α R₁ B M B₁ M₁ *
        ∫ r in (0)..(-s), PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm r) := by
  obtain ⟨hv, hv', hS, hS', hDv, hDv'⟩ := hp.fields
  have hK₁ := hp.katoBound_nonneg
  set K₂ : ℝ≥0 := Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 2 *
    secondDerivBound α (max R₁ 0) B B₁ M₁)
  set Cκ := 4 * (50 / α + 8 + 10 * (Real.pi * max R₁ 0 ^ 2))
  have hCκ : 0 ≤ Cκ := by have := hp.pos; positivity
  set A := pairModulusBound A' M
  have hA := modulus_pos (A' := A') (M := M)
  have hφmono := monotoneOn_osgoodModulus_comp hA hp.monotoneOn hp.nonneg_majorant hp.le_modulus
  have hneg {r : ℝ} (hr : r ∈ Icc (-T) 0) : -r ∈ Icc 0 T :=
    ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hψ : MonotoneOn (fun q : ℝ ↦ (K₂ : ℝ) * q) (Ici 0) :=
    fun q _ q' _ h ↦ mul_le_mul_of_nonneg_left h K₂.2
  have hDvψ : ∀ r ∈ Icc (-T) T, ∀ y ∈ H̄, ∀ z ∈ H̄,
      ‖historyFieldDeriv ω r y - historyFieldDeriv ω r z‖ ≤ (K₂ : ℝ) * ‖y - z‖ :=
    fun r hr y _ z _ ↦ (hv.lipschitzWith_deriv hr).norm_sub_le y z
  have hε₁ : AntitoneOn (fun r ↦ Cκ * PDE.Analysis.osgoodModulus A (Dm (-r))) (Icc (-T) 0) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left
      (hφmono (hneg hr') (hneg hr) (neg_le_neg hrr')) hCκ
  have hDanti : AntitoneOn (fun r ↦ flowSubConst T α R₁ B M * T * Dm (-r)) (Icc (-T) 0) :=
    fun r hr r' hr' hrr' ↦ mul_le_mul_of_nonneg_left
      (hp.monotoneOn (hneg hr') (hneg hr) (neg_le_neg hrr'))
      (mul_nonneg flowSubConst_nonneg hp.nonneg)
  have h := hv.toIsC1FieldOn.norm_variationOn_sub_variationOn_le_of_invariant_left
    hv'.toIsC1FieldOn hS hS' hDv hDv' hψ (fun q hq ↦ mul_nonneg K₂.2 hq) hDvψ hp.zero_mem hε₁
    (fun r hr ↦ mul_nonneg hCκ (PDE.Analysis.osgoodModulus_nonneg
      (hp.nonneg_majorant _ (hneg hr)) (hp.le_modulus _ (hneg hr))))
    (fun r hr y hy ↦ by
      simpa only [abs_of_nonpos hr.2] using
        hp.norm_historyFieldDeriv_sub_le (r := r) ⟨hr.1, by linarith [hr.2, hp.nonneg]⟩ hy)
    hx hDanti (fun r hr ↦ by
      simpa only [abs_of_nonpos hr.2] using
        hp.norm_flowOn_sub_le_majorant (s := r) ⟨hr.1, by linarith [hr.2, hp.nonneg]⟩ hx) hs
  have hs' := hneg hs
  rw [intervalIntegral.integral_comp_neg (fun r ↦ (K₂ : ℝ) * (flowSubConst T α R₁ B M * T *
    Dm r) + Cκ * PDE.Analysis.osgoodModulus A (Dm r)), neg_zero] at h
  have hint : ∫ r in (0)..(-s), ((K₂ : ℝ) * (flowSubConst T α R₁ B M * T * Dm r) +
        Cκ * PDE.Analysis.osgoodModulus A (Dm r)) ≤
      ((K₂ : ℝ) * flowSubConst T α R₁ B M * T + Cκ) *
        ∫ r in (0)..(-s), PDE.Analysis.osgoodModulus A (Dm r) := by
    rw [← intervalIntegral.integral_const_mul]
    have hm2 : MonotoneOn (fun r ↦ (K₂ : ℝ) * (flowSubConst T α R₁ B M * T * Dm r) +
        Cκ * PDE.Analysis.osgoodModulus A (Dm r)) (Icc 0 T) :=
      fun r hr r' hr' hrr' ↦ add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hp.monotoneOn hr hr' hrr')
          (mul_nonneg flowSubConst_nonneg hp.nonneg)) K₂.2)
        (mul_le_mul_of_nonneg_left (hφmono hr hr' hrr') hCκ)
    exact intervalIntegral.integral_mono_on hs'.1 (intervalIntegrable_of_monotoneOn hm2 hs')
      ((intervalIntegrable_of_monotoneOn hφmono hs').const_mul _) fun r hr ↦
        hp.forcing_le ⟨hr.1, hr.2.trans hs'.2⟩
  have he : Real.exp ((katoBound α (max R₁ 0) B M + katoBound α (max R₁ 0) B M) * (0 - s)) ≤
      Real.exp (2 * katoBound α (max R₁ 0) B M * T) :=
    Real.exp_le_exp.mpr (by nlinarith [hs.2, hs.1])
  have hI0 := integral_osgoodModulus_nonneg hp.nonneg_majorant hp.le_modulus hs'
  have hc0 : 0 ≤ (K₂ : ℝ) * flowSubConst T α R₁ B M * T + Cκ :=
    add_nonneg (mul_nonneg (mul_nonneg K₂.2 flowSubConst_nonneg) hp.nonneg) hCκ
  exact h.trans ((mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le).trans
    ((mul_le_mul_of_nonneg_right he (mul_nonneg hc0 hI0)).trans_eq
      (by unfold variationSubConst; ring)))

/-- **Comparison of the first variations** at any time `s ∈ [-T, T]`. -/
theorem norm_variationOn_sub_le {s : ℝ} (hs : s ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖variationOn (historyField ω) (historyFieldDeriv ω) (-T) T s 0 x -
        variationOn (historyField ω') (historyFieldDeriv ω') (-T) T s 0 x‖ ≤
      variationSubConst T α R₁ B M B₁ M₁ *
        ∫ r in (0)..|s|, PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm r) := by
  rcases le_total 0 s with h0 | h0
  · rw [abs_of_nonneg h0]
    exact hp.norm_variationOn_sub_le_forward ⟨h0, hs.2⟩ hx
  · rw [abs_of_nonpos h0]
    exact hp.norm_variationOn_sub_le_backward ⟨hs.1, h0⟩ hx

/-- **Comparison of the flow lines** with the Osgood modulus at any time `s ∈ [-T, T]`. -/
theorem norm_flowOn_sub_le_osgood {s : ℝ} (hs : s ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖flowOn (historyField ω) (-T) T s 0 x - flowOn (historyField ω') (-T) T s 0 x‖ ≤
      flowSubConst T α R₁ B M *
        ∫ r in (0)..|s|, PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm r) := by
  have hsT : |s| ∈ Icc 0 T := ⟨abs_nonneg s, abs_le.mpr ⟨hs.1, hs.2⟩⟩
  have h := integral_const_mul_le_integral_osgoodModulus (modulus_pos (A' := A') (M := M))
    hp.monotoneOn hp.nonneg_majorant hp.le_modulus (c := 1) zero_le_one hsT
  simp only [one_mul] at h
  exact (hp.norm_flowOn_sub_le hs hx).trans
    (mul_le_mul_of_nonneg_left h flowSubConst_nonneg)

end IsHistoryPair

end Comparison

/-! ### The difference estimate of the iteration map -/

section Difference

variable {ω ω' : ℝ → ℝ^2 → ℝ} {T α R₁ B M B₁ M₁ : ℝ} {Dm : ℝ → ℝ} {A' : ℝ}
  {ω₀ θ₀ : ℝ^2 → ℝ} {N L : ℝ}

/-- The constant of the difference estimate of the iteration map:
`L e^{K T} c_X + T N e^{2 K₁ T} c_J`, with `K` the global Lipschitz constant of the fields. -/
def carriedSubConst (T α R₁ B M B₁ M₁ N L : ℝ) : ℝ :=
  L * Real.exp ((Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 *
      katoBound α (max R₁ 0) B M) : ℝ) * T) * flowSubConst T α R₁ B M +
    T * (N * Real.exp (katoBound α (max R₁ 0) B M * T) *
      Real.exp (katoBound α (max R₁ 0) B M * T) * variationSubConst T α R₁ B M B₁ M₁)

/-- **The difference estimate of the iteration map.** Let `ω, ω'` be histories of the class on
`[-T, T]` that differ on the closed half-plane at time `r` by at most `Dm |r|`, with `Dm`
nondecreasing with values in `[0, A']`. If the carried amplitude of `ω` is `L`-Lipschitz in the
label on the closed half-plane and `‖Dθ₀‖ ≤ N` there, then at every `t ∈ [-T, T]` the carried
vorticities differ on the closed half-plane by at most
`carriedSubConst T α R₁ B M B₁ M₁ N L * ∫₀^{|t|} φ_A(Dm)`, `A = pairModulusBound A' M`. -/
theorem abs_carriedHistory_sub_le (hp : IsHistoryPair ω ω' T α R₁ B M B₁ M₁ Dm A')
    (hθ₀ : ContDiffOn ℝ 2 θ₀ H̄) (hN : ∀ y : ℝ^2, 0 ≤ y 1 → ‖fderivWithin ℝ θ₀ H̄ y‖ ≤ N)
    (hL0 : 0 ≤ L)
    (hLip : ∀ t ∈ Icc (-T) T, ∀ a' a'' : ℝ^2, 0 ≤ a' 1 → 0 ≤ a'' 1 →
      |forcedAmplitude (dataVorticity ω₀) (labelForcing (historyField ω) (historyFieldDeriv ω)
          (-T) T (dataTemperature θ₀) (EuclideanSpace.single 0 1)) a' t -
        forcedAmplitude (dataVorticity ω₀) (labelForcing (historyField ω) (historyFieldDeriv ω)
          (-T) T (dataTemperature θ₀) (EuclideanSpace.single 0 1)) a'' t| ≤ L * ‖a' - a''‖)
    {t : ℝ} (ht : t ∈ Icc (-T) T) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |carriedHistory ω₀ θ₀ (-T) T ω t x - carriedHistory ω₀ θ₀ (-T) T ω' t x| ≤
      carriedSubConst T α R₁ B M B₁ M₁ N L *
        ∫ r in (0)..|t|, PDE.Analysis.osgoodModulus (pairModulusBound A' M) (Dm r) := by
  obtain ⟨hv, hv', hS, hS', hDv, hDv'⟩ := hp.fields
  have hL := hv.isLipschitzFieldOn
  have hL' := hv'.isLipschitzFieldOn
  have h0 := hp.zero_mem
  have hK₁ := hp.katoBound_nonneg
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 (by simp))
  set A := pairModulusBound A' M
  set I := ∫ r in (0)..|t|, PDE.Analysis.osgoodModulus A (Dm r)
  have htT : |t| ∈ Icc 0 T := ⟨abs_nonneg t, abs_le.mpr ⟨ht.1, ht.2⟩⟩
  have hI0 : 0 ≤ I := integral_osgoodModulus_nonneg hp.nonneg_majorant hp.le_modulus htT
  set v := historyField ω
  set v' := historyField ω'
  set e : ℝ^2 := EuclideanSpace.single 0 1
  set Y := flowOn v (-T) T 0 t x
  set Y' := flowOn v' (-T) T 0 t x
  have hY : 0 ≤ Y 1 := hS 0 h0 t ht hx
  have hY' : 0 ≤ Y' 1 := hS' 0 h0 t ht hx
  set G := labelForcing v (historyFieldDeriv ω) (-T) T (dataTemperature θ₀) e
  set G' := labelForcing v' (historyFieldDeriv ω') (-T) T (dataTemperature θ₀) e
  have hθC2 : ContDiff ℝ 2 (dataTemperature θ₀) := contDiff_dataTemperature hθ₀
  have hθC1 : ContDiff ℝ 1 (dataTemperature θ₀) := hθC2.of_le (by norm_num)
  -- the amplitude is Lipschitz in the label
  have h1 : |forcedAmplitude (dataVorticity ω₀) G Y t - forcedAmplitude (dataVorticity ω₀) G Y' t|
      ≤ L * ‖Y - Y'‖ := hLip t ht Y Y' hY hY'
  -- the labels
  have hlab := hL.norm_flowOn_sub_flowOn_le_of_inverse hL' (s := t) (t := 0) ht h0 x
  have hflow := hp.norm_flowOn_sub_le_osgood ht hY'
  set Kg : ℝ≥0 := Real.toNNReal (2 * PDE.Analysis.reflectionBound 2 1 *
    katoBound α (max R₁ 0) B M)
  have heg : Real.exp (Kg * |0 - t|) ≤ Real.exp (Kg * T) := by gcongr; simpa using htT.2
  have hYY : ‖Y - Y'‖ ≤ Real.exp (Kg * T) * (flowSubConst T α R₁ B M * I) :=
    hlab.trans (mul_le_mul heg hflow (norm_nonneg _) (Real.exp_pos _).le)
  -- the forcing integrals
  have hGc (g : ℝ^2 → ℝ → ℝ)
      (hg : ContinuousOn (fun p : ℝ^2 × ℝ ↦ g p.1 p.2) (univ ×ˢ Icc (-T) T)) :
      IntervalIntegrable (fun r ↦ g Y' r) volume 0 t :=
    ((hg.comp (continuousOn_const.prodMk continuousOn_id) fun r hr ↦ ⟨mem_univ _, hr⟩).mono
      (uIcc_subset_Icc h0 ht)).intervalIntegrable
  have hGi := hGc G (continuousOn_labelForcing hv.toIsC1FieldOn h0 hθC1)
  have hG'i := hGc G' (continuousOn_labelForcing hv'.toIsC1FieldOn h0 hθC1)
  have hdiff2 : forcedAmplitude (dataVorticity ω₀) G Y' t -
      forcedAmplitude (dataVorticity ω₀) G' Y' t = ∫ r in (0)..t, (G Y' r - G' Y' r) := by
    simp only [forcedAmplitude]
    rw [intervalIntegral.integral_sub hGi hG'i]
    ring
  have hfd : ‖fderiv ℝ (dataTemperature θ₀) Y'‖ ≤ N := by
    unfold dataTemperature
    rw [PDE.Analysis.fderiv_weightedReflectionFun_of_nonneg 1 (k := 2) (by norm_num)
      (by exact_mod_cast hθ₀) hY']
    exact hN Y' hY'
  have hbound : ∀ r ∈ Set.uIoc (0 : ℝ) t, ‖G Y' r - G' Y' r‖ ≤
      N * Real.exp (katoBound α (max R₁ 0) B M * T) *
        Real.exp (katoBound α (max R₁ 0) B M * T) * (variationSubConst T α R₁ B M B₁ M₁ * I) := by
    intro r hr
    have hr' : |r - 0| ≤ |t - 0| := abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hr)
    rw [sub_zero, sub_zero] at hr'
    have hrT : r ∈ Icc (-T) T := ⟨by linarith [neg_abs_le r, htT.2],
      (le_abs_self r).trans (hr'.trans htT.2)⟩
    have hW := hv.toIsC1FieldOn.norm_variationOn_inverse_sub_le hv'.toIsC1FieldOn (s := r)
      (t := 0) hrT h0 Y'
    have hWb := hv.toIsC1FieldOn.norm_variationOn_le_of_invariant hS hDv h0 hrT
      (hS r hrT 0 h0 hY')
    have hWb' := hv'.toIsC1FieldOn.norm_variationOn_le_of_invariant hS' hDv' h0 hrT
      (hS' r hrT 0 h0 hY')
    have hJ := hp.norm_variationOn_sub_le hrT hY'
    have hJI : ∫ q in (0)..|r|, PDE.Analysis.osgoodModulus A (Dm q) ≤ I :=
      integral_osgoodModulus_mono (IsHistoryPair.modulus_pos (A' := A') (M := M)) hp.monotoneOn
        hp.nonneg_majorant hp.le_modulus (abs_nonneg r) hr' htT.2
    have hexp : Real.exp (katoBound α (max R₁ 0) B M * |0 - r|) ≤
        Real.exp (katoBound α (max R₁ 0) B M * T) := by
      gcongr; simpa using hr'.trans htT.2
    set W := variationOn v (historyFieldDeriv ω) (-T) T 0 r (flowOn v (-T) T r 0 Y')
    set W' := variationOn v' (historyFieldDeriv ω') (-T) T 0 r (flowOn v' (-T) T r 0 Y')
    have hWW : ‖W - W'‖ ≤ Real.exp (katoBound α (max R₁ 0) B M * T) *
        (variationSubConst T α R₁ B M B₁ M₁ * I) *
        Real.exp (katoBound α (max R₁ 0) B M * T) := by
      refine hW.trans (mul_le_mul (mul_le_mul (hWb.trans hexp)
        (hJ.trans (mul_le_mul_of_nonneg_left hJI hp.variationSubConst_nonneg)) (norm_nonneg _)
        (Real.exp_pos _).le) (hWb'.trans hexp) (norm_nonneg _)
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg hp.variationSubConst_nonneg hI0)))
    have he : ‖e‖ = 1 := by simp [e]
    have hGG : G Y' r - G' Y' r = fderiv ℝ (dataTemperature θ₀) Y' ((W - W') e) := by
      simp only [G, G', labelForcing, sub_apply, map_sub, W, W']
    rw [hGG]
    exact (ContinuousLinearMap.le_of_opNorm_le_of_le _ hfd
      (ContinuousLinearMap.le_of_opNorm_le_of_le _ hWW he.le)).trans_eq (by ring)
  have h2 : |forcedAmplitude (dataVorticity ω₀) G Y' t -
      forcedAmplitude (dataVorticity ω₀) G' Y' t| ≤
      N * Real.exp (katoBound α (max R₁ 0) B M * T) *
        Real.exp (katoBound α (max R₁ 0) B M * T) *
          (variationSubConst T α R₁ B M B₁ M₁ * I) * T := by
    rw [hdiff2, ← Real.norm_eq_abs]
    have := hp.variationSubConst_nonneg
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans ?_
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left htT.2 (by positivity)
  change |forcedAmplitude (dataVorticity ω₀) G Y t -
    forcedAmplitude (dataVorticity ω₀) G' Y' t| ≤ _
  unfold carriedSubConst
  linarith [abs_sub_le (forcedAmplitude (dataVorticity ω₀) G Y t)
    (forcedAmplitude (dataVorticity ω₀) G Y' t) (forcedAmplitude (dataVorticity ω₀) G' Y' t),
    h1.trans (mul_le_mul_of_nonneg_left hYY hL0)]

end Difference

end Boussinesq.HalfPlane
