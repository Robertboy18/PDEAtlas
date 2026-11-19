/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import PDE.Parabolic.Heat.Nonlinear.DirichletTest
public import PDE.Parabolic.Heat.MaximumPrinciple
public import PDE.DistributionTheory.TestFunction.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Prod
import PDE.Analysis.Calculus.CompactParametricIntegral.Interval
import PDE.Analysis.Evolution.LionsMagenes.Basic.WeakDerivative
import PDE.FDeriv.Laplacian.Continuity
import PDE.FDeriv.Laplacian.Congruence

/-!
# Compact moments from interior Dirichlet heat solutions

The candidate is `C²` only on the open space-time cylinder and continuous on its
closure. Initial values are imposed inside the domain, and lateral values only
at positive interior times. Continuity supplies the corner traces. Compact
spatial tests allow time differentiation and Green's identity without any
boundary derivative of the candidate.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian partialDeriv)
open PDE.Analysis PDE.Analysis.Evolution
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {T : ℝ}

/-- The interior smooth candidate class for the quadratic Dirichlet heat equation.
Only values, never derivative jets, are required on the closed faces. -/
structure IsInteriorDirichletSquareSolution (Ω : Set (ℝ^n)) (T : ℝ)
    (g : ℝ^n → ℝ) (u : ℝ → ℝ^n → ℝ) : Prop where
  /-- Continuous initial and lateral values. -/
  continuous : ContinuousOn u.uncurry (Icc 0 T ×ˢ closure Ω)
  /-- Joint smoothness is required only inside the cylinder. -/
  smooth : ContDiffOn ℝ 2 u.uncurry (Ioo 0 T ×ˢ Ω)
  /-- The time derivative satisfies the PDE inside the cylinder. -/
  equation : ∀ t ∈ Ioo 0 T, ∀ x ∈ Ω,
    deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2
  /-- Zero lateral values at interior times. -/
  boundary : ∀ x ∈ frontier Ω, ∀ t ∈ Ioo 0 T, u t x = 0
  /-- Initial values in the open spatial domain. -/
  initial : ∀ x ∈ Ω, u 0 x = g x

variable {g : ℝ^n → ℝ} {u : ℝ → ℝ^n → ℝ}

/-- Interior spatial slices inherit their regularity from the joint candidate. -/
theorem IsInteriorDirichletSquareSolution.space
    (hu : IsInteriorDirichletSquareSolution Ω T g u) (hΩ : IsOpen Ω)
    {t : ℝ} (ht : t ∈ Ioo 0 T) : ContDiffOn ℝ 2 (u t) Ω := by
  intro x hx
  exact ((hu.smooth.contDiffAt ((isOpen_Ioo.prod hΩ).mem_nhds ⟨ht, hx⟩)).comp x
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

/-- Interior time differentiation requires no endpoint trace. -/
theorem IsInteriorDirichletSquareSolution.hasDerivAt
    (hu : IsInteriorDirichletSquareSolution Ω T g u) (hΩ : IsOpen Ω)
    {x : ℝ^n} (hx : x ∈ Ω) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r ↦ u r x) (deriv (fun r ↦ u r x) t) t := by
  apply DifferentiableAt.hasDerivAt
  exact ((hu.smooth.contDiffAt ((isOpen_Ioo.prod hΩ).mem_nhds ⟨ht, hx⟩)).differentiableAt
    (by norm_num)).comp t (differentiableAt_id.prodMk (differentiableAt_const x))

/-- The time derivative is continuous on the open cylinder. -/
theorem IsInteriorDirichletSquareSolution.continuous_derivative
    (hu : IsInteriorDirichletSquareSolution Ω T g u) (hΩ : IsOpen Ω) :
    ContinuousOn (fun q : ℝ × ℝ^n ↦ deriv (fun r ↦ u r q.2) q.1) (Ioo 0 T ×ˢ Ω) := by
  have hd (q : ℝ × ℝ^n) (hq : q ∈ Ioo 0 T ×ˢ Ω) :
      HasDerivAt (fun r ↦ u r q.2) (fderiv ℝ u.uncurry q (1, 0)) q.1 := by
    exact ((hu.smooth.contDiffAt ((isOpen_Ioo.prod hΩ).mem_nhds hq)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt q.1
        ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  have hc : ContinuousOn (fun q ↦ fderiv ℝ u.uncurry q (1, 0)) (Ioo 0 T ×ˢ Ω) :=
    (hu.smooth.continuousOn_fderiv_of_isOpen (isOpen_Ioo.prod hΩ) (by norm_num)).clm_apply
      continuous_const.continuousOn
  exact hc.congr fun q hq ↦ (hd q hq).deriv

/-- Continuity extends zero lateral values to the two corner faces. -/
theorem IsInteriorDirichletSquareSolution.boundary_closed
    (hu : IsInteriorDirichletSquareSolution Ω T g u) (hT : 0 < T)
    {x : ℝ^n} (hx : x ∈ frontier Ω) {t : ℝ} (ht : t ∈ Icc 0 T) : u t x = 0 := by
  have hc : ContinuousOn (fun r ↦ u r x) (Icc 0 T) :=
    hu.continuous.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr ↦ ⟨hr, frontier_subset_closure hx⟩)
  exact Set.EqOn.of_subset_closure (hu.boundary x hx) hc continuousOn_const
    Ioo_subset_Icc_self (by rw [closure_Ioo hT.ne]) ht

/-- The heat minimum principle derives nonnegativity from the source data. -/
theorem IsInteriorDirichletSquareSolution.nonneg
    (hu : IsInteriorDirichletSquareSolution Ω T g u)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) (hT : 0 < T)
    (hg : ∀ x ∈ Ω, 0 ≤ g x) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ closure Ω, 0 ≤ u t x := by
  have hzero : ∀ x ∈ closure Ω, 0 ≤ u 0 x := by
    apply le_on_closure (fun x hx ↦ by rw [hu.initial x hx]; exact hg x hx)
      continuousOn_const
    exact hu.continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨⟨le_rfl, hT.le⟩, hx⟩)
  have hc : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.2 p.1)
      (ParabolicMaximum.closedCylinder Ω T) :=
    hu.continuous.comp continuous_swap.continuousOn (fun _ hp ↦ ⟨hp.2, hp.1⟩)
  have h := boundary_le_heat_supersolution hΩ hne hb.isCompact_closure hT
    (fun x t ↦ u t x) hc
    (fun x hx t ht ↦ (hu.space hΩ ht).contDiffAt (hΩ.mem_nhds hx))
    (fun _ hx _ ht ↦ (hu.hasDerivAt hΩ hx ht).differentiableAt)
    (fun x hx t ht ↦ by
      change 0 ≤ deriv (fun r ↦ u r x) t - laplacian (u t) x
      rw [hu.equation t ht x hx]
      exact sq_nonneg _) (M := 0) (by
        intro p hp
        rcases hp with hp | hp
        · rw [hu.boundary_closed hT hp.1 hp.2]
        · rw [hp.2]
          exact hzero p.1 hp.1)
  exact fun t ht x hx ↦ h (x, t) ⟨hx, ht⟩

/-- A compact interior test has a continuous moment, including its initial trace. -/
theorem IsInteriorDirichletSquareSolution.compact_moment_continuous
    (hu : IsInteriorDirichletSquareSolution Ω T g u)
    {φ : ℝ^n → ℝ} (hφ : Continuous φ) (hcpt : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ω) :
    ContinuousOn (fun t ↦ ∫ x, φ x * u t x) (Icc 0 T) := by
  have hf : ContinuousOn (fun q : ℝ × ℝ^n ↦ φ q.2 * u q.1 q.2)
      (Icc 0 T ×ˢ closure (tsupport φ)) :=
    (hφ.comp continuous_snd).continuousOn.mul (hu.continuous.mono (fun _ h ↦
      ⟨h.1, subset_closure (hsupp (by simpa only [(isClosed_tsupport φ).closure_eq] using h.2))⟩))
  have hcont := PDE.continuousOn_setIntegral_of_compact_interval
    (μ := volume) (f := fun t x ↦ φ x * u t x) (isClosed_tsupport φ).measurableSet
    hcpt.closure hcpt.measure_lt_top.ne hf
  have heq (t : ℝ) : (∫ x in tsupport φ, φ x * u t x) = ∫ x, φ x * u t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  simpa only [heq] using hcont

/-- Compact interior moments have their classical derivative and are absolutely
continuous on every interval strictly inside the time cylinder. -/
theorem IsInteriorDirichletSquareSolution.compact_moment_regularity
    (hu : IsInteriorDirichletSquareSolution Ω T g u) (hΩ : IsOpen Ω)
    {φ : ℝ^n → ℝ} (hφ : Continuous φ) (hcpt : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ω) {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ x, φ x * u t x) a b ∧
      ∀ t ∈ Ioo a b, HasDerivAt (fun r ↦ ∫ x, φ x * u r x)
        (∫ x, φ x * deriv (fun r ↦ u r x) t) t := by
  have hs : Icc a b ⊆ Ioo 0 T := Icc_subset_Ioo ha hb
  have hxΩ : closure (tsupport φ) ⊆ Ω := by
    simpa only [(isClosed_tsupport φ).closure_eq] using hsupp
  have hf : ContinuousOn (fun q : ℝ × ℝ^n ↦ φ q.2 * u q.1 q.2)
      (Icc a b ×ˢ closure (tsupport φ)) :=
    (hφ.comp continuous_snd).continuousOn.mul (hu.continuous.mono (fun _ h ↦
      ⟨Ioo_subset_Icc_self (hs h.1), subset_closure (hxΩ h.2)⟩))
  have hD : ContinuousOn (fun q : ℝ × ℝ^n ↦ φ q.2 * deriv (fun r ↦ u r q.2) q.1)
      (Icc a b ×ˢ closure (tsupport φ)) :=
    (hφ.comp continuous_snd).continuousOn.mul
      ((hu.continuous_derivative hΩ).mono (fun _ h ↦ ⟨hs h.1, hxΩ h.2⟩))
  have heq (f : ℝ^n → ℝ) : (∫ x in tsupport φ, φ x * f x) = ∫ x, φ x * f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hcont := PDE.continuousOn_setIntegral_of_compact_interval
    (μ := volume) (f := fun t x ↦ φ x * u t x) (isClosed_tsupport φ).measurableSet
    hcpt.closure hcpt.measure_lt_top.ne hf
  have hDcont := PDE.continuousOn_setIntegral_of_compact_interval
    (μ := volume) (f := fun t x ↦ φ x * deriv (fun r ↦ u r x) t)
    (isClosed_tsupport φ).measurableSet hcpt.closure hcpt.measure_lt_top.ne hD
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :=
    PDE.hasDerivAt_setIntegral_of_compact_interval
      (μ := volume) (f := fun t x ↦ φ x * u t x)
      (D := fun t x ↦ φ x * deriv (fun r ↦ u r x) t)
      (isClosed_tsupport φ).measurableSet hcpt.closure hcpt.measure_lt_top.ne hf hD
      (fun x hx r hr ↦ (hu.hasDerivAt hΩ (hsupp hx)
        (hs (Ioo_subset_Icc_self hr))).const_mul (φ x)) ht
  simp_rw [heq] at hcont hDcont hd
  refine ⟨?_, hd⟩
  apply absolutelyContinuousOnInterval_of_eq_add_integral (hDcont.intervalIntegrable_of_Icc hab)
  intro t ht
  rw [uIcc_of_le hab] at ht
  have hst : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hcont.mono hst) (fun r hr ↦ hd r ⟨hr.1, hr.2.trans_le ht.2⟩)
    ((hDcont.mono hst).intervalIntegrable_of_Icc ht.1)
  linarith

/-- Differentiate an interior compact moment at a positive time by localizing
its time interval. -/
theorem IsInteriorDirichletSquareSolution.hasDerivAt_compact_moment
    (hu : IsInteriorDirichletSquareSolution Ω T g u) (hΩ : IsOpen Ω)
    {φ : ℝ^n → ℝ} (hφ : Continuous φ) (hcpt : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ω) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r ↦ ∫ x, φ x * u r x)
      (∫ x, φ x * deriv (fun r ↦ u r x) t) t := by
  exact (hu.compact_moment_regularity hΩ hφ hcpt hsupp
    (a := t / 2) (b := (t + T) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    (by linarith [ht.1, ht.2])).2 t ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Compact interior testing requires no boundary derivatives of the second factor. -/
theorem integral_mul_laplacian_eq_interior
    {φ v : ℝ^n → ℝ} (hΩ : IsOpen Ω) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) (hv : ContDiffOn ℝ 2 v Ω) :
    (∫ x, φ x * laplacian v x) = ∫ x, laplacian φ x * v x :=
  PDE.DistributionTheory.integral_mul_laplacian_eq_of_contDiffAt hφ hc
    fun _ hx ↦ hv.contDiffAt (hΩ.mem_nhds (hs hx))

/-- A nonnegative test of mass at most one gives the quadratic moment bound,
with no sign assumption on the tested function. -/
theorem sq_integral_mul_le_of_mass_le_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {φ v : X → ℝ}
    (hφ : Integrable φ μ) (hv : Integrable (fun x ↦ φ x * v x) μ)
    (hv2 : Integrable (fun x ↦ φ x * v x ^ 2) μ)
    (hn : ∀ x, 0 ≤ φ x) (hmass : ∫ x, φ x ∂μ ≤ 1) :
    (∫ x, φ x * v x ∂μ) ^ 2 ≤ ∫ x, φ x * v x ^ 2 ∂μ := by
  let m := ∫ x, φ x * v x ∂μ
  have heq : (fun x ↦ φ x * (v x - m) ^ 2) =
      fun x ↦ φ x * v x ^ 2 - 2 * m * (φ x * v x) + m ^ 2 * φ x := by
    funext x
    ring
  have hnint : 0 ≤ ∫ x, φ x * (v x - m) ^ 2 ∂μ :=
    integral_nonneg fun x ↦ mul_nonneg (hn x) (sq_nonneg _)
  rw [heq] at hnint
  have hi : Integrable (fun x ↦ φ x * v x ^ 2 - 2 * m * (φ x * v x)) μ :=
    hv2.sub (hv.const_mul (2 * m))
  rw [integral_add hi (hφ.const_mul (m ^ 2)),
    integral_sub hv2 (hv.const_mul (2 * m)), integral_const_mul, integral_const_mul] at hnint
  have hmass' := mul_le_mul_of_nonneg_left hmass (sq_nonneg m)
  change m ^ 2 ≤ _
  change 0 ≤ (∫ x, φ x * v x ^ 2 ∂μ) - 2 * m * m + m ^ 2 * (∫ x, φ x ∂μ) at hnint
  nlinarith

/-- Compact testing yields the quadratic moment inequality without any sign
assumption on the candidate; the full Laplacian pairing remains explicit. -/
theorem IsInteriorDirichletSquareSolution.compact_moment_reaction_le
    (hu : IsInteriorDirichletSquareSolution Ω T g u) (hΩ : IsOpen Ω)
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) (hφpos : ∀ x, 0 ≤ φ x) (hmass : ∫ x, φ x ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    (∫ x, φ x * u t x) ^ 2 ≤ deriv (fun r ↦ ∫ x, φ x * u r x) t -
      ∫ x, laplacian φ x * u t x := by
  have huc : ContinuousOn (u t) (closure Ω) :=
    hu.continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨Ioo_subset_Icc_self ht, hx⟩)
  have hlocal : ContinuousOn (u t) (tsupport φ) := huc.mono (hs.trans subset_closure)
  have hiu : Integrable (fun x ↦ φ x * u t x) :=
    hc.integrable_of_continuousOn_tsupport (hφ.continuous.continuousOn.mul hlocal) fun x hx ↦ by
      simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hiR : Integrable (fun x ↦ φ x * u t x ^ 2) :=
    hc.integrable_of_continuousOn_tsupport (hφ.continuous.continuousOn.mul (hlocal.pow 2))
      fun x hx ↦ by simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hiL : Integrable (fun x ↦ φ x * laplacian (u t) x) := by
    apply hc.integrable_of_continuousOn_tsupport
    · intro x hx
      exact (hφ.continuous.continuousAt.mul
        ((hu.space hΩ ht).contDiffAt
          (hΩ.mem_nhds (hs hx))).continuousAt_coordinate_laplacian).continuousWithinAt
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hj := sq_integral_mul_le_of_mass_le_one
    (hφ.continuous.integrable_of_hasCompactSupport hc) hiu hiR hφpos hmass
  have hid : (∫ x, φ x * deriv (fun r ↦ u r x) t) =
      (∫ x, φ x * laplacian (u t) x) + ∫ x, φ x * u t x ^ 2 := by
    rw [← integral_add hiL hiR]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport φ
    · have heq := hu.equation t ht x (hs hx)
      linear_combination φ x * heq
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, add_zero]
  rw [(hu.hasDerivAt_compact_moment hΩ hφ.continuous hc hs ht).deriv, hid,
    integral_mul_laplacian_eq_interior hΩ hφ hc hs (hu.space hΩ ht)]
  linarith

/-- Interior testing gives the quadratic moment inequality with the additive
error supplied by the truncated eigenfunction. All Green terms have compact
support strictly inside the spatial domain. -/
theorem IsInteriorDirichletSquareSolution.compact_moment_inequality
    (hu : IsInteriorDirichletSquareSolution Ω T g u) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) {φ : ℝ^n → ℝ} {lambda δ C : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω)
    (hφpos : ∀ x, 0 ≤ φ x) (hmass : ∫ x, φ x ≤ 1)
    (hlap : ∀ x ∈ Ω, -lambda * φ x - δ ≤ laplacian φ x) (hδ : 0 ≤ δ)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hn : ∀ x ∈ Ω, 0 ≤ u t x) (hC : ∫ x in Ω, u t x ≤ C) :
    (∫ x, φ x * u t x) ^ 2 ≤ deriv (fun r ↦ ∫ x, φ x * u r x) t +
      lambda * (∫ x, φ x * u t x) + δ * C := by
  have huc : ContinuousOn (u t) (closure Ω) :=
    hu.continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨Ioo_subset_Icc_self ht, hx⟩)
  have hint {f : ℝ^n → ℝ} (hf : ContinuousOn f (closure Ω)) : IntegrableOn f Ω :=
    hf.integrableOn_of_subset_isCompact hb.isCompact_closure hΩ.measurableSet
      subset_closure hb.measure_lt_top.ne
  have heq : (∫ x in Ω, φ x * u t x) = ∫ x, φ x * u t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)), zero_mul]
  have hLeq : (∫ x in Ω, laplacian φ x * u t x) = ∫ x, laplacian φ x * u t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)), zero_mul]
  have his : IntegrableOn (fun x ↦ -lambda * (φ x * u t x)) Ω :=
    (hint (hφ.continuous.continuousOn.mul huc)).const_mul (-lambda)
  have hdiff := setIntegral_mono_on (his.sub ((hint huc).const_mul δ))
    (hint (hφ.continuous_coordinate_laplacian.continuousOn.mul huc)) hΩ.measurableSet
    (fun x hx ↦ by
      simpa only [Pi.sub_apply, Pi.mul_apply, sub_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right (hlap x hx) (hn x hx))
  change (∫ x in Ω, -lambda * (φ x * u t x) - δ * u t x) ≤
    ∫ x in Ω, laplacian φ x * u t x at hdiff
  rw [integral_sub his ((hint huc).const_mul δ),
    integral_const_mul, integral_const_mul, heq, hLeq] at hdiff
  have hreaction := hu.compact_moment_reaction_le hΩ hφ hc hs hφpos hmass ht
  have hbound := mul_le_mul_of_nonneg_left hC hδ
  linarith

end HeatEquation.Nonlinear
