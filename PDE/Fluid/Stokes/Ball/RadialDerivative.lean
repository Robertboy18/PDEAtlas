/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.Meridional
public import PDE.CoordinateSystems.Axisymmetric.Representative
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Radial derivatives of meridian coefficients

For a field `u` with weak derivatives `Du` on the ball, the Euler field
`(E u)ᵢ = ∑ⱼ xⱼ ∂ⱼ uᵢ` satisfies `∫ ⟪E u, Φ⟫ = -∫ ⟪u, 3 Φ + E Φ⟫` for every smooth `Φ` vanishing
on the sphere, by the integration by parts of
`PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero` against `Tᵢⱼ = xⱼ Φᵢ`. Tested with
the purely polar meridional fields `v(-l B / s, B)`, whose radial component vanishes, this gives
the weak derivative of the polar coefficient: `r b` has the weak derivative `b + e` on `(0, R)`,
where `b` is the meridian coefficient of `u` on `X_l` and `e` that of the rotation average of
`E u`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real MvPolynomial Filter
open PDE (partialDeriv laplacian divergence)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff Topology

namespace PDE.Fluid.Stokes.Ball

/-- The Euler field `(E u)ᵢ = ∑ⱼ xⱼ ∂ⱼ uᵢ` of weak derivatives `Du i j = ∂ⱼ uᵢ`. -/
def eulerField (Du : Fin 3 → Fin 3 → ℝ^3 → ℝ) (x : ℝ^3) : ℝ^3 :=
  WithLp.toLp 2 fun i ↦ ∑ j, x j * Du i j x

/-- **The Euler identity.** For `u` with integrable components and weak derivatives on the
ball and a smooth field `Φ` vanishing on the sphere,
`∫_B ⟪E u, Φ⟫ = -∫_B ∑ᵢ uᵢ (3 Φᵢ + ∑ⱼ xⱼ ∂ⱼ Φᵢ)`. -/
theorem integral_inner_eulerField {R : ℝ} (hR : 0 < R) {u : ℝ^3 → ℝ^3}
    {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    {Φ : ℝ^3 → ℝ^3} (hΦ : ContDiff ℝ ∞ Φ) (hΦR : ∀ x : ℝ^3, ‖x‖ = R → Φ x = 0) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪eulerField Du x, Φ x⟫ =
      -∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, u x i *
        (3 * Φ x i + ∑ j, x j * ∂[j] (fun y ↦ Φ y i) x) := by
  set B := Metric.ball (0 : ℝ^3) R
  have hΦi (i : Fin 3) : ContDiff ℝ ∞ (fun y ↦ Φ y i) := (contDiff_piLp_apply 2).comp hΦ
  have hcoord (j : Fin 3) : ContDiff ℝ ∞ (fun y : ℝ^3 ↦ y j) := contDiff_piLp_apply 2
  set T : Fin 3 → Fin 3 → ℝ^3 → ℝ := fun i j y ↦ y j * Φ y i with hT
  have hTC : ∀ i j, ContDiff ℝ ∞ (T i j) := fun i j ↦ (hcoord j).mul (hΦi i)
  have hTn : ∀ x : ℝ^3, ‖x‖ = R → ∀ i, ∑ j, T i j x * x j = 0 := by
    intro x hx i
    simp [hT, hΦR x hx]
  have htool := PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero hR hTC hTn
    (v := fun i x ↦ u x i) hu hDu hweak
  have hdT (x : ℝ^3) (i : Fin 3) : ∑ j, ∂[j] (T i j) x =
      3 * Φ x i + ∑ j, x j * ∂[j] (fun y ↦ Φ y i) x := by
    have h (j : Fin 3) : ∂[j] (T i j) x = Φ x i + x j * ∂[j] (fun y ↦ Φ y i) x := by
      simp only [hT]
      rw [partialDeriv_mul ((hcoord j).differentiable (by simp) x)
        ((hΦi i).differentiable (by simp) x), partialDeriv_coord]
      simp only [↓reduceIte, one_mul]
    simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
  have hmul : ∀ {g : ℝ^3 → ℝ}, Continuous g → ∀ {f : ℝ^3 → ℝ}, IntegrableOn f B →
      Integrable (fun x ↦ f x * g x) (volume.restrict B) := fun hg _ hf ↦
    hf.mul_continuousOn_of_subset hg.continuousOn measurableSet_ball
      (isCompact_closedBall 0 R) Metric.ball_subset_closedBall
  have hcE (i : Fin 3) : Continuous fun x : ℝ^3 ↦ 3 * Φ x i + ∑ j, x j * ∂[j] (fun y ↦ Φ y i) x :=
    (continuous_const.mul (hΦi i).continuous).add (continuous_finsetSum _ fun j _ ↦
      (hcoord j).continuous.mul (((hΦi i).partialDeriv j).continuous))
  have hI1 : Integrable (fun x ↦ ∑ i, u x i * (3 * Φ x i + ∑ j, x j * ∂[j] (fun y ↦ Φ y i) x))
      (volume.restrict B) := integrable_finsetSum _ fun i _ ↦ hmul (hcE i) (hu i)
  have hI2 : Integrable (fun x ↦ ∑ i, ∑ j, Du i j x * T i j x) (volume.restrict B) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      hmul (hTC i j).continuous (hDu i j)
  have hsplit : ∫ x in B, ∑ i, ∑ j, (u x i * ∂[j] (T i j) x + Du i j x * T i j x) =
      (∫ x in B, ∑ i, u x i * (3 * Φ x i + ∑ j, x j * ∂[j] (fun y ↦ Φ y i) x)) +
        ∫ x in B, ∑ i, ∑ j, Du i j x * T i j x := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdT]
  have hE : ∫ x in B, ∑ i, ∑ j, Du i j x * T i j x = ∫ x in B, ⟪eulerField Du x, Φ x⟫ := by
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [hT, eulerField, EuclideanSpace.real_inner_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hsplit, hE] at htool
  linarith

/-- A measurable equivariant field with the pairings of a field `f` integrable on the ball:
the rotation average of a strongly measurable representative of `f` on the ball. -/
theorem exists_average_representative {R : ℝ} {f : ℝ^3 → ℝ^3}
    (hf : IntegrableOn f (Metric.ball (0 : ℝ^3) R)) :
    ∃ g : ℝ^3 → ℝ^3, Measurable g ∧ IsEquivariantUnderAxisRotation g ∧
      IntegrableOn g (Metric.ball (0 : ℝ^3) R) ∧
      ∀ Φ : ℝ^3 → ℝ^3, Continuous Φ → IsEquivariantUnderAxisRotation Φ →
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪g x, Φ x⟫ =
          ∫ x in Metric.ball (0 : ℝ^3) R, ⟪f x, Φ x⟫ := by
  set B := Metric.ball (0 : ℝ^3) R
  set f₀ := hf.aestronglyMeasurable.mk f with hf₀
  have hf₀m : StronglyMeasurable f₀ := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hae : f =ᵐ[volume.restrict B] f₀ := hf.aestronglyMeasurable.ae_eq_mk
  set f₁ := B.indicator f₀ with hf₁
  have hf₁m : StronglyMeasurable f₁ := hf₀m.indicator measurableSet_ball
  have hae₁ : f =ᵐ[volume.restrict B] f₁ := by
    filter_upwards [hae, ae_restrict_mem measurableSet_ball] with x hx hxB
    rw [hf₁, indicator_of_mem hxB, hx]
  have hf₁int : IntegrableOn f₁ B := hf.congr_fun_ae hae₁
  refine ⟨axisAverage f₁, (stronglyMeasurable_axisAverage hf₁m).measurable,
    axisAverage_axisRotation f₁, integrableOn_axisAverage hf₁m hf₁int, fun Φ hΦ hΦeq ↦ ?_⟩
  rw [setIntegral_inner_axisAverage hf₁m hf₁int hΦ hΦeq]
  exact integral_congr_ae (by filter_upwards [hae₁] with x hx; rw [hx])

/-- The Euler field of integrable weak derivatives is integrable on the ball. -/
theorem integrableOn_eulerField {R : ℝ} {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R)) :
    IntegrableOn (eulerField Du) (Metric.ball (0 : ℝ^3) R) := by
  have hc (i j : Fin 3) : IntegrableOn (fun x ↦ Du i j x * x j) (Metric.ball (0 : ℝ^3) R) :=
    have hcj : Continuous fun x : ℝ^3 ↦ x j := (EuclideanSpace.proj j).continuous
    (hDu i j).mul_continuousOn_of_subset hcj.continuousOn
      measurableSet_ball (isCompact_closedBall 0 R) Metric.ball_subset_closedBall
  have heq : eulerField Du = fun x ↦ ∑ i, (∑ j, Du i j x * x j) •
      EuclideanSpace.single i (1 : ℝ) := by
    funext x
    ext k
    simp [eulerField, Pi.single_apply, mul_comm]
  rw [heq]
  exact integrable_finsetSum _ fun i _ ↦
    (integrable_finsetSum _ fun j _ ↦ hc i j).smul_const _

/-- **The weak radial derivative of the polar coefficient.** Let `u` have integrable
components and weak derivatives on the ball, let `w` be a measurable equivariant field equal to
`u` almost everywhere on the ball, and let `e` be a measurable equivariant field with the
pairings of the Euler field `E u` against continuous equivariant fields. With `b` and `c` the
meridian coefficients of `w` and `e` on `X_l`, the function `r b(r)` has the weak derivative
`b + c` on `(0, R)`: `∫ r b φ' = -∫ (b + c) φ` for every smooth `φ` with compact support in
`(0, R)`. -/
theorem integral_mul_meridianCoefficient_polar_mul_deriv {R : ℝ} (hR : 0 < R) {l : ℕ}
    (hl : 1 ≤ l)
    {u : ℝ^3 → ℝ^3} {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    {w : ℝ^3 → ℝ^3} (hwm : Measurable w) (hw : IsEquivariantUnderAxisRotation w)
    (hwint : IntegrableOn w (Metric.ball (0 : ℝ^3) R))
    (huw : u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w)
    {e : ℝ^3 → ℝ^3} (hem : Measurable e) (he : IsEquivariantUnderAxisRotation e)
    (heint : IntegrableOn e (Metric.ball (0 : ℝ^3) R))
    (hepair : ∀ Φ : ℝ^3 → ℝ^3, Continuous Φ → IsEquivariantUnderAxisRotation Φ →
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪e x, Φ x⟫ =
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪eulerField Du x, Φ x⟫)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ioo 0 R) :
    ∫ r in Ioo 0 R, r * meridianCoefficient w l 1 r * deriv φ r =
      -∫ r in Ioo 0 R, (meridianCoefficient w l 1 r + meridianCoefficient e l 1 r) * φ r := by
  obtain ⟨F, hF, hFcs, hFsupp, hF0, hFφ⟩ := exists_pow_mul_comp_sq_eq hR hφ hcs hsupp (l + 1)
  set A : ℝ → ℝ := fun s ↦ -(l * F s / s) with hA
  have hAC : ContDiff ℝ ∞ A := by
    refine contDiff_iff_contDiffAt.mpr fun s ↦ ?_
    rcases eq_or_ne s 0 with rfl | hs
    · have hev : A =ᶠ[𝓝 0] fun _ ↦ (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hF0] with t ht
        simp [hA, ht]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact ((contDiffAt_const.mul hF.contDiffAt).div contDiffAt_id hs).neg
  have hR2 : R ^ 2 ∉ tsupport F := fun h ↦ lt_irrefl _ (hFsupp h)
  have hFR : F (R ^ 2) = 0 := image_eq_zero_of_notMem_tsupport hR2
  set Φ := meridionalTest l A F with hΦdef
  have hΦC : ContDiff ℝ ∞ Φ := contDiff_meridionalTest l hAC hF
  have hΦR : ∀ x : ℝ^3, ‖x‖ = R → Φ x = 0 := by
    intro x hx
    ext i
    simp [hΦdef, meridionalTest_apply, hx, hA, hFR]
  have hEu := integral_inner_eulerField hR hu hDu hweak hΦC hΦR
  -- the transformed test field
  set A₂ : ℝ → ℝ := fun s ↦ 3 * A s + (2 * s * deriv A s + ((l : ℝ) + 1) * A s) with hA₂
  set B₂ : ℝ → ℝ := fun s ↦ 3 * F s + (2 * s * deriv F s + ((l : ℝ) - 1) * F s) with hB₂
  have hrhs : ∀ x, ∑ i, u x i * (3 * Φ x i + ∑ j, x j * ∂[j] (fun y ↦ Φ y i) x) =
      ⟪u x, meridionalTest l A₂ B₂ x⟫ := by
    intro x
    rw [EuclideanSpace.real_inner_eq_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := sum_partialDeriv_meridionalTest_mul l hAC hF x i
    have hcomm : ∑ j, x j * ∂[j] (fun y ↦ Φ y i) x =
        ∑ j, ∂[j] (fun y ↦ meridionalTest l A F y i) x * x j :=
      Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    rw [hcomm, h]
    simp only [hΦdef, meridionalTest_apply, hA₂, hB₂]
    ring
  have hA₂c : Continuous A₂ := by
    have h1 : Continuous (deriv A) := hAC.continuous_deriv (by simp)
    simp only [hA₂]
    exact (continuous_const.mul hAC.continuous).add
      (((continuous_const.mul continuous_id).mul h1).add (continuous_const.mul hAC.continuous))
  have hB₂c : Continuous B₂ := by
    have h1 : Continuous (deriv F) := hF.continuous_deriv (by simp)
    simp only [hB₂]
    exact (continuous_const.mul hF.continuous).add
      (((continuous_const.mul continuous_id).mul h1).add (continuous_const.mul hF.continuous))
  have hswap : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, meridionalTest l A₂ B₂ x⟫ =
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪w x, meridionalTest l A₂ B₂ x⟫ :=
    integral_congr_ae (by filter_upwards [huw] with x hx; rw [hx])
  have hmain : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪e x, Φ x⟫ =
      -∫ x in Metric.ball (0 : ℝ^3) R, ⟪w x, meridionalTest l A₂ B₂ x⟫ := by
    rw [hepair Φ hΦC.continuous (meridionalTest_axisRotation l A F), hEu, ← hswap]
    congr 1
    exact integral_congr_ae (ae_of_all _ hrhs)
  rw [hΦdef, setIntegral_inner_meridionalTest hem he heint l hAC.continuous hF.continuous,
    setIntegral_inner_meridionalTest hwm hw hwint l hA₂c hB₂c] at hmain
  -- the one-dimensional identity
  have hpos {r : ℝ} (hr : 0 < r) : r ^ (l + 1) * A (r ^ 2) + l * r ^ (l - 1) * F (r ^ 2) = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    simp only [hA, Nat.add_sub_cancel]
    field_simp
    ring
  have hAd {s : ℝ} (hs : 0 < s) : deriv A s = -(l * (deriv F s * s - F s) / s ^ 2) := by
    have h : HasDerivAt A (-(((l : ℝ) * deriv F s * id s - (l : ℝ) * F s * 1) / id s ^ 2)) s :=
      (((hF.differentiable (by simp) s).hasDerivAt.const_mul (l : ℝ)).div
        (hasDerivAt_id s) hs.ne').neg
    rw [h.deriv]
    simp only [id]
    ring
  have hpos₂ {r : ℝ} (hr : 0 < r) :
      r ^ (l + 1) * A₂ (r ^ 2) + l * r ^ (l - 1) * B₂ (r ^ 2) = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hr2 : 0 < r ^ 2 := by positivity
    simp only [hA₂, hB₂]
    rw [hAd hr2]
    simp only [hA, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have h2π : (2 * π) ≠ 0 := by positivity
  have hb := locallyIntegrableOn_meridianCoefficient hwm hw hwint l 1
  have hc := locallyIntegrableOn_meridianCoefficient hem he heint l 1
  have h1 : ∫ r in Ioo 0 R, φ r * meridianCoefficient e l 1 r =
      -∫ r in Ioo 0 R, (φ r + r * deriv φ r) * meridianCoefficient w l 1 r := by
    have hL : ∫ r in Ioo 0 R, r ^ 2 * ((r ^ (l + 1) * A (r ^ 2) + l * r ^ (l - 1) * F (r ^ 2)) *
        meridianCoefficient e l 0 r + r ^ (l - 1) * F (r ^ 2) * meridianCoefficient e l 1 r) =
        ∫ r in Ioo 0 R, φ r * meridianCoefficient e l 1 r := by
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
      rw [hpos hr.1, ← hFφ r hr.1]
      obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    have hR' : ∫ r in Ioo 0 R, r ^ 2 * ((r ^ (l + 1) * A₂ (r ^ 2) + l * r ^ (l - 1) *
        B₂ (r ^ 2)) * meridianCoefficient w l 0 r + r ^ (l - 1) * B₂ (r ^ 2) *
          meridianCoefficient w l 1 r) =
        ∫ r in Ioo 0 R, (φ r + r * deriv φ r) * meridianCoefficient w l 1 r := by
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
      have hev : (fun s ↦ s ^ (l + 1) * F (s ^ 2)) =ᶠ[𝓝 r] φ := by
        filter_upwards [Ioi_mem_nhds hr.1] with t ht
        exact hFφ t ht
      have hd := mul_deriv_pow_mul_comp_sq (hF.differentiable (by simp)) (l + 1) r
      rw [hev.deriv_eq] at hd
      rw [hpos₂ hr.1, ← hFφ r hr.1, hd]
      simp only [hB₂]
      obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
    rw [hL, hR'] at hmain
    have h3 : 2 * π * ((∫ r in Ioo 0 R, φ r * meridianCoefficient e l 1 r) +
        ∫ r in Ioo 0 R, (φ r + r * deriv φ r) * meridianCoefficient w l 1 r) = 0 := by
      linear_combination hmain
    linarith [(mul_eq_zero.mp h3).resolve_left h2π]
  have hφc := hφ.continuous
  have hdφ : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hint (q : ℝ → ℝ) (hq : LocallyIntegrableOn q (Ioo 0 R)) {ψ : ℝ → ℝ}
      (hψ : Continuous ψ) (hψs : tsupport ψ ⊆ Ioo 0 R) (hψc : HasCompactSupport ψ) :
      IntegrableOn (fun r ↦ ψ r * q r) (Ioo 0 R) := by
    have := PDE.Analysis.Evolution.HasWeakTimeDerivativeOn.integrable_mul_test hq hψ hψc hψs
    exact (this.congr (ae_of_all _ fun r ↦ mul_comm _ _)).integrableOn
  have hrφ : tsupport (fun r ↦ r * deriv φ r) ⊆ Ioo 0 R :=
    (tsupport_mul_subset_right).trans (tsupport_deriv_subset.trans hsupp)
  have hrφc : HasCompactSupport fun r ↦ r * deriv φ r := hcs.deriv.mul_left
  have hIb := hint _ hb hφc hsupp hcs
  have hIc := hint _ hc hφc hsupp hcs
  have hId := hint _ hb (continuous_id.mul hdφ) hrφ hrφc
  have hsplitb : ∫ r in Ioo 0 R, (φ r + r * deriv φ r) * meridianCoefficient w l 1 r =
      (∫ r in Ioo 0 R, φ r * meridianCoefficient w l 1 r) +
        ∫ r in Ioo 0 R, r * deriv φ r * meridianCoefficient w l 1 r := by
    rw [← integral_add (f := fun r ↦ φ r * meridianCoefficient w l 1 r)
      (g := fun r ↦ r * deriv φ r * meridianCoefficient w l 1 r) hIb hId]
    exact integral_congr_ae (ae_of_all _ fun r ↦ by ring)
  rw [hsplitb] at h1
  have hgoal : ∫ r in Ioo 0 R, (meridianCoefficient w l 1 r + meridianCoefficient e l 1 r) *
      φ r = (∫ r in Ioo 0 R, φ r * meridianCoefficient w l 1 r) +
        ∫ r in Ioo 0 R, φ r * meridianCoefficient e l 1 r := by
    rw [← integral_add (f := fun r ↦ φ r * meridianCoefficient w l 1 r)
      (g := fun r ↦ φ r * meridianCoefficient e l 1 r) hIb hIc]
    exact integral_congr_ae (ae_of_all _ fun r ↦ by ring)
  have hlhs : ∫ r in Ioo 0 R, r * meridianCoefficient w l 1 r * deriv φ r =
      ∫ r in Ioo 0 R, r * deriv φ r * meridianCoefficient w l 1 r :=
    integral_congr_ae (ae_of_all _ fun r ↦ by ring)
  rw [hgoal, hlhs]
  linarith [h1]

end PDE.Fluid.Stokes.Ball
