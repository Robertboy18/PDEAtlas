/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.RadialDerivative
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.Analysis.Evolution.Time.WeakDerivative.Basic

/-!
# Meridional coefficients of weak Neumann-Stokes eigenfunctions

Let `a` and `b` be the meridian coefficients of a weak eigenfunction on `Y_l` and `X_l`, and
`c` that of the averaged Euler field on `X_l`. The curl tests
`curl(F(‖x‖²)(x × ∇h_l))` of the eigenvalue equation, together with the weak derivative
`(r b)' = b + c`, show that the vorticity coefficient `ω = (l (l + 1) a - b - c) / r` solves the
radial equation in the sense of `ae_eq_smul_radialSolution_of_weak`, so `ω = A₀ r^l G_l(μ r²)`
almost everywhere. The same Euler identity gives `(r a)' = a + c₀` with `c₀` the coefficient of
the averaged Euler field on `Y_l`, and the gradient tests `∇(f(‖x‖²) h_l)` give the divergence
relation `(r² a)' = r b`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real MvPolynomial Filter
open PDE (partialDeriv laplacian divergence)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open PDE.Analysis.Evolution (HasWeakTimeDerivativeOn)
open scoped RealInnerProductSpace ContDiff Topology

namespace PDE.Fluid.Stokes.Ball

/-- Outside the topological support of `F`, the function and its first two derivatives
vanish. -/
private theorem jet_eq_zero_of_notMem_tsupport {F : ℝ → ℝ} {s : ℝ} (h : s ∉ tsupport F) :
    F s = 0 ∧ deriv F s = 0 ∧ deriv (deriv F) s = 0 :=
  ⟨image_eq_zero_of_notMem_tsupport h,
    image_eq_zero_of_notMem_tsupport fun h' ↦ h (tsupport_deriv_subset h'),
    image_eq_zero_of_notMem_tsupport fun h' ↦ h (tsupport_deriv_subset (tsupport_deriv_subset h'))⟩

/-- **The curl identity in one dimension.** For a weak eigenfunction of meridional parity and
every smooth `F` with compact support in `(-∞, R²)`, with `K = 4 s F'' + (4l + 6) F' + μ F`,
`∫₀^R r^{l+1} (l (l + 1) K(r²) a + ((l + 1) K(r²) + 2 r² K'(r²)) b) dr = 0`. -/
theorem integral_curl_of_weak_eigen {R μ ε : ℝ} (hR : 0 < R) {l : ℕ} (hl : 1 ≤ l)
    (hpar : modeParity .meridional l = ε) {u : ℝ^3 → ℝ^3} {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Du i i x = 0)
    (heig : ∀ v : ℝ^3 → ℝ^3, ContDiff ℝ ∞ v → (∀ x, divergence v x = 0) →
      IsEquivariantUnderAxisRotation v →
      (∀ x, v (equatorialReflection x) = ε • equatorialReflection (v x)) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, v x⟫)
    {w : ℝ^3 → ℝ^3} (hwm : Measurable w) (hw : IsEquivariantUnderAxisRotation w)
    (hwint : IntegrableOn w (Metric.ball (0 : ℝ^3) R))
    (huw : u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hFsupp : tsupport F ⊆ Iio (R ^ 2)) :
    ∫ r in Ioo 0 R, r ^ (l + 1) * (l * (l + 1) *
      (4 * r ^ 2 * deriv (deriv F) (r ^ 2) + (4 * l + 6) * deriv F (r ^ 2) + μ * F (r ^ 2)) *
        meridianCoefficient w l 0 r + (((l : ℝ) + 1) *
      (4 * r ^ 2 * deriv (deriv F) (r ^ 2) + (4 * l + 6) * deriv F (r ^ 2) + μ * F (r ^ 2)) +
        2 * r ^ 2 * deriv (fun s ↦ 4 * s * deriv (deriv F) s + (4 * l + 6) * deriv F s +
          μ * F s) (r ^ 2)) * meridianCoefficient w l 1 r) = 0 := by
  set A : ℝ → ℝ := fun s ↦ 2 * l * deriv F s with hA
  set B : ℝ → ℝ := fun s ↦ -(2 * s * deriv F s + ((l : ℝ) + 1) * F s) with hB
  set K : ℝ → ℝ := fun s ↦ 4 * s * deriv (deriv F) s + (4 * l + 6) * deriv F s + μ * F s
    with hK
  have hD1 : ContDiff ℝ ∞ (deriv F) := hF.iterate_deriv 1
  have hD2 : ContDiff ℝ ∞ (deriv (deriv F)) := by
    simpa [Function.iterate_succ] using hF.iterate_deriv 2
  have hAC : ContDiff ℝ ∞ A := contDiff_const.mul hD1
  have hBC : ContDiff ℝ ∞ B := (((contDiff_const.mul contDiff_id).mul hD1).add
    (contDiff_const.mul hF)).neg
  have hKC : ContDiff ℝ ∞ K := (((contDiff_const.mul contDiff_id).mul hD2).add
    (contDiff_const.mul hD1)).add (contDiff_const.mul hF)
  obtain ⟨hF0, hF1, hF2⟩ := jet_eq_zero_of_notMem_tsupport fun h ↦ lt_irrefl _ (hFsupp h)
  have hid := curlTest_identities hF l μ
  have hfree (s : ℝ) : 2 * s * deriv A s + ((l : ℝ) + 3) * A s + 2 * l * deriv B s = 0 :=
    (hid s).1
  have hAd (s : ℝ) : deriv A s = 2 * l * deriv (deriv F) s :=
    ((hD1.differentiable (by simp) s).hasDerivAt.const_mul _).deriv
  have hBd (s : ℝ) : deriv B s = -(2 * deriv F s + 2 * s * deriv (deriv F) s +
      ((l : ℝ) + 1) * deriv F s) :=
    ((((hasDerivAt_id' s).const_mul 2).mul (hD1.differentiable (by simp) s).hasDerivAt).add
      ((hF.differentiable (by simp) s).hasDerivAt.const_mul ((l : ℝ) + 1))).neg.deriv.trans
        (by ring)
  have hbc1 : 2 * R ^ 2 * deriv A (R ^ 2) + ((l : ℝ) + 1) * A (R ^ 2) =
      (fun _ : ℝ ↦ (0 : ℝ)) (R ^ 2) := by
    rw [hAd]
    simp only [hA, hF1, hF2]
    ring
  have hbc2 : 2 * R ^ 2 * deriv B (R ^ 2) + ((l : ℝ) - 1) * B (R ^ 2) = 0 := by
    rw [hBd]
    simp only [hB, hF0, hF1, hF2]
    ring
  have hNeu := integral_inner_meridional_eq_zero_of_weak_eigen hR hpar hu hDu hweak hdiv heig
    hAC hBC contDiff_const hfree hbc1 hbc2
  have hfA : (fun s ↦ radialLaplacian ((l : ℝ) + 1) A s - 2 * deriv (fun _ : ℝ ↦ (0 : ℝ)) s +
      μ * A s) = fun s ↦ 2 * l * deriv K s := by
    funext s
    rw [deriv_const, mul_zero, sub_zero]
    exact (hid s).2.1
  have hfB : (fun s ↦ 2 * A s + radialLaplacian ((l : ℝ) - 1) B s - (fun _ : ℝ ↦ (0 : ℝ)) s +
      μ * B s) = fun s ↦ -(2 * s * deriv K s + ((l : ℝ) + 1) * K s) := by
    funext s
    rw [sub_zero]
    exact (hid s).2.2
  rw [hfA, hfB] at hNeu
  have hKd : Continuous (deriv K) := hKC.continuous_deriv (by simp)
  have hc1 : Continuous fun s ↦ 2 * (l : ℝ) * deriv K s := continuous_const.mul hKd
  have hc2 : Continuous fun s ↦ -(2 * s * deriv K s + ((l : ℝ) + 1) * K s) :=
    (((continuous_const.mul continuous_id).mul hKd).add (continuous_const.mul hKC.continuous)).neg
  have hswap : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, meridionalTest l
      (fun s ↦ 2 * l * deriv K s) (fun s ↦ -(2 * s * deriv K s + ((l : ℝ) + 1) * K s)) x⟫ =
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪w x, meridionalTest l
      (fun s ↦ 2 * l * deriv K s) (fun s ↦ -(2 * s * deriv K s + ((l : ℝ) + 1) * K s)) x⟫ :=
    integral_congr_ae (by filter_upwards [huw] with x hx; rw [hx])
  rw [hswap, setIntegral_inner_meridionalTest hwm hw hwint l hc1 hc2] at hNeu
  have h0 := (mul_eq_zero.mp hNeu).resolve_left (by positivity)
  rw [← neg_eq_zero, ← integral_neg] at h0
  refine Eq.trans (setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_) h0
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel, hK]
  push_cast
  ring

/-- **The vorticity coefficient.** For a weak eigenfunction of meridional parity with
equivariant representative `w`, and `e` an equivariant field with the pairings of the Euler
field `∑ⱼ xⱼ ∂ⱼ u`, the coefficient `ω = (l (l + 1) a - b - c) / r` of the azimuthal vorticity
(`a`, `b` the meridian coefficients of `w` on `Y_l`, `X_l` and `c` that of `e` on `X_l`) is a
multiple of the regular radial solution `r^l G_l(μ r²)` almost everywhere on `(0, R)`. -/
theorem vorticity_ae_eq_of_weak_eigen {R μ ε : ℝ} (hR : 0 < R) {l : ℕ} (hl : 1 ≤ l)
    (hpar : modeParity .meridional l = ε) {u : ℝ^3 → ℝ^3} {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Du i i x = 0)
    (heig : ∀ v : ℝ^3 → ℝ^3, ContDiff ℝ ∞ v → (∀ x, divergence v x = 0) →
      IsEquivariantUnderAxisRotation v →
      (∀ x, v (equatorialReflection x) = ε • equatorialReflection (v x)) →
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j, Du i j x * ∂[j] (fun y ↦ v y i) x =
        μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, v x⟫)
    {w : ℝ^3 → ℝ^3} (hwm : Measurable w) (hw : IsEquivariantUnderAxisRotation w)
    (hwint : IntegrableOn w (Metric.ball (0 : ℝ^3) R))
    (huw : u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w)
    {e : ℝ^3 → ℝ^3} (hem : Measurable e) (he : IsEquivariantUnderAxisRotation e)
    (heint : IntegrableOn e (Metric.ball (0 : ℝ^3) R))
    (hepair : ∀ Φ : ℝ^3 → ℝ^3, Continuous Φ → IsEquivariantUnderAxisRotation Φ →
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪e x, Φ x⟫ =
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪eulerField Du x, Φ x⟫) :
    ∃ A₀ : ℝ, (fun r ↦ (l * (l + 1) * meridianCoefficient w l 0 r - meridianCoefficient w l 1 r -
        meridianCoefficient e l 1 r) / r) =ᵐ[volume.restrict (Ioo 0 R)]
      fun r ↦ A₀ * radialSolution l μ r := by
  set a := meridianCoefficient w l 0 with ha
  set b := meridianCoefficient w l 1 with hb
  set c := meridianCoefficient e l 1 with hc
  have hal := locallyIntegrableOn_meridianCoefficient hwm hw hwint l 0
  have hbl := locallyIntegrableOn_meridianCoefficient hwm hw hwint l 1
  have hcl := locallyIntegrableOn_meridianCoefficient hem he heint l 1
  have hloc : LocallyIntegrableOn (fun r ↦ (l * (l + 1) * a r - b r - c r) / r) (Ioo 0 R) := by
    simpa only [Pi.sub_apply, div_eq_mul_inv] using (((hal.continuousOn_mul
      (g := fun _ ↦ (l : ℝ) * (l + 1)) continuousOn_const isOpen_Ioo.isLocallyClosed).sub
      hbl).sub hcl).mul_continuousOn (g := fun r : ℝ ↦ r⁻¹)
      (continuousOn_inv₀.mono fun r hr ↦ hr.1.ne') isOpen_Ioo.isLocallyClosed
  refine ae_eq_smul_radialSolution_of_weak hR hloc fun F hF hFcs hFsupp hK0 ↦ ?_
  obtain ⟨δ, hδ, hK0⟩ := hK0
  set K : ℝ → ℝ := fun s ↦ 4 * s * deriv (deriv F) s + (4 * l + 6) * deriv F s + μ * F s
    with hK
  have hD1 : ContDiff ℝ ∞ (deriv F) := hF.iterate_deriv 1
  have hD2 : ContDiff ℝ ∞ (deriv (deriv F)) := by
    simpa [Function.iterate_succ] using hF.iterate_deriv 2
  have hKC : ContDiff ℝ ∞ K := (((contDiff_const.mul contDiff_id).mul hD2).add
    (contDiff_const.mul hD1)).add (contDiff_const.mul hF)
  have hKsub : tsupport K ⊆ tsupport F := by
    refine closure_minimal (fun s hs ↦ ?_) (isClosed_tsupport F)
    by_contra h
    obtain ⟨h0, h1, h2⟩ := jet_eq_zero_of_notMem_tsupport h
    exact hs (by simp only [hK, h0, h1, h2, mul_zero, add_zero])
  have hKcs : HasCompactSupport K := hFcs.of_isClosed_subset (isClosed_tsupport K) hKsub
  obtain ⟨φ, hφC, hφcs, hφsupp, hφ⟩ :=
    exists_test_pow_mul_comp_sq hR hδ hKC hKcs (hKsub.trans hFsupp) hK0 (l + 1)
  have hcurl := integral_curl_of_weak_eigen hR hl hpar hu hDu hweak hdiv heig hwm hw hwint huw
    hF hFsupp
  have heul := integral_mul_meridianCoefficient_polar_mul_deriv hR hl hu hDu hweak hwm hw hwint
    huw hem he heint hepair hφC hφcs hφsupp
  -- the radial derivative of the test
  have hφd : ∀ r ∈ Ioo 0 R, r * deriv φ r =
      r ^ (l + 1) * (((l : ℝ) + 1) * K (r ^ 2) + 2 * r ^ 2 * deriv K (r ^ 2)) := by
    intro r hr
    have hev : (fun s ↦ s ^ (l + 1) * K (s ^ 2)) =ᶠ[𝓝 r] φ := by
      filter_upwards [Ioi_mem_nhds hr.1] with s hs
      exact (hφ s hs).symm
    rw [← hev.deriv_eq, mul_deriv_pow_mul_comp_sq (hKC.differentiable (by simp)) (l + 1) r]
    push_cast
    ring
  have hI1 : Integrable (fun r ↦ a r * ((l : ℝ) * (l + 1) * φ r)) :=
    HasWeakTimeDerivativeOn.integrable_mul_test hal (continuous_const.mul hφC.continuous)
      hφcs.mul_left (tsupport_mul_subset_right.trans hφsupp)
  have hI2 : Integrable (fun r ↦ (b r + c r) * φ r) :=
    HasWeakTimeDerivativeOn.integrable_mul_test (hbl.add hcl) hφC.continuous hφcs hφsupp
  have hI3 : Integrable (fun r ↦ b r * (r * deriv φ r)) :=
    HasWeakTimeDerivativeOn.integrable_mul_test hbl
      (continuous_id.mul (hφC.continuous_deriv (by simp))) hφcs.deriv.mul_left
      (tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hφsupp))
  calc ∫ r in Ioo 0 R, r ^ (l + 2) * (4 * r ^ 2 * deriv (deriv F) (r ^ 2) +
        (4 * l + 6) * deriv F (r ^ 2) + μ * F (r ^ 2)) *
        ((l * (l + 1) * a r - b r - c r) / r)
      = ∫ r in Ioo 0 R, (a r * ((l : ℝ) * (l + 1) * φ r) - (b r + c r) * φ r) := by
        refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
        simp only [hφ r hr.1, hK]
        have hr0 : r ≠ 0 := hr.1.ne'
        rw [show r ^ (l + 2) = r ^ (l + 1) * r by ring]
        field_simp
        ring
    _ = (∫ r in Ioo 0 R, a r * ((l : ℝ) * (l + 1) * φ r)) +
          ∫ r in Ioo 0 R, b r * (r * deriv φ r) := by
        rw [integral_sub hI1.integrableOn hI2.integrableOn, sub_eq_add_neg, ← heul]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioo fun r _ ↦ ?_
        ring
    _ = ∫ r in Ioo 0 R, (a r * ((l : ℝ) * (l + 1) * φ r) + b r * (r * deriv φ r)) :=
        (integral_add hI1.integrableOn hI3.integrableOn).symm
    _ = 0 := by
        refine Eq.trans (setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_) hcurl
        simp only [hφd r hr, hφ r hr.1, hK]
        ring

/-- **The weak derivative of the radial coefficient.** For `u` with integrable components and
weak derivatives on the ball, an equivariant representative `w` of `u` and an equivariant field
`e` with the pairings of the Euler field, `r a` has the weak derivative `a + c` on `(0, R)`,
where `a` is the meridian coefficient of `w` on `Y_l` and `c` that of `e`. -/
theorem integral_mul_meridianCoefficient_radial_mul_deriv {R : ℝ} (hR : 0 < R) (l : ℕ)
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
    ∫ r in Ioo 0 R, r * meridianCoefficient w l 0 r * deriv φ r =
      -∫ r in Ioo 0 R, (meridianCoefficient w l 0 r + meridianCoefficient e l 0 r) * φ r := by
  obtain ⟨F, hF, hFcs, hFsupp, hF0, hFφ⟩ := exists_pow_mul_comp_sq_eq hR hφ hcs hsupp (l + 1)
  set A : ℝ → ℝ := fun s ↦ F s / s with hA
  have hFev : F =ᶠ[𝓝 0] 0 := notMem_tsupport_iff_eventuallyEq.mp hF0
  have hAC : ContDiff ℝ ∞ A := contDiff_iff_contDiffAt.mpr fun s ↦ by
    rcases eq_or_ne s 0 with rfl | hs
    · have hev : A =ᶠ[𝓝 0] fun _ ↦ (0 : ℝ) := hFev.mono fun t ht ↦ by simp [hA, ht]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact hF.contDiffAt.div contDiffAt_id hs
  have hFR : F (R ^ 2) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ lt_irrefl _ (hFsupp h)
  set Z : ℝ → ℝ := fun _ ↦ 0 with hZ
  have hZC : ContDiff ℝ ∞ Z := contDiff_const
  set Φ := meridionalTest l A Z with hΦdef
  have hΦC : ContDiff ℝ ∞ Φ := contDiff_meridionalTest l hAC hZC
  have hΦR (x : ℝ^3) (hx : ‖x‖ = R) : Φ x = 0 := by
    ext i
    simp [hΦdef, meridionalTest_apply, hx, hA, hFR, hZ]
  have hEu := integral_inner_eulerField hR hu hDu hweak hΦC hΦR
  set A₂ : ℝ → ℝ := fun s ↦ 3 * A s + (2 * s * deriv A s + ((l : ℝ) + 1) * A s) with hA₂
  set B₂ : ℝ → ℝ := fun s ↦ 3 * Z s + (2 * s * deriv Z s + ((l : ℝ) - 1) * Z s) with hB₂
  have hrhs (x : ℝ^3) : ∑ i, u x i * (3 * Φ x i + ∑ j, x j * ∂[j] (fun y ↦ Φ y i) x) =
      ⟪u x, meridionalTest l A₂ B₂ x⟫ := by
    rw [EuclideanSpace.real_inner_eq_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hcomm : ∑ j, x j * ∂[j] (fun y ↦ Φ y i) x =
        ∑ j, ∂[j] (fun y ↦ meridionalTest l A Z y i) x * x j :=
      Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    rw [hcomm, sum_partialDeriv_meridionalTest_mul l hAC hZC x i]
    simp only [hΦdef, meridionalTest_apply, hA₂, hB₂]
    ring
  have hA₂c : Continuous A₂ := (continuous_const.mul hAC.continuous).add
    (((continuous_const.mul continuous_id).mul (hAC.continuous_deriv (by simp))).add
      (continuous_const.mul hAC.continuous))
  have hB₂c : Continuous B₂ := by
    simp only [hB₂, hZ, deriv_const, mul_zero, add_zero]
    exact continuous_const
  have hmain : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪e x, Φ x⟫ =
      -∫ x in Metric.ball (0 : ℝ^3) R, ⟪w x, meridionalTest l A₂ B₂ x⟫ := by
    rw [hepair Φ hΦC.continuous (meridionalTest_axisRotation l A Z), hEu]
    exact congrArg Neg.neg (integral_congr_ae (huw.mono fun x hx ↦ (hrhs x).trans (by rw [hx])))
  rw [hΦdef, setIntegral_inner_meridionalTest hem he heint l hAC.continuous hZC.continuous,
    setIntegral_inner_meridionalTest hwm hw hwint l hA₂c hB₂c] at hmain
  -- the one-dimensional identity
  have hAd {s : ℝ} (hs : 0 < s) : deriv A s = (deriv F s * s - F s) / s ^ 2 :=
    ((hF.differentiable (by simp) s).hasDerivAt.div (hasDerivAt_id s) hs.ne').deriv.trans
      (by simp only [id, mul_one])
  have hZd : deriv Z = fun _ ↦ 0 := by simp [hZ]
  have h1 : ∫ r in Ioo 0 R, meridianCoefficient e l 0 r * φ r =
      -∫ r in Ioo 0 R, (meridianCoefficient w l 0 r * φ r +
        meridianCoefficient w l 0 r * (r * deriv φ r)) := by
    have hL : ∫ r in Ioo 0 R, r ^ 2 * ((r ^ (l + 1) * A (r ^ 2) + l * r ^ (l - 1) * Z (r ^ 2)) *
        meridianCoefficient e l 0 r + r ^ (l - 1) * Z (r ^ 2) * meridianCoefficient e l 1 r) =
        ∫ r in Ioo 0 R, meridianCoefficient e l 0 r * φ r := by
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
      have hr0 : r ≠ 0 := hr.1.ne'
      rw [← hFφ r hr.1]
      simp only [hA, hZ]
      field_simp
      ring
    have hR' : ∫ r in Ioo 0 R, r ^ 2 * ((r ^ (l + 1) * A₂ (r ^ 2) + l * r ^ (l - 1) *
        B₂ (r ^ 2)) * meridianCoefficient w l 0 r + r ^ (l - 1) * B₂ (r ^ 2) *
          meridianCoefficient w l 1 r) =
        ∫ r in Ioo 0 R, (meridianCoefficient w l 0 r * φ r +
          meridianCoefficient w l 0 r * (r * deriv φ r)) := by
      refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
      have hr0 : r ≠ 0 := hr.1.ne'
      have hev : (fun s ↦ s ^ (l + 1) * F (s ^ 2)) =ᶠ[𝓝 r] φ :=
        eventually_of_mem (Ioi_mem_nhds hr.1) fun t ht ↦ hFφ t ht
      have hd := mul_deriv_pow_mul_comp_sq (hF.differentiable (by simp)) (l + 1) r
      rw [hev.deriv_eq] at hd
      rw [← hFφ r hr.1, hd]
      simp only [hA₂, hB₂, hZd, hAd (by positivity : 0 < r ^ 2)]
      simp only [hA, hZ]
      push_cast
      field_simp
      ring
    rw [hL, hR'] at hmain
    exact mul_left_cancel₀ (by positivity : (2 * π) ≠ 0) (by linear_combination hmain)
  have hint {q ψ : ℝ → ℝ} (hq : LocallyIntegrableOn q (Ioo 0 R)) (hψ : Continuous ψ)
      (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ioo 0 R) :
      IntegrableOn (fun r ↦ q r * ψ r) (Ioo 0 R) := by
    have := HasWeakTimeDerivativeOn.integrable_mul_test hq hψ hψc hψs
    exact this.integrableOn
  have ha := locallyIntegrableOn_meridianCoefficient hwm hw hwint l 0
  have hIa := hint ha hφ.continuous hcs hsupp
  rw [integral_add hIa (hint (ψ := fun r ↦ r * deriv φ r) ha
    (continuous_id.mul (hφ.continuous_deriv (by simp)))
    hcs.deriv.mul_left (tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hsupp)))]
    at h1
  rw [show ∫ r in Ioo 0 R, r * meridianCoefficient w l 0 r * deriv φ r =
      ∫ r in Ioo 0 R, meridianCoefficient w l 0 r * (r * deriv φ r) by congr 1; ext r; ring]
  simp only [add_mul]
  rw [integral_add hIa (hint (locallyIntegrableOn_meridianCoefficient hem he heint l 0)
    hφ.continuous hcs hsupp)]
  linarith

/-- **The divergence relation.** For `u` with integrable components and weak derivatives on the
ball with vanishing divergence, an equivariant representative `w` of `u` and every smooth `f`
with `f(R²) = 0`, the gradient `∇(f(‖x‖²) h_l) = v(2 f', f)` is orthogonal to `w`. In polar
form, with `a`, `b` the meridian coefficients of `w` on `Y_l` and `X_l`,
`∫₀^R r² ((2 r^{l+1} f'(r²) + l r^{l-1} f(r²)) a + r^{l-1} f(r²) b) dr = 0`. -/
theorem integral_divergence_meridian {R : ℝ} (hR : 0 < R) (l : ℕ) {u : ℝ^3 → ℝ^3}
    {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Du i i x = 0)
    {w : ℝ^3 → ℝ^3} (hwm : Measurable w) (hw : IsEquivariantUnderAxisRotation w)
    (hwint : IntegrableOn w (Metric.ball (0 : ℝ^3) R))
    (huw : u =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) R)] w)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfR : f (R ^ 2) = 0) :
    ∫ r in Ioo 0 R, r ^ 2 * ((r ^ (l + 1) * (2 * deriv f (r ^ 2)) + l * r ^ (l - 1) * f (r ^ 2)) *
      meridianCoefficient w l 0 r + r ^ (l - 1) * f (r ^ 2) * meridianCoefficient w l 1 r) = 0 := by
  set B₀ := Metric.ball (0 : ℝ^3) R
  set h := zonalSolidHarmonicPolynomial l with hh
  set p : ℝ^3 → ℝ := fun y ↦ f (‖y‖ ^ 2) * eval y.ofLp h with hp
  have hpC : ContDiff ℝ ∞ p := contDiff_radial_mul_eval hf
  set T : Fin 3 → Fin 3 → ℝ^3 → ℝ := fun i j y ↦ (if i = j then 1 else 0) * p y with hT
  have hTC : ∀ i j, ContDiff ℝ ∞ (T i j) := fun i j ↦ contDiff_const.mul hpC
  have hTn : ∀ x : ℝ^3, ‖x‖ = R → ∀ i, ∑ j, T i j x * x j = 0 := by
    intro x hx i
    simp [hT, hp, hx, hfR]
  have htool := PDE.Analysis.integral_sum_mul_partialDeriv_add_mul_eq_zero hR hTC hTn
    (v := fun i x ↦ u x i) hu hDu hweak
  have hdT (x : ℝ^3) (i : Fin 3) : ∑ j, ∂[j] (T i j) x =
      meridionalTest l (fun s ↦ 2 * deriv f s) f x i := by
    have h' (j : Fin 3) : ∂[j] (T i j) x = (if i = j then 1 else 0) * ∂[j] p x := by
      simp only [hT]
      rw [partialDeriv_mul (differentiableAt_const _) (hpC.differentiable (by simp) x),
        partialDeriv_const, zero_mul, zero_add]
    simp only [h', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact partialDeriv_radial_mul_zonal l (hf.differentiable (by simp)) x i
  have hmul : ∀ {g : ℝ^3 → ℝ}, Continuous g → ∀ {q : ℝ^3 → ℝ}, IntegrableOn q B₀ →
      Integrable (fun x ↦ q x * g x) (volume.restrict B₀) := fun hg _ hq ↦
    hq.mul_continuousOn_of_subset hg.continuousOn measurableSet_ball
      (isCompact_closedBall 0 R) Metric.ball_subset_closedBall
  have hf1 : Continuous fun s ↦ 2 * deriv f s :=
    continuous_const.mul (hf.continuous_deriv (by simp))
  have hWC : Continuous (meridionalTest l (fun s ↦ 2 * deriv f s) f) :=
    continuous_meridionalTest l hf1 hf.continuous
  have hI1 : Integrable (fun x ↦ ∑ i, u x i * meridionalTest l (fun s ↦ 2 * deriv f s) f x i)
      (volume.restrict B₀) :=
    integrable_finsetSum _ fun i _ ↦ hmul ((continuous_apply i).comp
      ((PiLp.continuous_ofLp 2 _).comp hWC)) (hu i)
  have hI2 : Integrable (fun x ↦ ∑ i, ∑ j, Du i j x * T i j x) (volume.restrict B₀) :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      hmul (hTC i j).continuous (hDu i j)
  have hsplit : ∫ x in B₀, ∑ i, ∑ j, (u x i * ∂[j] (T i j) x + Du i j x * T i j x) =
      (∫ x in B₀, ∑ i, u x i * meridionalTest l (fun s ↦ 2 * deriv f s) f x i) +
        ∫ x in B₀, ∑ i, ∑ j, Du i j x * T i j x := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdT]
  have hzero : ∫ x in B₀, ∑ i, ∑ j, Du i j x * T i j x = 0 := by
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hdiv] with x hx
    have hsum : ∑ i, ∑ j, Du i j x * T i j x = (∑ i, Du i i x) * p x := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hT, Ne.symm hj]) (by simp)]
      simp [hT]
    simp [hsum, hx]
  rw [hsplit, hzero, add_zero] at htool
  have hinner : ∫ x in B₀, ⟪w x, meridionalTest l (fun s ↦ 2 * deriv f s) f x⟫ = 0 := by
    refine Eq.trans (integral_congr_ae ?_) htool
    filter_upwards [huw] with x hx
    rw [← hx, EuclideanSpace.real_inner_eq_sum]
  rw [setIntegral_inner_meridionalTest hwm hw hwint l hf1 hf.continuous] at hinner
  exact (mul_eq_zero.mp hinner).resolve_left (by positivity)

end PDE.Fluid.Stokes.Ball
