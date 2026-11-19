/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.MeridionalTraction

/-!
# The meridional blocks of weak Neumann-Stokes eigenfunctions

For every real `μ` the meridional field `M_μ = v(l μ G_{l+1}(μ s), (l + 1) G_l(μ s) -
μ s G_{l+1}(μ s))` of `ModeFields` solves `ΔM - μ M = 0` with zero pressure, is divergence
free, and has the vorticity profile `2 B' - A = -μ G_l(μ s)`; for `μ = κ²` it is the meridional
mode field without its gradient part. For `μ = 0` the polynomial field `v(-2l / (l + 3), s)`
takes its place, with pressure `(2 c₀ + 4l + 2) h_l`.

The meridional coefficients of a weak eigenfunction are those of `A M + C ∇h_l`
(`meridianCoefficient_ae_eq_of_weak_eigen`), and that field has zero traction on the sphere
(`traction_eq_zero_of_weak_eigen`). The two traction conditions are linear in `(A, C)`; their
determinant is `μ` times the meridional boundary expression
`((l - 1)(2l + 1) - t) G_l(t) + (t - l (l - 1)(l + 2)) G_{l+1}(t)` at `t = μ R²`, which is
positive for `t < 0`. Hence the block vanishes unless `μ = (α / R)²` for a root `α` of the
meridional boundary function, and then it is a multiple of `mode R .meridional l α`. For
`μ = 0` only `l = 1` survives, with the mode `mode R .meridional 1 0 = (4/5) e_z`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real MvPolynomial Filter
open PDE (partialDeriv laplacian divergence)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff Topology

namespace PDE.Fluid.Stokes.Ball

section Identities

variable (l : ℕ) (μ s : ℝ)

/-- `K_{l+1} A = -μ A` for the factor of `h_l x`. -/
theorem radialLaplacian_meridionalFactorA :
    radialLaplacian ((l : ℝ) + 1) (meridionalFactorA l μ) s = -(μ * meridionalFactorA l μ s) :=
  meridionalFactorA_ode l μ s

/-- `2 A + K_{l-1} B = -μ B` with zero pressure. -/
theorem radialLaplacian_meridionalFactorB :
    2 * meridionalFactorA l μ s + radialLaplacian ((l : ℝ) - 1) (meridionalFactorB l μ) s -
      (fun _ ↦ (0 : ℝ)) s = -(μ * meridionalFactorB l μ s) := by
  rw [sub_zero, radialLaplacian, ← add_assoc]
  exact meridionalFactorB_ode l μ s

/-- The traction of the factor of `h_l x`: `E_{l+1} A = μ l ((l + 1) G_{l+1} - μ s G_{l+2})`. -/
theorem radialEuler_meridionalFactorA :
    radialEuler ((l : ℝ) + 1) (meridionalFactorA l μ) s =
      μ * (l * ((l + 1) * besselFactor (l + 1) μ s - μ * s * besselFactor (l + 2) μ s)) :=
  meridionalFactorA_radial l μ s

/-- The traction of the factor of `∇h_l`: `E_{l-1} B` is the boundary expression minus
`(l - 1)` times the boundary coefficient. -/
theorem radialEuler_meridionalFactorB :
    radialEuler ((l : ℝ) - 1) (meridionalFactorB l μ) s =
      (((l : ℝ) - 1) * (2 * l + 1) - μ * s) * besselFactor l μ s +
        (μ * s - l * (l - 1) * (l + 2)) * besselFactor (l + 1) μ s -
        ((l : ℝ) - 1) * (l * ((l + 1) * besselFactor (l + 1) μ s -
          μ * s * besselFactor (l + 2) μ s)) :=
  meridionalFactorB_radial l μ s

end Identities

/-- The meridional boundary expression is positive at negative arguments. -/
theorem meridional_boundary_expression_pos {l : ℕ} (hl : 1 ≤ l) {t : ℝ} (ht : t < 0) :
    0 < (((l : ℝ) - 1) * (2 * l + 1) - t) * reducedSphericalBesselJSq l t +
      (t - l * (l - 1) * (l + 2)) * reducedSphericalBesselJSq (l + 1) t := by
  have T := reducedSphericalBesselJSq_eq_sub l t
  have h1 := reducedSphericalBesselJSq_pos_of_nonpos (l + 1) ht.le
  have h2 := reducedSphericalBesselJSq_pos_of_nonpos (l + 2) ht.le
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  rw [T]
  have e : (((l : ℝ) - 1) * (2 * l + 1) - t) * ((2 * l + 3) * reducedSphericalBesselJSq (l + 1) t -
      t * reducedSphericalBesselJSq (l + 2) t) +
      (t - l * (l - 1) * (l + 2)) * reducedSphericalBesselJSq (l + 1) t =
      (((l : ℝ) - 1) * (3 * l ^ 2 + 6 * l + 3) + (-t) * (2 * l + 2)) *
          reducedSphericalBesselJSq (l + 1) t +
        (-t) * (((l : ℝ) - 1) * (2 * l + 1) - t) * reducedSphericalBesselJSq (l + 2) t := by
    ring
  rw [e]
  have h3 : 0 < ((l : ℝ) - 1) * (3 * l ^ 2 + 6 * l + 3) + (-t) * (2 * l + 2) :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (by positivity))
      (mul_pos (neg_pos.2 ht) (by positivity))
  have h4 : 0 < (-t) * (((l : ℝ) - 1) * (2 * l + 1) - t) := mul_pos (neg_pos.2 ht)
    (by linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ l - 1) (by positivity : (0 : ℝ) ≤ 2 * l + 1)])
  positivity

/-- The meridional mode as a meridional field. -/
theorem mode_meridional_eq (R : ℝ) (l : ℕ) (α : ℝ) :
    mode R .meridional l α = meridionalTest l (meridionalFactorA l ((α / R) ^ 2))
      (fun s ↦ meridionalFactorB l ((α / R) ^ 2) s + boundaryCoefficient l α) :=
  rfl

/-- Scaling a meridional field scales its factors. -/
theorem smul_meridionalTest (c : ℝ) (l : ℕ) (A B : ℝ → ℝ) :
    c • meridionalTest l A B = meridionalTest l (fun s ↦ c * A s) (fun s ↦ c * B s) := by
  funext x
  ext i
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, meridionalTest_apply]
  ring

private theorem deriv_affine {F : ℝ → ℝ} (hF : Differentiable ℝ F) (A C : ℝ) :
    deriv (fun s ↦ A * F s + C) = fun s ↦ A * deriv F s := by
  funext s
  exact (((hF s).hasDerivAt.const_mul A).add_const C).deriv

private theorem deriv_mul_left' {F : ℝ → ℝ} (hF : Differentiable ℝ F) (A : ℝ) :
    deriv (fun s ↦ A * F s) = fun s ↦ A * deriv F s := by
  funext s
  exact ((hF s).hasDerivAt.const_mul A).deriv

/-- **Traction equations of a meridional block.** Let `u` be a weak eigenfunction of meridional
parity, `l ≥ 1`, and let `v(A_p, B_p)` with pressure `P_p(‖x‖²) h_l` be a divergence-free
classical solution of `Δv - ∇p = -μ v` whose vorticity profile is `2 B_p' - A_p = c G_l(μ s)`,
`c ≠ 0`. Then the meridional coefficients of `w` are those of `v(A A_p, A B_p + C)` for some
`A`, `C` satisfying the traction equations
`A (E_{l+1} A_p - P_p)(R²) = C μ` and `A E_{l-1} B_p (R²) + (l - 1) C = 0`. -/
theorem exists_meridional_block {R μ ε : ℝ} (hR : 0 < R) {l : ℕ} (hl : 1 ≤ l)
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
        ∫ x in Metric.ball (0 : ℝ^3) R, ⟪eulerField Du x, Φ x⟫)
    {Ap Bp Pp : ℝ → ℝ} (hAp : ContDiff ℝ ∞ Ap) (hBp : ContDiff ℝ ∞ Bp) (hPp : ContDiff ℝ ∞ Pp)
    (hfree : ∀ s, 2 * s * deriv Ap s + ((l : ℝ) + 3) * Ap s + 2 * l * deriv Bp s = 0)
    {c : ℝ} (hc : c ≠ 0)
    (hvort : ∀ s, 2 * deriv Bp s - Ap s = c * reducedSphericalBesselJSq l (μ * s))
    (heq1 : ∀ s, radialLaplacian ((l : ℝ) + 1) Ap s - 2 * deriv Pp s = -(μ * Ap s))
    (heq2 : ∀ s, 2 * Ap s + radialLaplacian ((l : ℝ) - 1) Bp s - Pp s = -(μ * Bp s)) :
    ∃ A C : ℝ,
      meridianCoefficient w l 0 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (meridionalTest l (fun s ↦ A * Ap s) (fun s ↦ A * Bp s + C)) l 0 ∧
      meridianCoefficient w l 1 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (meridionalTest l (fun s ↦ A * Ap s) (fun s ↦ A * Bp s + C)) l 1 ∧
      A * (radialEuler ((l : ℝ) + 1) Ap (R ^ 2) - Pp (R ^ 2)) - C * μ = 0 ∧
      A * radialEuler ((l : ℝ) - 1) Bp (R ^ 2) + ((l : ℝ) - 1) * C = 0 := by
  obtain ⟨A, C, ha, hb⟩ := meridianCoefficient_ae_eq_of_weak_eigen hR hl hpar hu hDu hweak hdiv
    heig hwm hw hwint huw hem he heint hepair hAp hBp hfree hc hvort
  refine ⟨A, C, ha, hb, ?_⟩
  have hA1 := deriv_mul_left' (hAp.differentiable (by simp)) A
  have hB1 := deriv_affine (hBp.differentiable (by simp)) A C
  have hP1 := deriv_affine (hPp.differentiable (by simp)) A (C * μ)
  have hA2 : deriv (deriv (fun s ↦ A * Ap s)) = fun s ↦ A * deriv (deriv Ap) s := by
    rw [hA1, deriv_mul_left' (F := deriv Ap) ((hAp.iterate_deriv 1).differentiable (by simp)) A]
  have hB2 : deriv (deriv (fun s ↦ A * Bp s + C)) = fun s ↦ A * deriv (deriv Bp) s := by
    rw [hB1, deriv_mul_left' (F := deriv Bp) ((hBp.iterate_deriv 1).differentiable (by simp)) A]
  obtain ⟨h1, h2⟩ := traction_eq_zero_of_weak_eigen hR hl hpar hu hDu hweak heig hwm hw hwint
    huw hem he heint hepair (A := fun s ↦ A * Ap s) (B := fun s ↦ A * Bp s + C)
    (P := fun s ↦ A * Pp s + C * μ) (contDiff_const.mul hAp)
    ((contDiff_const.mul hBp).add contDiff_const) ((contDiff_const.mul hPp).add contDiff_const)
    (fun s ↦ by rw [hA1, hB1]; linear_combination A * hfree s)
    (fun s ↦ by
      have h1 := heq1 s
      simp only [radialLaplacian] at h1 ⊢
      rw [hA2, hA1, hP1]
      linear_combination A * h1)
    (fun s ↦ by
      have h2 := heq2 s
      simp only [radialLaplacian] at h2 ⊢
      rw [hB2, hB1]
      linear_combination A * h2) ha hb
  simp only [radialEuler, hA1, hB1] at h1 h2 ⊢
  exact ⟨by linear_combination h1, by linear_combination h2⟩

private theorem reducedSphericalBesselJSq_zero' (m : ℕ) :
    reducedSphericalBesselJSq m 0 = 1 / ((2 * m + 1).doubleFactorial : ℝ) := by
  have h := reducedSphericalBesselJ_eq_sq m 0
  rw [zero_pow two_ne_zero, reducedSphericalBesselJ_zero] at h
  exact h.symm

/-- The meridional mode of degree one and root zero is `v(0, 4/5)`. -/
theorem mode_meridional_one_zero_eq (R : ℝ) :
    mode R .meridional 1 0 = meridionalTest 1 (fun _ ↦ 0) (fun _ ↦ 4 / 5) := by
  rw [mode_meridional_eq]
  congr 1
  · funext s
    simp [meridionalFactorA]
  · funext s
    simp only [meridionalFactorB, besselFactor, boundaryCoefficient, zero_div,
      zero_pow two_ne_zero, zero_mul, sub_zero, reducedSphericalBesselJSq_zero',
      reducedSphericalBesselJ_zero]
    norm_num [Nat.doubleFactorial]

private theorem meridionalTest_zero_eq (l : ℕ) (A B : ℝ → ℝ) (R α : ℝ) :
    meridionalTest l (fun s ↦ 0 * A s) (fun s ↦ 0 * B s + 0) =
      (0 : ℝ) • mode R .meridional l α := by
  funext x
  ext i
  simp [meridionalTest_apply]

/-- **The meridional block of a weak eigenfunction.** Let `u` be a weak eigenfunction of
meridional parity on the ball, with equivariant representative `w` and an equivariant field `e`
with the pairings of the Euler field, and `l ≥ 1`. The meridian coefficients of `w` on `Y_l`
and `X_l` are almost everywhere those of `c • mode R .meridional l α`, where `c = 0` or `α` is
a root of the meridional boundary function with `(α / R)² = μ`. -/
theorem meridional_block_of_weak_eigen {R μ ε : ℝ} (hR : 0 < R) {l : ℕ} (hl : 1 ≤ l)
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
    ∃ c α : ℝ, (c = 0 ∨ (boundaryFunction .meridional l α = 0 ∧ (α / R) ^ 2 = μ)) ∧
      meridianCoefficient w l 0 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (c • mode R .meridional l α) l 0 ∧
      meridianCoefficient w l 1 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (c • mode R .meridional l α) l 1 := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  by_cases hμ : μ = 0
  · -- the polynomial particular field
    subst hμ
    set c₀ : ℝ := -(2 * l) / ((l : ℝ) + 3) with hc₀
    have hl3 : (0 : ℝ) < (l : ℝ) + 3 := by linarith
    have hc₀neg : c₀ < 0 := div_neg_of_neg_of_pos (by linarith) hl3
    have hfree : ∀ s, 2 * s * deriv (fun _ : ℝ ↦ c₀) s + ((l : ℝ) + 3) * c₀ +
        2 * l * deriv (fun s : ℝ ↦ s) s = 0 := fun s ↦ by
      simp only [deriv_const', mul_zero, zero_add, deriv_id'', mul_one, hc₀]
      field_simp
      ring
    have hG0 := reducedSphericalBesselJSq_pos_of_nonpos l (le_refl (0 : ℝ))
    set cv : ℝ := (2 - c₀) / reducedSphericalBesselJSq l 0 with hcv
    have hcv0 : cv ≠ 0 := div_ne_zero (by linarith) hG0.ne'
    obtain ⟨A, C, ha, hb, h1, h2⟩ := exists_meridional_block hR hl hpar hu hDu hweak hdiv heig
      hwm hw hwint huw hem he heint hepair (Ap := fun _ ↦ c₀) (Bp := fun s ↦ s)
      (Pp := fun _ ↦ 2 * c₀ + 4 * l + 2) contDiff_const contDiff_id contDiff_const hfree hcv0
      (fun s ↦ by
        simp only [deriv_id'', zero_mul, hcv]
        field_simp)
      (fun s ↦ by simp [radialLaplacian])
      (fun s ↦ by
        simp only [radialLaplacian, deriv_id'', deriv_const', mul_zero, zero_add]
        ring)
    simp only [radialEuler, deriv_const', deriv_id'', mul_zero, zero_add, mul_one] at h1 h2
    have hA : A = 0 := by
      have h4 : ((l : ℝ) - 1) * c₀ - 4 * l - 2 ≠ 0 := by
        linarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ l - 1) hc₀neg.le]
      exact (mul_eq_zero.mp (by linear_combination h1)).resolve_right h4
    subst hA
    rcases eq_or_lt_of_le hl with hl1 | hl2
    · -- degree one: the multiple `C` of `∇h_1 = e_z`
      subst hl1
      refine ⟨5 / 4 * C, 0, Or.inr ⟨boundaryFunction_meridional_one_zero, by simp⟩, ?_, ?_⟩
      · filter_upwards [ha] with r hr
        rw [hr, mode_meridional_one_zero_eq, smul_meridionalTest]
        simp only [meridianCoefficient_meridionalTest_zero, radialProfile]
        ring
      · filter_upwards [hb] with r hr
        rw [hr, mode_meridional_one_zero_eq, smul_meridionalTest]
        simp only [meridianCoefficient_meridionalTest_one, polarProfile]
        ring
    · have hl1 : (1 : ℝ) < l := by exact_mod_cast hl2
      have hC : C = 0 := (mul_eq_zero.mp (by linear_combination h2)).resolve_left
        (by linarith : (l : ℝ) - 1 ≠ 0)
      subst hC
      rw [meridionalTest_zero_eq _ _ _ R 0] at ha hb
      exact ⟨0, 0, Or.inl rfl, ha, hb⟩
  · -- the Bessel particular field
    have hc : -μ ≠ 0 := neg_ne_zero.mpr hμ
    obtain ⟨A, C, ha, hb, h1, h2⟩ := exists_meridional_block hR hl hpar hu hDu hweak hdiv heig
      hwm hw hwint huw hem he heint hepair (Ap := meridionalFactorA l μ)
      (Bp := meridionalFactorB l μ) (Pp := fun _ ↦ 0) (contDiff_meridionalFactorA l μ)
      (contDiff_meridionalFactorB l μ) contDiff_const (meridionalFactor_free l μ) hc
      (meridionalFactor_vorticity l μ)
      (fun s ↦ by rw [radialLaplacian_meridionalFactorA]; simp)
      (radialLaplacian_meridionalFactorB l μ)
    rw [radialEuler_meridionalFactorA, sub_zero] at h1
    rw [radialEuler_meridionalFactorB] at h2
    set t := μ * R ^ 2 with ht
    set b₀ := (l : ℝ) * ((l + 1) * besselFactor (l + 1) μ (R ^ 2) -
      μ * R ^ 2 * besselFactor (l + 2) μ (R ^ 2)) with hb₀
    have hC : C = A * b₀ := mul_left_cancel₀ hμ (by linear_combination -h1)
    set E := (((l : ℝ) - 1) * (2 * l + 1) - t) * reducedSphericalBesselJSq l t +
      (t - l * (l - 1) * (l + 2)) * reducedSphericalBesselJSq (l + 1) t with hE
    have hAE : A * E = 0 := by
      rw [hC] at h2
      simp only [besselFactor] at h2 hb₀
      rw [hE, ht]
      linear_combination h2
    by_cases hA : A = 0
    · subst hA
      have hC0 : C = 0 := by rw [hC]; ring
      subst hC0
      rw [meridionalTest_zero_eq _ _ _ R 0] at ha hb
      exact ⟨0, 0, Or.inl rfl, ha, hb⟩
    · have hE0 : E = 0 := (mul_eq_zero.mp hAE).resolve_left hA
      have hμpos : 0 < μ := (lt_or_gt_of_ne hμ).resolve_left fun hlt ↦ by
        have htneg : t < 0 := mul_neg_of_neg_of_pos hlt (by positivity)
        linarith [hE ▸ meridional_boundary_expression_pos hl htneg]
      set α := √μ * R with hα
      have hαR : (α / R) ^ 2 = μ := by
        rw [hα, mul_div_assoc, div_self hR.ne', mul_one, Real.sq_sqrt hμpos.le]
      have hα2 : α ^ 2 = t := by
        rw [hα, mul_pow, Real.sq_sqrt hμpos.le]
      have hmode : A • mode R .meridional l α = meridionalTest l
          (fun s ↦ A * meridionalFactorA l μ s) (fun s ↦ A * meridionalFactorB l μ s + C) := by
        rw [mode_meridional_eq, hαR, smul_meridionalTest]
        congr 1
        funext s
        rw [hC, mul_add]
        congr 2
        simp only [boundaryCoefficient, reducedSphericalBesselJ_eq_sq, hα2, hb₀, besselFactor, ht]
      refine ⟨A, α, Or.inr ⟨?_, hαR⟩, hmode ▸ ha, hmode ▸ hb⟩
      simp only [boundaryFunction, reducedSphericalBesselJ_eq_sq, hα2]
      rw [← hE0, hE]

end PDE.Fluid.Stokes.Ball
