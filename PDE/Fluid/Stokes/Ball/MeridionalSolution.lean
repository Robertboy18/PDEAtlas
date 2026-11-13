/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.MeridionalAnalysis
import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Meridional coefficients of weak Neumann-Stokes eigenfunctions

The meridional field `v(A, B) = A(‖x‖²) h_l x + B(‖x‖²) ∇h_l` has, on the meridian of azimuth
zero, the radial profile `ρ(r) = r^{l+1} A(r²) + l r^{l-1} B(r²)` along `Y_l` and the polar
profile `τ(r) = r^{l-1} B(r²)` along `X_l`, so its meridian coefficients are `‖Y_l‖² ρ` and
`‖X_l‖² τ` and vanish on the other vector harmonics.

For a weak eigenfunction of meridional parity and degree `l ≥ 1`, let `a`, `b` be the meridian
coefficients on `Y_l`, `X_l`. The divergence relation gives `(r² a)' = r b`, and the Euler
relation with the vorticity theorem gives `(r b)' = l (l + 1) a - r ω` with `ω = A₀ r^l G_l(μ r²)`.
A divergence-free field `v(A_p, B_p)` with `2 B_p' - A_p = c G_l(μ s)`, `c ≠ 0`, solves the same
system with vorticity `-l (l + 1) ‖Y_l‖² c r^l G_l(μ r²)`. The difference of the two solves the
harmonic system, so by `ae_eq_pow_of_weak_harmonic` the coefficients of the eigenfunction are
almost everywhere those of `v(A A_p, A B_p + C)` for some constants `A`, `C`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Real MvPolynomial Filter
open PDE (partialDeriv laplacian divergence)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open PDE.Analysis.Evolution (HasWeakTimeDerivativeOn)
open scoped RealInnerProductSpace ContDiff Topology

namespace PDE.Fluid.Stokes.Ball

/-- A field whose values on the meridian of radius `r` are a combination `∑ₖ cₖ X_{l,k}` of the
vector harmonics of degree `l` has meridian coefficients `c_j ‖X_{l,j}‖²` in degree `l` and
zero in the other degrees. -/
theorem meridianCoefficient_eq_of_point {W : ℝ^3 → ℝ^3} {l : ℕ} {r : ℝ} {c : Fin 3 → ℝ}
    (hW : ∀ θ, W (point r θ 0) = ∑ k, c k • vectorHarmonic l k θ) (m : ℕ) (j : Fin 3) :
    meridianCoefficient W m j r = if l = m then c j * vectorHarmonicNormSq l j else 0 := by
  have hpt (θ : ℝ) : ⟪W (point r θ 0), vectorHarmonic m j θ⟫ * sin θ =
      ∑ k, c k * (⟪vectorHarmonic l k θ, vectorHarmonic m j θ⟫ * sin θ) := by
    rw [hW, sum_inner, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [real_inner_smul_left]
    ring
  have hint (k : Fin 3) : IntervalIntegrable
      (fun θ ↦ c k * (⟪vectorHarmonic l k θ, vectorHarmonic m j θ⟫ * sin θ)) volume 0 π :=
    (continuous_const.mul (((continuous_vectorHarmonic l k).inner
      (continuous_vectorHarmonic m j)).mul continuous_sin)).intervalIntegrable _ _
  rw [meridianCoefficient, intervalIntegral.integral_congr (fun θ _ ↦ hpt θ),
    intervalIntegral.integral_finsetSum fun k _ ↦ hint k]
  simp_rw [intervalIntegral.integral_const_mul, integral_inner_vectorHarmonic_mul_sin]
  by_cases hlm : l = m
  · simp [hlm]
  · simp [hlm]

/-- The radial profile `r^{l+1} A(r²) + l r^{l-1} B(r²)` of the meridional field `v(A, B)`. -/
def radialProfile (l : ℕ) (A B : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (l + 1) * A (r ^ 2) + l * r ^ (l - 1) * B (r ^ 2)

/-- The polar profile `r^{l-1} B(r²)` of the meridional field `v(A, B)`. -/
def polarProfile (l : ℕ) (B : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ (l - 1) * B (r ^ 2)

private theorem meridionalTest_point_sum (l : ℕ) (A B : ℝ → ℝ) (r θ : ℝ) :
    meridionalTest l A B (point r θ 0) =
      ∑ k, (![radialProfile l A B r, polarProfile l B r, 0] : Fin 3 → ℝ) k •
        vectorHarmonic l k θ := by
  rw [meridionalTest_point, Fin.sum_univ_three]
  simp [radialProfile, polarProfile]

/-- The meridian coefficient of `v(A, B)` on `Y_l` is `‖Y_l‖² ρ(r)`. -/
theorem meridianCoefficient_meridionalTest_zero (l : ℕ) (A B : ℝ → ℝ) (r : ℝ) :
    meridianCoefficient (meridionalTest l A B) l 0 r =
      vectorHarmonicNormSq l 0 * radialProfile l A B r := by
  rw [meridianCoefficient_eq_of_point (meridionalTest_point_sum l A B r)]
  simp [mul_comm]

/-- The meridian coefficient of `v(A, B)` on `X_l` is `‖X_l‖² τ(r)`. -/
theorem meridianCoefficient_meridionalTest_one (l : ℕ) (A B : ℝ → ℝ) (r : ℝ) :
    meridianCoefficient (meridionalTest l A B) l 1 r =
      vectorHarmonicNormSq l 1 * polarProfile l B r := by
  rw [meridianCoefficient_eq_of_point (meridionalTest_point_sum l A B r)]
  simp [mul_comm]

/-- The meridian coefficient of `v(A, B)` on `Z_l` vanishes. -/
theorem meridianCoefficient_meridionalTest_two (l : ℕ) (A B : ℝ → ℝ) (r : ℝ) :
    meridianCoefficient (meridionalTest l A B) l 2 r = 0 := by
  rw [meridianCoefficient_eq_of_point (meridionalTest_point_sum l A B r)]
  simp

/-- The meridian coefficients of `v(A, B)` vanish in the degrees other than `l`. -/
theorem meridianCoefficient_meridionalTest_of_ne {l m : ℕ} (h : l ≠ m) (A B : ℝ → ℝ) (k : Fin 3)
    (r : ℝ) : meridianCoefficient (meridionalTest l A B) m k r = 0 := by
  rw [meridianCoefficient_eq_of_point (meridionalTest_point_sum l A B r)]
  simp [h]

/-- The divergence relation of the profiles: for `2 s A' + (l + 3) A + 2 l B' = 0`,
`(r² ρ)' = l (l + 1) r τ`. -/
theorem hasDerivAt_sq_mul_radialProfile {l : ℕ} (hl : 1 ≤ l) {A B : ℝ → ℝ}
    (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hfree : ∀ s, 2 * s * deriv A s + ((l : ℝ) + 3) * A s + 2 * l * deriv B s = 0) (r : ℝ) :
    HasDerivAt (fun r ↦ r ^ 2 * radialProfile l A B r)
      (l * (l + 1) * (r * polarProfile l B r)) r := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have h2 : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have hAr := (hA (r ^ 2)).hasDerivAt.comp r h2
  have hBr := (hB (r ^ 2)).hasDerivAt.comp r h2
  have h := ((hasDerivAt_pow (m + 4) r).mul hAr).add
    (((hasDerivAt_pow (m + 2) r).mul hBr).const_mul ((m : ℝ) + 1))
  have hfun : (fun r ↦ r ^ 2 * radialProfile (m + 1) A B r) =
      fun r ↦ r ^ (m + 4) * (A ∘ fun s ↦ s ^ 2) r +
        ((m : ℝ) + 1) * (r ^ (m + 2) * (B ∘ fun s ↦ s ^ 2) r) := by
    funext r
    simp only [radialProfile, Function.comp_apply, Nat.add_sub_cancel]
    push_cast
    ring
  rw [hfun]
  convert h using 1
  have hf := hfree (r ^ 2)
  simp only [polarProfile, Nat.add_sub_cancel, Function.comp_apply,
    show m + 4 - 1 = m + 3 from rfl, show m + 2 - 1 = m + 1 from rfl]
  push_cast at hf ⊢
  linear_combination -(r ^ (m + 3)) * hf

/-- The polar profile satisfies `(r τ)' = ρ + r^{l+1} (2 B'(r²) - A(r²))`. -/
theorem hasDerivAt_mul_polarProfile {l : ℕ} (hl : 1 ≤ l) (A : ℝ → ℝ) {B : ℝ → ℝ}
    (hB : Differentiable ℝ B) (r : ℝ) :
    HasDerivAt (fun r ↦ r * polarProfile l B r)
      (radialProfile l A B r + r ^ (l + 1) * (2 * deriv B (r ^ 2) - A (r ^ 2))) r := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have h2 : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have hBr := (hB (r ^ 2)).hasDerivAt.comp r h2
  have h := (hasDerivAt_pow (m + 1) r).mul hBr
  have hfun : (fun r ↦ r * polarProfile (m + 1) B r) =
      fun r ↦ r ^ (m + 1) * (B ∘ fun s ↦ s ^ 2) r := by
    funext r
    simp only [polarProfile, Function.comp_apply, Nat.add_sub_cancel]
    ring
  rw [hfun]
  convert h using 1
  simp only [radialProfile, Nat.add_sub_cancel, Function.comp_apply]
  push_cast
  ring

/-- **The meridional coefficients.** Let `u` be a weak eigenfunction of meridional parity on the
ball with equivariant representative `w`, `e` an equivariant field with the pairings of the
Euler field, and `l ≥ 1`. For a divergence-free meridional field `v(A_p, B_p)` whose vorticity
profile `2 B_p' - A_p = c G_l(μ s)` has `c ≠ 0`, the meridian coefficients of `w` on `Y_l` and
`X_l` are almost everywhere on `(0, R)` those of `v(A A_p, A B_p + C)` for some constants
`A`, `C`. -/
theorem meridianCoefficient_ae_eq_of_weak_eigen {R μ ε : ℝ} (hR : 0 < R) {l : ℕ} (hl : 1 ≤ l)
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
    {Ap Bp : ℝ → ℝ} (hAp : ContDiff ℝ ∞ Ap) (hBp : ContDiff ℝ ∞ Bp)
    (hfree : ∀ s, 2 * s * deriv Ap s + ((l : ℝ) + 3) * Ap s + 2 * l * deriv Bp s = 0)
    {c : ℝ} (hc : c ≠ 0)
    (hvort : ∀ s, 2 * deriv Bp s - Ap s = c * reducedSphericalBesselJSq l (μ * s)) :
    ∃ A C : ℝ,
      meridianCoefficient w l 0 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (meridionalTest l (fun s ↦ A * Ap s) (fun s ↦ A * Bp s + C)) l 0 ∧
      meridianCoefficient w l 1 =ᵐ[volume.restrict (Ioo 0 R)]
        meridianCoefficient (meridionalTest l (fun s ↦ A * Ap s) (fun s ↦ A * Bp s + C)) l 1 := by
  obtain ⟨A₀, hω⟩ := vorticity_ae_eq_of_weak_eigen hR hl hpar hu hDu hweak hdiv heig hwm hw
    hwint huw hem he heint hepair
  set N0 := vectorHarmonicNormSq l 0 with hN0def
  set N1 := vectorHarmonicNormSq l 1 with hN1def
  have hN1 : N1 = l * (l + 1) * N0 := vectorHarmonicNormSq_one l
  have hN0 : 0 < N0 := vectorHarmonicNormSq_zero_pos l
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hN1pos : 0 < N1 := by rw [hN1]; positivity
  set a := meridianCoefficient w l 0
  set b := meridianCoefficient w l 1 with hb
  set e₁ := meridianCoefficient e l 1 with he₁
  have hal := locallyIntegrableOn_meridianCoefficient hwm hw hwint l 0
  have hbl := locallyIntegrableOn_meridianCoefficient hwm hw hwint l 1
  have hel := locallyIntegrableOn_meridianCoefficient hem he heint l 1
  set ap : ℝ → ℝ := fun r ↦ N0 * radialProfile l Ap Bp r with hap
  set bp : ℝ → ℝ := fun r ↦ N1 * polarProfile l Bp r with hbp
  have hApc := hAp.continuous
  have hBpc := hBp.continuous
  have hapc : Continuous ap := by simp only [hap, radialProfile]; fun_prop
  have hbpc : Continuous bp := by simp only [hbp, polarProfile]; fun_prop
  have hRSc : Continuous (radialSolution l μ) := (contDiff_radialSolution l μ).continuous
  have hIoo {f : ℝ → ℝ} (hf : Continuous f) : IntegrableOn f (Ioo 0 R) :=
    hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- the classical relations of the particular field
  have hapd (r : ℝ) : HasDerivAt (fun r ↦ r ^ 2 * ap r) (r * bp r) r := by
    convert (hasDerivAt_sq_mul_radialProfile hl (hAp.differentiable (by simp))
      (hBp.differentiable (by simp)) hfree r).const_mul N0 using 1
    · funext r
      simp only [hap]
      ring
    · simp only [hbp, hN1]
      ring
  have hbpd (r : ℝ) : HasDerivAt (fun r ↦ r * bp r)
      (l * (l + 1) * ap r + N1 * c * (r * radialSolution l μ r)) r := by
    convert (hasDerivAt_mul_polarProfile hl Ap (hBp.differentiable (by simp)) r).const_mul N1
      using 1
    · funext r
      simp only [hbp]
      ring
    · rw [hvort (r ^ 2)]
      simp only [hap, hN1, radialSolution]
      ring
  set lam : ℝ := -A₀ / (N1 * c) with hlam
  have hlamc : lam * (N1 * c) = -A₀ := div_mul_cancel₀ _ (mul_ne_zero hN1pos.ne' hc)
  -- the harmonic system for the difference
  set α : ℝ → ℝ := fun r ↦ a r - lam * ap r with hα
  set β : ℝ → ℝ := fun r ↦ b r - lam * bp r with hβ
  have hαl : LocallyIntegrableOn α (Ioo 0 R) :=
    hal.sub ((continuous_const.mul hapc).locallyIntegrable.locallyIntegrableOn _)
  have hβl : LocallyIntegrableOn β (Ioo 0 R) :=
    hbl.sub ((continuous_const.mul hbpc).locallyIntegrable.locallyIntegrableOn _)
  have hαi : IntegrableOn (fun r ↦ r ^ 2 * α r) (Ioo 0 R) := by
    have h1 := integrableOn_sq_mul_meridianCoefficient hwm hw hwint l 0
    have h2 : IntegrableOn (fun r ↦ r ^ 2 * (lam * ap r)) (Ioo 0 R) := hIoo (by fun_prop)
    exact (h1.sub h2).congr_fun (fun r _ ↦ by simp only [Pi.sub_apply, hα]; ring) measurableSet_Ioo
  have h1 : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 R →
      ∫ r in Ioo 0 R, r ^ 2 * α r * deriv φ r = -∫ r in Ioo 0 R, r * β r * φ r := by
    intro φ hφ hcs hsupp
    obtain ⟨F, hF, -, hFsupp, -, hFφ⟩ := exists_pow_mul_comp_sq_eq hR hφ hcs hsupp l
    have hFR : F (R ^ 2) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ lt_irrefl _ (hFsupp h)
    have hD := integral_divergence_meridian hR l hu hDu hweak hdiv hwm hw hwint huw hF hFR
    have hφc := hφ.continuous
    have hdφ : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
    have hs1 : tsupport (fun r ↦ r ^ 2 * deriv φ r) ⊆ Ioo 0 R :=
      tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hsupp)
    have hs2 : tsupport (fun r ↦ r * φ r) ⊆ Ioo 0 R := tsupport_mul_subset_right.trans hsupp
    have hI1 : IntegrableOn (fun r ↦ a r * (r ^ 2 * deriv φ r)) (Ioo 0 R) :=
      integrableOn_mul_test hal ((continuous_pow 2).mul hdφ) hcs.deriv.mul_left hs1
    have hI2 : IntegrableOn (fun r ↦ b r * (r * φ r)) (Ioo 0 R) :=
      integrableOn_mul_test hbl (continuous_id.mul hφc) hcs.mul_left hs2
    have hI3 : IntegrableOn (fun r ↦ r ^ 2 * ap r * deriv φ r) (Ioo 0 R) := hIoo (by fun_prop)
    have hI4 : IntegrableOn (fun r ↦ r * bp r * φ r) (Ioo 0 R) := hIoo (by fun_prop)
    -- the divergence relation in the form `∫ r² a φ' = -∫ r b φ`
    have hDa : ∫ r in Ioo 0 R, a r * (r ^ 2 * deriv φ r) =
        -∫ r in Ioo 0 R, b r * (r * φ r) := by
      have hsum : ∫ r in Ioo 0 R, (a r * (r ^ 2 * deriv φ r) + b r * (r * φ r)) = 0 := by
        refine Eq.trans (setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_) hD
        have hev : (fun s ↦ s ^ l * F (s ^ 2)) =ᶠ[𝓝 r] φ :=
          eventually_of_mem (Ioi_mem_nhds hr.1) hFφ
        have hd := hev.deriv_eq ▸ mul_deriv_pow_mul_comp_sq (hF.differentiable (by simp)) l r
        have hd' : r ^ 2 * deriv φ r = r * (r ^ l * (l * F (r ^ 2) + 2 * r ^ 2 *
            deriv F (r ^ 2))) := by
          rw [← hd]
          ring
        rw [hd', ← hFφ r hr.1]
        obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      exact eq_neg_of_add_eq_zero_left ((integral_add hI1 hI2).symm.trans hsum)
    have hDp := setIntegral_mul_deriv_eq_neg hR hapd (continuous_id.mul hbpc) hφ hsupp
    calc ∫ r in Ioo 0 R, r ^ 2 * α r * deriv φ r
        = (∫ r in Ioo 0 R, a r * (r ^ 2 * deriv φ r)) -
            lam * ∫ r in Ioo 0 R, r ^ 2 * ap r * deriv φ r := by
          rw [← integral_const_mul, ← integral_sub hI1 (hI3.const_mul lam)]
          exact integral_congr_ae (ae_of_all _ fun r ↦ by simp only [hα]; ring)
      _ = -((∫ r in Ioo 0 R, b r * (r * φ r)) -
            lam * ∫ r in Ioo 0 R, r * bp r * φ r) := by
          rw [hDa, hDp]
          ring
      _ = -∫ r in Ioo 0 R, r * β r * φ r := by
          rw [← integral_const_mul, ← integral_sub hI2 (hI4.const_mul lam)]
          congr 1
          exact integral_congr_ae (ae_of_all _ fun r ↦ by simp only [hβ]; ring)
  have h2 : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 R →
      ∫ r in Ioo 0 R, r * β r * deriv φ r = -∫ r in Ioo 0 R, l * (l + 1) * α r * φ r := by
    intro φ hφ hcs hsupp
    have hE := integral_mul_meridianCoefficient_polar_mul_deriv hR hl hu hDu hweak hwm hw hwint
      huw hem he heint hepair hφ hcs hsupp
    have hφc := hφ.continuous
    have hdφ : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
    have hs1 : tsupport (fun r ↦ r * deriv φ r) ⊆ Ioo 0 R :=
      tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans hsupp)
    have hI1 : IntegrableOn (fun r ↦ b r * (r * deriv φ r)) (Ioo 0 R) :=
      integrableOn_mul_test hbl (continuous_id.mul hdφ) hcs.deriv.mul_left hs1
    have hI3 : IntegrableOn (fun r ↦ r * bp r * deriv φ r) (Ioo 0 R) := hIoo (by fun_prop)
    have hI5 : IntegrableOn (fun r ↦ a r * (l * (l + 1) * φ r)) (Ioo 0 R) :=
      integrableOn_mul_test hal (continuous_const.mul hφc) hcs.mul_left
        (tsupport_mul_subset_right.trans hsupp)
    have hI6 : IntegrableOn (fun r ↦ r * radialSolution l μ r * φ r) (Ioo 0 R) :=
      hIoo (by fun_prop)
    have hI7 : IntegrableOn (fun r ↦ ap r * φ r) (Ioo 0 R) := hIoo (by fun_prop)
    have hDp := setIntegral_mul_deriv_eq_neg hR hbpd (by fun_prop) hφ hsupp
    -- `b + e₁ = l (l + 1) a - r A₀ φ₀` almost everywhere
    have hbe : ∫ r in Ioo 0 R, (b r + e₁ r) * φ r =
        (∫ r in Ioo 0 R, a r * (l * (l + 1) * φ r)) -
          A₀ * ∫ r in Ioo 0 R, r * radialSolution l μ r * φ r := by
      rw [← integral_const_mul, ← integral_sub hI5 (hI6.const_mul A₀)]
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hω] with r hr hrI
      have h := hr hrI
      have hr0 : r ≠ 0 := hrI.1.ne'
      field_simp at h
      linear_combination (-φ r) * h
    have hβφ : ∫ r in Ioo 0 R, r * β r * deriv φ r = (∫ r in Ioo 0 R, r * b r * deriv φ r) -
        lam * ∫ r in Ioo 0 R, r * bp r * deriv φ r := by
      rw [← integral_const_mul, ← integral_sub (hI1.congr_fun (fun r _ ↦ by ring)
        measurableSet_Ioo) (hI3.const_mul lam)]
      exact integral_congr_ae (ae_of_all _ fun r ↦ by simp only [hβ]; ring)
    have hsplit : ∫ r in Ioo 0 R, (l * (l + 1) * ap r + N1 * c * (r * radialSolution l μ r)) * φ r =
        (l * (l + 1)) * (∫ r in Ioo 0 R, ap r * φ r) +
          (N1 * c) * ∫ r in Ioo 0 R, r * radialSolution l μ r * φ r := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add (hI7.const_mul _) (hI6.const_mul _)]
      exact integral_congr_ae (ae_of_all _ fun r ↦ by ring)
    have hαφ : ∫ r in Ioo 0 R, l * (l + 1) * α r * φ r =
        (∫ r in Ioo 0 R, a r * (l * (l + 1) * φ r)) -
          lam * ((l * (l + 1)) * ∫ r in Ioo 0 R, ap r * φ r) := by
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_sub hI5 ((hI7.const_mul _).const_mul lam)]
      exact integral_congr_ae (ae_of_all _ fun r ↦ by simp only [hα]; ring)
    linear_combination hβφ + hE - lam * hDp - hbe + lam * hsplit + hαφ +
      (∫ r in Ioo 0 R, r * radialSolution l μ r * φ r) * hlamc
  obtain ⟨C', hαC, hβC⟩ := ae_eq_pow_of_weak_harmonic hR hl hαl hβl hαi h1 h2
  have hlN : (l : ℝ) * N0 ≠ 0 := by positivity
  refine ⟨lam, C' / (l * N0), ?_, ?_⟩
  · filter_upwards [hαC] with r hr
    simp only [hα] at hr
    rw [meridianCoefficient_meridionalTest_zero, show a r = lam * ap r + C' * r ^ (l - 1) by
      linarith]
    simp only [hap, radialProfile]
    field_simp
    ring
  · filter_upwards [hβC] with r hr
    simp only [hβ] at hr
    rw [meridianCoefficient_meridionalTest_one, show b r = lam * bp r + C' * (l + 1) * r ^ (l - 1)
      by linarith, show vectorHarmonicNormSq l 1 = l * (l + 1) * N0 from hN1]
    simp only [hbp, polarProfile, hN1]
    field_simp

end PDE.Fluid.Stokes.Ball
