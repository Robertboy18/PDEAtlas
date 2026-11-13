/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Elliptic.PrincipalEigenfunction.SineModes
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Complex
import PDE.Elliptic.Variational.Eigenfunction.Full.Principal
import PDE.Analysis.MeasureTheory.Lp.PositivePairing
import CAS.ExactTactic

/-!
# The principal spectral bound for a nonsymmetric interval operator

The operator `-u'' + 2u'` on `(0, π)` satisfies the hypotheses of the principal-eigenpair
theorem `exists_principal_eigenpair`. Pairing the positive adjoint eigenfunction with
the positive mode `exp(x) sin(x)` identifies the principal eigenvalue as `2`, so every
complex weak Dirichlet eigenvalue has real part at least `2`
(`two_le_re_of_complex_eigenfunction`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Elliptic.PrincipalEigenfunction

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace Sobolev

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

/-- The interval is connected and nonempty. -/
theorem domain_connected : IsConnected domain := by
  let e : ℝ^1 ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  exact e.toHomeomorph.isConnected_preimage.mpr (isConnected_Ioo Real.pi_pos)

/-- The constant principal coefficient is symmetric. -/
theorem coefficients_symmetric (x : ℝ^1) :
    (Matrix.of (coefficients.principal x)).IsSymm := by
  rfl

/-- The quadratic ellipticity inequality holds with constant one. -/
theorem coefficients_elliptic (x : ℝ^1) :
    MatrixEllipticLowerBound (coefficients.principal x) 1 := by
  intro ξ
  simp [principalEnergy, coefficients, dotProduct]

/-- Neither of the two classical modes is the zero `L²` class. -/
theorem base_ne_zero_of_ae_mode (k : ℝ) (hk : k = 1 ∨ k = 2)
    (u : H¹₀(domain))
    (hu : (baseCoordCLM u : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 domain] mode k) :
    baseCoordCLM u ≠ 0 := by
  intro hzero
  have hbase : (baseCoordCLM u : ℝ^1 → ℝ) =ᵐ[domainMeasure 1 domain] 0 := by
    simpa only [hzero] using Lp.coeFn_zero ℝ 2 (domainMeasure 1 domain)
  have hae : mode k =ᵐ[domainMeasure 1 domain] 0 :=
    hu.symm.trans hbase
  have heq : EqOn (mode k) 0 domain :=
    Measure.eqOn_open_of_ae_eq (μ := volume) hae domain_open
      (mode_contDiff k).continuous.continuousOn continuousOn_const
  obtain rfl | rfl := hk
  · let x : ℝ^1 := EuclideanSpace.single 0 (Real.pi / 2)
    have hx : x ∈ domain := by
      change 0 < x 0 ∧ x 0 < Real.pi
      simp only [x, PiLp.single_eq_same]
      constructor <;> linarith [Real.pi_pos]
    exact (mode_one_pos x hx).ne' (heq hx)
  · let x : ℝ^1 := EuclideanSpace.single 0 (Real.pi / 4)
    have hx : x ∈ domain := by
      change 0 < x 0 ∧ x 0 < Real.pi
      simp only [x, PiLp.single_eq_same]
      constructor <;> linarith [Real.pi_pos]
    have hangle : (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 := by cas
    have hpos : 0 < mode 2 x := by
      simpa only [mode, x, PiLp.single_eq_same, hangle,
        Real.sin_pi_div_two, mul_one] using Real.exp_pos (Real.pi / 4)
    exact hpos.ne' (heq hx)

/-- Every complex Dirichlet eigenvalue of `-u'' + 2u'` on `(0, π)` has real part at
least two. The constant comes from the positive mode `exp(x) sin(x)`. -/
theorem two_le_re_of_complex_eigenfunction
    (lambda : ℂ) (U : ComplexWkSpaceOn 1 1 domain)
    (hUr : U.re ∈ h10SubmoduleOn (n := 1) (Ω := domain))
    (hUi : U.im ∈ h10SubmoduleOn (n := 1) (Ω := domain))
    (hUne : U.1 (baseIndex 1 1) ≠ 0)
    (hUeq : ∀ v : H¹₀(domain),
      coefficients.complexForm domain_open domain_bounded U v =
        lambda * ∫ x, U.1 (baseIndex 1 1) x *
          (baseCoordCLM v x : ℂ) ∂domainMeasure 1 domain) :
    2 ≤ lambda.re := by
  obtain ⟨r, u, _, z, _, hnorm, _, _, _, _, hzae, _, hzpos, _, hueq, _, hbound, _⟩ :=
    coefficients.exists_principal_eigenpair domain_open domain_bounded domain_connected
      domain_graph (by norm_num : (0 : ℝ) < 1)
      (fun x _ ↦ coefficients_elliptic x) (fun _ _ ↦ le_rfl)
  have hunonneg : ∀ᵐ x ∂domainMeasure 1 domain, 0 ≤ baseCoordCLM u x := by
    filter_upwards [hzae, ae_restrict_mem domain_open.measurableSet] with x hx hxΩ
    exact (hzpos x hxΩ).le.trans_eq hx
  have hune : baseCoordCLM u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨q, w, _, _, _, hwae, _, hwpos, hq⟩ :=
    coefficients.exists_pos_adjoint_eigenfunction domain_open domain_bounded domain_connected
      domain_graph (by norm_num : (0 : ℝ) < 1)
      (fun x _ ↦ coefficients_elliptic x) r u hunonneg hune hueq
  obtain ⟨v, hv, hveq⟩ := exists_native_mode 1 (Or.inl rfl)
  have hqpos : ∀ᵐ x ∂domainMeasure 1 domain, 0 < baseCoordCLM q x := by
    filter_upwards [hwae, ae_restrict_mem domain_open.measurableSet] with x hx hxΩ
    exact (hwpos x hxΩ).trans_eq hx
  have hvnonneg : ∀ᵐ x ∂domainMeasure 1 domain, 0 ≤ baseCoordCLM v x := by
    filter_upwards [hv, ae_restrict_mem domain_open.measurableSet] with x hx hxΩ
    exact (mode_one_pos x hxΩ).le.trans_eq hx.symm
  have hpair := Lp.inner_pos_of_pos_ae_of_nonneg_ae _ _ hqpos hvnonneg
    (base_ne_zero_of_ae_mode 1 (Or.inl rfl) v hv)
  have hr : r = 2 := by
    have h := hq v
    rw [hveq] at h
    rw [real_inner_comm (baseCoordCLM v) (baseCoordCLM q)] at hpair
    have hnum : (1 : ℝ) + 1 ^ 2 = 2 := by norm_num
    rw [hnum] at h
    exact (mul_right_cancel₀ hpair.ne' h).symm
  simpa only [hr] using hbound lambda U hUr hUi hUne hUeq

end PDE.Examples.Elliptic.PrincipalEigenfunction
