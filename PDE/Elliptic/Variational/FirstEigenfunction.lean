/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.Superharmonic
public import PDE.Elliptic.Variational.DirichletSpectrum
public import PDE.Elliptic.Variational.RayleighEquality
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.AbsoluteValue
import PDE.Analysis.MeasureTheory.Lp.Nonvanishing

/-!
# Nonnegative first weak eigenfunctions

A symmetric uniformly elliptic divergence form with bounded measurable coefficients on a
bounded nonempty open domain in positive dimension has a normalized nonnegative first weak
eigenfunction. Absolute value preserves its local quadratic energy and `L²` mass; equality
in the least Rayleigh quotient supplies the weak eigen-equation.

For the Dirichlet Laplacian, strict positivity on connected open domains is proved assuming
a classical `C²` representative satisfying the pointwise eigen-equation. Simplicity assumes
such representatives for the weak eigenfunctions at the least Rayleigh quotient.
-/

@[expose] public section

open PDE (laplacian)

open scoped Sobolev

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Every bounded measurable local coefficient matrix has the same quadratic energy
at `u` and `|u|`. Symmetry and ellipticity are unnecessary for this identity. -/
theorem variableCoeffForm_multiplication_absoluteValueH10
    (hΩ : IsOpen Ω) (a : Fin n → Fin n → DerivLp n ∞ Ω) (u : H¹₀(Ω)) :
    variableCoeffForm (multiplicationCoefficientOperator a)
      (absoluteValueH10 hΩ u) (absoluteValueH10 hΩ u) =
    variableCoeffForm (multiplicationCoefficientOperator a) u u := by
  rw [variableCoeffForm_apply, variableCoeffForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplicationCoefficientOperator_apply_ae a i j
    (derivCoordCLM j (absoluteValueH10 hΩ u)),
    multiplicationCoefficientOperator_apply_ae a i j (derivCoordCLM j u),
    absoluteValueH10_derivative_mul_ae hΩ u j i] with x hleft hright hprod
  rw [hleft, hright]
  simp only [RCLike.inner_apply, conj_trivial]
  nlinarith [congrArg (a i j x * ·) hprod]

/-- Absolute value preserves the Dirichlet energy, including on unbounded open domains. -/
theorem dirichletForm_absoluteValueH10 (hΩ : IsOpen Ω) (u : H¹₀(Ω)) :
    dirichletForm (absoluteValueH10 hΩ u) (absoluteValueH10 hΩ u) =
      dirichletForm (n := n) (Ω := Ω) u u := by
  rw [dirichletForm_apply, dirichletForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [absoluteValueH10_derivative_mul_ae hΩ u i i] with x hx
  simpa only [RCLike.inner_apply, conj_trivial] using hx

/-- Attainment of the least `L²` Rayleigh quotient gives a zero-boundary weak
eigenfunction for any symmetric continuous energy form. -/
theorem isWeakEigenfunction_of_isLeast_l2_rayleigh
    (hΩ : IsOpen Ω)
    (B : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (hsymm : ∀ u v, B u v = B v u) (lambda : ℝ)
    (hleast : IsLeast ((fun v : H¹₀(Ω) ↦
      B v v / ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2) '' {v | v ≠ 0}) lambda)
    {u : H¹₀(Ω)} (hu : u ≠ 0)
    (heq : B u u / ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 = lambda) :
    Weak.IsWeakEigenfunction B (massFormCLM (n := n) (Ω := Ω)) lambda u := by
  have hmass (v : H¹₀(Ω)) :
      massFormCLM v v = ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2 := by
    rw [massFormCLM_apply, real_inner_self_eq_norm_sq]
  have hmasssym (v w : H¹₀(Ω)) : massFormCLM v w = massFormCLM w v := by
    rw [massFormCLM_apply, massFormCLM_apply, real_inner_comm]
  have hmasspos (v : H¹₀(Ω)) (hv : v ≠ 0) : 0 < massFormCLM v v := by
    rw [hmass]
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hzero
    exact hv ((baseCoordCLM_injective hΩ)
      (hzero.trans (baseCoordCLM (n := n) (Ω := Ω)).map_zero.symm))
  have hleastmass : IsLeast ((fun v : H¹₀(Ω) ↦
      B v v / massFormCLM v v) '' {v | v ≠ 0}) lambda := by
    simpa only [hmass] using hleast
  have heqmass : B u u / massFormCLM u u = lambda := by
    simpa only [hmass] using heq
  exact @Weak.isWeakEigenfunction_of_isLeast_rayleigh (H¹₀(Ω))
    inferInstance inferInstance B massFormCLM lambda hsymm hmasssym hmasspos hleastmass
    u hu heqmass

/-- Absolute value remains a weak eigenfunction at the least Dirichlet Rayleigh
quotient. This uses the equality case, not an asserted differential equation for `|u|`. -/
theorem isWeakEigenfunction_absoluteValueH10_dirichlet
    (hΩ : IsOpen Ω) (lambda : ℝ)
    (hleast : IsLeast ((fun v : H¹₀(Ω) ↦
      dirichletForm v v / ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2) ''
        {v | v ≠ 0}) lambda)
    {u : H¹₀(Ω)}
    (hu : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω)) (massFormCLM (n := n) (Ω := Ω)) lambda u) :
    Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω)) (massFormCLM (n := n) (Ω := Ω))
      lambda (absoluteValueH10 hΩ u) := by
  have hnorm : ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro hzero
    exact hu.1 ((baseCoordCLM_injective hΩ)
      (hzero.trans (baseCoordCLM (n := n) (Ω := Ω)).map_zero.symm))
  apply isWeakEigenfunction_of_isLeast_l2_rayleigh (n := n) (Ω := Ω) hΩ
    (dirichletForm (n := n) (Ω := Ω)) (dirichletForm_symm (n := n) (Ω := Ω))
    lambda hleast
  · intro hzero
    have h := norm_base_absoluteValueH10 hΩ u
    rw [hzero, map_zero, norm_zero] at h
    exact hnorm h.symm
  · rw [dirichletForm_absoluteValueH10, norm_base_absoluteValueH10,
      hu.2 u, massFormCLM_apply, real_inner_self_eq_norm_sq]
    exact mul_div_cancel_right₀ lambda (pow_ne_zero 2 hnorm)

/-- A nonzero nonnegative `H¹₀` function with a classical representative solving
`−Δf = lambda f`, for `lambda ≥ 0`, has a strictly positive representative on a
connected open domain. Existence of the `C²` representative is an explicit input. -/
theorem pos_of_nonnegative_h10_representative
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    {u : H¹₀(Ω)} (hu : u ≠ 0)
    (hnonneg : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ (baseCoordCLM u) x)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) {f : ℝ^n → ℝ}
    (hrep : (baseCoordCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f)
    (hreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 f x)
    (heq : ∀ x ∈ Ω, -laplacian f x = lambda * f x) :
    ∀ x ∈ Ω, 0 < f x := by
  have hcont : ContinuousOn f Ω :=
    fun x hx ↦ (hreg x hx).continuousAt.continuousWithinAt
  have habs : f =ᵐ[domainMeasure n Ω] fun x ↦ |f x| := by
    filter_upwards [hrep, hnonneg] with x hr hn
    rw [← hr, abs_of_nonneg hn]
  have habsOn := Measure.eqOn_open_of_ae_eq (μ := volume) habs hΩ hcont hcont.abs
  have hpointwise (x : ℝ^n) (hx : x ∈ Ω) : 0 ≤ f x := by
    rw [habsOn hx]
    exact abs_nonneg _
  apply EllipticMaximum.pos_of_nonneg_of_neg_laplacian_nonneg hΩ hconn hreg hpointwise
  · intro x hx
    rw [heq x hx]
    exact mul_nonneg hlambda (hpointwise x hx)
  · by_contra hnone
    push Not at hnone
    have hzero (x : ℝ^n) (hx : x ∈ Ω) : f x = 0 :=
      le_antisymm (hnone x hx) (hpointwise x hx)
    apply hu
    apply baseCoordCLM_injective hΩ
    rw [map_zero]
    apply Lp.ext
    filter_upwards [hrep, ae_restrict_mem hΩ.measurableSet,
      Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (domainMeasure n Ω)] with x hr hx hz
    rw [hr, hzero x hx, hz]
    simp only [Pi.zero_apply]

/-- The first Dirichlet eigenspace is one-dimensional provided its weak eigenfunctions
have classical `C²` representatives solving the eigen-equation. That regularity
is an explicit hypothesis. Connectedness is needed for the strong maximum principle. -/
theorem eq_smul_of_first_dirichlet_eigenfunctions
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (lambda : ℝ)
    (hleast : IsLeast ((fun v : H¹₀(Ω) ↦
      dirichletForm v v / ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2) ''
        {v | v ≠ 0}) lambda)
    (hregular : ∀ w : H¹₀(Ω),
      Weak.IsWeakEigenfunction (V := H¹₀(Ω))
        (dirichletForm (n := n) (Ω := Ω)) (massFormCLM (n := n) (Ω := Ω)) lambda w →
      ∃ f : ℝ^n → ℝ, (baseCoordCLM w : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
        (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
        ∀ x ∈ Ω, -laplacian f x = lambda * f x)
    {u v : H¹₀(Ω)}
    (hu : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω)) (massFormCLM (n := n) (Ω := Ω)) lambda u)
    (hv : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω)) (massFormCLM (n := n) (Ω := Ω)) lambda v) :
    ∃ c : ℝ, v = c • u := by
  have hlambda : 0 ≤ lambda := by
    obtain ⟨w, _, hvalue⟩ := hleast.1
    rw [← hvalue]
    exact div_nonneg (dirichletForm_self_nonneg w) (sq_nonneg _)
  have hnozero (w : H¹₀(Ω))
      (hw : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
        (dirichletForm (n := n) (Ω := Ω))
        (massFormCLM (n := n) (Ω := Ω)) lambda w)
      (f : ℝ^n → ℝ) (hf : (baseCoordCLM w : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f)
      (hfreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 f x) :
      ∀ x ∈ Ω, f x ≠ 0 := by
    have habseig := isWeakEigenfunction_absoluteValueH10_dirichlet (n := n) (Ω := Ω)
      hΩ lambda hleast hw
    obtain ⟨g, hg, hgreg, hgeq⟩ := hregular (absoluteValueH10 hΩ w) habseig
    have habsrep : g =ᵐ[domainMeasure n Ω] fun x ↦ |f x| :=
      hg.symm.trans ((absoluteValueH10_base_ae hΩ w).trans (hf.fun_comp abs))
    have hsame := Measure.eqOn_open_of_ae_eq (μ := volume) habsrep hΩ
      (fun x hx ↦ (hgreg x hx).continuousAt.continuousWithinAt)
      ((show ContinuousOn f Ω from
        fun x hx ↦ (hfreg x hx).continuousAt.continuousWithinAt).abs)
    have hgpos := pos_of_nonnegative_h10_representative hΩ hconn habseig.1
      (by
        filter_upwards [absoluteValueH10_base_ae hΩ w] with x hx
        rw [hx]
        exact abs_nonneg _) hlambda hg hgreg hgeq
    intro x hx hfx
    have h := hgpos x hx
    rw [hsame hx] at h
    dsimp only at h
    rw [hfx, abs_zero] at h
    exact (lt_irrefl 0) h
  let W : Submodule ℝ (H¹₀(Ω)) :=
    Weak.weakEigenspace (V := H¹₀(Ω)) dirichletForm massFormCLM lambda
  apply W.exists_eq_smul_of_nonvanishing_representatives hΩ hne
    baseCoordCLM.toLinearMap _
    ((Weak.mem_weakEigenspace_iff _ _ _ _).mpr hu.2) hu.1
    ((Weak.mem_weakEigenspace_iff _ _ _ _).mpr hv.2)
  intro w hw hwne
  have hweq : Weak.IsWeakEigenfunction dirichletForm massFormCLM lambda w :=
    ⟨hwne, (Weak.mem_weakEigenspace_iff _ _ _ _).mp hw⟩
  obtain ⟨f, hf, hfreg, _⟩ := hregular w hweq
  exact ⟨f, hf, fun x hx ↦ (hfreg x hx).continuousAt.continuousWithinAt,
    hnozero w hweq f hf hfreg⟩

/-- A symmetric uniformly elliptic local divergence-form operator on a bounded
nonempty open domain has a nonnegative normalized first weak eigenfunction. No
connectedness or classical regularity is asserted. -/
theorem exists_nonnegative_first_weakDivergence_eigenfunction
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hne : Ω.Nonempty) (a : Fin n → Fin n → DerivLp n ∞ Ω) {alpha : ℝ}
    (helliptic : AEUniformlyElliptic (n := n) (Ω := Ω) a alpha)
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω) a) :
    ∃ (lambda : ℝ) (u : H¹₀(Ω)), 0 < lambda ∧
      ‖baseCoordCLM u‖ = 1 ∧ (∀ᵐ x ∂domainMeasure n Ω, 0 ≤ (baseCoordCLM u) x) ∧
      Weak.IsWeakEigenfunction (V := H¹₀(Ω))
        (variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω) a))
        (massFormCLM (n := n) (Ω := Ω)) lambda u ∧
      IsWeakDivergenceSolution a (lambda • baseCoordCLM u) u ∧
      IsLeast ((fun v : H¹₀(Ω) ↦
        variableCoeffForm (multiplicationCoefficientOperator a) v v / ‖baseCoordCLM v‖ ^ 2) ''
          {v | v ≠ 0}) lambda := by
  let B : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    variableCoeffForm (n := n) (Ω := Ω)
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
  obtain ⟨lambda, u, hpos, hnorm, heig, hleast⟩ :=
    exists_first_variableCoeff_eigenfunction (n := n) (Ω := Ω) hn hΩ hbounded hne
      (multiplicationCoefficientOperator (n := n) (Ω := Ω) a)
      (integratedElliptic_multiplication_of_ae a helliptic)
      (symmetricCoefficientOperator_multiplication_of_ae a hsymm)
  let v := absoluteValueH10 hΩ u
  have hvnorm : ‖baseCoordCLM v‖ = 1 :=
    (norm_base_absoluteValueH10 hΩ u).trans hnorm
  have hvne : v ≠ 0 := by
    intro hv
    simp only [hv, map_zero, norm_zero] at hvnorm
    exact zero_ne_one hvnorm
  have hvenergy : B v v = B u u :=
    variableCoeffForm_multiplication_absoluteValueH10 hΩ a u
  have huenergy : B u u = lambda * ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 := by
    rw [heig.2 u, massFormCLM_apply, real_inner_self_eq_norm_sq]
  have hvquot : B v v / ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2 = lambda := by
    rw [hvenergy, huenergy, hvnorm, hnorm]
    simp
  have hveig : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      B (massFormCLM (n := n) (Ω := Ω)) lambda v := by
    exact isWeakEigenfunction_of_isLeast_l2_rayleigh (n := n) (Ω := Ω) hΩ B
      (variableCoeffForm_symm (symmetricCoefficientOperator_multiplication_of_ae a hsymm))
      lambda hleast hvne hvquot
  refine ⟨lambda, v, hpos, hvnorm, ?_, hveig, ?_, hleast⟩
  · filter_upwards [absoluteValueH10_base_ae hΩ u] with x hx
    rw [hx]
    exact abs_nonneg _
  · apply (isWeakSolution_iff_isWeakDivergenceSolution hΩ a
      (lambda • baseCoordCLM v) v).mp
    intro w
    have hload : loadFunctional (n := n) (Ω := Ω)
        (lambda • baseCoordCLM (n := n) (Ω := Ω) v) w =
        lambda * massFormCLM (n := n) (Ω := Ω) v w := by
      rw [loadFunctional_apply, real_inner_smul_left, massFormCLM_apply]
    exact (hveig.2 w).trans hload.symm

end SobolevSpace.GraphSpace
