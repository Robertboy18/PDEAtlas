/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixEigenfunction
public import PDE.Elliptic.Regularity.Coefficients.ClassicalEllipticity
public import PDE.Elliptic.Regularity.Interior.Eigenfunction.LocalCoefficients
public import PDE.Elliptic.Variational.FirstEigenfunction
import PDE.Analysis.MeasureTheory.Lp.Nonvanishing
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# The first eigenfunction with classical coefficients

Interior regularity and the strong maximum principle make the nonnegative Rayleigh minimizer
strictly positive on a connected domain. The same argument applied to the absolute value of
any first eigenfunction makes its continuous representative nowhere zero. A linear combination
vanishing at one interior point must therefore be zero, proving simplicity for all weak
solutions in the first eigenspace.

The domain is bounded, open, and connected. The coefficients have their classical
closure derivatives; no boundary regularity or ambient coefficient extension is assumed.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A nonnegative nonzero weak eigenfunction is strictly positive in the interior, using
only finite-order classical closure regularity of its coefficients. -/
theorem IsInteriorWeakDivergenceSolution.exists_pos_eigenfunction_of_contDiffUpToBoundary
    (hn : 0 < n) (hbounded : Bornology.IsBounded Ω) (hconn : IsPreconnected Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary (n + 2) (a i j) Ω)
    (hA : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {alpha : ℝ} (helliptic : AEUniformlyElliptic A alpha)
    {lambda : ℝ} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution A (lambda • wkpBaseCoordinateCLM u) u)
    (hne : u ≠ 0)
    (hnonneg : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ wkpBaseCoordinateCLM u x) :
    ∃ f : ℝ^n → ℝ,
      (wkpBaseCoordinateCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      (∀ x ∈ Ω, EllipticMaximum.matrixOperator (fun y i j ↦ a i j y)
        (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y)))
        (fun _ ↦ 0) f x = lambda * f x) ∧
      ∀ x ∈ Ω, 0 < f x := by
  obtain ⟨f, hrep, hreg, heq⟩ :=
    hu.exists_classical_eigenfunction_of_contDiffUpToBoundary hn hbounded A a ha hA helliptic
  have haC1 (i j : Fin n) (x : ℝ^n) (hx : x ∈ Ω) :
      ContDiffAt ℝ 1 (a i j) x :=
    ((ha i j).contDiffOn.contDiffAt (hu.isOpen.mem_nhds hx)).of_le (by norm_cast; omega)
  have hcont : ContinuousOn f Ω :=
    fun x hx ↦ (hreg x hx).continuousAt.continuousWithinAt
  have habs : f =ᵐ[domainMeasure n Ω] fun x ↦ |f x| := by
    filter_upwards [hrep, hnonneg] with x hr hx
    rw [← hr, abs_of_nonneg hx]
  have habsOn := Measure.eqOn_open_of_ae_eq (μ := volume) habs hu.isOpen hcont hcont.abs
  have hpointwise (x : ℝ^n) (hx : x ∈ Ω) : 0 ≤ f x := by
    rw [habsOn hx]
    exact abs_nonneg _
  have hpositive : ∃ x ∈ Ω, 0 < f x := by
    by_contra hnone
    push Not at hnone
    have hzero (x : ℝ^n) (hx : x ∈ Ω) : f x = 0 :=
      le_antisymm (hnone x hx) (hpointwise x hx)
    apply hne
    apply WkpSpaceOn.ext_of_base_ae hu.isOpen u 0
    change (wkpBaseCoordinateCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpBaseCoordinateCLM (0 : H¹(Ω)) : ℝ^n → ℝ)
    rw [map_zero]
    filter_upwards [hrep, ae_restrict_mem hu.isOpen.measurableSet,
      Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (domainMeasure n Ω)] with x hr hx hz
    rw [hr, hzero x hx, hz]
    rfl
  have htrace : ContinuousOn (fun x ↦ ∑ i : Fin n, a i i x) Ω := by
    apply continuousOn_finsetSum
    intro i _
    exact fun x hx ↦ (haC1 i i x hx).continuousAt.continuousWithinAt
  have hdrift : ContinuousOn
      (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y))) Ω := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro j
    apply ContinuousOn.neg
    apply continuousOn_finsetSum
    intro i _ x hx
    exact (PDE.contDiffAt_partialDeriv 0 (haC1 i j x hx) i).continuousAt.continuousWithinAt
  have hquad := helliptic.le_of_continuousOn hu.isOpen a hA
    (fun i j x hx ↦ (haC1 i j x hx).continuousAt.continuousWithinAt)
  refine ⟨f, hrep, hreg, heq, ?_⟩
  apply EllipticMaximum.pos_of_nonneg_of_matrix_eigenfunction
    hu.isOpen hconn (fun y i j ↦ a i j y)
    (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y)))
    htrace hdrift helliptic.1 _ hreg heq hpointwise hpositive
  intro x hx v
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc]
    using hquad x hx (fun i ↦ v i)

/-- The distributional eigen-equation is membership in the real weak eigenspace.
This formulation includes the zero solution. -/
theorem isWeakDivergenceSolution_eigenvalue_iff
    (hΩ : IsOpen Ω) (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (lambda : ℝ) (u : H¹₀(Ω)) :
    IsWeakDivergenceSolution A (lambda • baseCoordCLM u) u ↔
      u ∈ Weak.weakEigenspace (variableCoeffForm (multiplicationCoefficientOperator A))
        massFormCLM lambda := by
  rw [← isWeakSolution_iff_isWeakDivergenceSolution hΩ,
    Weak.mem_weakEigenspace_iff]
  change (∀ v, variableCoeffForm (multiplicationCoefficientOperator A) u v =
    loadFunctional (lambda • baseCoordCLM u) v) ↔ _
  simp only [loadFunctional_apply, real_inner_smul_left, massFormCLM_apply]

/-- Absolute value is a weak eigenfunction at the least Rayleigh quotient of a symmetric
local divergence form. Its weak equation follows from the equality case of the quotient. -/
theorem isWeakEigenfunction_absoluteValueH10_multiplication
    (hΩ : IsOpen Ω) (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (hsymm : AESymmetricCoefficient A) (lambda : ℝ)
    (hleast : IsLeast ((fun v : H¹₀(Ω) ↦
      variableCoeffForm (multiplicationCoefficientOperator A) v v / ‖baseCoordCLM v‖ ^ 2) ''
        {v | v ≠ 0}) lambda)
    {u : H¹₀(Ω)}
    (hu : Weak.IsWeakEigenfunction (variableCoeffForm (multiplicationCoefficientOperator A))
      massFormCLM lambda u) :
    Weak.IsWeakEigenfunction (variableCoeffForm (multiplicationCoefficientOperator A))
      massFormCLM lambda (absoluteValueH10 hΩ u) := by
  have hnorm : ‖baseCoordCLM u‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro hzero
    exact hu.1 ((baseCoordCLM_injective hΩ) (hzero.trans (map_zero baseCoordCLM).symm))
  apply isWeakEigenfunction_of_isLeast_l2_rayleigh hΩ _
    (variableCoeffForm_symm (symmetricCoefficientOperator_multiplication_of_ae A hsymm))
    lambda hleast
  · intro hzero
    have h := norm_base_absoluteValueH10 hΩ u
    rw [hzero, map_zero, norm_zero] at h
    exact hnorm h.symm
  · rw [variableCoeffForm_multiplication_absoluteValueH10, norm_base_absoluteValueH10,
      hu.2 u, massFormCLM_apply, real_inner_self_eq_norm_sq]
    exact mul_div_cancel_right₀ lambda (pow_ne_zero 2 hnorm)

/-- Every first weak eigenfunction of a symmetric uniformly elliptic operator is a scalar
multiple of any nonzero first eigenfunction. Closure regularity supplies all needed
interior regularity, and no regularity of the domain boundary is required. -/
theorem eq_smul_of_first_weakDivergence_eigenfunctions
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary (n + 2) (a i j) Ω)
    (hA : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    {alpha : ℝ} (helliptic : AEUniformlyElliptic A alpha)
    (hsymm : AESymmetricCoefficient A) (lambda : ℝ)
    (hleast : IsLeast ((fun v : H¹₀(Ω) ↦
      variableCoeffForm (multiplicationCoefficientOperator A) v v / ‖baseCoordCLM v‖ ^ 2) ''
        {v | v ≠ 0}) lambda)
    {u v : H¹₀(Ω)} (hu : u ≠ 0)
    (hueq : IsWeakDivergenceSolution A (lambda • baseCoordCLM u) u)
    (hveq : IsWeakDivergenceSolution A (lambda • baseCoordCLM v) v) :
    ∃ c : ℝ, v = c • u := by
  let W : Submodule ℝ (H¹₀(Ω)) :=
    Weak.weakEigenspace (V := H¹₀(Ω))
      (variableCoeffForm (multiplicationCoefficientOperator A)) massFormCLM lambda
  apply W.exists_eq_smul_of_nonvanishing_representatives hΩ hne
    baseCoordCLM.toLinearMap _
    ((isWeakDivergenceSolution_eigenvalue_iff hΩ A lambda u).mp hueq) hu
    ((isWeakDivergenceSolution_eigenvalue_iff hΩ A lambda v).mp hveq)
  intro w hw hwne
  have hweq := (isWeakDivergenceSolution_eigenvalue_iff hΩ A lambda w).mpr hw
  have hweig : Weak.IsWeakEigenfunction (variableCoeffForm (multiplicationCoefficientOperator A))
      massFormCLM lambda w :=
    ⟨hwne, (Weak.mem_weakEigenspace_iff _ _ _ _).mp hw⟩
  obtain ⟨f, hf, hfreg, _⟩ :=
    hweq.toInterior.exists_classical_eigenfunction_of_contDiffUpToBoundary
      hn hbounded A a ha hA helliptic
  have habseig := isWeakEigenfunction_absoluteValueH10_multiplication
    hΩ A hsymm lambda hleast hweig
  have habseq := (isWeakDivergenceSolution_eigenvalue_iff hΩ A lambda
    (absoluteValueH10 hΩ w)).mpr ((Weak.mem_weakEigenspace_iff _ _ _ _).mpr habseig.2)
  have habsne : (absoluteValueH10 hΩ w : H¹(Ω)) ≠ 0 :=
    fun hz ↦ habseig.1 (Subtype.ext hz)
  obtain ⟨g, hg, hgreg, _, hgpos⟩ :=
    habseq.toInterior.exists_pos_eigenfunction_of_contDiffUpToBoundary hn hbounded hconn
      A a ha hA helliptic habsne (by
        filter_upwards [absoluteValueH10_base_ae hΩ w] with x hx
        change 0 ≤ baseCoordCLM (absoluteValueH10 hΩ w) x
        rw [hx]
        exact abs_nonneg _)
  have hcont : ContinuousOn f Ω :=
    fun x hx ↦ (hfreg x hx).continuousAt.continuousWithinAt
  have habsrep : g =ᵐ[domainMeasure n Ω] fun x ↦ |f x| :=
    hg.symm.trans ((absoluteValueH10_base_ae hΩ w).trans (hf.fun_comp abs))
  have hsame := Measure.eqOn_open_of_ae_eq (μ := volume) habsrep hΩ
    (fun x hx ↦ (hgreg x hx).continuousAt.continuousWithinAt) hcont.abs
  refine ⟨f, hf, hcont, fun x hx hfx ↦ ?_⟩
  have h := hgpos x hx
  rw [hsame hx] at h
  simp only [hfx, abs_zero, lt_self_iff_false] at h

/-- The principal eigenvalue is the minimum of the energy on the `L²` unit sphere. It
has a strictly positive eigenfunction, and every weak solution at this eigenvalue is
a scalar multiple of it. The `L∞` coefficients are constructed from classical data.

The coefficients have finite `C^{n+2}` closure regularity, and the open bounded connected
domain has no boundary regularity assumption. -/
theorem exists_pos_simple_first_eigenfunction_of_contDiffUpToBoundary
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary (n + 2) (a i j) Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (helliptic : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, a i j x * ξ j * ξ i)
    (hsymm : ∀ i j, ∀ x ∈ Ω, a i j x = a j i x) :
    let A := fun i j ↦ (ha i j).toLp hΩ hbounded ∞
    ∃ (lambda : ℝ) (u : H¹₀(Ω)) (f : ℝ^n → ℝ),
      0 < lambda ∧ ‖baseCoordCLM u‖ = 1 ∧
      IsLeast ((fun v : H¹₀(Ω) ↦
        variableCoeffForm (multiplicationCoefficientOperator A) v v) ''
          {v | ‖baseCoordCLM v‖ = 1}) lambda ∧
      IsLeast ((fun v : H¹₀(Ω) ↦
        variableCoeffForm (multiplicationCoefficientOperator A) v v / ‖baseCoordCLM v‖ ^ 2) ''
          {v | v ≠ 0}) lambda ∧
      IsWeakDivergenceSolution A (lambda • baseCoordCLM u) u ∧
      (baseCoordCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      (∀ x ∈ Ω, 0 < f x) ∧
      ∀ v : H¹₀(Ω),
        IsWeakDivergenceSolution A (lambda • baseCoordCLM v) v → ∃ c : ℝ, v = c • u := by
  let A := fun i j ↦ (ha i j).toLp hΩ hbounded ∞
  have hA (i j : Fin n) : (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j :=
    (ha i j).toLp_coeFn hΩ hbounded ∞
  have hAelliptic : AEUniformlyElliptic A alpha := by
    refine ⟨halpha, ?_⟩
    filter_upwards [ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ hA i j,
      ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    simpa only [hx] using helliptic x hxΩ
  have hAsymm : AESymmetricCoefficient A := by
    intro i j
    filter_upwards [hA i j, hA j i, ae_restrict_mem hΩ.measurableSet] with x hij hji hx
    rw [hij, hji, hsymm i j x hx]
  obtain ⟨lambda, u, hpos, hnorm, hnonneg, heig, hweak, hleast⟩ :=
    exists_nonnegative_first_weakDivergence_eigenfunction hn hΩ hbounded hne
      A hAelliptic hAsymm
  have hune : (u : H¹(Ω)) ≠ 0 := fun hz ↦ heig.1 (Subtype.ext hz)
  obtain ⟨f, hf, hfreg, _, hfpos⟩ :=
    hweak.toInterior.exists_pos_eigenfunction_of_contDiffUpToBoundary hn hbounded hconn
      A a ha hA hAelliptic hune hnonneg
  refine ⟨lambda, u, f, hpos, hnorm, ?_, hleast, hweak, hf, hfreg, hfpos,
    fun v hv ↦ eq_smul_of_first_weakDivergence_eigenfunctions hn hΩ hbounded hconn hne
      A a ha hA hAelliptic hAsymm lambda hleast heig.1 hweak hv⟩
  constructor
  · refine ⟨u, hnorm, ?_⟩
    change variableCoeffForm (multiplicationCoefficientOperator A) u u = lambda
    rw [heig.2 u, massFormCLM_apply, real_inner_self_eq_norm_sq, hnorm]
    simp
  · rintro r ⟨v, hv, rfl⟩
    change ‖baseCoordCLM v‖ = 1 at hv
    have hvne : v ≠ 0 := by
      intro hz
      simp only [hz, map_zero, norm_zero, zero_ne_one] at hv
    have h := hleast.2 ⟨v, hvne, rfl⟩
    simpa only [hv, one_pow, div_one] using h

end SobolevSpace.GraphSpace
