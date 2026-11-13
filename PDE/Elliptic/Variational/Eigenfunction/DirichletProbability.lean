/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.ClassicalDirichletEigenfunction

/-!
# First Dirichlet eigenfunctions with integral one

On a bounded connected nonempty open domain, the positive first Dirichlet
eigenfunction defines a probability density after division by its integral.
The construction starts with the variational eigenfunction and its positive
interior representative. No eigenfunction or normalization is a domain hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A positive first Dirichlet eigenfunction normalized as a probability density.
The zero boundary condition is carried by membership in `H¹₀(Ω)`. -/
structure FirstDirichletEigenfunctionWeight (Ω : Set (ℝ^n)) where
  /-- The least Dirichlet eigenvalue. -/
  eigenvalue : ℝ
  /-- Its zero-trace eigenfunction. -/
  vector : H¹₀(Ω)
  /-- Strict positivity of the eigenvalue. -/
  eigenvalue_pos : 0 < eigenvalue
  /-- The weak eigen-equation against every zero-trace energy test. -/
  eigenfunction : Weak.IsWeakEigenfunction dirichletForm massFormCLM eigenvalue vector
  /-- Strict positivity almost everywhere in the domain. -/
  positive : ∀ᵐ x ∂domainMeasure n Ω, 0 < baseCoordCLM vector x
  /-- Finiteness of the density integral. -/
  integrable : Integrable (baseCoordCLM vector) (domainMeasure n Ω)
  /-- Unit spatial mass. -/
  integral_eq_one : ∫ x, baseCoordCLM vector x ∂domainMeasure n Ω = 1
  /-- The eigenvalue is the attained least Rayleigh quotient. -/
  least : IsLeast ((fun v : H¹₀(Ω) ↦
    dirichletForm v v / ‖baseCoordCLM v‖ ^ 2) '' {v | v ≠ 0}) eigenvalue

/-- Domain hypotheses alone construct a positive principal Dirichlet eigenfunction
with integral one. Neither boundary smoothness nor a boundary atlas is needed. -/
theorem nonempty_firstDirichletEigenfunctionWeight
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) :
    Nonempty (FirstDirichletEigenfunctionWeight Ω) := by
  let : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  obtain ⟨lambda, v, f, hlambda, _, hv, hrep, _, _, hfpos, hleast⟩ :=
    exists_pos_first_dirichlet_eigenfunction hn hΩ hbounded hconn hne
  have hvpos : ∀ᵐ x ∂domainMeasure n Ω, 0 < baseCoordCLM v x := by
    filter_upwards [hrep, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    rw [hx]
    exact hfpos x hxΩ
  have hvint : Integrable (baseCoordCLM v) (domainMeasure n Ω) :=
    (Lp.memLp (baseCoordCLM v)).integrable (by norm_num)
  let m := ∫ x, baseCoordCLM v x ∂domainMeasure n Ω
  have hmnonneg : 0 ≤ m := integral_nonneg_of_ae (hvpos.mono fun _ h ↦ h.le)
  have hm : 0 < m := by
    apply lt_of_le_of_ne hmnonneg
    intro hz
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (hvpos.mono fun _ h ↦ h.le) hvint).mp hz.symm
    apply hv.1
    apply baseCoordCLM_injective hΩ
    rw [map_zero]
    exact Lp.ext (hae.trans (Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)).symm)
  let w : H¹₀(Ω) := m⁻¹ • v
  have hwrep : (baseCoordCLM w : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ m⁻¹ * baseCoordCLM v x := by
    rw [show baseCoordCLM w = m⁻¹ • baseCoordCLM v from map_smul _ _ _]
    exact Lp.coeFn_smul _ _
  refine ⟨{
    eigenvalue := lambda
    vector := w
    eigenvalue_pos := hlambda
    eigenfunction := ?_
    positive := ?_
    integrable := (hvint.const_mul _).congr hwrep.symm
    integral_eq_one := ?_
    least := hleast
  }⟩
  · constructor
    · exact smul_ne_zero (inv_ne_zero hm.ne') hv.1
    · intro z
      change dirichletForm (m⁻¹ • v) z = lambda * massFormCLM (m⁻¹ • v) z
      simp only [map_smul, smul_apply, smul_eq_mul, hv.2 z]
      ring
  · filter_upwards [hwrep, hvpos] with x hx hp
    rw [hx]
    exact mul_pos (inv_pos.mpr hm) hp
  · rw [integral_congr_ae hwrep, integral_const_mul]
    exact inv_mul_cancel₀ hm.ne'

end SobolevSpace.GraphSpace
