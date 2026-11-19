/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.ReactionDiffusion.Turing.Spectrum
public import PDE.Elliptic.Variational.DirichletSpectrum
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import CAS.ExactTactic

/-!
# Turing modes on a prescribed Dirichlet domain

For a weak Dirichlet eigenfunction `φ` of `-Δ` with eigenvalue `μ` and an eigenvector `vector` of
the mode matrix at `μ` with eigenvalue `rate`, the mode `dirichletMode φ rate vector`,
`t ↦ exp(rate * t) * vector * φ`, solves the linear reaction-diffusion system
(`dirichletMode_isSolution`). The boundary condition is encoded by `H¹₀(Ω)`, and the equation is
tested against all of `H¹₀(Ω)` (`IsWeakDirichletSolution`). No interval or spatial frequency is
chosen to fit the coefficients.

If the reaction is stable and the mode determinant at a positive eigenvalue `μ` is negative, the
rate is positive and the first species grows without bound in `L²` (`exists_growing_dirichletMode`);
a zero determinant gives a stationary mode (`exists_stationary_dirichletMode`). The eigenfunctions
come from the Dirichlet spectral theorem on a bounded open set in positive dimension
(`exists_dirichlet_eigenbasis`). All statements concern the linear system. SymLean's `cas` tactic
verifies the scalar mode identities.

Evans's §4.1.2 works on a bounded smooth planar domain with the problem (20). The mode is one term
`s_j(t) w_j` of his expansion (23), where `s_j' = A_j s_j`, (24)-(25), and the eigenfunctions `w_j`
are those of his §6.5.1, Theorem 1. A negative determinant `p(λ_j)` of `A_j`, (28)-(29), gives a
positive rate, and `p(λ_j) = 0` is his threshold (30). The weak construction works on every bounded
open set in positive dimension, and zero diffusivities are allowed, as in Evans's (20).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.2 (Application: Turing instability), (20)-(30),
  pp. 172-174; §6.5.1, Theorem 1 (Eigenvalues of symmetric elliptic operators), pp. 355-356.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace ReactionDiffusion.Turing

open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Stable reaction and nonnegative diffusion force nonzero coupling whenever a
positive Dirichlet eigenvalue has nonpositive mode determinant. -/
theorem coupling_ne_zero_of_mode_det_nonpos {C : Coefficients} {μ : ℝ}
    (htrace : C.a + C.d < 0) (hdet : 0 < C.a * C.d - C.b * C.c)
    (h₁ : 0 ≤ C.diffusion₁) (h₂ : 0 ≤ C.diffusion₂) (hμ : 0 ≤ μ)
    (hmode : (C.modeMatrix μ).det ≤ 0) : C.b ≠ 0 := by
  intro hb
  have had : 0 < C.a * C.d := by simpa [hb] using hdet
  have ha : C.a < 0 := by
    by_contra hna
    have ha0 : 0 ≤ C.a := le_of_not_gt hna
    have hd0 : C.d < 0 := by linarith
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha0 hd0.le)) had
  have hd : C.d < 0 := by
    by_contra hnd
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg ha.le (le_of_not_gt hnd))) had
  have ha' : C.a - C.diffusion₁ * μ < 0 :=
    by linarith [mul_nonneg h₁ hμ]
  have hd' : C.d - C.diffusion₂ * μ < 0 :=
    by linarith [mul_nonneg h₂ hμ]
  have hp := mul_pos_of_neg_of_neg ha' hd'
  have hm : (C.a - C.diffusion₁ * μ) * (C.d - C.diffusion₂ * μ) ≤ 0 := by
    simpa [Coefficients.modeMatrix, Matrix.det_fin_two, hb] using hmode
  exact (not_lt_of_ge hm) hp

/-- At the threshold `det = 0`, Evans's (30) in §4.1.2, the mode matrix has a nonzero vector
with eigenvalue zero. -/
theorem exists_zero_mode_eigenvector (C : Coefficients) (μ : ℝ)
    (hdet : (C.modeMatrix μ).det = 0) (hb : C.b ≠ 0) :
    ∃ vector : Fin 2 → ℝ,
      Module.End.HasEigenvector (C.modeMatrix μ).toLin' 0 vector ∧ vector 0 ≠ 0 := by
  have hroot : (C.a - C.diffusion₁ * μ) * (C.d - C.diffusion₂ * μ) - C.b * C.c = 0 := by
    simpa [Coefficients.modeMatrix, Matrix.det_fin_two] using hdet
  refine ⟨![C.b, -(C.a - C.diffusion₁ * μ)], ⟨?_, ?_⟩, hb⟩
  · rw [Module.End.mem_eigenspace_iff]
    ext i
    fin_cases i <;>
      simp only [Matrix.toLin'_apply, Coefficients.modeMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul] <;> cas using hroot
  · intro hz
    exact hb (congrFun hz 0)

/-- A separated mode built from the specified Dirichlet eigenfunction. -/
def dirichletMode (φ : H¹₀(Ω)) (rate : ℝ) (vector : Fin 2 → ℝ)
    (t : ℝ) (i : Fin 2) : H¹₀(Ω) :=
  (Real.exp (rate * t) * vector i) • φ

/-- The linear reaction-diffusion equation with zero Dirichlet boundary condition.
Time derivatives are strong derivatives in `H¹₀`; spatial Laplacians are weak. -/
def IsWeakDirichletSolution (C : Coefficients)
    (u velocity : ℝ → Fin 2 → H¹₀(Ω)) : Prop :=
  (∀ t i, HasDerivAt (fun s ↦ u s i) (velocity t i) t) ∧
    ∀ t (v : H¹₀(Ω)),
      massFormCLM (velocity t 0) v =
        -C.diffusion₁ * dirichletForm (u t 0) v +
          C.a * massFormCLM (u t 0) v + C.b * massFormCLM (u t 1) v ∧
      massFormCLM (velocity t 1) v =
        -C.diffusion₂ * dirichletForm (u t 1) v +
          C.c * massFormCLM (u t 0) v + C.d * massFormCLM (u t 1) v

private theorem mode_mass_identity (rate a b diffusion μ v w E M : ℝ)
    (h : (a - diffusion * μ) * v + b * w = rate * v) :
    rate * (E * v * M) = -diffusion * (E * v * (μ * M)) +
      a * (E * v * M) + b * (E * w * M) := by
  cas using h

/-- A matrix eigenvector and a Dirichlet eigenfunction solve the
linearized PDE, including its boundary condition. -/
theorem dirichletMode_isSolution {C : Coefficients} {μ rate : ℝ}
    {φ : H¹₀(Ω)} (hφ : Weak.IsWeakEigenfunction dirichletForm massFormCLM μ φ)
    {vector : Fin 2 → ℝ}
    (hv : Module.End.HasEigenvector (C.modeMatrix μ).toLin' rate vector) :
    IsWeakDirichletSolution C (dirichletMode φ rate vector)
      (fun t i ↦ rate • dirichletMode φ rate vector t i) := by
  have heq := Module.End.mem_eigenspace_iff.mp hv.1
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  simp only [Matrix.toLin'_apply, Coefficients.modeMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at h0 h1
  constructor
  · intro t i
    have hd : HasDerivAt (fun s ↦ Real.exp (rate * s) * vector i)
        (rate * (Real.exp (rate * t) * vector i)) t := by cas
    simpa [dirichletMode, smul_smul] using hd.smul_const φ
  · intro t v
    have hw := hφ.2 v
    simp only [dirichletMode, map_smul, smul_apply,
      smul_eq_mul]
    rw [hw]
    constructor
    · exact mode_mass_identity rate C.a C.b C.diffusion₁ μ _ _ _ _ h0
    · change C.c * vector 0 + (C.d - C.diffusion₂ * μ) * vector 1 =
        rate * vector 1 at h1
      rw [add_comm] at h1
      convert mode_mass_identity rate C.d C.c C.diffusion₂ μ (vector 1) (vector 0)
        (Real.exp (rate * t)) (massFormCLM φ v) h1 using 1
      ac_rfl

/-- Positive rate gives unbounded growth of the first species in the domain's `L²` norm. -/
theorem dirichletMode_norm_tendsto {φ : H¹₀(Ω)} {rate : ℝ} {vector : Fin 2 → ℝ}
    (hφ : baseCoordCLM φ ≠ 0) (hrate : 0 < rate) (hv : vector 0 ≠ 0) :
    Filter.Tendsto (fun t ↦ ‖baseCoordCLM (dirichletMode φ rate vector t 0)‖)
      Filter.atTop Filter.atTop := by
  have hc : 0 < |vector 0| * ‖baseCoordCLM φ‖ :=
    mul_pos (abs_pos.mpr hv) (norm_pos_iff.mpr hφ)
  have ht := Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop hrate)
  convert ht.atTop_mul_const hc using 1
  ext t
  simp only [dirichletMode, map_smul, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  exact mul_assoc _ _ _

/-- A qualifying discrete Dirichlet eigenvalue produces an exponentially growing
solution. The positive rate and matrix eigenvector are derived, not hypothesized. -/
theorem exists_growing_dirichletMode {C : Coefficients} {μ : ℝ}
    (htrace : C.a + C.d < 0) (hdet : 0 < C.a * C.d - C.b * C.c)
    (h₁ : 0 ≤ C.diffusion₁) (h₂ : 0 ≤ C.diffusion₂) (hμ : 0 < μ)
    {φ : H¹₀(Ω)} (hΩ : IsOpen Ω)
    (hφ : Weak.IsWeakEigenfunction dirichletForm massFormCLM μ φ)
    (hmode : (C.modeMatrix μ).det < 0) :
    ∃ rate : ℝ, 0 < rate ∧ ∃ vector : Fin 2 → ℝ,
      vector 0 ≠ 0 ∧
      IsWeakDirichletSolution C (dirichletMode φ rate vector)
        (fun t i ↦ rate • dirichletMode φ rate vector t i) ∧
      Filter.Tendsto (fun t ↦ ‖baseCoordCLM (dirichletMode φ rate vector t 0)‖)
        Filter.atTop Filter.atTop := by
  have hb := coupling_ne_zero_of_mode_det_nonpos htrace hdet h₁ h₂ hμ.le hmode.le
  obtain ⟨rate, hrate, vector, hv, hv0⟩ := exists_positive_mode_eigenvector C μ hmode hb
  refine ⟨rate, hrate, vector, hv0, dirichletMode_isSolution hφ hv, ?_⟩
  apply dirichletMode_norm_tendsto (hrate := hrate) (hv := hv0)
  intro hz
  exact hφ.1 ((baseCoordCLM_injective hΩ) (hz.trans (map_zero _).symm))

/-- Zero determinant yields a nonzero stationary Dirichlet mode. It does not yield
positive exponential growth. Zero diffusivities are allowed, as in Evans's (20) in §4.1.2,
where `a₁, a₂ ≥ 0`. -/
theorem exists_stationary_dirichletMode {C : Coefficients} {μ : ℝ}
    (htrace : C.a + C.d < 0) (hdet : 0 < C.a * C.d - C.b * C.c)
    (h₁ : 0 ≤ C.diffusion₁) (h₂ : 0 ≤ C.diffusion₂) (hμ : 0 < μ)
    {φ : H¹₀(Ω)} (hφ : Weak.IsWeakEigenfunction dirichletForm massFormCLM μ φ)
    (hmode : (C.modeMatrix μ).det = 0) :
    ∃ vector : Fin 2 → ℝ,
      IsWeakDirichletSolution C (dirichletMode φ 0 vector) (fun _ _ ↦ 0) ∧
      (∀ t i, dirichletMode φ 0 vector t i = vector i • φ) ∧
      dirichletMode φ 0 vector 0 0 ≠ 0 := by
  have hb := coupling_ne_zero_of_mode_det_nonpos htrace hdet h₁ h₂ hμ.le hmode.le
  obtain ⟨vector, hv, hv0⟩ := exists_zero_mode_eigenvector C μ hmode hb
  refine ⟨vector, ?_, ?_, ?_⟩
  · simpa using dirichletMode_isSolution hφ hv
  · intro t i
    simp [dirichletMode]
  · simpa [dirichletMode] using smul_ne_zero hv0 hφ.1

/-- The eigenfunctions needed by the mode construction come from the domain's
Dirichlet spectral theorem, as in Evans's §6.5.1, Theorem 1: a Hilbert basis of `L²(Ω)`
of weak eigenfunctions with positive eigenvalues. No mode-existence assumption is added. -/
theorem exists_dirichlet_eigenbasis (hn : 0 < n) (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (DerivLp n 2 Ω))
      (μ : ι → ℝ) (φ : ι → H¹₀(Ω)),
      ∀ i, 0 < μ i ∧ baseCoordCLM (φ i) = b i ∧
        Weak.IsWeakEigenfunction dirichletForm massFormCLM (μ i) (φ i) := by
  have hidentity : variableCoeffForm (identityCoefficientOperator (n := n) (Ω := Ω)) =
      dirichletForm := by
    ext u v
    exact variableCoeffForm_identity u v
  simpa only [hidentity] using exists_hilbertBasis_variableCoeff_eigenfunctions
    hn hΩ hbounded identityCoefficientOperator
    integratedElliptic_identity symmetricCoefficientOperator_identity

end ReactionDiffusion.Turing
