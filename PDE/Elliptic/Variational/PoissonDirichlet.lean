/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.QuadraticEnergy
public import PDE.Analysis.Variational.LaxMilgram
public import PDE.Elliptic.Variational.PrincipalForms

/-!
# Dirichlet variational problem

We treat the homogeneous Dirichlet problem for Poisson's equation, `-Δu = f` in `Ω` and `u = 0` on
`∂Ω`, in the weak sense (9) of Evans's §6.1.2: the Lax-Milgram solution `dirichletSolve`, its
variational characterization, and its concrete coordinate weak equation. The energy-minimization
statements are the case `aⁱʲ = δᵢⱼ` on `H¹₀` of the generalized Dirichlet principle, Example 2 of
Evans's §8.1.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.2, (8)-(9), p. 314; §6.2.1, Theorem 1 (Lax-Milgram
  Theorem), pp. 315-317; §8.1.2, Example 1 (Dirichlet's principle) and Example 2 (Generalized
  Dirichlet's principle), p. 456.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open PDE.Analysis.Variational
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}


/-- The Dirichlet solution operator `L²(Ω) → H¹₀(Ω)` obtained from
Lax-Milgram. -/
noncomputable def dirichletSolveCLM
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    DerivLp n 2 Ω →L[ℝ] H¹₀(Ω) := by
  have hB : @IsCoercive
      (H¹₀(Ω)) inferInstance
      inferInstance
      (dirichletForm (n := n) (Ω := Ω)) :=
    dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded
  let S : StrongDual ℝ (H¹₀(Ω)) →L[ℝ]
      H¹₀(Ω) :=
    solveCLM (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω)) hB
  let L : DerivLp n 2 Ω →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    loadFunctionalCLM (n := n) (Ω := Ω)
  exact S.comp L

/-- The Lax-Milgram weak solution for the concrete Dirichlet form. -/
noncomputable def dirichletSolve
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) : H¹₀(Ω) :=
  dirichletSolveCLM (n := n) (Ω := Ω) hn hΩbounded f

/-- Evaluating the bounded Dirichlet solution operator at `f` gives the named solver
`dirichletSolve f`. -/
@[simp]
theorem dirichletSolveCLM_apply
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) :
    dirichletSolveCLM (n := n) (Ω := Ω) hn hΩbounded f =
      dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f :=
  rfl

/-- The named Dirichlet solver satisfies the weak formulation. -/
theorem dirichletSolve.isWeakSolution
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) :
    IsWeakSolution
      (dirichletForm (n := n) (Ω := Ω))
      (loadFunctional (n := n) (Ω := Ω) f)
      (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f) := by
  unfold dirichletSolve dirichletSolveCLM
  rw [ContinuousLinearMap.comp_apply, loadFunctionalCLM_apply]
  exact solveCLM.isWeakSolution _ _ _

/-- The homogeneous Dirichlet problem has the zero Lax-Milgram solution. -/
theorem dirichletSolve_zero
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    dirichletSolve (n := n) (Ω := Ω) hn hΩbounded
      (0 : DerivLp n 2 Ω) = 0 := by
  change dirichletSolveCLM (n := n) (Ω := Ω) hn hΩbounded 0 = 0
  exact map_zero (dirichletSolveCLM (n := n) (Ω := Ω) hn hΩbounded)

/-- A priori estimate for the concrete Dirichlet weak solution in terms of the load. -/
theorem dirichletSolve_norm_le_load
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : DerivLp n 2 Ω,
      ‖dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f‖ ≤
        C * ‖loadFunctional (n := n) (Ω := Ω) f‖ := by
  let S : StrongDual ℝ (H¹₀(Ω)) →L[ℝ] H¹₀(Ω) :=
    solveCLM
      (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω))
      (dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded)
  rcases @ContinuousLinearMap.bound
      ℝ ℝ
      (StrongDual ℝ (H¹₀(Ω)))
      (H¹₀(Ω))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance
      (RingHom.id ℝ) inferInstance S with
    ⟨C, hC, hS⟩
  refine ⟨C, hC, ?_⟩
  intro f
  rw [dirichletSolve, dirichletSolveCLM, ContinuousLinearMap.comp_apply,
    loadFunctionalCLM_apply]
  exact hS (loadFunctional (n := n) (Ω := Ω) f)

/-- A priori estimate directly in terms of the `L²` forcing datum. -/
theorem dirichletSolve_norm_le
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : DerivLp n 2 Ω,
      ‖dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f‖ ≤ C * ‖f‖ := by
  rcases dirichletSolve_norm_le_load (n := n) (Ω := Ω) hn hΩbounded with
    ⟨C, hC, hsolve⟩
  refine ⟨C, hC, ?_⟩
  intro f
  exact (hsolve f).trans <|
    mul_le_mul_of_nonneg_left
      (norm_loadFunctional_le (n := n) (Ω := Ω) f) (le_of_lt hC)

/-- Continuous dependence for the concrete Dirichlet weak solution in the dual norm. -/
theorem dirichletSolve_sub_dirichletSolve_norm_le_load
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : DerivLp n 2 Ω,
      ‖dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f -
          dirichletSolve (n := n) (Ω := Ω) hn hΩbounded g‖ ≤
        C * ‖loadFunctional (n := n) (Ω := Ω) f -
          loadFunctional (n := n) (Ω := Ω) g‖ := by
  let S : StrongDual ℝ (H¹₀(Ω)) →L[ℝ] H¹₀(Ω) :=
    solveCLM
      (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω))
      (dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded)
  rcases @ContinuousLinearMap.bound
      ℝ ℝ
      (StrongDual ℝ (H¹₀(Ω)))
      (H¹₀(Ω))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance
      (RingHom.id ℝ) inferInstance S with
    ⟨C, hC, hS⟩
  refine ⟨C, hC, ?_⟩
  intro f g
  simp only [dirichletSolve, dirichletSolveCLM]
  calc
    ‖S (loadFunctional (n := n) (Ω := Ω) f) -
        S (loadFunctional (n := n) (Ω := Ω) g)‖ =
        ‖S (loadFunctional (n := n) (Ω := Ω) f -
          loadFunctional (n := n) (Ω := Ω) g)‖ := by
      exact congrArg norm (map_sub S _ _).symm
    _ ≤ C * ‖loadFunctional (n := n) (Ω := Ω) f -
        loadFunctional (n := n) (Ω := Ω) g‖ :=
      hS (loadFunctional (n := n) (Ω := Ω) f -
        loadFunctional (n := n) (Ω := Ω) g)

/-- Continuous dependence directly in terms of the `L²` forcing data. -/
theorem dirichletSolve_sub_dirichletSolve_norm_le
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : DerivLp n 2 Ω,
      ‖dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f -
          dirichletSolve (n := n) (Ω := Ω) hn hΩbounded g‖ ≤
        C * ‖f - g‖ := by
  rcases dirichletSolve_sub_dirichletSolve_norm_le_load
      (n := n) (Ω := Ω) hn hΩbounded with
    ⟨C, hC, hsolve⟩
  refine ⟨C, hC, ?_⟩
  intro f g
  have hload :
      ‖loadFunctional (n := n) (Ω := Ω) f -
          loadFunctional (n := n) (Ω := Ω) g‖ ≤ ‖f - g‖ := by
    rw [← loadFunctional_sub (n := n) (Ω := Ω) f g]
    exact norm_loadFunctional_le (n := n) (Ω := Ω) (f - g)
  exact (hsolve f g).trans <| mul_le_mul_of_nonneg_left hload (le_of_lt hC)

/-- The Dirichlet functional `J(v) = 1/2 ∫|Dv|² - ∫fv` on `H¹₀(Ω)`. -/
noncomputable def dirichletEnergy
    (f : DerivLp n 2 Ω)
    (v : H¹₀(Ω)) : ℝ :=
  @energy (H¹₀(Ω)) inferInstance
    inferInstance
    (dirichletForm (n := n) (Ω := Ω))
    (loadFunctional (n := n) (Ω := Ω) f)
    v

/-- At any Dirichlet weak solution, the energy difference is one half of the Dirichlet
energy of the perturbation. -/
theorem dirichletEnergy_sub_eq
    (f : DerivLp n 2 Ω)
    {u : H¹₀(Ω)}
    (hu :
      IsWeakSolution
        (dirichletForm (n := n) (Ω := Ω))
        (loadFunctional (n := n) (Ω := Ω) f)
        u)
    (v : H¹₀(Ω)) :
    dirichletEnergy (n := n) (Ω := Ω) f v -
        dirichletEnergy (n := n) (Ω := Ω) f u =
      (1 / 2 : ℝ) *
        dirichletForm (n := n) (Ω := Ω) (v - u) (v - u) := by
  exact @energy_sub_energy_eq
    (H¹₀(Ω))
    inferInstance
    inferInstance
    (dirichletForm (n := n) (Ω := Ω))
    (loadFunctional (n := n) (Ω := Ω) f)
    u
    (fun a b ↦ dirichletForm_symm (n := n) (Ω := Ω) a b)
    hu v

/-- Every Dirichlet weak solution minimizes the Dirichlet functional over `H¹₀(Ω)`. -/
theorem dirichletEnergy_minimal_of_weakSolution
    (f : DerivLp n 2 Ω)
    {u : H¹₀(Ω)}
    (hu :
      IsWeakSolution
        (dirichletForm (n := n) (Ω := Ω))
        (loadFunctional (n := n) (Ω := Ω) f)
        u)
    (v : H¹₀(Ω)) :
    dirichletEnergy (n := n) (Ω := Ω) f u ≤
      dirichletEnergy (n := n) (Ω := Ω) f v := by
  exact @IsWeakSolution.energy_le
    (H¹₀(Ω))
    inferInstance
    inferInstance
    (dirichletForm (n := n) (Ω := Ω))
    (loadFunctional (n := n) (Ω := Ω) f)
    u
    (fun a b ↦ dirichletForm_symm (n := n) (Ω := Ω) a b)
    (fun w ↦ dirichletForm_self_nonneg (n := n) (Ω := Ω) w)
    hu v

/-- The Lax-Milgram Dirichlet solution minimizes the Dirichlet functional. -/
theorem dirichletSolve.minimizesEnergy
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) (v : H¹₀(Ω)) :
    dirichletEnergy (n := n) (Ω := Ω) f
        (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f) ≤
      dirichletEnergy (n := n) (Ω := Ω) f v :=
  dirichletEnergy_minimal_of_weakSolution
    (n := n) (Ω := Ω) f
    (dirichletSolve.isWeakSolution (n := n) (Ω := Ω) hn hΩbounded f)
    v

/-- Coercivity makes the Dirichlet weak solution the unique point with the same minimal
energy. -/
theorem dirichletEnergy.eq_dirichletSolve_of_eq_min
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) {v : H¹₀(Ω)}
    (hv :
      dirichletEnergy (n := n) (Ω := Ω) f v =
        dirichletEnergy (n := n) (Ω := Ω) f
          (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f)) :
    v = dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f := by
  apply @IsWeakSolution.eq_of_energy_eq
    (H¹₀(Ω))
    inferInstance
    inferInstance
    (dirichletForm (n := n) (Ω := Ω))
    (dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded)
    (loadFunctional (n := n) (Ω := Ω) f)
    (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f)
    v
  · exact fun a b ↦ dirichletForm_symm (n := n) (Ω := Ω) a b
  · exact dirichletSolve.isWeakSolution
      (n := n) (Ω := Ω) hn hΩbounded f
  · simpa [dirichletEnergy] using hv

/-- Equality in the Dirichlet energy principle occurs exactly at the Lax-Milgram solution. -/
theorem dirichletEnergy.eq_min_iff
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) {v : H¹₀(Ω)} :
    dirichletEnergy (n := n) (Ω := Ω) f v =
        dirichletEnergy (n := n) (Ω := Ω) f
          (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f) ↔
      v = dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f := by
  constructor
  · intro hv
    exact dirichletEnergy.eq_dirichletSolve_of_eq_min
      (n := n) (Ω := Ω) hn hΩbounded f hv
  · rintro rfl
    rfl

/-- Every other `H¹₀` field has strictly larger energy than the weak solution. -/
theorem dirichletSolve.energy_lt_of_ne
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) {v : H¹₀(Ω)}
    (hv : v ≠ dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f) :
    dirichletEnergy (n := n) (Ω := Ω) f
        (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f) <
      dirichletEnergy (n := n) (Ω := Ω) f v := by
  have hle :=
    dirichletSolve.minimizesEnergy (n := n) (Ω := Ω) hn hΩbounded f v
  exact lt_of_le_of_ne hle (by
    intro hEq
    exact hv ((dirichletEnergy.eq_min_iff
      (n := n) (Ω := Ω) hn hΩbounded f).mp hEq.symm))

/-- The Lax-Milgram solution is the unique minimizer of the Dirichlet functional. -/
theorem dirichletSolve.unique_energyMinimizer
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) {v : H¹₀(Ω)}
    (hv : ∀ w : H¹₀(Ω),
      dirichletEnergy (n := n) (Ω := Ω) f v ≤
        dirichletEnergy (n := n) (Ω := Ω) f w) :
    v = dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f := by
  apply dirichletEnergy.eq_dirichletSolve_of_eq_min
    (n := n) (Ω := Ω) hn hΩbounded f
  exact le_antisymm
    (hv (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f))
    (dirichletSolve.minimizesEnergy (n := n) (Ω := Ω) hn hΩbounded f v)

/-- Minimizing the Dirichlet functional is equivalent to satisfying its weak
Euler-Lagrange equation. -/
theorem dirichletEnergy.minimizer_iff_weakSolution
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) {u : H¹₀(Ω)} :
    (∀ v : H¹₀(Ω),
      dirichletEnergy (n := n) (Ω := Ω) f u ≤
        dirichletEnergy (n := n) (Ω := Ω) f v) ↔
      IsWeakSolution
        (dirichletForm (n := n) (Ω := Ω))
        (loadFunctional (n := n) (Ω := Ω) f)
        u := by
  constructor
  · intro hmin
    have hu :=
      dirichletSolve.unique_energyMinimizer
        (n := n) (Ω := Ω) hn hΩbounded f hmin
    rw [hu]
    exact dirichletSolve.isWeakSolution (n := n) (Ω := Ω) hn hΩbounded f
  · intro hu v
    exact dirichletEnergy_minimal_of_weakSolution (n := n) (Ω := Ω) f hu v

/-- The concrete weak formulation in coordinate form. -/
theorem dirichlet_weakSolution_equation
    (f : DerivLp n 2 Ω) {u : H¹₀(Ω)}
    (hu :
      IsWeakSolution
        (dirichletForm (n := n) (Ω := Ω))
        (loadFunctional (n := n) (Ω := Ω) f)
        u)
    (v : H¹₀(Ω)) :
    (∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i u,
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ) =
      ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
  calc
    (∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i u,
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ)
        = dirichletForm (n := n) (Ω := Ω) u v := by
          rw [dirichletForm_apply]
    _ = loadFunctional (n := n) (Ω := Ω) f v :=
      IsWeakSolution.apply (V := H¹₀(Ω)) hu v
    _ = ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
      rw [loadFunctional_apply]

/-- The concrete Lax-Milgram solver satisfies the coordinate weak equation. -/
theorem dirichletSolve_equation
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) (v : H¹₀(Ω)) :
    (∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i
            (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f),
          derivCoordCLM (n := n) (Ω := Ω) i v⟫_ℝ) =
      ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ :=
  dirichlet_weakSolution_equation
    (n := n) (Ω := Ω) f
    (dirichletSolve.isWeakSolution
      (n := n) (Ω := Ω) hn hΩbounded f)
    v

end GraphSpace

end SobolevSpace
