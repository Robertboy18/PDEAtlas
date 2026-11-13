/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.HalfPlane.Assembly
public import PDE.Fluid.Boussinesq.HalfPlane.FixedPoint
public import PDE.Fluid.Boussinesq.HalfPlane.IterationBounds

/-!
# Local existence for the half-plane Boussinesq system

For data `ω₀ ∈ C^{1,α}`, `θ₀ ∈ C^{2,α}` within the closed half-plane, vanishing there outside a
disc, the system has a solution in the class `IsSolutionOn` on a time interval `(-T, T)` whose
length depends only on `α`, the support radius `R` and the bound `N` of the norms of the data.
At every time of `(-T, T)` the fields are again data of the class, with support radius `R + 1`
and the bound `iterationOutputBound α R N T`; negative times are included so that the time
derivatives at `t = 0` are two-sided, as the classical class requires.

## Main results

* `exists_isSolutionOn_Ioo`, `exists_isRegularSolutionOn_Ioo`: local existence with a lifespan
  depending only on `α`, `R`, `N`.

## How it works

We use the particle-trajectory method of Majda and Bertozzi, Chapter 4, as Chae, Kim and Nam do for
the whole plane. They make the Picard iteration converge by a Lipschitz estimate; our difference
estimate `abs_carriedHistory_sub_le` has the Osgood modulus instead, and the iterates converge by
Osgood's lemma. The solution is the assembly (`isSolutionOn_of_fixedPoint`) of the fixed point of
the iteration map `carriedHistory` (`exists_fixedPoint_of_isHolderData`), which exists because the
map sends the class `IsIterationClass` into itself for these times (`exists_iterationTime`,
`isIterationClass_carriedHistory`).

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 4, The Particle-Trajectory Method for
  Existence and Uniqueness of Solutions to the Euler Equation, pp. 136-167.
  <https://doi.org/10.1017/CBO9780511613203>
* D. Chae, S.-K. Kim and H.-S. Nam, "Local existence and blow-up criterion of Hölder continuous
  solutions of the Boussinesq equations", *Nagoya Math. J.* 155 (1999), 55-80.
  <https://doi.org/10.1017/S0027763000006991>
-/

@[expose] public section

noncomputable section

open Set
open IncompressibleFlow PDE.Analysis.ODE PDE.Hyperbolic.Transport

namespace Boussinesq.HalfPlane

/-- **Local existence at regularity `C^{1,α} × C^{2,α}`.** For `0 < α < 1` and bounds `R, N ≥ 0`
there is a time `T > 0` such that all data of the class `IsHolderData ω₀ θ₀ α R N` have a solution
on `(-T, T)` with these data at time zero, whose time slices are data of the class with support
radius `R + 1` and bound `iterationOutputBound α R N T`. -/
theorem exists_isSolutionOn_Ioo {α R N : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R)
    (hN : 0 ≤ N) :
    ∃ T > 0, ∀ ω₀ θ₀ : ℝ^2 → ℝ, IsHolderData ω₀ θ₀ α R N →
      ∃ sol : VorticityStreamFields, IsSolutionOn sol (Ioo (-T) T) ∧ HasDataAt sol 0 ω₀ θ₀ ∧
        ∀ t ∈ Ioo (-T) T, IsHolderData (fun x ↦ sol.vorticity x t)
          (fun x ↦ sol.temperature x t) α (R + 1) (iterationOutputBound α R N T) := by
  obtain ⟨T, hT, h₁, h₂, h₃, h₄⟩ := exists_iterationTime (R := R) hα hN
  refine ⟨T, hT, fun ω₀ θ₀ hd ↦ ?_⟩
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hstart : IsIterationClass T α R N (fun _ ↦ dataVorticity ω₀) :=
    isIterationClass_dataVorticity hd hα.le hα1.le
  have hinv (ω : ℝ → ℝ^2 → ℝ) (hω : IsIterationClass T α R N ω) :
      IsIterationClass T α R N (carriedHistory ω₀ θ₀ (-T) T ω) :=
    isIterationClass_carriedHistory hd hα hα1 hR hT h₁ h₂ h₃ h₄ hω
  have hσ : 0 ≤ iterationSecondBound α R N T :=
    (hstart.isBoundedFlowOn hα hα1 (by linarith) (by linarith)).zero_le_σ h0
  have hL0 : 0 ≤ iterationAmplitudeLipschitz α R N T :=
    add_nonneg hN (mul_nonneg hT.le (forcingDerivBound_nonneg hN (Real.exp_pos _).le hσ))
  obtain ⟨ω, hω, hfix⟩ := exists_fixedPoint_of_isHolderData hd hT.le hα hα1 hL0 hstart hinv
    fun ω' hω' t ht a' a'' ha' ha'' ↦
      IsIterationClass.abs_amplitude_sub_le hω' hd hα hα1 hR hT.le ht ha' ha''
  obtain ⟨hsol, hdat⟩ := isSolutionOn_of_fixedPoint hα hα1 hd (by linarith) hT hω hfix
  exact ⟨assembled ω₀ θ₀ ω (-T) T, hsol, hdat, fun t ht ↦
    isHolderData_carried hd hα hα1 hR hT h₄ hω (hinv ω hω) (Ioo_subset_Icc_self ht)⟩

/-- **Local existence of regular solutions.** The solutions of `exists_isSolutionOn_Ioo` are
regular on `(-T, T)`, with one support radius and one bound for all times. -/
theorem exists_isRegularSolutionOn_Ioo {α R N : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R)
    (hN : 0 ≤ N) :
    ∃ T > 0, ∀ ω₀ θ₀ : ℝ^2 → ℝ, IsHolderData ω₀ θ₀ α R N →
      ∃ sol : VorticityStreamFields, IsRegularSolutionOn sol (Ioo (-T) T) α ∧
        HasDataAt sol 0 ω₀ θ₀ ∧
        ∀ t ∈ Ioo (-T) T, IsHolderData (fun x ↦ sol.vorticity x t)
          (fun x ↦ sol.temperature x t) α (R + 1) (iterationOutputBound α R N T) := by
  obtain ⟨T, hT, h⟩ := exists_isSolutionOn_Ioo hα hα1 hR hN
  refine ⟨T, hT, fun ω₀ θ₀ hd ↦ ?_⟩
  obtain ⟨sol, hsol, hdat, hbd⟩ := h ω₀ θ₀ hd
  exact ⟨sol, ⟨hsol, fun a b hab ↦ ⟨R + 1, iterationOutputBound α R N T,
    fun t ht ↦ hbd t (hab ht)⟩⟩, hdat, hbd⟩

end Boussinesq.HalfPlane
