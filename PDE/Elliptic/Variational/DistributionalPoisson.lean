/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PoissonDirichlet
public import PDE.Elliptic.Variational.DivergenceSolution

/-!
# Distributional Poisson equation

On an open set `Ω ⊆ ℝ^n`, a function `u ∈ H¹₀(Ω)` is a weak solution of the homogeneous
Dirichlet problem `-Δu = f` with `f ∈ L²(Ω)` when

`∑ᵢ ∫_Ω ∂ᵢu ∂ᵢφ = ∫_Ω f φ  for every φ ∈ C_c^∞(Ω)`.

Evans derives this identity for smooth test functions (§6.1.2, (7)) and then, by approximation,
defines weak solutions by testing against all of `H¹₀(Ω)` (his (9)). That definition is the
Hilbert-space formulation in `PDE.Elliptic.Variational.PoissonDirichlet`, whose Lax–Milgram
solution is `dirichletSolve`. The two formulations agree
on open sets, which transfers existence, uniqueness, Dirichlet's principle, and the
linear-superposition identities to the distributional side.

## Main results

* `IsWeakPoissonSolution`: the distributional weak formulation, with openness of `Ω` built in.
* `isWeakSolution_iff_isWeakPoissonSolution`: equivalence with the `H¹₀` Hilbert-space weak
  equation on open sets.
* `IsWeakPoissonSolution.existsUnique`, `IsWeakPoissonSolution.iff_eq_dirichletSolve`: on a
  bounded open set with `0 < n` the distributional problem has exactly one solution, namely
  the Lax–Milgram solver.
* `dirichletEnergy.minimizer_iff_isWeakPoissonSolution`: Dirichlet's principle in the
  distributional formulation.
* `IsWeakPoissonSolution.add`, `IsWeakPoissonSolution.smul`,
  `IsWeakPoissonSolution.linear_combination`, `dirichletSolve_add`, `dirichletSolve_smul`:
  superposition of solutions and linearity of the solver.
* `variableCoeffSolve_identity_eq_dirichletSolve`: the variable-coefficient solver with
  identity coefficients is the Dirichlet solver.

## Implementation notes

Openness of `Ω` is built into `IsWeakPoissonSolution` itself; the solvability theorems take it
as an explicit hypothesis `hΩopen` as well. On a positive-measure set with empty interior the
space of compactly supported smooth test functions can be trivial, and the integral identity
alone would not characterize a distributional equation. Every displayed product is integrable,
so the definition does not depend on the fallback value of Mathlib's totalized integral.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.2, (7) and Definitions (8)-(9), p. 314; §6.2.1,
  Theorem 1 (Lax–Milgram Theorem), pp. 315-317; §2.2.5, Theorem 17 (Dirichlet's principle, for
  classical solutions), pp. 42-43.
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


/-- The weak formulation of the homogeneous Dirichlet Poisson problem `-Δu = f` on an open
set, tested against `C_c^∞(Ω)` as in Evans's identity (7) of §6.1.2.

Openness is part of the proposition, rather than merely a theorem-side convention: on a
positive-measure set with empty interior the class of compactly supported smooth test functions
can be trivial, so the integral identity alone would not characterize a distributional PDE.
Every displayed product is integrable: both weak derivatives and the forcing
are in `L²`, and the canonical test-function embedding places each test and
its first derivatives in `L²`. Thus the definition does not rely on the
fallback value of Mathlib's totalized integral. -/
def IsWeakPoissonSolution
    (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω)) : Prop :=
  IsOpen Ω ∧
    ∀ φ : TestFunctionOn n Ω,
      (∑ i : Fin n,
        ∫ x, (derivCoordCLM (n := n) (Ω := Ω) i u :
            ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x
          ∂domainMeasure n Ω) =
        ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω

/-- The Hilbert-space equation is equivalent to the distributional weak Poisson equation. -/
theorem isWeakSolution_iff_isWeakPoissonSolution
    (hΩopen : IsOpen Ω) (f : DerivLp n 2 Ω)
    (u : H¹₀(Ω)) :
    IsWeakSolution
        (dirichletForm (n := n) (Ω := Ω))
        (loadFunctional (n := n) (Ω := Ω) f) u ↔
      IsWeakPoissonSolution (n := n) (Ω := Ω) f u := by
  constructor
  · intro hu
    refine ⟨hΩopen, ?_⟩
    intro φ
    have heq := dirichlet_weakSolution_equation
      (n := n) (Ω := Ω) f hu
      (testFunctionToH10 (n := n) (Ω := Ω) φ)
    simpa only [inner_deriv_testFunction_eq_integral,
      inner_base_testFunction_eq_integral] using heq
  · intro hu
    have htest :
        (dirichletForm (n := n) (Ω := Ω) u :
            H¹₀(Ω) → ℝ) ∘
            testFunctionToH10Linear (n := n) (Ω := Ω) =
          (loadFunctional (n := n) (Ω := Ω) f :
            H¹₀(Ω) → ℝ) ∘
            testFunctionToH10Linear (n := n) (Ω := Ω) := by
      funext φ
      have hφ := hu.2 φ
      change dirichletForm (n := n) (Ω := Ω) u
          (testFunctionToH10 (n := n) (Ω := Ω) φ) =
        loadFunctional (n := n) (Ω := Ω) f
          (testFunctionToH10 (n := n) (Ω := Ω) φ)
      rw [dirichletForm_apply, loadFunctional_apply]
      simpa only [inner_deriv_testFunction_eq_integral,
        inner_base_testFunction_eq_integral] using hφ
    have hall :=
      (denseRange_testFunctionToH10Linear
        (n := n) (Ω := Ω)).equalizer
        (dirichletForm (n := n) (Ω := Ω) u).continuous
        (loadFunctional (n := n) (Ω := Ω) f).continuous htest
    intro v
    exact congrFun hall v

/-- Existence and uniqueness for the homogeneous Dirichlet Poisson problem on a bounded
domain. -/
theorem IsWeakPoissonSolution.existsUnique
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (f : DerivLp n 2 Ω) :
    ∃! u : H¹₀(Ω),
      IsWeakPoissonSolution (n := n) (Ω := Ω) f u := by
  let u := dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f
  refine ⟨u, ?_, ?_⟩
  · exact (isWeakSolution_iff_isWeakPoissonSolution
      (n := n) (Ω := Ω) hΩopen f u).1
        (dirichletSolve.isWeakSolution
          (n := n) (Ω := Ω) hn hΩbounded f)
  · intro v hv
    exact @IsWeakSolution.eq_solve
      (H¹₀(Ω))
      inferInstance
      (Submodule.innerProductSpace
        ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule))
      inferInstance
      (dirichletForm (n := n) (Ω := Ω))
      (dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded)
      (loadFunctional (n := n) (Ω := Ω) f)
      v
      ((isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen f v).2 hv)

/-- The named Lax–Milgram solution satisfies the distributional Poisson identity. -/
theorem dirichletSolve.isWeakPoissonSolution
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (f : DerivLp n 2 Ω) :
    IsWeakPoissonSolution (n := n) (Ω := Ω) f
      (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f) :=
  (isWeakSolution_iff_isWeakPoissonSolution
    (n := n) (Ω := Ω) hΩopen f
    (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f)).1
      (dirichletSolve.isWeakSolution
        (n := n) (Ω := Ω) hn hΩbounded f)

/-- The zero `H¹₀` field solves the zero-forcing weak Poisson equation. -/
theorem IsWeakPoissonSolution.zero
    (hΩopen : IsOpen Ω) :
    IsWeakPoissonSolution (n := n) (Ω := Ω) (0 : DerivLp n 2 Ω) 0 :=
by
  let B : H¹₀(Ω) →L[ℝ]
      H¹₀(Ω) →L[ℝ] ℝ :=
    dirichletForm (n := n) (Ω := Ω)
  rw [← isWeakSolution_iff_isWeakPoissonSolution
    (n := n) (Ω := Ω) hΩopen (0 : DerivLp n 2 Ω) 0]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (0 : DerivLp n 2 Ω)) 0
  intro w
  calc
    B 0 w = (0 : StrongDual ℝ (H¹₀(Ω))) w :=
      @IsWeakSolution.zero (H¹₀(Ω)) inferInstance
        inferInstance B w
    _ = 0 := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (0 : DerivLp n 2 Ω) w := by
      simp only [loadFunctional_apply, inner_zero_left]

/-- Superposition for weak Poisson solutions. -/
theorem IsWeakPoissonSolution.add
    {f g : DerivLp n 2 Ω}
    {u v : H¹₀(Ω)}
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω) f u)
    (hv : IsWeakPoissonSolution (n := n) (Ω := Ω) g v) :
    IsWeakPoissonSolution (n := n) (Ω := Ω) (f + g) (u + v) := by
  let B : H¹₀(Ω) →L[ℝ]
      H¹₀(Ω) →L[ℝ] ℝ :=
    dirichletForm (n := n) (Ω := Ω)
  rw [← isWeakSolution_iff_isWeakPoissonSolution
    (n := n) (Ω := Ω) hu.1 (f + g) (u + v)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (f + g)) (u + v)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hu.1 f u).2 hu
  have hv' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) g) v := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hv.1 g v).2 hv
  have h := hu'.add hv'
  intro w
  calc
    B (u + v) w =
        (loadFunctional (n := n) (Ω := Ω) f +
          loadFunctional (n := n) (Ω := Ω) g) w := h w
    _ = loadFunctional (n := n) (Ω := Ω) f w +
          loadFunctional (n := n) (Ω := Ω) g w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (f + g) w := by
      simp only [loadFunctional_apply, inner_add_left]

/-- Negating a weak Poisson solution negates the forcing datum. -/
theorem IsWeakPoissonSolution.neg
    {f : DerivLp n 2 Ω}
    {u : H¹₀(Ω)}
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω) f u) :
    IsWeakPoissonSolution (n := n) (Ω := Ω) (-f) (-u) := by
  let B : H¹₀(Ω) →L[ℝ]
      H¹₀(Ω) →L[ℝ] ℝ :=
    dirichletForm (n := n) (Ω := Ω)
  rw [← isWeakSolution_iff_isWeakPoissonSolution
    (n := n) (Ω := Ω) hu.1 (-f) (-u)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (-f)) (-u)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hu.1 f u).2 hu
  have h := hu'.neg
  intro w
  calc
    B (-u) w = (-loadFunctional (n := n) (Ω := Ω) f) w := h w
    _ = -loadFunctional (n := n) (Ω := Ω) f w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (-f) w := by
      simp only [loadFunctional_apply, inner_neg_left]

/-- Difference of two weak Poisson solutions solves the difference-forcing problem. -/
theorem IsWeakPoissonSolution.sub
    {f g : DerivLp n 2 Ω}
    {u v : H¹₀(Ω)}
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω) f u)
    (hv : IsWeakPoissonSolution (n := n) (Ω := Ω) g v) :
    IsWeakPoissonSolution (n := n) (Ω := Ω) (f - g) (u - v) := by
  let B : H¹₀(Ω) →L[ℝ]
      H¹₀(Ω) →L[ℝ] ℝ :=
    dirichletForm (n := n) (Ω := Ω)
  rw [← isWeakSolution_iff_isWeakPoissonSolution
    (n := n) (Ω := Ω) hu.1 (f - g) (u - v)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (f - g)) (u - v)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hu.1 f u).2 hu
  have hv' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) g) v := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hv.1 g v).2 hv
  have h := hu'.sub hv'
  intro w
  calc
    B (u - v) w =
        (loadFunctional (n := n) (Ω := Ω) f -
          loadFunctional (n := n) (Ω := Ω) g) w := h w
    _ = loadFunctional (n := n) (Ω := Ω) f w -
          loadFunctional (n := n) (Ω := Ω) g w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (f - g) w := by
      simp only [loadFunctional_apply, inner_sub_left]

/-- Scaling a weak Poisson solution scales its forcing datum. -/
theorem IsWeakPoissonSolution.smul
    {f : DerivLp n 2 Ω}
    {u : H¹₀(Ω)} (c : ℝ)
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω) f u) :
    IsWeakPoissonSolution (n := n) (Ω := Ω) (c • f) (c • u) := by
  let B : H¹₀(Ω) →L[ℝ]
      H¹₀(Ω) →L[ℝ] ℝ :=
    dirichletForm (n := n) (Ω := Ω)
  rw [← isWeakSolution_iff_isWeakPoissonSolution
    (n := n) (Ω := Ω) hu.1 (c • f) (c • u)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (c • f)) (c • u)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hu.1 f u).2 hu
  have h := hu'.smul c
  intro w
  calc
    B (c • u) w = (c • loadFunctional (n := n) (Ω := Ω) f) w := h w
    _ = c * loadFunctional (n := n) (Ω := Ω) f w := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (c • f) w := by
      simp only [loadFunctional_apply, real_inner_smul_left]

/-- Linear combinations of weak Poisson solutions. -/
theorem IsWeakPoissonSolution.linear_combination
    {f g : DerivLp n 2 Ω}
    {u v : H¹₀(Ω)} (c₁ c₂ : ℝ)
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω) f u)
    (hv : IsWeakPoissonSolution (n := n) (Ω := Ω) g v) :
    IsWeakPoissonSolution (n := n) (Ω := Ω)
      (c₁ • f + c₂ • g) (c₁ • u + c₂ • v) := by
  let B : H¹₀(Ω) →L[ℝ]
      H¹₀(Ω) →L[ℝ] ℝ :=
    dirichletForm (n := n) (Ω := Ω)
  rw [← isWeakSolution_iff_isWeakPoissonSolution
    (n := n) (Ω := Ω) hu.1 (c₁ • f + c₂ • g) (c₁ • u + c₂ • v)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (c₁ • f + c₂ • g))
    (c₁ • u + c₂ • v)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hu.1 f u).2 hu
  have hv' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) g) v := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hv.1 g v).2 hv
  have h := hu'.linear_combination c₁ c₂ hv'
  intro w
  calc
    B (c₁ • u + c₂ • v) w =
        (c₁ • loadFunctional (n := n) (Ω := Ω) f +
          c₂ • loadFunctional (n := n) (Ω := Ω) g) w := h w
    _ = c₁ * loadFunctional (n := n) (Ω := Ω) f w +
          c₂ * loadFunctional (n := n) (Ω := Ω) g w := rfl
    _ = loadFunctional (n := n) (Ω := Ω)
          (c₁ • f + c₂ • g) w := by
      simp only [loadFunctional_apply, inner_add_left, real_inner_smul_left]

/-- Difference of weak Poisson solutions with the same forcing is homogeneous. -/
theorem IsWeakPoissonSolution.sub_same_load
    {f : DerivLp n 2 Ω}
    {u v : H¹₀(Ω)}
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω) f u)
    (hv : IsWeakPoissonSolution (n := n) (Ω := Ω) f v) :
    IsWeakPoissonSolution (n := n) (Ω := Ω) 0 (u - v) := by
  let B : H¹₀(Ω) →L[ℝ]
      H¹₀(Ω) →L[ℝ] ℝ :=
    dirichletForm (n := n) (Ω := Ω)
  rw [← isWeakSolution_iff_isWeakPoissonSolution
    (n := n) (Ω := Ω) hu.1 0 (u - v)]
  change IsWeakSolution B
    (loadFunctional (n := n) (Ω := Ω) (0 : DerivLp n 2 Ω)) (u - v)
  have hu' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) u := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hu.1 f u).2 hu
  have hv' : IsWeakSolution B
      (loadFunctional (n := n) (Ω := Ω) f) v := by
    simpa only [B] using
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hv.1 f v).2 hv
  have h := hu'.sub_same_load hv'
  intro w
  calc
    B (u - v) w = (0 : StrongDual ℝ (H¹₀(Ω))) w := h w
    _ = 0 := rfl
    _ = loadFunctional (n := n) (Ω := Ω) (0 : DerivLp n 2 Ω) w := by
      simp only [loadFunctional_apply, inner_zero_left]

/-- A field minimizes the Dirichlet energy exactly when it is a weak Poisson solution. -/
theorem dirichletEnergy.minimizer_iff_isWeakPoissonSolution
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (f : DerivLp n 2 Ω)
    {u : H¹₀(Ω)} :
    (∀ v : H¹₀(Ω),
      dirichletEnergy (n := n) (Ω := Ω) f u ≤
        dirichletEnergy (n := n) (Ω := Ω) f v) ↔
      IsWeakPoissonSolution (n := n) (Ω := Ω) f u :=
  (dirichletEnergy.minimizer_iff_weakSolution
    (n := n) (Ω := Ω) hn hΩbounded f).trans
      (isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen f u)

/-- A distributional Poisson solution is precisely the Lax–Milgram Dirichlet solver. -/
theorem IsWeakPoissonSolution.iff_eq_dirichletSolve
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (f : DerivLp n 2 Ω)
    {u : H¹₀(Ω)} :
    IsWeakPoissonSolution (n := n) (Ω := Ω) f u ↔
      u = dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f := by
  constructor
  · intro hu
    exact @IsWeakSolution.eq_solve
      (H¹₀(Ω))
      inferInstance
      (Submodule.innerProductSpace
        ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule))
      inferInstance
      (dirichletForm (n := n) (Ω := Ω))
      (dirichletForm_isCoercive (n := n) (Ω := Ω) hn hΩbounded)
      (loadFunctional (n := n) (Ω := Ω) f)
      u
      ((isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen f u).2 hu)
  · rintro rfl
    exact dirichletSolve.isWeakPoissonSolution
      (n := n) (Ω := Ω) hΩopen hn hΩbounded f

/-- A zero-forcing weak Poisson solution is exactly the zero field. -/
theorem IsWeakPoissonSolution.zero_iff
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω)
    {u : H¹₀(Ω)} :
    IsWeakPoissonSolution (n := n) (Ω := Ω) (0 : DerivLp n 2 Ω) u ↔
      u = 0 := by
  rw [IsWeakPoissonSolution.iff_eq_dirichletSolve
    (n := n) (Ω := Ω) hΩopen hn hΩbounded (0 : DerivLp n 2 Ω)]
  rw [dirichletSolve_zero (n := n) (Ω := Ω) hn hΩbounded]

/-- Additivity of the Dirichlet Poisson solution operator. -/
theorem dirichletSolve_add
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (f g : DerivLp n 2 Ω) :
    dirichletSolve (n := n) (Ω := Ω) hn hΩbounded (f + g) =
      dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f +
        dirichletSolve (n := n) (Ω := Ω) hn hΩbounded g := by
  have hweak :
      IsWeakPoissonSolution (n := n) (Ω := Ω) (f + g)
        (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f +
          dirichletSolve (n := n) (Ω := Ω) hn hΩbounded g) :=
    IsWeakPoissonSolution.add (n := n) (Ω := Ω)
      (dirichletSolve.isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen hn hΩbounded f)
      (dirichletSolve.isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen hn hΩbounded g)
  exact ((IsWeakPoissonSolution.iff_eq_dirichletSolve
    (n := n) (Ω := Ω) hΩopen hn hΩbounded (f + g)).1 hweak).symm

/-- The Dirichlet Poisson solution operator commutes with negation. -/
theorem dirichletSolve_neg
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (f : DerivLp n 2 Ω) :
    dirichletSolve (n := n) (Ω := Ω) hn hΩbounded (-f) =
      -dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f := by
  have hweak :
      IsWeakPoissonSolution (n := n) (Ω := Ω) (-f)
        (-dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f) :=
    IsWeakPoissonSolution.neg (n := n) (Ω := Ω)
      (dirichletSolve.isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen hn hΩbounded f)
  exact ((IsWeakPoissonSolution.iff_eq_dirichletSolve
    (n := n) (Ω := Ω) hΩopen hn hΩbounded (-f)).1 hweak).symm

/-- Difference form of linearity for the Dirichlet Poisson solution operator. -/
theorem dirichletSolve_sub
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (f g : DerivLp n 2 Ω) :
    dirichletSolve (n := n) (Ω := Ω) hn hΩbounded (f - g) =
      dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f -
        dirichletSolve (n := n) (Ω := Ω) hn hΩbounded g := by
  have hweak :
      IsWeakPoissonSolution (n := n) (Ω := Ω) (f - g)
        (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f -
          dirichletSolve (n := n) (Ω := Ω) hn hΩbounded g) :=
    IsWeakPoissonSolution.sub (n := n) (Ω := Ω)
      (dirichletSolve.isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen hn hΩbounded f)
      (dirichletSolve.isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen hn hΩbounded g)
  exact ((IsWeakPoissonSolution.iff_eq_dirichletSolve
    (n := n) (Ω := Ω) hΩopen hn hΩbounded (f - g)).1 hweak).symm

/-- Scalar homogeneity of the Dirichlet Poisson solution operator. -/
theorem dirichletSolve_smul
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (c : ℝ) (f : DerivLp n 2 Ω) :
    dirichletSolve (n := n) (Ω := Ω) hn hΩbounded (c • f) =
      c • dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f := by
  have hweak :
      IsWeakPoissonSolution (n := n) (Ω := Ω) (c • f)
        (c • dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f) :=
    IsWeakPoissonSolution.smul (n := n) (Ω := Ω) c
      (dirichletSolve.isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen hn hΩbounded f)
  exact ((IsWeakPoissonSolution.iff_eq_dirichletSolve
    (n := n) (Ω := Ω) hΩopen hn hΩbounded (c • f)).1 hweak).symm

/-- Linear-combination form of the Dirichlet Poisson superposition principle. -/
theorem dirichletSolve_linear_combination
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (c₁ c₂ : ℝ) (f g : DerivLp n 2 Ω) :
    dirichletSolve (n := n) (Ω := Ω) hn hΩbounded (c₁ • f + c₂ • g) =
      c₁ • dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f +
        c₂ • dirichletSolve (n := n) (Ω := Ω) hn hΩbounded g := by
  have hweak :
      IsWeakPoissonSolution (n := n) (Ω := Ω) (c₁ • f + c₂ • g)
        (c₁ • dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f +
          c₂ • dirichletSolve (n := n) (Ω := Ω) hn hΩbounded g) :=
    IsWeakPoissonSolution.linear_combination (n := n) (Ω := Ω) c₁ c₂
      (dirichletSolve.isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen hn hΩbounded f)
      (dirichletSolve.isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen hn hΩbounded g)
  exact ((IsWeakPoissonSolution.iff_eq_dirichletSolve
    (n := n) (Ω := Ω) hΩopen hn hΩbounded (c₁ • f + c₂ • g)).1 hweak).symm

/-- The weak equation tested against a compactly supported smooth function. -/
theorem dirichlet_weakSolution_equation_testFunction
    (f : DerivLp n 2 Ω) {u : H¹₀(Ω)}
    (hu :
      IsWeakSolution
        (dirichletForm (n := n) (Ω := Ω))
        (loadFunctional (n := n) (Ω := Ω) f)
        u)
    (φ : TestFunctionOn n Ω) :
    (∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i u,
          derivCoordCLM (n := n) (Ω := Ω) i
            (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ) =
      ⟪f,
        baseCoordCLM (n := n) (Ω := Ω)
          (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ :=
  dirichlet_weakSolution_equation
    (n := n) (Ω := Ω) f hu
    (testFunctionToH10 (n := n) (Ω := Ω) φ)

/-- The concrete solver satisfies the weak equation against every compactly supported smooth
test function. -/
theorem dirichletSolve_equation_testFunction
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (f : DerivLp n 2 Ω) (φ : TestFunctionOn n Ω) :
    (∑ i : Fin n,
        ⟪derivCoordCLM (n := n) (Ω := Ω) i
            (dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f),
          derivCoordCLM (n := n) (Ω := Ω) i
            (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ) =
      ⟪f,
        baseCoordCLM (n := n) (Ω := Ω)
          (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ :=
  dirichletSolve_equation
    (n := n) (Ω := Ω) hn hΩbounded f
    (testFunctionToH10 (n := n) (Ω := Ω) φ)

/-- For identity coefficients, the variable-coefficient solver is the Dirichlet solver. -/
theorem variableCoeffSolve_identity_eq_dirichletSolve
    (hΩopen : IsOpen Ω) (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω) (f : DerivLp n 2 Ω) :
    variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded
        (identityCoefficientOperator (n := n) (Ω := Ω))
        (integratedElliptic_identity (n := n) (Ω := Ω)) f =
      dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f := by
  let u := variableCoeffSolve (n := n) (Ω := Ω) hn hΩbounded
    (identityCoefficientOperator (n := n) (Ω := Ω))
    (integratedElliptic_identity (n := n) (Ω := Ω)) f
  have huVar := variableCoeffSolve_isWeakSolution
    (n := n) (Ω := Ω) hn hΩbounded
      (identityCoefficientOperator (n := n) (Ω := Ω))
      (integratedElliptic_identity (n := n) (Ω := Ω)) f
  have huDir :
      IsWeakSolution
        (dirichletForm (n := n) (Ω := Ω))
        (loadFunctional (n := n) (Ω := Ω) f) u := by
    intro v
    calc
      dirichletForm (n := n) (Ω := Ω) u v =
          variableCoeffForm (n := n) (Ω := Ω)
            (identityCoefficientOperator (n := n) (Ω := Ω)) u v :=
        (variableCoeffForm_identity (n := n) (Ω := Ω) u v).symm
      _ = loadFunctional (n := n) (Ω := Ω) f v := by
        exact huVar v
  change u = dirichletSolve (n := n) (Ω := Ω) hn hΩbounded f
  exact (IsWeakPoissonSolution.iff_eq_dirichletSolve
    (n := n) (Ω := Ω) hΩopen hn hΩbounded f).1
      ((isWeakSolution_iff_isWeakPoissonSolution
        (n := n) (Ω := Ω) hΩopen f u).1 huDir)

end GraphSpace

end SobolevSpace
