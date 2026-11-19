/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphLinearization
public import PDE.Analysis.Variational.LaxMilgram.Subspace

/-!
# Solving the self-similar linearization in its graph domain

Let `T` be a `DilationTestSpace` with closed span `E`, `b` a coefficient with components in
`L∞`, `K : E → E*` bounded and `μ` real. `existsUnique_graph_solution`: if
`κ ‖φ‖²_{H¹} ≤ ⟨(L_b + K + μ J) φ, φ⟩` on the test fields, where `J` is the `L²` pairing, then
for every `f ∈ E*` there is exactly one `h` in the graph domain with `L_b h + K h + μ J h = f`,
and `‖h‖_{H¹} ≤ κ⁻¹ ‖f‖`.

Uniqueness is `eq_of_linearization_add_eq`. For existence, Lax–Milgram
(`PDE.Analysis.Variational.exists_forall_eq_of_coercive_subspace`, built on Mathlib's
`IsCoercive.continuousLinearEquivOfBilin`) is applied on the ball spaces, where the drift is bounded
and agrees with the graph-domain drift; the solutions are bounded by `κ⁻¹ ‖f‖`, and a weak limit
satisfies every tested equation, which places it in the graph domain. This is the increasing-ball
construction of Hou, Wang and Yang, Section 4.3, for the linear problem.
`existsUnique_graph_solution_of_weighted` is the same statement for the energy norm
`‖∇h‖² + c ‖h‖²`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, Lax–Milgram for
  (4.26), p. 29, and the weak limit of (4.37) as `R → ∞`, p. 31.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Selfsimilar

open Stationary
open PDE.Analysis.Evolution (restrictForm restrictForm_apply)

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

namespace DilationTestSpace

variable (T : DilationTestSpace n)

/-- The operator `B + K + μ J` of the shifted linearization without its drift term. -/
def shiftedBoundedPart (b : Fin n → DerivLp n ∞ univ) (K : T.space →L[ℝ] StrongDual ℝ T.space)
    (μ : ℝ) : T.space →L[ℝ] StrongDual ℝ T.space :=
  restrictForm T.space (boundedPart b) + K + μ • T.l2Form

theorem shiftedBoundedPart_apply (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) (μ : ℝ) (v w : T.space) :
    T.shiftedBoundedPart b K μ v w = boundedPart b (v : H) (w : H) + K v w + μ * T.l2Form v w :=
  rfl

theorem linearization_add_apply (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) (μ : ℝ) (h : T.graphDomain) (w : T.space) :
    (T.linearization b h + K h + μ • T.l2Form h) w =
      T.shiftedBoundedPart b K μ h w - (1 / 2) * T.dilationDrift h w := by
  simp only [shiftedBoundedPart_apply, add_apply, linearization_apply, sub_apply, smul_apply,
    smul_eq_mul, restrictForm_apply]
  ring

/-- The shifted linearization on a ball space, where the drift is bounded. -/
def ballForm (b : Fin n → DerivLp n ∞ univ) (K : T.space →L[ℝ] StrongDual ℝ T.space) (μ : ℝ)
    (R : ℝ) : T.ballSpace R →L[ℝ] T.ballSpace R →L[ℝ] ℝ :=
  (T.shiftedBoundedPart b K μ - (1 / 2 : ℝ) • restrictForm T.space (cutoffDrift R)).bilinearComp
    (T.ballSpace R).subtypeL (T.ballSpace R).subtypeL

theorem ballForm_apply (b : Fin n → DerivLp n ∞ univ) (K : T.space →L[ℝ] StrongDual ℝ T.space)
    (μ : ℝ) (R : ℝ) (v w : T.ballSpace R) :
    T.ballForm b K μ R v w = T.shiftedBoundedPart b K μ v w -
      (1 / 2) * cutoffDrift R ((v : T.space) : H) ((w : T.space) : H) := by
  simp only [ballForm, ContinuousLinearMap.bilinearComp_apply, sub_apply, smul_apply,
    smul_eq_mul, Submodule.subtypeL_apply, restrictForm_apply]

/-- On a ball space the shifted linearization is the ball form. -/
theorem ballForm_eq (b : Fin n → DerivLp n ∞ univ) (K : T.space →L[ℝ] StrongDual ℝ T.space)
    (μ : ℝ) (R : ℝ) (v w : T.ballSpace R) :
    T.ballForm b K μ R v w = (T.linearization b ⟨v, T.mem_graphDomain_of_mem_ballSpace v.2⟩ +
      K v + μ • T.l2Form v) w := by
  rw [ballForm_apply, linearization_add_apply,
    T.dilationDrift_of_mem_ballSpace ⟨v, T.mem_graphDomain_of_mem_ballSpace v.2⟩ v.2,
    restrictForm_apply]

/-- Coercivity on the test fields gives coercivity of the ball forms. -/
theorem coercive_ballForm (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) {κ μ : ℝ}
    (hcoer : ∀ φ, κ * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    (R : ℝ) (v : T.ballSpace R) : κ * ‖v‖ ^ 2 ≤ T.ballForm b K μ R v v := by
  rw [ballForm_eq, ← Submodule.norm_coe]
  exact T.coercive_graphDomain b K hcoer ⟨v, T.mem_graphDomain_of_mem_ballSpace v.2⟩

/-- The shifted linearization tested against one test field, as a functional of the unknown. -/
def testedOperator (b : Fin n → DerivLp n ∞ univ) (K : T.space →L[ℝ] StrongDual ℝ T.space)
    (μ : ℝ) (φ : T.carrier) : StrongDual ℝ T.space :=
  (T.shiftedBoundedPart b K μ).flip (T.point φ) -
    (1 / 2 : ℝ) • (T.driftAt φ).comp T.space.subtypeL

theorem testedOperator_apply (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) (μ : ℝ) (φ : T.carrier) (v : T.space) :
    T.testedOperator b K μ φ v =
      T.shiftedBoundedPart b K μ v (T.point φ) - (1 / 2) * T.driftAt φ (v : H) := by
  simp only [testedOperator, sub_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

/-- Lax–Milgram on the ball spaces. -/
theorem exists_ballForm_eq (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) {κ μ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ φ, κ * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    (f : StrongDual ℝ T.space) (R : ℝ) :
    ∃ u : T.ballSpace R, (∀ w, T.ballForm b K μ R u w = f w) ∧ ‖u‖ ≤ κ⁻¹ * ‖f‖ :=
  PDE.Analysis.Variational.exists_forall_eq_of_coercive_subspace (T.ballSpace R)
    (T.ballForm b K μ R) hκ (T.coercive_ballForm b K hcoer R) f

/-- The weak limit of the ball solutions satisfies every tested equation. -/
theorem exists_testedOperator_eq (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) {κ μ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ φ, κ * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    (f : StrongDual ℝ T.space) :
    ∃ h₀ : T.space, ‖h₀‖ ≤ κ⁻¹ * ‖f‖ ∧ ∀ φ, T.testedOperator b K μ φ h₀ = f (T.point φ) := by
  choose u hu hunorm using fun R : ℕ ↦ T.exists_ballForm_eq b K hκ hcoer f R
  have hlinear : ∀ φ, ∀ᶠ R : ℕ in atTop,
      T.testedOperator b K μ φ (u R) + 0 = f (T.point φ) := by
    intro φ
    filter_upwards [T.eventually_point_mem_ballSpace φ] with R hR
    rw [add_zero, testedOperator_apply, ← T.cutoffDrift_toH1 (u R).2 φ]
    have h := hu R ⟨T.point φ, hR⟩
    rwa [ballForm_apply] at h
  have hbounded : Bornology.IsBounded (range fun R : ℕ ↦ (u R : T.space)) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨κ⁻¹ * ‖f‖, ?_⟩
    rintro _ ⟨R, rfl⟩
    rw [Submodule.norm_coe]
    exact hunorm R
  obtain ⟨h₀, hh₀norm, -, -, hh₀⟩ := PDE.Analysis.Variational.exists_solution_of_eventually_eq
    (M := T.space) (D := ℝ) (C := ℝ) (Y := ℝ) (J := Empty)
    atTop (fun R : ℕ ↦ (u R : T.space)) hbounded (ContinuousLinearMap.id ℝ T.space) 0
    (κ⁻¹ * ‖f‖) 0 (Eventually.of_forall fun R ↦ by
      rw [ContinuousLinearMap.id_apply, Submodule.norm_coe]; exact hunorm R)
    (Eventually.of_forall fun _ ↦ by rw [zero_apply, norm_zero]) (fun j ↦ j.elim)
    (Eventually.of_forall fun _ j ↦ j.elim) (T.testedOperator b K μ) (fun _ ↦ 0)
    (fun _ ↦ isCompactOperator_zero) (fun _ _ ↦ 0) (fun _ ↦ continuous_const)
    (fun φ ↦ f (T.point φ)) hlinear
  refine ⟨h₀, hh₀norm, fun φ ↦ ?_⟩
  have h := hh₀ φ
  simp only [add_zero] at h
  exact h

/-- A field satisfying every tested equation lies in the graph domain. -/
theorem mem_graphDomain_of_testedOperator_eq (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) (μ : ℝ) (f : StrongDual ℝ T.space)
    {h₀ : T.space} (hh₀ : ∀ φ, T.testedOperator b K μ φ h₀ = f (T.point φ)) :
    h₀ ∈ T.graphDomain := by
  refine ⟨(2 : ℝ) • (T.shiftedBoundedPart b K μ h₀ - f), fun φ ↦ ?_⟩
  rw [smul_apply, sub_apply, smul_eq_mul, ← hh₀ φ, testedOperator_apply]
  ring

/-- A field of the graph domain satisfying every tested equation solves the equation. -/
theorem linearization_eq_of_testedOperator_eq (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) (μ : ℝ) (f : StrongDual ℝ T.space)
    (h : T.graphDomain) (hh : ∀ φ, T.testedOperator b K μ φ h = f (T.point φ)) :
    T.linearization b h + K h + μ • T.l2Form h = f := by
  refine T.ext_point fun φ ↦ ?_
  rw [← hh φ, testedOperator_apply, linearization_add_apply, dilationDrift_point]

end DilationTestSpace

/-- **Existence and uniqueness in the graph domain.** Let `E` be the closed span of a
dilation-invariant space of test fields, `b` a coefficient with components in `L∞`,
`K : E → E*` bounded and `μ` real. If `L_b + K + μ J` is coercive with constant `κ > 0` on the
test fields, where `L_b` is the weak linearization and `J` the `L²` pairing, then for every
`f ∈ E*` there is exactly one `h` in the graph domain with `L_b h + K h + μ J h = f` and
`‖h‖ ≤ κ⁻¹ ‖f‖`; uniqueness holds among all solutions in the graph domain, without the norm
bound (`DilationTestSpace.eq_of_linearization_add_eq`). The solution is the weak limit of
Lax–Milgram solutions on the ball spaces of growing radius, on which the drift is bounded.

The hypotheses are weaker than a `W^{1,∞}`, divergence-free profile acting on an invariant
closed subspace. Only `b ∈ L∞` is used, because the weak form moves the derivative of the
coefficient onto the unknown and the test field, and coercivity is assumed. The space is the
closed span of its test fields, since the drift functional is defined through its values on a
dense family of tests and the dilation identity needs that family to be dilation invariant.
For bounded coefficients the graph domain is the domain of the drift and does not depend on
`b`. Coercivity is assumed only on the test fields and extends to the graph domain, and `μ` is
any real number. -/
theorem existsUnique_graph_solution (T : DilationTestSpace n)
    (b : Fin n → DerivLp n ∞ univ) (K : T.space →L[ℝ] StrongDual ℝ T.space) {κ : ℝ}
    (hκ : 0 < κ) (μ : ℝ)
    (hcoer : ∀ φ, κ * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    (f : StrongDual ℝ T.space) :
    ∃! h : T.graphDomain, T.linearization b h + K h + μ • T.l2Form h = f ∧
      ‖(h : T.space)‖ ≤ κ⁻¹ * ‖f‖ := by
  obtain ⟨h₀, hnorm, hh₀⟩ := T.exists_testedOperator_eq b K hκ hcoer f
  have hmem := T.mem_graphDomain_of_testedOperator_eq b K μ f hh₀
  have heq := T.linearization_eq_of_testedOperator_eq b K μ f ⟨h₀, hmem⟩ hh₀
  exact ⟨⟨h₀, hmem⟩, ⟨heq, hnorm⟩, fun h' ⟨heq', _⟩ ↦
    T.eq_of_linearization_add_eq b K hκ hcoer (heq'.trans heq.symm)⟩

/-- The weighted form of `existsUnique_graph_solution`: coercivity on the test fields in the
energy norm `‖∇h‖² + c ‖h‖²`, `c > 0`, gives a unique solution in the graph domain for every
`f ∈ E*`, with `κ (‖∇h‖² + c ‖h‖²) ≤ f h`. Uniqueness holds without the bound
(`DilationTestSpace.eq_of_linearization_add_eq`). -/
theorem existsUnique_graph_solution_of_weighted (T : DilationTestSpace n)
    (b : Fin n → DerivLp n ∞ univ) (K : T.space →L[ℝ] StrongDual ℝ T.space) {κ c : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (μ : ℝ)
    (hcoer : ∀ φ, κ * (‖gradientCLM (T.toH1 φ)‖ ^ 2 + c * ‖massCLM (T.toH1 φ)‖ ^ 2) ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    (f : StrongDual ℝ T.space) :
    ∃! h : T.graphDomain, T.linearization b h + K h + μ • T.l2Form h = f ∧
      κ * (‖gradientCLM ((h : T.space) : H)‖ ^ 2 + c * ‖massCLM ((h : T.space) : H)‖ ^ 2) ≤
        f h := by
  have hκ' : 0 < κ * min 1 c := mul_pos hκ (lt_min one_pos hc)
  have hcoer' : ∀ φ, κ * min 1 c * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ))
        (T.point φ) := fun φ ↦ (T.mul_min_mul_norm_sq_le hκ.le c (T.point φ)).trans (hcoer φ)
  obtain ⟨h, ⟨heq, -⟩, -⟩ := existsUnique_graph_solution T b K hκ' μ hcoer' f
  refine ⟨h, ⟨heq, ?_⟩, fun h' ⟨heq', _⟩ ↦
    T.eq_of_linearization_add_eq b K hκ' hcoer' (heq'.trans heq.symm)⟩
  have hle := T.le_linearization_apply_self b K (T.continuous_weightedEnergy κ c) hcoer h
  rwa [heq] at hle

end NavierStokes.Selfsimilar
