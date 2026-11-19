/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.ValidatedNonlinear
public import PDE.Elliptic.Semilinear.DirichletNemytskii
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.Subcritical.ZeroTraceL4
import PDE.Elliptic.Variational.DivergenceSolution

/-!
# Validated quadratic Dirichlet equations

For `-Δu + u² = f`, a candidate `p` leaves a residual and a quadratic correction.
The linearized operator is `-Δ + 2p`. A verified reconstruction can make this operator
coercive even when `p` changes sign. The abstract validated existence theorem then
produces a genuine weak solution near `p`.

On bounded open domains in dimensions one through three, the compact embedding
`H¹₀ → L⁴` provides the weaker topology. Hölder's inequality represents `u²` in `L²`,
so the conclusion includes integrability and the usual tested PDE equation.
All numerical bounds are hypotheses; this module does not certify a particular profile.

## Main statements

* `exists_dirichlet_quadratic_weak_solution_near`: a residual bound, a coercive linear
  reconstruction, bounds on the embedding and the reconstruction, and a scalar radius budget
  give a weak solution near an arbitrary candidate.
* `exists_dirichlet_quadratic_weak_solution_near_poisson`: a nonnegative solution `p` of the
  linear Poisson problem with the same forcing has residual `-p²`. A pointwise range bound
  controls this residual, and nonnegativity keeps the linearization at least as coercive as
  the Dirichlet form.

## Reference

T. Hou, Y. Wang, C. Yang, *Nonuniqueness of Leray–Hopf solutions to the unforced
incompressible 3D Navier–Stokes Equation*, arXiv:2509.25116, §3.1.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local instance : ENNReal.HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal 4) 2 := ⟨by
  rw [ENNReal.ofReal_ofNat]
  change ((4 : NNReal) : ℝ≥0∞)⁻¹ + ((4 : NNReal) : ℝ≥0∞)⁻¹ =
    ((2 : NNReal) : ℝ≥0∞)⁻¹
  rw [← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
    ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0), ← ENNReal.coe_add]
  norm_num⟩

/-- The compact `L⁴` inclusion used for quadratic Dirichlet equations in dimensions
one through three. Its representative agrees with the Sobolev base coordinate. -/
def dirichletL4Embedding (hn : 0 < n) (hn4 : n < 4)
    (hΩopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    H¹₀(Ω) →L[ℝ] Lp ℝ (ENNReal.ofReal 4) (domainMeasure n Ω) := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hbounded
  exact h10LpEmbedding hn hΩopen.measurableSet (q := 4) (by norm_num)
      (fun h ↦ (four_lt_sobolevExponent_of_lt_four hn4 h).le)

/-- The `L⁴` and `L²` coordinates represent the same scalar field. -/
theorem dirichletL4Embedding_ae (hn : 0 < n) (hn4 : n < 4)
    (hΩopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (u : H¹₀(Ω)) :
    (dirichletL4Embedding hn hn4 hΩopen hbounded u : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] (baseCoordCLM u : ℝ^n → ℝ) := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hbounded
  exact h10LpEmbedding_ae hn hΩopen.measurableSet (q := 4) (by norm_num)
      (fun h ↦ (four_lt_sobolevExponent_of_lt_four hn4 h).le) u

/-- The compact inclusion retains the full Sobolev field because weak derivatives
on an open domain are determined by the base coordinate. -/
theorem dirichletL4Embedding_injective (hn : 0 < n) (hn4 : n < 4)
    (hΩopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    Function.Injective (dirichletL4Embedding hn hn4 hΩopen hbounded) := by
  intro u v huv
  apply baseCoordCLM_injective hΩopen
  apply Lp.ext
  have h := (dirichletL4Embedding_ae hn hn4 hΩopen hbounded u).symm
  rw [huv] at h
  exact h.trans (dirichletL4Embedding_ae hn hn4 hΩopen hbounded v)

/-- Rellich compactness at exponent four; no boundary smoothness is needed. -/
theorem dirichletL4Embedding_isCompactOperator (hn : 0 < n) (hn4 : n < 4)
    (hΩopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    IsCompactOperator (dirichletL4Embedding hn hn4 hΩopen hbounded) := by
  exact h10LpEmbedding_isCompactOperator hn hΩopen.measurableSet hbounded
      (q := 4) (by norm_num) (four_lt_sobolevExponent_of_lt_four hn4)

/-- Products of two `L⁴` fields as loads on `H¹₀`, paired against its `L²` coordinate. -/
def dirichletProductLoad :
    Lp ℝ (ENNReal.ofReal 4) (domainMeasure n Ω) →L[ℝ]
      Lp ℝ (ENNReal.ofReal 4) (domainMeasure n Ω) →L[ℝ]
      StrongDual ℝ H¹₀(Ω) :=
  ContinuousLinearMap.productLoad (baseCoordCLM (n := n) (Ω := Ω))

/-- The coordinate inclusion has norm at most one, so the product form needs no
extra constant beyond Hölder and Cauchy--Schwarz. -/
theorem dirichletProductLoad_isBoundedBy :
    PDE.Analysis.ContinuousTrilinearForm.IsBoundedBy
      (dirichletProductLoad (n := n) (Ω := Ω)) 1 := by
  intro a b v
  calc
    ‖dirichletProductLoad a b v‖ ≤ ‖baseCoordCLM (n := n) (Ω := Ω)‖ * ‖a‖ * ‖b‖ * ‖v‖ :=
      ContinuousLinearMap.norm_productLoad_apply_le _ a b v
    _ ≤ 1 * ‖a‖ * ‖b‖ * ‖v‖ := by
      gcongr
      exact (baseCoordCLM (n := n) (Ω := Ω)).opNorm_le_bound zero_le_one
        (fun v ↦ by simpa only [one_mul] using baseCoordCLM_norm_le v)

/-- The product load is exactly the existing `L²` load functional. -/
theorem dirichletProductLoad_apply
    (a b : Lp ℝ (ENNReal.ofReal 4) (domainMeasure n Ω)) (v : H¹₀(Ω)) :
    dirichletProductLoad a b v =
      loadFunctional ((ContinuousLinearMap.mul ℝ ℝ).holder 2 a b) v :=
  rfl

section Existence

variable (hn : 0 < n) (hn4 : n < 4) (hΩopen : IsOpen Ω)
  (hbounded : Bornology.IsBounded Ω)

local notation "J₄" => dirichletL4Embedding hn hn4 hΩopen hbounded
local notation "P₂" => dirichletProductLoad (n := n) (Ω := Ω)

/-- The abstract quadratic equation is the integral weak Dirichlet equation,
including integrability of the nonlinear term against every Sobolev test. -/
theorem isDirichletSemilinearWeakSolution_iff_quadraticLoad
    (f : DerivLp n 2 Ω) (u : H¹₀(Ω)) :
    IsDirichletSemilinearWeakSolution (fun _ z ↦ z ^ 2) f u ↔
      ∀ v : H¹₀(Ω), dirichletForm u v +
        PDE.Analysis.Variational.quadraticLoad J₄ P₂ u v = loadFunctional f v := by
  let N : H¹₀(Ω) → DerivLp n 2 Ω :=
    fun u ↦ (ContinuousLinearMap.mul ℝ ℝ).holder 2 (J₄ u) (J₄ u)
  have hNrep (u : H¹₀(Ω)) :
      (N u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ (baseCoordCLM u x) ^ 2 := by
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (J₄ u) (J₄ u),
      dirichletL4Embedding_ae hn hn4 hΩopen hbounded u] with x hmul hcoord
    simpa only [N, ContinuousLinearMap.mul_apply', hcoord, pow_two] using hmul
  exact isDirichletSemilinearWeakSolution_iff_nemytskii_load (n := n) (Ω := Ω)
    (fun _ z ↦ z ^ 2) N hNrep f u

/-- A nonnegative candidate adds a nonnegative term to the Dirichlet energy:
the linearized quadratic load pairs as `2 ∫ p u²`. Positivity is only required
almost everywhere, so the statement is independent of representative choices. -/
theorem dirichlet_quadraticLinearization_self_nonneg
    (p u : H¹₀(Ω)) (hp : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM p x) :
    0 ≤ PDE.Analysis.Variational.quadraticLinearization J₄ P₂ p u u := by
  have hpair (a b : Lp ℝ (ENNReal.ofReal 4) (domainMeasure n Ω))
      (hab : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ a x * b x * baseCoordCLM u x) :
      0 ≤ P₂ a b u := by
    rw [dirichletProductLoad_apply, loadFunctional_apply, L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) a b,
      hab] with x hmul hx
    simpa only [Pi.zero_apply, Real.inner_apply, hmul,
      ContinuousLinearMap.mul_apply'] using hx
  change 0 ≤ P₂ (J₄ p) (J₄ u) u + P₂ (J₄ u) (J₄ p) u
  apply add_nonneg
  · apply hpair
    filter_upwards [hp, dirichletL4Embedding_ae hn hn4 hΩopen hbounded p,
      dirichletL4Embedding_ae hn hn4 hΩopen hbounded u] with x hx hp' hu'
    simpa only [hp', hu', pow_two, mul_assoc] using
      mul_nonneg hx (sq_nonneg (baseCoordCLM u x))
  · apply hpair
    filter_upwards [hp, dirichletL4Embedding_ae hn hn4 hΩopen hbounded p,
      dirichletL4Embedding_ae hn hn4 hΩopen hbounded u] with x hx hp' hu'
    rw [hp', hu', mul_comm (baseCoordCLM u x) (baseCoordCLM p x), mul_assoc]
    exact mul_nonneg hx (mul_self_nonneg _)

/-- A pointwise range certificate bounds the quadratic load in the dual energy norm.
The square belongs to `L²` by Hölder; its uniform bound contributes `M²`, and
the domain's measure contributes its square root. -/
theorem norm_dirichlet_quadraticLoad_le_of_ae_bound
    (p : H¹₀(Ω)) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ᵐ x ∂domainMeasure n Ω, ‖baseCoordCLM p x‖ ≤ M) :
    ‖PDE.Analysis.Variational.quadraticLoad J₄ P₂ p‖ ≤
      (volume Ω).toReal ^ (1 / 2 : ℝ) * M ^ 2 := by
  have : IsFiniteMeasure (domainMeasure n Ω) :=
    isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let w := (ContinuousLinearMap.mul ℝ ℝ).holder 2 (J₄ p) (J₄ p)
  have hw : ∀ᵐ x ∂domainMeasure n Ω, ‖w x‖ ≤ M ^ 2 := by
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (J₄ p) (J₄ p),
      dirichletL4Embedding_ae hn hn4 hΩopen hbounded p, hp] with x hmul hcoord hx
    change ‖(ContinuousLinearMap.mul ℝ ℝ).holder 2 (J₄ p) (J₄ p) x‖ ≤ _
    rw [hmul, ContinuousLinearMap.mul_apply', hcoord, norm_mul, ← pow_two]
    exact (sq_le_sq₀ (norm_nonneg _) hM).mpr hx
  have hnorm := Lp.norm_le_of_ae_bound (sq_nonneg M) hw
  change ‖loadFunctional w‖ ≤ _
  apply (norm_loadFunctional_le w).trans
  simpa only [measureUnivNNReal, domainMeasure, Measure.restrict_apply_univ,
    NNReal.coe_rpow, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofNat,
    one_div] using hnorm

/-- A verified residual and linear reconstruction give a genuine weak solution of
`-Δu + u² = f` near an arbitrary candidate. The radius is in the full `H¹₀` norm.
The reconstruction may be obtained from finite-rank correction; no positivity of the
candidate and no contraction estimate are assumed. -/
theorem exists_dirichlet_quadratic_weak_solution_near
    (p : H¹₀(Ω)) (f : DerivLp n 2 Ω)
    (B : H¹₀(Ω) →L[ℝ] StrongDual ℝ H¹₀(Ω)) (R : H¹₀(Ω) →L[ℝ] H¹₀(Ω))
    (hfactor : B = (dirichletForm +
      PDE.Analysis.Variational.quadraticLinearization J₄ P₂ p).comp R)
    {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r)
    (hcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    {g γ s : NNReal} (hembedding : ‖J₄‖ ≤ s) (hR : ‖R‖ ≤ g)
    (hRweak : ∀ u, ‖J₄ (R u)‖ ≤ γ * ‖J₄ u‖)
    {β : ℝ} (hresidual : ‖loadFunctional f - dirichletForm p -
      PDE.Analysis.Variational.quadraticLoad J₄ P₂ p‖ ≤ β)
    (hbudget : β + s ^ 2 * (g * r) ^ 2 ≤ c * r) :
    ∃ u : H¹₀(Ω), ‖u - p‖ ≤ g * r ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ z ^ 2) f u := by
  obtain ⟨u, hu, heq⟩ := PDE.Analysis.Variational.exists_solution_near_quadratic
    (V := H¹₀(Ω)) (W := Lp ℝ (ENNReal.ofReal 4) (domainMeasure n Ω))
    (dirichletForm (n := n) (Ω := Ω)) J₄
    (dirichletL4Embedding_injective hn hn4 hΩopen hbounded)
    (dirichletL4Embedding_isCompactOperator hn hn4 hΩopen hbounded)
    P₂ (k := 1) dirichletProductLoad_isBoundedBy hembedding p (loadFunctional f)
    B R hfactor hc hr hcoercive hR hRweak hresidual (by simpa only [NNReal.coe_one, one_mul]
      using hbudget)
  exact ⟨u, hu, (isDirichletSemilinearWeakSolution_iff_quadraticLoad
    hn hn4 hΩopen hbounded f u).mpr heq⟩

/-- A nonnegative solution of the linear Poisson problem is a candidate for the
quadratic equation with the same forcing. Its genuine residual is `-p²`.
A range certificate and an energy-radius inequality suffice for validation;
all constants remain explicit so a sharper certificate can reuse the proof. -/
theorem exists_dirichlet_quadratic_weak_solution_near_poisson
    (p : H¹₀(Ω)) (f : DerivLp n 2 Ω)
    (hlinear : dirichletForm p = loadFunctional f)
    (hp : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM p x)
    {M c r : ℝ} (hM : 0 ≤ M) (hc : 0 < c) (hr : 0 ≤ r)
    (hbound : ∀ᵐ x ∂domainMeasure n Ω, ‖baseCoordCLM p x‖ ≤ M)
    (hcoercive : ∀ u : H¹₀(Ω), c * ‖u‖ * ‖u‖ ≤ dirichletForm u u)
    {s : NNReal} (hembedding : ‖J₄‖ ≤ s)
    (hbudget : (volume Ω).toReal ^ (1 / 2 : ℝ) * M ^ 2 + s ^ 2 * r ^ 2 ≤ c * r) :
    ∃ u : H¹₀(Ω), ‖u - p‖ ≤ r ∧
      IsDirichletSemilinearWeakSolution (fun _ z ↦ z ^ 2) f u := by
  let B := dirichletForm + PDE.Analysis.Variational.quadraticLinearization J₄ P₂ p
  have hB (u : H¹₀(Ω)) : c * ‖u‖ * ‖u‖ ≤ B u u := by
    exact (hcoercive u).trans (le_add_of_nonneg_right
      (dirichlet_quadraticLinearization_self_nonneg hn hn4 hΩopen hbounded p u hp))
  have hresidual : ‖loadFunctional f - dirichletForm p -
      PDE.Analysis.Variational.quadraticLoad J₄ P₂ p‖ ≤
      (volume Ω).toReal ^ (1 / 2 : ℝ) * M ^ 2 := by
    rw [hlinear, sub_self, zero_sub, norm_neg]
    exact norm_dirichlet_quadraticLoad_le_of_ae_bound hn hn4 hΩopen hbounded p hM hbound
  simpa only [NNReal.coe_one, one_mul] using
    exists_dirichlet_quadratic_weak_solution_near hn hn4 hΩopen hbounded p f B
      (ContinuousLinearMap.id ℝ H¹₀(Ω)) (by simp only [B, ContinuousLinearMap.comp_id])
      hc hr hB (g := 1) (γ := 1) hembedding ContinuousLinearMap.norm_id_le
      (fun _ ↦ by simp only [ContinuousLinearMap.id_apply, NNReal.coe_one, one_mul, le_refl])
      hresidual (by simpa only [NNReal.coe_one, one_mul] using hbudget)

end Existence

end SobolevSpace.GraphSpace
