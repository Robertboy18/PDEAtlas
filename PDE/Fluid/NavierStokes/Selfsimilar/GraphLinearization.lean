/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphDomain

/-!
# The weak self-similar linearization on its graph domain

For a coefficient `b` with components in `L∞`, the weak linearization in the coercive sign
convention, the negative of the operator (1.9) of Hou, Wang and Yang, is

`⟨L_b h, φ⟩ = -½ ∫ h·φ - ½ ∫ (x·∇h)·φ + ∫ ∇h : ∇φ + Σᵢⱼ ∫ (bⱼ ∂ⱼhᵢ φᵢ - bᵢ ∂ⱼhⱼ φᵢ - bᵢ hⱼ ∂ⱼφᵢ)`,

the weak form of `-½ h - ½ x·∇h + (b·∇)h + (h·∇)b - Δh` for a `C¹` coefficient `b` with
bounded derivative. The derivative of `b` is moved onto `h` and `φ`, so only `b ∈ L∞` enters.
`linearization` realizes `L_b` on the graph domain of a `DilationTestSpace`, with values in the
dual of the closed span `E`; all terms except the drift form the bounded part `boundedPart b`.

By the dilation identity the drift contributes `(n/4) ‖h‖²_{L²}` to `⟨L_b h, h⟩`
(`linearization_add_apply_self`), so for bounded `K : E → E*` and real `μ` the quadratic form of
`L_b + K + μ J` on the graph domain, `J` the `L²` pairing, is the restriction of a continuous
quadratic form on `E`. A lower bound on the test fields therefore holds on the whole graph domain
(`le_linearization_apply_self`), and coercivity on the test fields gives uniqueness
(`eq_of_linearization_add_eq`).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 1.3, (1.9), p. 3.
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

/-! ### The weak linearization -/

/-- The gradient pairing `(u, v) ↦ Σᵢⱼ ∫ ∂ⱼuᵢ ∂ⱼvᵢ` on vector `H¹`. -/
def gradientForm : H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp gradientCLM gradientCLM

/-- The convection terms of the linearization in weak form, for a coefficient `b` with
components in `L∞`: `(v, w) ↦ Σᵢⱼ ∫ (bⱼ ∂ⱼvᵢ wᵢ - bᵢ ∂ⱼvⱼ wᵢ - bᵢ vⱼ ∂ⱼwᵢ)`. For a `C¹`
coefficient `b` with bounded derivative this is `∫ ((b·∇)v + (v·∇)b)·w`; the derivative of `b`
is moved onto `v` and `w`. -/
def convectionForm (b : Fin n → DerivLp n ∞ univ) : H →L[ℝ] H →L[ℝ] ℝ :=
  ∑ i, ∑ j,
    ((innerSL ℝ).bilinearComp
        ((mulLpLeft (b j)).comp ((wkpCoordinateCLM (singleDerivIndex n j)).comp
          (PiLp.proj 2 (fun _ : Fin n ↦ H¹(ℝ^n)) i)))
      (wkpBaseCoordinateCLM.comp (PiLp.proj 2 (fun _ : Fin n ↦ H¹(ℝ^n)) i)) -
    (innerSL ℝ).bilinearComp
        ((mulLpLeft (b i)).comp ((wkpCoordinateCLM (singleDerivIndex n j)).comp
          (PiLp.proj 2 (fun _ : Fin n ↦ H¹(ℝ^n)) j)))
      (wkpBaseCoordinateCLM.comp (PiLp.proj 2 (fun _ : Fin n ↦ H¹(ℝ^n)) i)) -
    (innerSL ℝ).bilinearComp ((mulLpLeft (b i)).comp
        (wkpBaseCoordinateCLM.comp (PiLp.proj 2 (fun _ : Fin n ↦ H¹(ℝ^n)) j)))
      ((wkpCoordinateCLM (singleDerivIndex n j)).comp (PiLp.proj 2 (fun _ : Fin n ↦ H¹(ℝ^n)) i)))

/-- The bounded part of the weak linearization:
`-½ ∫ v·w + ∫ ∇v : ∇w + (convection terms)`. -/
def boundedPart (b : Fin n → DerivLp n ∞ univ) : H →L[ℝ] H →L[ℝ] ℝ :=
  -(1 / 2 : ℝ) • massForm + gradientForm + convectionForm b

theorem gradientForm_apply (v w : H) :
    gradientForm v w = ∑ i, ∑ j, inner ℝ (wkpCoordinateCLM (singleDerivIndex n j) (v i))
      (wkpCoordinateCLM (singleDerivIndex n j) (w i)) := by
  simp only [gradientForm, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    PiLp.inner_apply]
  rfl

theorem gradientForm_self (v : H) : gradientForm v v = ‖gradientCLM v‖ ^ 2 := by
  rw [gradientForm, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply,
    real_inner_self_eq_norm_sq]

theorem convectionForm_apply (b : Fin n → DerivLp n ∞ univ) (v w : H) :
    convectionForm b v w = ∑ i, ∑ j,
      (inner ℝ (mulLpLeft (b j) (wkpCoordinateCLM (singleDerivIndex n j) (v i)))
          (wkpBaseCoordinateCLM (w i)) -
        inner ℝ (mulLpLeft (b i) (wkpCoordinateCLM (singleDerivIndex n j) (v j)))
          (wkpBaseCoordinateCLM (w i)) -
        inner ℝ (mulLpLeft (b i) (wkpBaseCoordinateCLM (v j)))
          (wkpCoordinateCLM (singleDerivIndex n j) (w i))) := by
  simp only [convectionForm, sum_apply, sub_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, PiLp.proj_apply]

theorem boundedPart_apply (b : Fin n → DerivLp n ∞ univ) (v w : H) :
    boundedPart b v w = -(1 / 2) * massPairing v w + gradientForm v w + convectionForm b v w := by
  simp only [boundedPart, add_apply, smul_apply, smul_eq_mul, massForm_apply]

namespace DilationTestSpace

variable (T : DilationTestSpace n)

/-- The `L²` pairing on the closed span of the test fields. -/
def l2Form : T.space →L[ℝ] StrongDual ℝ T.space :=
  restrictForm T.space massForm

theorem l2Form_apply (u v : T.space) : T.l2Form u v = massPairing (u : H) (v : H) :=
  massForm_apply _ _

/-- The weak self-similar linearization with coefficient `b` on the graph domain, in the
coercive sign convention: `L h = -½ h - ½ x·∇h + (b·∇)h + (h·∇)b - Δh`, tested against the
closed span of the test fields. -/
def linearization (b : Fin n → DerivLp n ∞ univ) : T.graphDomain →ₗ[ℝ] StrongDual ℝ T.space :=
  (restrictForm T.space (boundedPart b)).toLinearMap ∘ₗ T.graphDomain.subtype -
    (1 / 2 : ℝ) • T.dilationDrift

theorem linearization_apply (b : Fin n → DerivLp n ∞ univ) (h : T.graphDomain) :
    T.linearization b h =
      restrictForm T.space (boundedPart b) h - (1 / 2 : ℝ) • T.dilationDrift h :=
  rfl

/-- The tested linearization: against a test field the drift is `-½ ∫ (x·∇h)·φ`. -/
theorem linearization_point (b : Fin n → DerivLp n ∞ univ) (h : T.graphDomain)
    (φ : T.carrier) :
    T.linearization b h (T.point φ) =
      boundedPart b ((h : T.space) : H) (T.toH1 φ) -
        (1 / 2) * T.driftAt φ ((h : T.space) : H) := by
  rw [linearization_apply, sub_apply, smul_apply, dilationDrift_point, smul_eq_mul]
  rfl

/-- The energy identity on the graph domain: the drift contributes `(n/4) ‖h‖²_{L²}`. -/
theorem linearization_add_apply_self (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) (μ : ℝ) (h : T.graphDomain) :
    (T.linearization b h + K h + μ • T.l2Form h) h =
      restrictForm T.space (boundedPart b) h h + K h h + (μ + n / 4) * T.l2Form h h := by
  have hD := T.dilationDrift_self h
  rw [← l2Form_apply] at hD
  simp only [add_apply, linearization_apply, sub_apply, smul_apply, smul_eq_mul]
  rw [hD]
  ring

/-- A continuous lower bound of the energy on the test fields holds on the whole closed span. -/
theorem le_energy_of_forall_point (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) {μ : ℝ} {N : T.space → ℝ} (hN : Continuous N)
    (hcoer : ∀ φ, N (T.point φ) ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    (v : T.space) :
    N v ≤ restrictForm T.space (boundedPart b) v v + K v v + (μ + n / 4) * T.l2Form v v := by
  refine T.denseRange_point.induction_on v (isClosed_le hN ?_) fun φ ↦ ?_
  · exact (((restrictForm T.space (boundedPart b)).continuous.clm_apply continuous_id).add
      (K.continuous.clm_apply continuous_id)).add
      (continuous_const.mul (T.l2Form.continuous.clm_apply continuous_id))
  · have h := hcoer φ
    rwa [← coe_graphPoint, linearization_add_apply_self] at h

/-- A continuous lower bound of the energy on the test fields holds on the graph domain. -/
theorem le_linearization_apply_self (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) {μ : ℝ} {N : T.space → ℝ} (hN : Continuous N)
    (hcoer : ∀ φ, N (T.point φ) ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    (h : T.graphDomain) : N h ≤ (T.linearization b h + K h + μ • T.l2Form h) h := by
  rw [linearization_add_apply_self]
  exact T.le_energy_of_forall_point b K hN hcoer h

/-- Coercivity on the test fields gives coercivity on the graph domain. -/
theorem coercive_graphDomain (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) {κ μ : ℝ}
    (hcoer : ∀ φ, κ * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    (h : T.graphDomain) :
    κ * ‖(h : T.space)‖ ^ 2 ≤ (T.linearization b h + K h + μ • T.l2Form h) h :=
  T.le_linearization_apply_self b K (continuous_const.mul (continuous_norm.pow 2)) hcoer h

/-- Uniqueness: a field of the graph domain annihilated by a coercive shifted linearization
vanishes. -/
theorem eq_zero_of_linearization_eq_zero (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) {κ μ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ φ, κ * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    {h : T.graphDomain} (hh : T.linearization b h + K h + μ • T.l2Form h = 0) : h = 0 := by
  have h1 := T.coercive_graphDomain b K hcoer h
  rw [hh, zero_apply] at h1
  have hsq : ‖(h : T.space)‖ ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h1 hκ) (sq_nonneg _)
  exact Submodule.coe_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))

/-- Uniqueness in the graph domain. -/
theorem eq_of_linearization_add_eq (b : Fin n → DerivLp n ∞ univ)
    (K : T.space →L[ℝ] StrongDual ℝ T.space) {κ μ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ φ, κ * ‖T.point φ‖ ^ 2 ≤
      (T.linearization b (T.graphPoint φ) + K (T.point φ) + μ • T.l2Form (T.point φ)) (T.point φ))
    {h₁ h₂ : T.graphDomain}
    (h : T.linearization b h₁ + K h₁ + μ • T.l2Form h₁ =
      T.linearization b h₂ + K h₂ + μ • T.l2Form h₂) : h₁ = h₂ := by
  have e1 : T.linearization b (h₁ - h₂) = T.linearization b h₁ - T.linearization b h₂ :=
    (T.linearization b).map_sub h₁ h₂
  have e2 : ((h₁ - h₂ : T.graphDomain) : T.space) = (h₁ : T.space) - h₂ :=
    Submodule.coe_sub _ h₁ h₂
  have e3 : K ((h₁ : T.space) - h₂) = K h₁ - K h₂ := K.map_sub _ _
  have e4 : T.l2Form ((h₁ : T.space) - h₂) = T.l2Form h₁ - T.l2Form h₂ := T.l2Form.map_sub _ _
  have h0 : T.linearization b (h₁ - h₂) + K ((h₁ - h₂ : T.graphDomain) : T.space) +
      μ • T.l2Form ((h₁ - h₂ : T.graphDomain) : T.space) = 0 := by
    rw [e1, e2, e3, e4, smul_sub, sub_add_sub_comm, sub_add_sub_comm, h, sub_self]
  exact sub_eq_zero.mp (T.eq_zero_of_linearization_eq_zero b K hκ hcoer h0)

theorem continuous_weightedEnergy (κ c : ℝ) :
    Continuous fun v : T.space ↦ κ * (‖gradientCLM (v : H)‖ ^ 2 + c * ‖massCLM (v : H)‖ ^ 2) :=
  continuous_const.mul (((gradientCLM.continuous.comp continuous_subtype_val).norm.pow 2).add
    (continuous_const.mul ((massCLM.continuous.comp continuous_subtype_val).norm.pow 2)))

/-- The energy norm `‖∇v‖² + c ‖v‖²` dominates `min 1 c` times the squared `H¹` norm. -/
theorem mul_min_mul_norm_sq_le {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) (v : T.space) :
    κ * min 1 c * ‖v‖ ^ 2 ≤ κ * (‖gradientCLM (v : H)‖ ^ 2 + c * ‖massCLM (v : H)‖ ^ 2) := by
  have hsq : ‖v‖ ^ 2 = ‖massCLM (v : H)‖ ^ 2 + ‖gradientCLM (v : H)‖ ^ 2 := by
    rw [← Submodule.norm_coe, norm_sq_eq_mass_add_gradient]
  have hm := sq_nonneg ‖massCLM (v : H)‖
  have hg := sq_nonneg ‖gradientCLM (v : H)‖
  have h1 : min 1 c ≤ 1 := min_le_left _ _
  have h2 : min 1 c ≤ c := min_le_right _ _
  have hineq : min 1 c * (‖massCLM (v : H)‖ ^ 2 + ‖gradientCLM (v : H)‖ ^ 2) ≤
      ‖gradientCLM (v : H)‖ ^ 2 + c * ‖massCLM (v : H)‖ ^ 2 := by nlinarith
  rw [hsq, mul_assoc]
  exact mul_le_mul_of_nonneg_left hineq hκ

end DilationTestSpace

end NavierStokes.Selfsimilar
