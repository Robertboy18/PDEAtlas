/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.ProfileExhaustion
public import PDE.Fluid.NavierStokes.FiniteRankCorrection
public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Ball
import PDE.Analysis.MeasureTheory.Lp.ConstantMultiplier

/-!
# Ball corrections tested against smooth fields

A solenoidal zero-boundary velocity `u` on `B(0,ρ)` extends by zero to a solenoidal whole-space `H¹`
velocity `zeroExtendBall ρ u` with the same mass and gradient norms. A ball solution of the
corrected profile equation (4.37) of Hou, Wang and Yang makes the candidate `B` plus the
reconstructed zero extension a weak profile against the even tests supported in the ball
(`integral_weakProfileDensity_eq_zero_of_ball`). Ball solutions for all large radii with uniform
mass and gradient bounds then give an even solenoidal whole-space `w` for which
`B + w + ∑ⱼ ⟪qⱼ, w⟫ Φⱼ` is an even axisymmetric weak profile
(`exists_weakProfileEquation_of_ball_corrections`).

## How it works

We test the ball equation against a smooth solenoidal field supported in the ball, where the forms
of the bounded-domain profile correction become whole-space integrals of the zero extension. The
stationary similarity form with a bounded divergence-free background is the pairing with the adjoint
of the linearization (`similarityPrincipalForm_ballTestField`), and the transport of the finite-rank
reconstruction is the tested convection of the reconstructed whole-space velocity
(`l4Convection_add_transportPairing_ballTestField`). With the linearized equations of the fields
`Φⱼ` and the residual `E` of `B`, the ball equation becomes the weak profile equation of `B` plus
the reconstruction at that test. For the limit we take the radii `ρ₀ + n` and pass the zero
extensions to `exists_weakProfileEquation_of_ball_tests`, which extracts a weak limit of the bounded
family.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.3, (4.37) and the weak
  limit that follows it, p. 31.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert
open scoped Topology Distributions

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

open NavierStokes.Symmetry

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))
local notation "M" => PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 univ)
local notation "Vb" ρ => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))

variable {ρ : ℝ}

/-! ### Zero extension -/

/-- The mass coordinates of the zero extension are the zero extensions of the coordinates. -/
theorem massCLM_zeroExtendBall_apply (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (i : Fin 3) :
    Stationary.massCLM (zeroExtendBall ρ u) i =
      Extension.Lp.zeroExtendLp measurableSet_ball (baseCoordCLM (u i)) :=
  rfl

/-- The gradient coordinates of the zero extension are the zero extensions of the weak
derivatives. -/
theorem gradientCLM_zeroExtendBall_apply (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))
    (i j : Fin 3) :
    Stationary.gradientCLM (zeroExtendBall ρ u) i j =
      Extension.Lp.zeroExtendLp measurableSet_ball (derivCoordCLM j (u i)) :=
  rfl

/-- The zero extension keeps the `L²` norm. -/
theorem norm_massCLM_zeroExtendBall (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :
    ‖Stationary.massCLM (zeroExtendBall ρ u)‖ = ‖ZeroBoundaryVectorSpace.toLp u‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [PiLp.norm_sq_eq_of_L2, ZeroBoundaryVectorSpace.norm_toLp_sq]
  simp only [massCLM_zeroExtendBall_apply, Extension.Lp.norm_zeroExtendLp]

/-- The zero extension keeps the gradient norm. -/
theorem norm_gradientCLM_zeroExtendBall (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) :
    ‖Stationary.gradientCLM (zeroExtendBall ρ u)‖ = ‖ZeroBoundaryVectorSpace.gradient u‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [PiLp.norm_sq_eq_of_L2, ZeroBoundaryVectorSpace.norm_gradient_sq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [gradientCLM_zeroExtendBall_apply, Extension.Lp.norm_zeroExtendLp]

/-- The zero extension of a solenoidal field is solenoidal. -/
theorem divergenceCLM_zeroExtendBall {u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)}
    (hu : ZeroBoundaryVectorSpace.divergence u = 0) :
    Stationary.divergenceCLM (zeroExtendBall ρ u) = 0 := by
  have h : ∑ j, derivCoordCLM j (u j) = 0 := by
    rw [← ZeroBoundaryVectorSpace.divergence_apply]
    exact hu
  rw [Stationary.divergenceCLM_apply]
  change ∑ j, Extension.Lp.zeroExtendLp measurableSet_ball (derivCoordCLM j (u j)) = 0
  rw [← map_sum, h, map_zero]


/-- The pairing in `L²(B(0,ρ))` of a class `g`, represented on the ball by `G`, with a class
`f` is the whole-space integral of `G` against the zero extension of `f`, and the whole-space
integrand is integrable. -/
theorem inner_eq_integral_zeroExtendLp {g : DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)}
    {G : ℝ^3 → ℝ} (hg : (g : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)] G)
    (f : DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)) :
    Integrable (fun x ↦ G x * Extension.Lp.zeroExtendLp measurableSet_ball f x) ∧
      ⟪g, f⟫ = ∫ x, G x * Extension.Lp.zeroExtendLp measurableSet_ball f x := by
  have h1 := Extension.Lp.zeroExtendLp_apply_ae measurableSet_ball f
  simp only [domainMeasure, Measure.restrict_univ] at h1
  have h2 : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : ℝ^3) ρ → g x = G x :=
    (ae_restrict_iff' measurableSet_ball).mp hg
  have hext : (fun x ↦ G x * Extension.Lp.zeroExtendLp measurableSet_ball f x) =ᵐ[volume]
      (Metric.ball (0 : ℝ^3) ρ).indicator (fun x ↦ g x * f x) := by
    filter_upwards [h1, h2] with x hx hx2
    rw [hx, Extension.Lp.extensionByZero]
    by_cases hxB : x ∈ Metric.ball (0 : ℝ^3) ρ
    · rw [indicator_of_mem hxB, indicator_of_mem hxB, hx2 hxB]
    · rw [indicator_of_notMem hxB, indicator_of_notMem hxB, mul_zero]
  have hint : IntegrableOn (fun x ↦ g x * f x) (Metric.ball (0 : ℝ^3) ρ) :=
    MemLp.integrable_mul (p := 2) (q := 2) (Lp.memLp g) (Lp.memLp f)
  refine ⟨(hint.integrable_indicator measurableSet_ball).congr hext.symm, ?_⟩
  rw [integral_congr_ae hext, integral_indicator measurableSet_ball, L2.inner_def]
  simp only [domainMeasure, RCLike.inner_apply, conj_trivial]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)

/-- `inner_eq_integral_zeroExtendLp` for a base coordinate, in terms of the representative of
the zero extension. -/
theorem inner_baseCoordCLM_eq_integral {g : DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)}
    {G : ℝ^3 → ℝ} (hg : (g : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)] G)
    (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (m : Fin 3) :
    Integrable (fun x ↦ G x * Stationary.representative (zeroExtendBall ρ u) x m) ∧
      ⟪g, baseCoordCLM (u m)⟫ =
        ∫ x, G x * Stationary.representative (zeroExtendBall ρ u) x m :=
  inner_eq_integral_zeroExtendLp hg (baseCoordCLM (u m))

/-- `inner_eq_integral_zeroExtendLp` for a weak derivative, in terms of the gradient
representative of the zero extension. -/
theorem inner_derivCoordCLM_eq_integral {g : DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)}
    {G : ℝ^3 → ℝ} (hg : (g : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)] G)
    (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (m j : Fin 3) :
    Integrable (fun x ↦ G x * Stationary.gradientRepresentative (zeroExtendBall ρ u) x m j) ∧
      ⟪g, derivCoordCLM j (u m)⟫ =
        ∫ x, G x * Stationary.gradientRepresentative (zeroExtendBall ρ u) x m j :=
  inner_eq_integral_zeroExtendLp hg (derivCoordCLM j (u m))


/-! ### The similarity form at a test field -/

variable {φ : ℝ^3 → ℝ^3}

/-- Polarized integration by parts on the ball for a bounded Sobolev coefficient and two
zero-boundary fields. -/
private theorem inner_mul_deriv_add (A : W^{1,∞}(Metric.ball (0 : ℝ^3) ρ)) (i : Fin 3)
    (U V : H¹₀(Metric.ball (0 : ℝ^3) ρ)) :
    ⟪((A : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ)) (baseIndex 3 1)) •
        derivCoordCLM i U, baseCoordCLM V⟫ +
      ⟪((A : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ)) (baseIndex 3 1)) •
        derivCoordCLM i V, baseCoordCLM U⟫ =
      -⟪((A : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ)) (singleDerivIndex 3 i)) •
        baseCoordCLM U, baseCoordCLM V⟫ := by
  simpa only [baseCoordCLM_apply, derivCoordCLM_apply] using
    inner_mul_deriv_add_inner_mul_deriv_H10 Metric.isOpen_ball A i
      (U : H¹(Metric.ball (0 : ℝ^3) ρ)) V

/-- A bounded multiplier distributes over a finite sum. -/
private theorem lpSMul_sum {Ω : Set (ℝ^3)} (a : DerivLp 3 ∞ Ω) (f : Fin 3 → DerivLp 3 2 Ω) :
    a • ∑ j, f j = ∑ j, a • f j := by
  simp only [Fin.sum_univ_three, Lp.add_smul]

/-- A finite sum of bounded multipliers acts termwise. -/
private theorem sum_lpSMul {Ω : Set (ℝ^3)} (a : Fin 3 → DerivLp 3 ∞ Ω) (f : DerivLp 3 2 Ω) :
    (∑ j, a j) • f = ∑ j, a j • f := by
  simp only [Fin.sum_univ_three, Lp.smul_add]

/-- The second derivative `∂ᵢ∂ᵢφₘ` of a test field supported in the ball, as an element of
`L²(B(0,ρ))`. -/
private theorem memLp_secondPartial (hφ : IsSolenoidalTestField φ) (m i : Fin 3) :
    MemLp (fun x ↦ PDE.partialDeriv i (fun z ↦ PDE.partialDeriv i (fun y ↦ φ y m) z) x) 2
      (domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)) := by
  have hφm : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ y m) :=
    (EuclideanSpace.proj m : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ.1
  have hc : HasCompactSupport (fun y ↦ φ y m) :=
    hφ.2.1.comp_left (g := fun v : ℝ^3 ↦ v m) rfl
  have hcont := ((hφm.partialDeriv i (k := (⊤ : ℕ∞))).partialDeriv i (k := 0)).continuous
  exact (hcont.memLp_of_hasCompactSupport ((hc.partialDeriv i).partialDeriv i)).restrict _

/-- The bounded-domain stationary similarity form with a bounded divergence-free background `b`,
equal to `B` on the ball, tested with a smooth solenoidal field supported in the ball, is the
whole-space pairing of the zero extension with the adjoint `profileAdjoint B φ` of the
linearization at `B`. -/
theorem similarityPrincipalForm_ballTestField {B : ℝ^3 → ℝ^3}
    (b : Fin 3 → W^{1,∞}(Metric.ball (0 : ℝ^3) ρ))
    (hb : ∀ i, (((b i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ)) (baseIndex 3 1) :
      DerivLp 3 ∞ (Metric.ball (0 : ℝ^3) ρ)) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
        (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ B x i)
    (hbdiv : ∑ i, (b i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ))
      (singleDerivIndex 3 i) = 0)
    {u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)} (hu : ZeroBoundaryVectorSpace.divergence u = 0)
    (hφ : IsSolenoidalTestField φ) (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) :
    similarityPrincipalForm Metric.isOpen_ball Metric.isBounded_ball b 0 u
        (ballTestField hφ hsupp) =
      ∫ x, ⟪Stationary.representative (zeroExtendBall ρ u) x, profileAdjoint B φ x⟫ := by
  set v := ballTestField hφ hsupp
  set r := Stationary.representative (zeroExtendBall ρ u)
  let b₀ : Fin 3 → DerivLp 3 ∞ (Metric.ball (0 : ℝ^3) ρ) := fun i ↦
    (b i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ)) (baseIndex 3 1)
  let X : Fin 3 → W^{1,∞}(Metric.ball (0 : ℝ^3) ρ) := fun i ↦
    coordinateW1Top (Ω := Metric.ball (0 : ℝ^3) ρ) Metric.isOpen_ball Metric.isBounded_ball i
  let x₀ : Fin 3 → DerivLp 3 ∞ (Metric.ball (0 : ℝ^3) ρ) := fun i ↦
    (X i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ)) (baseIndex 3 1)
  let d2 : Fin 3 → Fin 3 → DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ) := fun m i ↦
    (memLp_secondPartial hφ m i).toLp _
  -- transport by the background
  have hT (k : Fin 3) : ∑ i, ⟪b₀ i • derivCoordCLM i (u k), baseCoordCLM (v k)⟫ =
      -∑ i, ⟪b₀ i • derivCoordCLM i (v k), baseCoordCLM (u k)⟫ := by
    have hsum : ∑ i, ⟪(b i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ))
        (singleDerivIndex 3 i) • baseCoordCLM (u k), baseCoordCLM (v k)⟫ = 0 := by
      rw [← sum_inner, ← sum_lpSMul, hbdiv, Lp.zero_smul, inner_zero_left]
    have h := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦
      inner_mul_deriv_add (b i) i (u k) (v k)
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum, neg_zero] at h
    linarith
  -- stretching by the background
  have hE (k : Fin 3) : ∑ j, ⟪(b k : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ))
      (singleDerivIndex 3 j) • baseCoordCLM (u j), baseCoordCLM (v k)⟫ =
      -∑ j, ⟪b₀ k • derivCoordCLM j (v k), baseCoordCLM (u j)⟫ := by
    have hsum : ∑ j, ⟪b₀ k • derivCoordCLM j (u j), baseCoordCLM (v k)⟫ = 0 := by
      have hdiv : ∑ j, derivCoordCLM j (u j) = 0 := by
        rw [← ZeroBoundaryVectorSpace.divergence_apply]
        exact hu
      rw [← sum_inner, ← lpSMul_sum, hdiv, Lp.smul_zero, inner_zero_left]
    have h := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦
      inner_mul_deriv_add (b k) j (u j) (v k)
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum, zero_add] at h
    linarith
  -- dilation
  have hX (k : Fin 3) : ∑ i, ⟪x₀ i • derivCoordCLM i (u k), baseCoordCLM (v k)⟫ =
      -∑ i, ⟪x₀ i • derivCoordCLM i (v k), baseCoordCLM (u k)⟫ -
        3 * ⟪baseCoordCLM (u k), baseCoordCLM (v k)⟫ := by
    have hone (i : Fin 3) : (X i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ))
        (singleDerivIndex 3 i) •
          baseCoordCLM (u k) = baseCoordCLM (u k) := by
      rw [Lp.lpSMul_eq_const_smul _ 1
        (coordinateW1Top_deriv_self_ae Metric.isOpen_ball Metric.isBounded_ball i), one_smul]
    have h := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦
      inner_mul_deriv_add (X i) i (u k) (v k)
    simp only [hone, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    change ∑ i, ⟪x₀ i • derivCoordCLM i (u k), baseCoordCLM (v k)⟫ +
      ∑ i, ⟪x₀ i • derivCoordCLM i (v k), baseCoordCLM (u k)⟫ =
        -(3 * ⟪baseCoordCLM (u k), baseCoordCLM (v k)⟫) at h
    linarith
  -- the coordinates of the test field
  have hvb (k : Fin 3) : (baseCoordCLM (v k) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ φ x k := by
    simpa only [baseCoordCLM_apply, baseIndex_toList, iteratedPartialDeriv] using
      coord_ballTestField_ae hφ hsupp k (baseIndex 3 1)
  have hvd (k i : Fin 3) : (derivCoordCLM i (v k) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ PDE.partialDeriv i (fun y ↦ φ y k) x := by
    simpa only [derivCoordCLM_apply, singleDerivIndex_toList, iteratedPartialDeriv] using
      coord_ballTestField_ae hφ hsupp k (singleDerivIndex 3 i)
  have hd2 (k i : Fin 3) : (d2 k i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ PDE.partialDeriv i (fun z ↦ PDE.partialDeriv i (fun y ↦ φ y k) z) x :=
    MemLp.coeFn_toLp _
  -- the Dirichlet form
  have hD (k i : Fin 3) : ⟪derivCoordCLM i (u k), derivCoordCLM i (v k)⟫ =
      -⟪d2 k i, baseCoordCLM (u k)⟫ := by
    have hφk : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ φ y k) :=
      (EuclideanSpace.proj k : ℝ^3 →L[ℝ] ℝ).contDiff.comp hφ.1
    have hck : HasCompactSupport (fun y ↦ φ y k) :=
      hφ.2.1.comp_left (g := fun v : ℝ^3 ↦ v k) rfl
    have h1 := (inner_derivCoordCLM_eq_integral (hvd k i) u k i).2
    have h2 := Stationary.integral_representative_mul_partialDeriv (zeroExtendBall ρ u) k i
      (hφk.partialDeriv i (k := (⊤ : ℕ∞))) (hck.partialDeriv i)
    have h3 := (inner_baseCoordCLM_eq_integral (hd2 k i) u k).2
    rw [real_inner_comm, h1, h3]
    simp_rw [mul_comm (PDE.partialDeriv i (fun z ↦ PDE.partialDeriv i (fun y ↦ φ y k) z) _)]
    rw [h2, neg_neg]
    simp_rw [mul_comm (PDE.partialDeriv i (fun y ↦ φ y k) _)]
  -- the adjoint field on the ball
  let G : Fin 3 → DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ) := fun m ↦
    baseCoordCLM (v m) + (1 / 2 : ℝ) • ∑ i, x₀ i • derivCoordCLM i (v m) - ∑ i, d2 m i -
      ∑ k, b₀ k • derivCoordCLM m (v k) - ∑ i, b₀ i • derivCoordCLM i (v m)
  have hG (m : Fin 3) : (G m : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ profileAdjoint B φ x m := by
    have hx := coordinateW1Top_base_ae (Ω := Metric.ball (0 : ℝ^3) ρ) Metric.isOpen_ball
      Metric.isBounded_ball
    filter_upwards [Lp.coeFn_sub (baseCoordCLM (v m) + (1 / 2 : ℝ) • ∑ i, x₀ i •
        derivCoordCLM i (v m) - ∑ i, d2 m i - ∑ k, b₀ k • derivCoordCLM m (v k))
        (∑ i, b₀ i • derivCoordCLM i (v m)),
      Lp.coeFn_sub (baseCoordCLM (v m) + (1 / 2 : ℝ) • ∑ i, x₀ i •
        derivCoordCLM i (v m) - ∑ i, d2 m i) (∑ k, b₀ k • derivCoordCLM m (v k)),
      Lp.coeFn_sub (baseCoordCLM (v m) + (1 / 2 : ℝ) • ∑ i, x₀ i •
        derivCoordCLM i (v m)) (∑ i, d2 m i),
      Lp.coeFn_add (baseCoordCLM (v m)) ((1 / 2 : ℝ) • ∑ i, x₀ i • derivCoordCLM i (v m)),
      Lp.coeFn_smul (1 / 2 : ℝ) (∑ i, x₀ i • derivCoordCLM i (v m)),
      Lp.coeFn_fun_finsetSum Finset.univ fun i ↦ x₀ i • derivCoordCLM i (v m),
      Lp.coeFn_fun_finsetSum Finset.univ fun i ↦ d2 m i,
      Lp.coeFn_fun_finsetSum Finset.univ fun k ↦ b₀ k • derivCoordCLM m (v k),
      Lp.coeFn_fun_finsetSum Finset.univ fun i ↦ b₀ i • derivCoordCLM i (v m),
      ae_all_iff.mpr fun i ↦ Lp.coeFn_lpSMul (r := 2) (x₀ i) (derivCoordCLM i (v m)),
      ae_all_iff.mpr fun k ↦ Lp.coeFn_lpSMul (r := 2) (b₀ k) (derivCoordCLM m (v k)),
      ae_all_iff.mpr fun i ↦ Lp.coeFn_lpSMul (r := 2) (b₀ i) (derivCoordCLM i (v m)),
      ae_all_iff.mpr hx, ae_all_iff.mpr hb, hvb m, ae_all_iff.mpr fun i ↦ hvd m i,
      ae_all_iff.mpr fun k ↦ hvd k m, ae_all_iff.mpr fun i ↦ hd2 m i]
      with x e1 e2 e3 e4 e5 e6 e7 e8 e9 m1 m2 m3 cx cb cv cd cd' c2
    rw [profileAdjoint_apply hφ.1 x m]
    simp only [G, e1, e2, e3, e4, e5, e6, e7, e8, e9, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, m1, m2, m3, Pi.mul_apply, x₀, X, b₀, cx, cb, cv, cd, cd', c2]
  -- assembly
  have hsum : similarityPrincipalForm Metric.isOpen_ball Metric.isBounded_ball b 0 u v =
      ∑ m, ⟪G m, baseCoordCLM (u m)⟫ := by
    simp only [b₀, x₀, X] at hT hX hE
    rw [similarityPrincipalForm_apply]
    simp only [Pi.zero_apply, add_zero, hD, hT, hX, hE]
    simp only [G, inner_add_left, inner_sub_left, real_inner_smul_left, b₀, x₀, X,
      Fin.sum_univ_three, real_inner_comm (baseCoordCLM (u _)) (baseCoordCLM (v _))]
    ring
  have hint (m : Fin 3) := (inner_baseCoordCLM_eq_integral (hG m) u m).1
  rw [hsum]
  simp_rw [fun m ↦ (inner_baseCoordCLM_eq_integral (hG m) u m).2]
  rw [← integral_finsetSum _ fun m _ ↦ hint m]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, r]


/-! ### Transport at a test field -/

/-- The transport of a ball field by an `L⁴` coefficient, with a supplied derivative matrix for
the transported correction, tested with a smooth solenoidal field supported in the ball, is
the tested convection of a whole-space `H¹` velocity `W` that agrees with the coefficient on
the ball and whose weak gradient on the ball is the gradient of the field plus the supplied
matrix. -/
theorem l4Convection_add_transportPairing_ballTestField
    (J : H¹₀(Metric.ball (0 : ℝ^3) ρ) →L[ℝ] DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ))
    (hJ : ∀ u, (J u : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (baseCoordCLM u : ℝ^3 → ℝ))
    (A : PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)))
    (D : PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (W : H)
    (hA : ∀ i, (A i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.representative W x i)
    (hD : ∀ k i, ∀ᵐ x ∂domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ),
      derivCoordCLM i (u k) x + D (k, i) x = Stationary.gradientRepresentative W x k i)
    (hφ : IsSolenoidalTestField φ) (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) :
    IncompressibleFlow.l4Convection J A u (ballTestField hφ hsupp) +
        ContinuousLinearMap.transportPairing A D
          (IncompressibleFlow.vectorL4Embedding J (ballTestField hφ hsupp)) =
      Stationary.testedConvection (testFieldSobolev hφ.1 hφ.2.1) (fun j ↦ W j) := by
  set v := ballTestField hφ hsupp
  have hvb (k : Fin 3) : (baseCoordCLM (v k) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ φ x k := by
    simpa only [baseCoordCLM_apply, baseIndex_toList, iteratedPartialDeriv] using
      coord_ballTestField_ae hφ hsupp k (baseIndex 3 1)
  have hterm (k i : Fin 3) :
      ⟪(ContinuousLinearMap.mul ℝ ℝ).holder 2 (A i) (J (v k)), derivCoordCLM i (u k)⟫ +
        ⟪(ContinuousLinearMap.mul ℝ ℝ).holder 2 (A i) (J (v k)), D (k, i)⟫ =
      ⟪wkpBaseCoordinateCLM (testFieldSobolev hφ.1 hφ.2.1 k) • wkpBaseCoordinateCLM (W i),
        wkpCoordinateCLM (singleDerivIndex 3 i) (W k)⟫ := by
    rw [← inner_add_right, L2.inner_def, L2.inner_def]
    have hR : (fun x ↦ ⟪(wkpBaseCoordinateCLM (testFieldSobolev hφ.1 hφ.2.1 k) •
        wkpBaseCoordinateCLM (W i) : DerivLp 3 2 univ) x,
          (wkpCoordinateCLM (singleDerivIndex 3 i) (W k) : DerivLp 3 2 univ) x⟫) =ᵐ[
        volume] fun x ↦ φ x k * Stationary.representative W x i *
          Stationary.gradientRepresentative W x k i := by
      have hs := Lp.coeFn_lpSMul (r := 2)
        (wkpBaseCoordinateCLM (testFieldSobolev hφ.1 hφ.2.1 k)) (wkpBaseCoordinateCLM (W i))
      simp only [domainMeasure, Measure.restrict_univ] at hs
      filter_upwards [hs, base_testFieldSobolev_ae hφ.1 hφ.2.1 k] with x h1 h2
      rw [h1, Pi.smul_apply', h2, smul_eq_mul, RCLike.inner_apply, conj_trivial,
        Stationary.representative_apply, Stationary.massCLM_apply]
      simp only [Stationary.gradientRepresentative, Stationary.gradientCLM_apply]
      ring
    have hL : (fun x ↦ ⟪((ContinuousLinearMap.mul ℝ ℝ).holder 2 (A i) (J (v k)) :
        DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)) x,
          (derivCoordCLM i (u k) + D (k, i) : DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)) x⟫) =ᵐ[
        domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ φ x k *
          Stationary.representative W x i * Stationary.gradientRepresentative W x k i := by
      filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (A i) (J (v k)),
        Lp.coeFn_add (derivCoordCLM i (u k)) (D (k, i)), hA i, hJ (v k), hvb k, hD k i]
        with x h1 h2 h3 h4 h5 h6
      rw [h1, h2, Pi.add_apply, h6, ContinuousLinearMap.mul_apply', h3, h4, h5,
        RCLike.inner_apply, conj_trivial]
      ring
    simp only [domainMeasure, Measure.restrict_univ] at hL ⊢
    rw [integral_congr_ae hL, integral_congr_ae hR]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp h)]
    simp
  rw [IncompressibleFlow.l4Convection_apply, ContinuousLinearMap.transportPairing_apply]
  simp only [IncompressibleFlow.scalarL4Transport_apply, IncompressibleFlow.vectorL4Embedding_apply]
  rw [Stationary.testedConvection, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ hterm k i


/-! ### The finite-rank reconstruction -/

section FiniteRank

variable {F : Type*} [Fintype F]

/-- The finite-rank correction `W ↦ ∑ⱼ ⟪qⱼ, W⟫ Φⱼ` of whole-space velocities, the pairing taken
with the mass coordinates. -/
def finiteRankCorrection (q : F → M) (Φ : F → H) : H →L[ℝ] H :=
  ∑ j, ((innerSL ℝ (q j)).comp Stationary.massCLM).smulRight (Φ j)

/-- Evaluation of the finite-rank correction. -/
theorem finiteRankCorrection_apply (q : F → M) (Φ : F → H) (W : H) :
    finiteRankCorrection q Φ W = ∑ j, ⟪q j, Stationary.massCLM W⟫ • Φ j := by
  simp [finiteRankCorrection]

/-- The finite-rank correction of solenoidal fields is solenoidal. -/
theorem divergenceCLM_finiteRankCorrection {q : F → M} {Φ : F → H}
    (hΦ : ∀ j, Stationary.divergenceCLM (Φ j) = 0) (W : H) :
    Stationary.divergenceCLM (finiteRankCorrection q Φ W) = 0 := by
  simp [finiteRankCorrection_apply, map_sum, map_smul, hΦ]

/-- The finite-rank correction of even fields is even. -/
theorem finiteRankCorrection_mem_evenSectorH1 {q : F → M} {Φ : F → H}
    (hΦ : ∀ j, Φ j ∈ evenSectorH1) (W : H) : finiteRankCorrection q Φ W ∈ evenSectorH1 := by
  rw [finiteRankCorrection_apply]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hΦ j)

/-- The mass coordinates of `W + ∑ⱼ cⱼ Φⱼ` are the combination of the mass coordinates,
almost everywhere. -/
theorem massCLM_add_sum_smul_ae (W : H) (c : F → ℝ) (Φ : F → H) (i : Fin 3) :
    (Stationary.massCLM (W + ∑ j, c j • Φ j) i : ℝ^3 → ℝ) =ᵐ[volume]
      fun x ↦ (Stationary.massCLM W i : ℝ^3 → ℝ) x +
        ∑ j, c j * (Stationary.massCLM (Φ j) i : ℝ^3 → ℝ) x := by
  have h1 := Lp.coeFn_add (Stationary.massCLM W i) (∑ j, c j • Stationary.massCLM (Φ j) i)
  have h2 := Lp.coeFn_fun_finsetSum Finset.univ fun j ↦ c j • Stationary.massCLM (Φ j) i
  have h3 (j : F) := Lp.coeFn_smul (c j) (Stationary.massCLM (Φ j) i)
  simp only [domainMeasure, Measure.restrict_univ] at h1 h2 h3
  have heq : Stationary.massCLM (W + ∑ j, c j • Φ j) i =
      Stationary.massCLM W i + ∑ j, c j • Stationary.massCLM (Φ j) i := by
    simp only [map_add, map_sum, map_smul, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply]
  rw [heq]
  filter_upwards [h1, h2, ae_all_iff.mpr h3] with x hx1 hx2 hx3
  rw [hx1, Pi.add_apply, hx2]
  simp only [hx3, Pi.smul_apply, smul_eq_mul]

/-- The gradient coordinates of `W + ∑ⱼ cⱼ Φⱼ` are the combination of the gradient
coordinates, almost everywhere. -/
theorem gradientCLM_add_sum_smul_ae (W : H) (c : F → ℝ) (Φ : F → H) (i k : Fin 3) :
    (Stationary.gradientCLM (W + ∑ j, c j • Φ j) i k : ℝ^3 → ℝ) =ᵐ[volume]
      fun x ↦ (Stationary.gradientCLM W i k : ℝ^3 → ℝ) x +
        ∑ j, c j * (Stationary.gradientCLM (Φ j) i k : ℝ^3 → ℝ) x := by
  have h1 := Lp.coeFn_add (Stationary.gradientCLM W i k)
    (∑ j, c j • Stationary.gradientCLM (Φ j) i k)
  have h2 := Lp.coeFn_fun_finsetSum Finset.univ fun j ↦ c j • Stationary.gradientCLM (Φ j) i k
  have h3 (j : F) := Lp.coeFn_smul (c j) (Stationary.gradientCLM (Φ j) i k)
  simp only [domainMeasure, Measure.restrict_univ] at h1 h2 h3
  have heq : Stationary.gradientCLM (W + ∑ j, c j • Φ j) i k =
      Stationary.gradientCLM W i k + ∑ j, c j • Stationary.gradientCLM (Φ j) i k := by
    simp only [map_add, map_sum, map_smul, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply]
  rw [heq]
  filter_upwards [h1, h2, ae_all_iff.mpr h3] with x hx1 hx2 hx3
  rw [hx1, Pi.add_apply, hx2]
  simp only [hx3, Pi.smul_apply, smul_eq_mul]

end FiniteRank

/-! ### Ball solutions of the corrected profile equation -/

section BallSolution

variable {F : Type*} [Fintype F]

/-- The zero extension of a base coordinate equals the coordinate on the ball and vanishes
outside it, almost everywhere. -/
private theorem zeroExtendLp_ae_on_ball (f : DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)) :
    ∀ᵐ x ∂domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ),
      Extension.Lp.zeroExtendLp measurableSet_ball f x = f x := by
  have h := Extension.Lp.zeroExtendLp_apply_ae measurableSet_ball f
  simp only [domainMeasure, Measure.restrict_univ] at h
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_ball] with x hx hxB
  rw [hx, Extension.Lp.extensionByZero, indicator_of_mem hxB]

/-- The pairing of the restriction to the ball of a whole-space `L²` field with the mass
coordinates of a zero-boundary field is the whole-space pairing with the zero extension. -/
theorem inner_solenoidalMassCoordinates_eq {qB : PiLp 2 (fun _ : Fin 3 ↦
      DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ))} {q : M}
    (hq : ∀ i, (qB i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (q i : ℝ^3 → ℝ)) (u : Vb ρ) :
    ⟪qB, solenoidalMassCoordinates u⟫ =
      ⟪q, Stationary.massCLM (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)))⟫ := by
  simp only [PiLp.inner_apply, solenoidalMassCoordinates_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [(inner_baseCoordCLM_eq_integral (hq i) _ i).2, L2.inner_def]
  simp only [domainMeasure, Measure.restrict_univ, RCLike.inner_apply, conj_trivial,
    Stationary.representative_apply]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)

/-- The zero extension of a base coordinate of the test velocity is the component of the
test field. -/
theorem zeroExtendLp_baseCoordCLM_ballTestField_ae (hφ : IsSolenoidalTestField φ)
    (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) (k : Fin 3) :
    (Extension.Lp.zeroExtendLp measurableSet_ball (baseCoordCLM (ballTestField hφ hsupp k)) :
      ℝ^3 → ℝ) =ᵐ[volume] fun x ↦ φ x k := by
  have hvb : (baseCoordCLM (ballTestField hφ hsupp k) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ φ x k := by
    simpa only [baseCoordCLM_apply, baseIndex_toList, iteratedPartialDeriv] using
      coord_ballTestField_ae hφ hsupp k (baseIndex 3 1)
  have h := Extension.Lp.zeroExtendLp_apply_ae measurableSet_ball
    (baseCoordCLM (ballTestField hφ hsupp k))
  simp only [domainMeasure, Measure.restrict_univ] at h
  have h2 : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : ℝ^3) ρ →
      baseCoordCLM (ballTestField hφ hsupp k) x = φ x k :=
    (ae_restrict_iff' measurableSet_ball).mp hvb
  filter_upwards [h, h2] with x hx hx2
  rw [hx, Extension.Lp.extensionByZero]
  by_cases hxB : x ∈ Metric.ball (0 : ℝ^3) ρ
  · rw [indicator_of_mem hxB, hx2 hxB]
  · rw [indicator_of_notMem hxB, image_eq_zero_of_notMem_tsupport fun h ↦ hxB (hsupp h)]
    rfl

/-- The pairing in `L²(B(0,ρ))` of the restriction of a field `f` with the mass coordinates of
the test velocity is the whole-space pairing `∫ f·φ`. -/
theorem inner_solenoidalMassCoordinates_ballTest {fB : PiLp 2 (fun _ : Fin 3 ↦
      DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ))} {f : ℝ^3 → ℝ^3}
    (hf : ∀ i, (fB i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ f x i) (hφ : IsSolenoidalTestField φ) (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) :
    ⟪fB, solenoidalMassCoordinates (ballTest hφ hsupp)⟫ = ∫ x, ⟪f x, φ x⟫ := by
  have hext := zeroExtendLp_baseCoordCLM_ballTestField_ae hφ hsupp
  have hint' (i : Fin 3) : Integrable (fun x ↦ f x i * φ x i) volume :=
    (inner_eq_integral_zeroExtendLp (hf i) _).1.congr
      (by filter_upwards [hext i] with x hx; rw [hx])
  have hval (i : Fin 3) : ⟪fB i, baseCoordCLM (ballTestField hφ hsupp i)⟫ =
      ∫ x, f x i * φ x i := by
    rw [(inner_eq_integral_zeroExtendLp (hf i) _).2]
    exact integral_congr_ae (by filter_upwards [hext i] with x hx; rw [hx])
  rw [PiLp.inner_apply]
  change ∑ i, ⟪fB i, baseCoordCLM (ballTestField hφ hsupp i)⟫ = _
  simp only [hval]
  rw [← integral_finsetSum _ fun i _ ↦ hint' i]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- The pairing on the ball of a field with the test velocity is the whole-space pairing with
the test field. -/
theorem setIntegral_inner_toLp_ballTestField (E : ℝ^3 → ℝ^3) (hφ : IsSolenoidalTestField φ)
    (hsupp : tsupport φ ⊆ Metric.ball 0 ρ) :
    ∫ x in Metric.ball (0 : ℝ^3) ρ,
      ⟪E x, (ZeroBoundaryVectorSpace.toLp (ballTestField hφ hsupp) : ℝ^3 → ℝ^3) x⟫ =
      ∫ x, ⟪E x, φ x⟫ := by
  have hv := ballField_ballTest hφ hsupp
  have hon : (fun x ↦ ⟪E x, (ZeroBoundaryVectorSpace.toLp (ballTestField hφ hsupp) :
      ℝ^3 → ℝ^3) x⟫) =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ ⟪E x, φ x⟫ := by
    filter_upwards [ae_restrict_of_ae hv, ae_restrict_mem measurableSet_ball] with x hx hxB
    rw [← hx, ballField, indicator_of_mem hxB]
    rfl
  rw [integral_congr_ae hon]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
  rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp h), inner_zero_right]

/-- On the ball, the reconstruction `u + ∑ⱼ cⱼ φⱼ` of the restrictions agrees with the
representative of the whole-space reconstruction `W + ∑ⱼ cⱼ Φⱼ`, `W` the zero extension. -/
theorem representative_reconstruction_ae (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))
    (Φ : F → H) (c : F → ℝ)
    (φB : F → PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (hφB : ∀ j i, (φB j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.representative (Φ j) x i) (i : Fin 3) :
    ((WithLp.toLp 2 (fun k ↦ baseCoordCLM (u k)) + ∑ j, c j • φB j :
      PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ))) i : ℝ^3 → ℝ)
      =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.representative (zeroExtendBall ρ u + ∑ j, c j • Φ j) x i := by
  have h1 := Lp.coeFn_add (baseCoordCLM (u i)) (∑ j, c j • φB j i)
  have h2 := Lp.coeFn_fun_finsetSum Finset.univ fun j ↦ c j • φB j i
  have h3 (j : F) := Lp.coeFn_smul (c j) (φB j i)
  have hW := massCLM_add_sum_smul_ae (zeroExtendBall ρ u) c Φ i
  have heq : ((WithLp.toLp 2 (fun k ↦ baseCoordCLM (u k)) + ∑ j, c j • φB j :
      PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ))) i) =
      baseCoordCLM (u i) + ∑ j, c j • φB j i := by
    simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  rw [heq]
  filter_upwards [h1, h2, ae_all_iff.mpr h3, ae_restrict_of_ae hW,
    zeroExtendLp_ae_on_ball (baseCoordCLM (u i)), ae_all_iff.mpr fun j ↦ hφB j i]
    with x hx1 hx2 hx3 hxW hx0 hxφ
  rw [Stationary.representative_apply, hxW, hx1, Pi.add_apply, hx2]
  change _ = Extension.Lp.zeroExtendLp measurableSet_ball (baseCoordCLM (u i)) x + _
  rw [hx0]
  simp only [hx3, Pi.smul_apply, smul_eq_mul, hxφ, Stationary.representative_apply]

/-- On the ball, the weak gradient of a zero-boundary field plus a combination of the
restricted gradients of the `Φⱼ` is the gradient representative of the whole-space
reconstruction. -/
theorem gradientRepresentative_reconstruction_ae (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))
    (Φ : F → H) (c : F → ℝ)
    (D₂ : F → PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (hD₂ : ∀ j k i, (D₂ j (k, i) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.gradientRepresentative (Φ j) x k i) (k i : Fin 3) :
    ∀ᵐ x ∂domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ),
      derivCoordCLM i (u k) x + (∑ j, c j • D₂ j :
        PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ))) (k, i) x =
      Stationary.gradientRepresentative (zeroExtendBall ρ u + ∑ j, c j • Φ j) x k i := by
  have h2 := Lp.coeFn_fun_finsetSum Finset.univ fun j ↦ c j • D₂ j (k, i)
  have h3 (j : F) := Lp.coeFn_smul (c j) (D₂ j (k, i))
  have hW := gradientCLM_add_sum_smul_ae (zeroExtendBall ρ u) c Φ k i
  have heq : ((∑ j, c j • D₂ j :
      PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ))) (k, i)) =
      ∑ j, c j • D₂ j (k, i) := by
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  rw [heq]
  filter_upwards [h2, ae_all_iff.mpr h3, ae_restrict_of_ae hW,
    zeroExtendLp_ae_on_ball (derivCoordCLM i (u k)), ae_all_iff.mpr fun j ↦ hD₂ j k i]
    with x hx2 hx3 hxW hx0 hxD
  simp only [Stationary.gradientRepresentative] at hxD ⊢
  rw [hxW, hx2]
  change _ = Extension.Lp.zeroExtendLp measurableSet_ball (derivCoordCLM i (u k)) x + _
  rw [hx0]
  simp only [hx3, Pi.smul_apply, smul_eq_mul, hxD]

/-- A ball solution of the corrected profile equation (Hou, Wang and Yang, (4.37)) tested with
a smooth solenoidal field supported in the ball gives the weak profile equation of the background
plus the reconstructed zero extension against that field.

The ball equation is the one produced by the finite-rank correction theorem
`exists_solenoidal_transport_correction_of_finiteRank_on`: the stationary similarity form with
a bounded divergence-free background `b`, a finite-rank term `∑ⱼ ⟪qⱼ, u⟫ ⟪fⱼ, v⟫`, transport by
the reconstruction `A = u + ∑ⱼ ⟪qⱼ, u⟫ φⱼ` of `u` with derivative matrix
`D = ∑ⱼ ⟪qⱼ, u⟫ D₂ⱼ` of the correction, and the residual `E` on the right. The ball data are
the restrictions of whole-space data: `b = B`, `qB = q`, `φB = Φ`, `D₂ = ∇Φ` and `fB = f` on
the ball, and each `Φⱼ` weakly solves the linearized equation at `B` with right side `fⱼ`
(`hΦeq`), while `E` is the residual of `B` (`hE`). -/
theorem integral_weakProfileDensity_eq_zero_of_ball {B E : ℝ^3 → ℝ^3}
    (hBm : AEStronglyMeasurable B volume) (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume)
    (q : F → M) (Φ : F → H) (hΦ : ∀ j, Stationary.divergenceCLM (Φ j) = 0)
    (f : F → ℝ^3 → ℝ^3) (b : Fin 3 → W^{1,∞}(Metric.ball (0 : ℝ^3) ρ))
    (hb : ∀ i, (((b i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ)) (baseIndex 3 1) :
      DerivLp 3 ∞ (Metric.ball (0 : ℝ^3) ρ)) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
        (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ B x i)
    (hbdiv : ∑ i, (b i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ))
      (singleDerivIndex 3 i) = 0)
    (J : H¹₀(Metric.ball (0 : ℝ^3) ρ) →L[ℝ] DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ))
    (hJ : ∀ u, (J u : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (baseCoordCLM u : ℝ^3 → ℝ))
    (qB φB fB : F → PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (D₂ : F → PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (hq : ∀ j i, (qB j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (q j i : ℝ^3 → ℝ))
    (hφB : ∀ j i, (φB j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.representative (Φ j) x i)
    (hD₂ : ∀ j k i, (D₂ j (k, i) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.gradientRepresentative (Φ j) x k i)
    (hfB : ∀ j i, (fB j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ f j x i)
    (A : PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)))
    (D : PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (u : Vb ρ)
    (hA : ∀ i, (A i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      ((solenoidalMassCoordinates u + ∑ j, ⟪qB j, solenoidalMassCoordinates u⟫ • φB j) i :
        ℝ^3 → ℝ))
    (hD : D = ∑ j, ⟪qB j, solenoidalMassCoordinates u⟫ • D₂ j)
    (hφ : IsSolenoidalTestField φ) (hsupp : tsupport φ ⊆ Metric.ball 0 ρ)
    (hΦeq : ∀ j, ∫ x, ⟪Stationary.representative (Φ j) x, profileAdjoint B φ x⟫ =
      ∫ x, ⟪f j x, φ x⟫)
    (hE : ∫ x, weakProfileDensity B φ x = ∫ x, ⟪E x, φ x⟫)
    (hball : similarityPrincipalForm Metric.isOpen_ball Metric.isBounded_ball b 0
        (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (ballTestField hφ hsupp) +
        ∑ j, ⟪qB j, solenoidalMassCoordinates u⟫ *
          ⟪fB j, solenoidalMassCoordinates (ballTest hφ hsupp)⟫ +
        IncompressibleFlow.l4Convection J A (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))
          (ballTestField hφ hsupp) +
        ContinuousLinearMap.transportPairing A D
          (IncompressibleFlow.vectorL4Embedding J (ballTestField hφ hsupp)) =
      -∫ x in Metric.ball (0 : ℝ^3) ρ, ⟪E x,
        (ZeroBoundaryVectorSpace.toLp (ballTestField hφ hsupp) : ℝ^3 → ℝ^3) x⟫) :
    ∫ x, weakProfileDensity (B + Stationary.representative
      ((ContinuousLinearMap.id ℝ H + finiteRankCorrection q Φ)
        (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))))) φ x = 0 := by
  have hc (j : F) := inner_solenoidalMassCoordinates_eq (hq j) u
  have hf (j : F) := inner_solenoidalMassCoordinates_ballTest (hfB j) hφ hsupp
  rw [setIntegral_inner_toLp_ballTestField E hφ hsupp] at hball
  simp only [hc, hf] at hball hA hD
  have hdivU : ZeroBoundaryVectorSpace.divergence (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) = 0 :=
    u.2
  have hRW : (ContinuousLinearMap.id ℝ H + finiteRankCorrection q Φ)
      (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))) =
      zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) + ∑ j,
        ⟪q j, Stationary.massCLM (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)))⟫ •
          Φ j := by
    simp only [add_apply, ContinuousLinearMap.id_apply, finiteRankCorrection_apply]
  rw [hRW]
  set W := zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))
  set c : F → ℝ := fun j ↦ ⟪q j, Stationary.massCLM W⟫
  have hA' (i : Fin 3) : (A i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      fun x ↦ Stationary.representative (W + ∑ j, c j • Φ j) x i :=
    (hA i).trans (representative_reconstruction_ae _ Φ c φB hφB i)
  have hD' (k i : Fin 3) : ∀ᵐ x ∂domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ),
      derivCoordCLM i ((u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) k) x + D (k, i) x =
        Stationary.gradientRepresentative (W + ∑ j, c j • Φ j) x k i := by
    rw [hD]
    exact gradientRepresentative_reconstruction_ae _ Φ c D₂ hD₂ k i
  have hW0 : Stationary.divergenceCLM W = 0 := divergenceCLM_zeroExtendBall hdivU
  have hdiv : Stationary.divergenceCLM (W + ∑ j, c j • Φ j) = 0 := by
    simp only [map_add, map_sum, map_smul, hW0, hΦ, smul_zero, Finset.sum_const_zero, add_zero]
  have hconv := l4Convection_add_transportPairing_ballTestField J hJ A D _ _ hA' hD' hφ hsupp
  rw [Stationary.testedConvection_eq_testedFlux _ _ (by
    simpa only [Stationary.divergenceCLM_apply] using hdiv)] at hconv
  have hlin : ⟪Stationary.massCLM (W + ∑ j, c j • Φ j),
      profileAdjointCoordinates hBm hB2 hφ.1 hφ.2.1⟫ =
      similarityPrincipalForm Metric.isOpen_ball Metric.isBounded_ball b 0
        (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (ballTestField hφ hsupp) +
        ∑ j, c j * ∫ x, ⟪f j x, φ x⟫ := by
    rw [similarityPrincipalForm_ballTestField b hb hbdiv hdivU hφ hsupp]
    simp only [map_add, map_sum, map_smul, inner_add_left, sum_inner, real_inner_smul_left,
      inner_massCLM_profileAdjointCoordinates, hΦeq]
    rfl
  rw [integral_weakProfileDensity_add_representative_eq hBm hB2 hφ.1 hφ.2.1, hlin, hE]
  change _ + Stationary.testedFlux _ (Stationary.massValues fun k ↦ (W + ∑ j, c j • Φ j) k) = 0
  rw [← hconv]
  linarith

/-- **The exact profile as a limit of ball corrections.** Let `B` be an even axisymmetric
background in `L²_loc` with weak residual `E` against even tests, and let finite-rank fields
`Φⱼ` (even, solenoidal) weakly solve the linearized equation at `B` with right sides `fⱼ`. For
every `ρ ≥ ρ₀` let the bounded-domain data on `B(0,ρ)` be the restrictions of these (`hb`, `hq`,
`hφB`, `hD₂`, `hfB`) and let `u` be a solution in the even sector, with radii `r₀`, `r₁`, of the
corrected profile equation in the form of `exists_solenoidal_transport_correction_of_finiteRank_on`
(`hball`, with the profile form `hprofile` and the finite-rank reconstructions `hR`, `hS`). Then
some even solenoidal whole-space `w` with the same radii makes
`B + w + ∑ⱼ ⟪qⱼ, w⟫ Φⱼ` an even axisymmetric weak profile. -/
theorem exists_weakProfileEquation_of_ball_corrections {B E : ℝ^3 → ℝ^3}
    (hB : IsEvenAxisymmetric B) (hBm : AEStronglyMeasurable B volume)
    (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume)
    (hE : ∀ φ, IsSolenoidalTestField φ → IsEvenAxisymmetric φ →
      ∫ x, weakProfileDensity B φ x = ∫ x, ⟪E x, φ x⟫)
    (q : F → M) (Φ : F → H) (f : F → ℝ^3 → ℝ^3)
    (hΦ : ∀ j, Stationary.divergenceCLM (Φ j) = 0) (hΦe : ∀ j, Φ j ∈ evenSectorH1)
    (hΦeq : ∀ j φ, IsSolenoidalTestField φ → IsEvenAxisymmetric φ →
      ∫ x, ⟪Stationary.representative (Φ j) x, profileAdjoint B φ x⟫ = ∫ x, ⟪f j x, φ x⟫)
    (ρ₀ : ℝ) (b : ∀ ρ : ℝ, Fin 3 → W^{1,∞}(Metric.ball (0 : ℝ^3) ρ))
    (hb : ∀ ρ, ρ₀ ≤ ρ → ∀ i, (((b ρ i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ))
      (baseIndex 3 1) : DerivLp 3 ∞ (Metric.ball (0 : ℝ^3) ρ)) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
        (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ B x i)
    (hbdiv : ∀ ρ, ρ₀ ≤ ρ → ∑ i, (b ρ i : WkpAmbientOn 3 1 ∞ (Metric.ball (0 : ℝ^3) ρ))
      (singleDerivIndex 3 i) = 0)
    (J : ∀ ρ : ℝ, H¹₀(Metric.ball (0 : ℝ^3) ρ) →L[ℝ] DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ))
    (hJ : ∀ ρ, ρ₀ ≤ ρ → ∀ u, (J ρ u : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 (Metric.ball (0 : ℝ^3) ρ)]
      (baseCoordCLM u : ℝ^3 → ℝ))
    (R : ∀ ρ : ℝ, PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)) →L[ℝ]
      PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)))
    (S : ∀ ρ : ℝ, PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ)) →L[ℝ]
      PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (profileForm : ∀ ρ : ℝ, (Vb ρ) →L[ℝ] StrongDual ℝ (Vb ρ))
    (qB φB fB : ∀ ρ : ℝ, F → PiLp 2 (fun _ : Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (D₂ : ∀ ρ : ℝ, F → PiLp 2 (fun _ : Fin 3 × Fin 3 ↦ DerivLp 3 2 (Metric.ball (0 : ℝ^3) ρ)))
    (hq : ∀ ρ, ρ₀ ≤ ρ → ∀ j i, (qB ρ j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] (q j i : ℝ^3 → ℝ))
    (hφB : ∀ ρ, ρ₀ ≤ ρ → ∀ j i, (φB ρ j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ Stationary.representative (Φ j) x i)
    (hD₂ : ∀ ρ, ρ₀ ≤ ρ → ∀ j k i, (D₂ ρ j (k, i) : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ Stationary.gradientRepresentative (Φ j) x k i)
    (hfB : ∀ ρ, ρ₀ ≤ ρ → ∀ j i, (fB ρ j i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
      (Metric.ball (0 : ℝ^3) ρ)] fun x ↦ f j x i)
    (hR : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ evenSector ρ, ∀ i,
      (R ρ (solenoidalL4Embedding (J ρ) u) i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3
        (Metric.ball (0 : ℝ^3) ρ)] ((solenoidalMassCoordinates u +
          ∑ j, ⟪qB ρ j, solenoidalMassCoordinates u⟫ • φB ρ j) i : ℝ^3 → ℝ))
    (hS : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ evenSector ρ, S ρ (solenoidalL4Embedding (J ρ) u) =
      ∑ j, ⟪qB ρ j, solenoidalMassCoordinates u⟫ • D₂ ρ j)
    (hprofile : ∀ ρ, ρ₀ ≤ ρ → ∀ u v, profileForm ρ u v =
      similarityPrincipalForm Metric.isOpen_ball Metric.isBounded_ball (b ρ) 0
        (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) +
        ∑ j, ⟪qB ρ j, solenoidalMassCoordinates u⟫ * ⟪fB ρ j, solenoidalMassCoordinates v⟫)
    (r₀ r₁ : ℝ)
    (hball : ∀ ρ, ρ₀ ≤ ρ → ∃ u ∈ evenSector ρ,
      ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ≤ r₀ ∧
      ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ≤ r₁ ∧
      ∀ v ∈ evenSector ρ, profileForm ρ u v +
        IncompressibleFlow.l4Convection (J ρ) (R ρ (solenoidalL4Embedding (J ρ) u))
          (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) +
        ContinuousLinearMap.transportPairing (R ρ (solenoidalL4Embedding (J ρ) u))
          (S ρ (solenoidalL4Embedding (J ρ) u)) (solenoidalL4Embedding (J ρ) v) =
        -∫ x in Metric.ball (0 : ℝ^3) ρ, ⟪E x, (ZeroBoundaryVectorSpace.toLp
          (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) : ℝ^3 → ℝ^3) x⟫) :
    ∃ w ∈ evenSectorH1, ‖Stationary.massCLM w‖ ≤ r₀ ∧ ‖Stationary.gradientCLM w‖ ≤ r₁ ∧
      Stationary.divergenceCLM w = 0 ∧
      IsEvenAxisymmetric (B + Stationary.representative (w + finiteRankCorrection q Φ w)) ∧
      WeakProfileEquation (B + Stationary.representative (w + finiteRankCorrection q Φ w)) := by
  let ρ : ℕ → ℝ := fun n ↦ ρ₀ + n
  have hρ (n : ℕ) : ρ₀ ≤ ρ n := le_add_of_nonneg_right n.cast_nonneg
  have hρt : Tendsto ρ atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  choose u hu hu₀ hu₁ hueq using fun n ↦ hball (ρ n) (hρ n)
  exact exists_weakProfileEquation_of_ball_tests atTop hρt hB hBm hB2
    (ContinuousLinearMap.id ℝ H + finiteRankCorrection q Φ)
    (fun w hw ↦ add_mem hw (finiteRankCorrection_mem_evenSectorH1 hΦe w))
    (fun n ↦ zeroExtendBall (ρ n) (u n : H¹₀(Metric.ball (0 : ℝ^3) (ρ n); ℝ^3)))
    (fun n ↦ zeroExtendBall_mem_evenSectorH1 (hu n)) r₀ r₁
    (fun n ↦ (norm_massCLM_zeroExtendBall _).trans_le (hu₀ n))
    (fun n ↦ (norm_gradientCLM_zeroExtendBall _).trans_le (hu₁ n))
    (fun n ↦ divergenceCLM_zeroExtendBall (u n).2)
    (fun n φ hφ he hsupp ↦ by
      have hv := hueq n (ballTest hφ hsupp) (ballTest_mem_evenSector hφ hsupp he)
      rw [hprofile _ (hρ n)] at hv
      exact integral_weakProfileDensity_eq_zero_of_ball hBm hB2 q Φ hΦ f (b (ρ n))
        (hb _ (hρ n)) (hbdiv _ (hρ n)) (J (ρ n)) (hJ _ (hρ n)) (qB (ρ n)) (φB (ρ n)) (fB (ρ n))
        (D₂ (ρ n)) (hq _ (hρ n)) (hφB _ (hρ n)) (hD₂ _ (hρ n)) (hfB _ (hρ n))
        (R (ρ n) (solenoidalL4Embedding (J (ρ n)) (u n)))
        (S (ρ n) (solenoidalL4Embedding (J (ρ n)) (u n))) (u n) (hR _ (hρ n) _ (hu n))
        (hS _ (hρ n) _ (hu n)) hφ hsupp (fun j ↦ hΦeq j φ hφ he) (hE φ hφ he) hv)

end BallSolution

end NavierStokes.Nonuniqueness
