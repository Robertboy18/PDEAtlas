/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.BallCorrection
public import PDE.Analysis.Variational.WeakLimitSolution
import PDE.Analysis.MeasureTheory.Function.LocalL2

/-!
# The exact profile as a weak limit of ball corrections, with every shared bound

The ball corrections of an approximate self-similar profile have a weak limit, along an
ultrafilter, that solves the whole-space weak profile equation. This module returns the limit as
a weak limit, so that every weakly lower semicontinuous bound of the ball corrections passes to
it, not only a mass radius and a gradient radius. For the ball corrections this is used with all
combinations `p ‖u‖ + q ‖∇u‖`, `p, q ≥ 0`: a function `bound p q` that dominates them on every
ball dominates them at the limit. A box of two radii is the bound `p r₀ + q r₁`, a weighted
energy ball of radius `r` is the bound `r √(p² / η + q²)`, and the refined estimate at a fixed
point is a bound of this kind as well. The nonlinear term is taken in flux form, as
`WeakProfileEquation` has it; on each ball it agrees with the product form of the paper by
`l4Convection_add_transportPairing_ballTestField`.

## Main results

* `exists_tested_weakProfile_tendsto_weak`: for every background in `L²_loc` and every bounded
  family, the tested weak profile equations pass to a weak limit along an ultrafilter.
* `exists_weakProfileEquation_of_ball_tests_tendsto_weak`: for every even background, the same
  over an exhausting family of balls, and the limit is even, divergence-free and a weak profile.
* `exists_weakProfileEquation_of_ball_corrections_of_bound`: for every even background and all
  finite-rank data, the exact profile from ball corrections, with every bound `bound p q` of the
  ball solutions. `exists_weakProfileEquation_of_ball_corrections` is the case of a box.

## How it works

For each test field, the tested density of `B + R W` is the tested density of `B`, plus a
continuous linear functional of `W`, plus the tested flux of a compact cutoff observation of `W`
(`integral_weakProfileDensity_add_representative`). So
`PDE.Analysis.Variational.exists_tendsto_weak_solution_of_eventually_eq` passes the equations to
a weak limit along an ultrafilter. Evenness and zero divergence are closed linear constraints
and pass to the limit (`PDE.Analysis.constraints_eq_zero_of_tendsto_weak`), and
`WeakProfileEquation.of_symmetric_tests` extends the equation of the even limit from the even
tests to all tests. Every combination `p ‖·‖ + q ‖∇·‖` is weakly lower semicontinuous
(`PDE.Analysis.Variational.mul_norm_add_mul_norm_le_of_tendsto_weak`).

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.3, "Taking weak
  limits". <https://arxiv.org/abs/2509.25116>
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

section Limit

variable {B : ℝ^3 → ℝ^3}

/-- **Tested weak profile equations pass to a weak limit.** Let `B` be in `L²_loc`, `R` a
bounded reconstruction of whole-space `H¹` velocities and `U i` a bounded family. If for each
test field the weak profile equation of `B + R (U i)` holds eventually, then some weak limit
`w` of the family along an ultrafilter satisfies the weak profile equation of `B + R w` against
every test field. -/
theorem exists_tested_weakProfile_tendsto_weak {ι T : Type*} (l : Filter ι) [l.NeBot]
    (hBm : AEStronglyMeasurable B volume)
    (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume) (R : H →L[ℝ] H)
    (U : ι → H) (hbounded : Bornology.IsBounded (Set.range U))
    (test : T → ℝ^3 → ℝ^3) (htest : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (test t))
    (htestc : ∀ t, HasCompactSupport (test t))
    (hequation : ∀ t, ∀ᶠ i in l,
      ∫ x, weakProfileDensity (B + Stationary.representative (R (U i))) (test t) x = 0) :
    ∃ (w : H) (F : Ultrafilter ι), (F : Filter ι) ≤ l ∧
      Tendsto (fun i ↦ toWeakSpace ℝ H (U i)) F (𝓝 (toWeakSpace ℝ H w)) ∧
      ∀ t, ∫ x, weakProfileDensity (B + Stationary.representative (R w)) (test t) x = 0 := by
  classical
  choose ψ hψ using fun t ↦ exists_testCutoff (htestc t)
  let linear : T → StrongDual ℝ H := fun t ↦
    (innerSL ℝ (profileAdjointCoordinates hBm hB2 (htest t) (htestc t))).comp
      (Stationary.massCLM.comp R)
  let observe : T → H →L[ℝ] M := fun t ↦ (Stationary.cutoffValues (ψ t)).comp R
  let nonlinear : T → M → ℝ := fun t ↦
    Stationary.testedFlux (Stationary.testGradient (testFieldSobolev (htest t) (htestc t)))
  let forcing : T → ℝ := fun t ↦ -∫ x, weakProfileDensity B (test t) x
  have hkey (t : T) (W : H) :
      ∫ x, weakProfileDensity (B + Stationary.representative (R W)) (test t) x =
        linear t W + nonlinear t (observe t W) - forcing t := by
    rw [integral_weakProfileDensity_add_representative hBm hB2 (htest t) (htestc t) (hψ t)]
    simp only [linear, observe, nonlinear, forcing, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, real_inner_comm (Stationary.massCLM (R W))]
    ring
  have hcompact (t : T) : IsCompactOperator (observe t) :=
    (Stationary.cutoffValues_isCompactOperator (ψ t)).comp_clm R
  have hcontinuous (t : T) : Continuous (nonlinear t) :=
    ((ContinuousLinearMap.l2MatrixTransport _).continuous.inner continuous_id).neg
  obtain ⟨w, F, hle, hweak, hweq⟩ :=
    PDE.Analysis.Variational.exists_tendsto_weak_solution_of_eventually_eq l U hbounded
      linear observe hcompact nonlinear hcontinuous forcing
      (fun t ↦ (hequation t).mono fun i hi ↦ by rw [hkey] at hi; linarith)
  exact ⟨w, F, hle, hweak, fun t ↦ by rw [hkey, hweq t, sub_self]⟩

/-- **The whole-space weak profile equation as a weak limit over an exhausting family of
balls.** Let `B` be even axisymmetric and in `L²_loc`, `R` a bounded reconstruction preserving
the even sector, and `U i` a bounded family of even solenoidal velocities such that
`B + R (U i)` satisfies the weak profile equation against the even tests supported in
`B(0, ρ i)`, with `ρ i → ∞`. Then some weak limit `w` of the family along an ultrafilter is even
and solenoidal and makes `B + R w` an even axisymmetric weak profile. -/
theorem exists_weakProfileEquation_of_ball_tests_tendsto_weak {ι : Type*} (l : Filter ι)
    [l.NeBot] {ρ : ι → ℝ} (hρ : Tendsto ρ l atTop) (hB : IsEvenAxisymmetric B)
    (hBm : AEStronglyMeasurable B volume) (hB2 : LocallyIntegrable (fun x ↦ ‖B x‖ ^ 2) volume)
    (R : H →L[ℝ] H) (hR : ∀ w ∈ evenSectorH1, R w ∈ evenSectorH1)
    (U : ι → H) (hU : ∀ i, U i ∈ evenSectorH1) (hbounded : Bornology.IsBounded (Set.range U))
    (hdiv : ∀ i, Stationary.divergenceCLM (U i) = 0)
    (hequation : ∀ i φ, IsSolenoidalTestField φ → IsEvenAxisymmetric φ →
      tsupport φ ⊆ Metric.ball 0 (ρ i) →
        ∫ x, weakProfileDensity (B + Stationary.representative (R (U i))) φ x = 0) :
    ∃ (w : H) (F : Ultrafilter ι), (F : Filter ι) ≤ l ∧
      Tendsto (fun i ↦ toWeakSpace ℝ H (U i)) F (𝓝 (toWeakSpace ℝ H w)) ∧
      w ∈ evenSectorH1 ∧ Stationary.divergenceCLM w = 0 ∧
      IsEvenAxisymmetric (B + Stationary.representative (R w)) ∧
      WeakProfileEquation (B + Stationary.representative (R w)) := by
  let T := {φ : ℝ^3 → ℝ^3 // IsSolenoidalTestField φ ∧ IsEvenAxisymmetric φ}
  obtain ⟨w, F, hle, hweak, hweq⟩ := exists_tested_weakProfile_tendsto_weak l hBm hB2 R U
    hbounded (fun t : T ↦ t.1) (fun t ↦ t.2.1.1) (fun t ↦ t.2.1.2.1)
    (fun t ↦ (eventually_tsupport_subset_ball hρ t.2.1.2.1).mono fun i hi ↦
      hequation i t.1 t.2.1 t.2.2 hi)
  have hwS : w ∈ evenSectorH1 :=
    Symmetry.mem_evenSectorH1_iff_sectorConstraint.mpr
      (PDE.Analysis.constraints_eq_zero_of_tendsto_weak (Symmetry.sectorConstraint false) hweak
        (Eventually.of_forall fun i ↦ Symmetry.mem_evenSectorH1_iff_sectorConstraint.mp (hU i)))
  have hwdiv : Stationary.divergenceCLM w = 0 :=
    PDE.Analysis.constraints_eq_zero_of_tendsto_weak (fun _ : Unit ↦ Stationary.divergenceCLM)
      hweak (Eventually.of_forall fun i _ ↦ hdiv i) ()
  have hV := Stationary.memLp_representative (R w)
  have heven : IsEvenAxisymmetric (B + Stationary.representative (R w)) :=
    hB.add (mem_evenSectorH1_iff.mp (hR w hwS))
  refine ⟨w, F, hle, hweak, hwS, hwdiv, heven, ?_⟩
  exact WeakProfileEquation.of_symmetric_tests heven (hBm.add hV.aestronglyMeasurable)
    (MeasureTheory.locallyIntegrable_norm_add_sq hBm hV.aestronglyMeasurable hB2
      hV.locallyIntegrable_norm_sq)
    fun φ hφ he ↦ hweq ⟨φ, hφ, he⟩

end Limit

section BallSolution

variable {F : Type*} [Fintype F]

/-- **The exact profile as a limit of ball corrections, with every shared bound** (Hou–Wang–Yang,
Section 4.3, "Taking weak limits"). The data are an even axisymmetric background `B` in
`L²_loc` with weak residual `E` against even tests, finite-rank fields `Φⱼ` (even, solenoidal)
that weakly solve the linearized equation at `B` with right sides `fⱼ`, their restrictions to
the balls `B(0, ρ)`, `ρ ≥ ρ₀` (`hb`, `hq`, `hφB`, `hD₂`, `hfB`), and for each such ball a
solution `u` in the even sector of the corrected profile equation (`hball`, with the profile
form `hprofile` and the finite-rank reconstructions `hR`, `hS`). If
`p ‖u‖ + q ‖∇u‖ ≤ bound p q` for all `p, q ≥ 0` on every ball, then some even solenoidal
whole-space `w` with `p ‖w‖ + q ‖∇w‖ ≤ bound p q` for all `p, q ≥ 0` makes
`B + w + ∑ⱼ ⟪qⱼ, w⟫ Φⱼ` an even axisymmetric weak profile. The zero extensions of the ball
solutions converge weakly along an ultrafilter, and every combination `p ‖·‖ + q ‖∇·‖` is weakly
lower semicontinuous. -/
theorem exists_weakProfileEquation_of_ball_corrections_of_bound {B E : ℝ^3 → ℝ^3}
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
    (bound : ℝ → ℝ → ℝ)
    (hball : ∀ ρ, ρ₀ ≤ ρ → ∃ u ∈ evenSector ρ,
      (∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
        p * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ +
          q * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ≤
            bound p q) ∧
      ∀ v ∈ evenSector ρ, profileForm ρ u v +
        IncompressibleFlow.l4Convection (J ρ) (R ρ (solenoidalL4Embedding (J ρ) u))
          (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) +
        ContinuousLinearMap.transportPairing (R ρ (solenoidalL4Embedding (J ρ) u))
          (S ρ (solenoidalL4Embedding (J ρ) u)) (solenoidalL4Embedding (J ρ) v) =
        -∫ x in Metric.ball (0 : ℝ^3) ρ, ⟪E x, (ZeroBoundaryVectorSpace.toLp
          (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)) : ℝ^3 → ℝ^3) x⟫) :
    ∃ w ∈ evenSectorH1,
      (∀ p q : ℝ, 0 ≤ p → 0 ≤ q →
        p * ‖Stationary.massCLM w‖ + q * ‖Stationary.gradientCLM w‖ ≤ bound p q) ∧
      Stationary.divergenceCLM w = 0 ∧
      IsEvenAxisymmetric (B + Stationary.representative (w + finiteRankCorrection q Φ w)) ∧
      WeakProfileEquation (B + Stationary.representative (w + finiteRankCorrection q Φ w)) := by
  let ρ : ℕ → ℝ := fun n ↦ ρ₀ + n
  have hρ (n : ℕ) : ρ₀ ≤ ρ n := le_add_of_nonneg_right n.cast_nonneg
  have hρt : Tendsto ρ atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  choose u hu hub hueq using fun n ↦ hball (ρ n) (hρ n)
  let U : ℕ → H := fun n ↦ zeroExtendBall (ρ n) (u n : H¹₀(Metric.ball (0 : ℝ^3) (ρ n); ℝ^3))
  have hUb (n : ℕ) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
      p * ‖Stationary.massCLM (U n)‖ + q * ‖Stationary.gradientCLM (U n)‖ ≤ bound p q := by
    rw [norm_massCLM_zeroExtendBall, norm_gradientCLM_zeroExtendBall]
    exact hub n p q hp hq
  have hbounded : Bornology.IsBounded (Set.range U) :=
    Stationary.isBounded_range_of_mass_gradient_bounds U (bound 1 0) (bound 0 1)
      (fun n ↦ by simpa using hUb n 1 0 zero_le_one le_rfl)
      (fun n ↦ by simpa using hUb n 0 1 le_rfl zero_le_one)
  obtain ⟨w, F, -, hweak, hwS, hwdiv, heven, heq⟩ :=
    exists_weakProfileEquation_of_ball_tests_tendsto_weak atTop hρt hB hBm hB2
      (ContinuousLinearMap.id ℝ H + finiteRankCorrection q Φ)
      (fun w hw ↦ add_mem hw (finiteRankCorrection_mem_evenSectorH1 hΦe w)) U
      (fun n ↦ zeroExtendBall_mem_evenSectorH1 (hu n)) hbounded
      (fun n ↦ divergenceCLM_zeroExtendBall (u n).2)
      (fun n φ hφ he hsupp ↦ by
        have hv := hueq n (ballTest hφ hsupp) (ballTest_mem_evenSector hφ hsupp he)
        rw [hprofile _ (hρ n)] at hv
        exact integral_weakProfileDensity_eq_zero_of_ball hBm hB2 q Φ hΦ f (b (ρ n))
          (hb _ (hρ n)) (hbdiv _ (hρ n)) (J (ρ n)) (hJ _ (hρ n)) (qB (ρ n)) (φB (ρ n))
          (fB (ρ n)) (D₂ (ρ n)) (hq _ (hρ n)) (hφB _ (hρ n)) (hD₂ _ (hρ n)) (hfB _ (hρ n))
          (R (ρ n) (solenoidalL4Embedding (J (ρ n)) (u n)))
          (S (ρ n) (solenoidalL4Embedding (J (ρ n)) (u n))) (u n) (hR _ (hρ n) _ (hu n))
          (hS _ (hρ n) _ (hu n)) hφ hsupp (fun j ↦ hΦeq j φ hφ he) (hE φ hφ he) hv)
  exact ⟨w, hwS, fun p q hp hq ↦
    PDE.Analysis.Variational.mul_norm_add_mul_norm_le_of_tendsto_weak Stationary.massCLM
      Stationary.gradientCLM hp hq hweak (Eventually.of_forall fun n ↦ hUb n p q hp hq),
    hwdiv, heven, heq⟩

/-- **The exact profile as a limit of ball corrections, in a box.** The data are those of
`exists_weakProfileEquation_of_ball_corrections_of_bound`. If every ball `B(0, ρ)`, `ρ ≥ ρ₀`, has
a solution `u` in the even sector of the corrected profile equation with `‖u‖ ≤ r₀` and
`‖∇u‖ ≤ r₁`, then some even solenoidal whole-space `w` with the same radii makes
`B + w + ∑ⱼ ⟪qⱼ, w⟫ Φⱼ` an even axisymmetric weak profile. This is the bound `s r₀ + t r₁` of
`exists_weakProfileEquation_of_ball_corrections_of_bound`, read at `(s, t) = (1, 0)` and
`(0, 1)`. -/
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
  obtain ⟨w, hwS, hwb, hwdiv, heven, heq⟩ :=
    exists_weakProfileEquation_of_ball_corrections_of_bound hB hBm hB2 hE q Φ f hΦ hΦe hΦeq ρ₀ b
      hb hbdiv J hJ R S profileForm qB φB fB D₂ hq hφB hD₂ hfB hR hS hprofile
      (fun s t ↦ s * r₀ + t * r₁) fun ρ hρ ↦ by
        obtain ⟨u, hu, hu₀, hu₁, hueq⟩ := hball ρ hρ
        exact ⟨u, hu, fun s t hs ht ↦ add_le_add (mul_le_mul_of_nonneg_left hu₀ hs)
          (mul_le_mul_of_nonneg_left hu₁ ht), hueq⟩
  exact ⟨w, hwS, by simpa using hwb 1 0 zero_le_one le_rfl,
    by simpa using hwb 0 1 le_rfl zero_le_one, hwdiv, heven, heq⟩

end BallSolution

end NavierStokes.Nonuniqueness
