/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.BallCorrection
public import PDE.Analysis.Variational.ScalarFeedback
public import PDE.Analysis.Variational.WeakLimitSolution

/-!
# Scalar-feedback problems on an exhausting family of balls, and their weak limit

An eigenvalue problem near an approximate eigenpair is solved on the balls `B(0, ρ)`, with the
eigenvalue correction a linear functional `ℓ(u)` of the unknown. This module shows that the
solutions on the balls have a weak limit in the whole space that solves the tested equations and
stays in the weighted energy ball. The forms on the balls, their bounds and the identification of
the tested equations with whole-space functionals are hypotheses. The limit is returned as a weak
limit, so that the caller can read off the linear constraints of the ball solutions (a symmetry
sector, orthogonality to a field, zero divergence).

## Main results

* `exists_tendsto_weak_of_ball_scalar_feedback`: for forms on the balls with the stated bounds
  and a capacity condition that does not depend on the ball, some weak limit `w` of zero
  extensions of ball solutions lies in the weighted energy ball and satisfies
  `lin t w - ℓ w · coef t w = forcing t` for every test `t`.

## How it works

On every ball the problem `B u - ℓ(u) C u = f` has a solution strictly inside the weighted energy
ball (`PDE.Analysis.Variational.exists_solution_of_scalar_feedback_on_submodule`), with the
compact inclusion of the solenoidal zero-boundary fields into `L⁴` as the weaker space. The radius
does not depend on the ball, so the zero extensions are bounded in `H¹(ℝ³)` and have a weak limit
along an ultrafilter. If a tested equation on the balls is, for large balls, the value at the zero
extension of fixed bounded linear functionals of the whole space, it passes to the limit
(`PDE.Analysis.Variational.exists_tendsto_weak_solution_of_scalar_feedback`): bounded linear
functionals are weakly continuous, and the scalar `ℓ(u)` converges with them. The weighted ball
passes to the limit through its support function. The companion theorem for a transport
nonlinearity, where the limit needs a compact observation, is
`exists_weakProfileEquation_of_weighted_ball`.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.4: the map (4.48), the
  ball (4.60), the fixed point and "Taking weak limits".
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

open NavierStokes.Symmetry

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))
local notation "Vb" ρ => IncompressibleFlow.SolenoidalSpace
  (ZeroBoundaryVectorSpace.divergence (n := 3) (Ω := Metric.ball (0 : ℝ^3) ρ))

-- The cached norms of `SimilarityTransport`, before the mixed Lebesgue operator spaces.
attribute [local instance] innerProductSpaceSolenoidal normedSpaceSolenoidal
  completeSpaceSolenoidal normedAddCommGroupSolenoidal seminormedAddCommGroupSolenoidal
  normedAddCommGroupL4Field normedSpaceL4Field seminormedAddCommGroupL4Field
  normedAddCommGroupSolenoidalDual seminormedAddCommGroupSolenoidalDual

/-- **Scalar-feedback problems on balls and their weak limit** (Hou–Wang–Yang, Section 4.4).
For every `ρ ≥ ρ₀` let `S ρ` be a closed subspace of the solenoidal zero-boundary fields of
`B(0, ρ)`, and let `B ρ`, `C ρ`, `ell ρ` be forms and a load on the ball with, on `S ρ`:
the lower bound `a ‖u‖² + b ‖∇u‖² - c ‖u‖ ‖∇u‖ ≤ B u u`, `|C u u| ≤ Θ ‖u‖²` and
`|ell v| ≤ ε ‖v‖`. Let `ℓ` be a bounded linear functional of whole-space `H¹` velocities that, on
the zero extensions of the fields of `S ρ`, is at most `Λ` on the weighted ball
`η ‖u‖² + ‖∇u‖² ≤ r²` and at most `γ ρ` times the `L⁴` norm on the ball; the constant `γ ρ` may
depend on the ball. Under the capacity condition

`b > c / (2 √η)`,  `(a - Θ Λ - η b) (b - c / (2 √η)) > ε² / (4 r²)`,

each ball has a solution `u ∈ S ρ` of `B u v - ℓ(u) C u v = ell v`, `v ∈ S ρ`, strictly inside
the weighted ball. If each test `t` is eventually represented on the balls by a field
`g ∈ S ρ` with `B u g = lin t u`, `C u g = coef t u` and `ell g = forcing t` on zero extensions,
then some weak limit `w` of zero extensions of ball solutions lies in the weighted ball, has
weighted energy at most `ε² / (4 (a - Θ Λ - η b) (b - c / (2 √η)))`, and satisfies
`lin t w - ℓ w · coef t w = forcing t` for every `t`. -/
theorem exists_tendsto_weak_of_ball_scalar_feedback {T : Type*} (ρ₀ : ℝ)
    (S : ∀ ρ : ℝ, Submodule ℝ (Vb ρ)) (hS : ∀ ρ, ρ₀ ≤ ρ → IsClosed (S ρ : Set (Vb ρ)))
    (J : ∀ ρ : ℝ, H¹₀(Metric.ball (0 : ℝ^3) ρ) →L[ℝ] DerivLp 3 4 (Metric.ball (0 : ℝ^3) ρ))
    (hinj : ∀ ρ, ρ₀ ≤ ρ → Function.Injective (J ρ))
    (hcompact : ∀ ρ, ρ₀ ≤ ρ → IsCompactOperator (J ρ))
    (B C : ∀ ρ : ℝ, (Vb ρ) →L[ℝ] StrongDual ℝ (Vb ρ)) (ell : ∀ ρ : ℝ, StrongDual ℝ (Vb ρ))
    (ℓ : StrongDual ℝ H)
    {a b c η r ε Θ Λ : ℝ} {γ : ℝ → ℝ} (hη : 0 < η) (hr : 0 < r) (hc : 0 ≤ c)
    (hγ : ∀ ρ, ρ₀ ≤ ρ → 0 ≤ γ ρ)
    (hcoercive : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ S ρ,
      a * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 +
        b * ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 -
        c * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ *
          ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ≤
            B ρ u u)
    (hC : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ S ρ, |C ρ u u| ≤
      Θ * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2)
    (hℓ : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ S ρ,
      η * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 +
        ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 ≤
          r ^ 2 →
      |ℓ (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)))| ≤ Λ)
    (hℓweak : ∀ ρ, ρ₀ ≤ ρ → ∀ u ∈ S ρ,
      |ℓ (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)))| ≤
        γ ρ * ‖solenoidalL4Embedding (J ρ) u‖)
    (hell : ∀ ρ, ρ₀ ≤ ρ → ∀ v ∈ S ρ, |ell ρ v| ≤
      ε * ‖ZeroBoundaryVectorSpace.toLp (v : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖)
    (hb : c / (2 * √η) < b)
    (hcap : ε ^ 2 / (4 * r ^ 2) < (a - Θ * Λ - η * b) * (b - c / (2 * √η)))
    (lin coef : T → StrongDual ℝ H) (forcing : T → ℝ)
    (htest : ∀ t, ∃ ρ₁, ∀ ρ, ρ₁ ≤ ρ → ρ₀ ≤ ρ → ∃ g ∈ S ρ, ell ρ g = forcing t ∧
      ∀ u ∈ S ρ, B ρ u g = lin t (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))) ∧
        C ρ u g = coef t (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)))) :
    ∃ (w : H) (U : ℕ → H) (F : Ultrafilter ℕ),
      (∀ n, ∃ ρ, ρ₀ ≤ ρ ∧ ∃ u ∈ S ρ,
        U n = zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (U n)) F (𝓝 (toWeakSpace ℝ H w)) ∧
      η * ‖Stationary.massCLM w‖ ^ 2 + ‖Stationary.gradientCLM w‖ ^ 2 ≤
        min (r ^ 2) (ε ^ 2 / (4 * (a - Θ * Λ - η * b) * (b - c / (2 * √η)))) ∧
      ∀ t, lin t w - ℓ w * coef t w = forcing t := by
  -- A solution on every ball, strictly inside the weighted ball.
  have hexists (ρ : ℝ) (hρ : ρ₀ ≤ ρ) : ∃ u ∈ S ρ,
      η * ‖ZeroBoundaryVectorSpace.toLp (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 +
        ‖ZeroBoundaryVectorSpace.gradient (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))‖ ^ 2 ≤
          min (r ^ 2) (ε ^ 2 / (4 * (a - Θ * Λ - η * b) * (b - c / (2 * √η)))) ∧
      ∀ v ∈ S ρ, B ρ u v -
        ℓ (zeroExtendBall ρ (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3))) * C ρ u v = ell ρ v := by
    let inc := (ZeroBoundaryVectorSpace.divergence (n := 3)
      (Ω := Metric.ball (0 : ℝ^3) ρ)).ker.subtypeL
    let e := solenoidalL4Embedding (J ρ)
    have he : Function.Injective e := by
      intro u v huv
      apply Subtype.ext
      exact IncompressibleFlow.vectorL4Embedding_injective (J ρ) (hinj ρ hρ) huv
    have hecompact : IsCompactOperator e :=
      (IncompressibleFlow.vectorL4Embedding_isCompactOperator (J ρ) (hcompact ρ hρ)).comp_clm
        inc
    obtain ⟨u, hu, hlt, hle, heq⟩ :=
      PDE.Analysis.Variational.exists_solution_of_scalar_feedback_on_submodule (S ρ)
      (hS ρ hρ) (ZeroBoundaryVectorSpace.toLp.comp inc)
      (ZeroBoundaryVectorSpace.gradient.comp inc)
      (fun u _ ↦ ZeroBoundaryVectorSpace.norm_sq (u : H¹₀(Metric.ball (0 : ℝ^3) ρ; ℝ^3)))
      (B ρ) (C ρ) (ℓ.comp ((zeroExtendBall ρ).comp inc)) (ell ρ) e he.injOn hecompact
      hη hr hc (hγ ρ hρ) (hcoercive ρ hρ) (hC ρ hρ)
      (hℓ ρ hρ)
      (hℓweak ρ hρ) (hell ρ hρ) hb hcap
    exact ⟨u, hu, le_min hlt.le hle, heq⟩
  let ρ : ℕ → ℝ := fun n ↦ ρ₀ + n
  have hρ (n : ℕ) : ρ₀ ≤ ρ n := le_add_of_nonneg_right n.cast_nonneg
  have hρt : Tendsto ρ atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  choose u hu hub hueq using fun n ↦ hexists (ρ n) (hρ n)
  let U : ℕ → H := fun n ↦ zeroExtendBall (ρ n) (u n : H¹₀(Metric.ball (0 : ℝ^3) (ρ n); ℝ^3))
  obtain ⟨m, hm⟩ : ∃ m : ℝ,
      m = min (r ^ 2) (ε ^ 2 / (4 * (a - Θ * Λ - η * b) * (b - c / (2 * √η)))) := ⟨_, rfl⟩
  have hUb (n : ℕ) :
      η * ‖Stationary.massCLM (U n)‖ ^ 2 + ‖Stationary.gradientCLM (U n)‖ ^ 2 ≤ m := by
    rw [hm, norm_massCLM_zeroExtendBall, norm_gradientCLM_zeroExtendBall]
    exact hub n
  have hm0 : 0 ≤ m := le_trans (by positivity) (hUb 0)
  have hmr : m ≤ r ^ 2 := hm ▸ min_le_left _ _
  have hbounded : Bornology.IsBounded (Set.range U) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨r / √η + r, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact PDE.Analysis.Variational.norm_le_of_mem_weightedEnergyBall hη hr.le
      (Stationary.norm_sq_eq_mass_add_gradient (U n)) ((hUb n).trans hmr)
  obtain ⟨w, F, -, hweak, hweq⟩ :=
    PDE.Analysis.Variational.exists_tendsto_weak_solution_of_scalar_feedback atTop U hbounded ℓ
      lin coef forcing (fun t ↦ by
        obtain ⟨ρ₁, hρ₁⟩ := htest t
        filter_upwards [hρt.eventually_ge_atTop ρ₁] with n hn
        obtain ⟨g, hg, hforce, hlin⟩ := hρ₁ (ρ n) hn (hρ n)
        obtain ⟨hB, hCc⟩ := hlin (u n) (hu n)
        have h := hueq n g hg
        rw [hB, hCc, hforce] at h
        exact h)
  refine ⟨w, U, F, fun n ↦ ⟨ρ n, hρ n, u n, hu n, rfl⟩, hweak, ?_, hweq⟩
  -- The weighted ball of radius `√m` passes to the limit through its support function.
  have hsq : √m ^ 2 = m := Real.sq_sqrt hm0
  rw [← hm, ← hsq]
  exact PDE.Analysis.Variational.weighted_energy_le_of_forall_mul_add_mul_le hη
    (Real.sqrt_nonneg m) (norm_nonneg _) (norm_nonneg _) fun p q hp hq ↦
      PDE.Analysis.Variational.mul_norm_add_mul_norm_le_of_tendsto_weak Stationary.massCLM
        Stationary.gradientCLM hp hq hweak (Eventually.of_forall fun n ↦
          PDE.Analysis.Variational.mul_add_mul_le_of_weighted_energy_le hη (Real.sqrt_nonneg m)
            (by rw [hsq]; exact hUb n) p q)

end NavierStokes.Nonuniqueness
