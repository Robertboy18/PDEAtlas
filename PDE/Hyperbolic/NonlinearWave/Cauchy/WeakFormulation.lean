/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Lipschitz

/-!
# Spatial and temporal weak equations for the constructed Cauchy solution

For every dimension `n`, every globally Lipschitz `f : ℝ → ℝ` with `f 0 = 0`,
and every initial state in `H¹(ℝ^n) × L²(ℝ^n)`,
`exists_unique_energySolution` constructs a forward global energy solution of
`u_tt - Δu + f(u) = 0`. It gives strong initial data and uniqueness among all
forward energy-continuous solutions of the two integrated PDE equations.

The acceleration pairs a spatial H¹ test with `-∇u · ∇w - f(u)w`. On each
finite time interval, the energy solution has Bochner displacement, velocity,
and acceleration classes satisfying the weak-wave predicate, with the
nonlinear load and both initial data identified.

We also state the scalar weak PDE directly: integration by parts moves the time
derivative of the velocity onto the time test, while the spatial term is the sum
of L² pairings of the weak derivatives. No formal differential-operator symbols
or assumed residual identities replace these pairings.

In the notation of Evans, §12.2, `IsEnergySolution.weakWave_on` shows that an energy solution is a
weak solution of (1) with `f = f(u)`: on each interval `(0, b]` we have `u ∈ L²(0, b; H¹)`,
`u' ∈ L²(0, b; L²)` and `u'' ∈ L²(0, b; H⁻¹)`, and `⟨u'', v⟩ + B[u, v] = (f, v)` for the load
`f = -f(u)` and `B[u, v] = ∫ Du · Dv dx`, for every `v ∈ H¹(ℝⁿ)` and not only for those with
compact support. `IsEnergySolution.weak_pde` is this identity integrated against a time test.

The dense whole-space inclusion `H¹ ↪ L²` and the coercive form
`B(u,w) = ∫ (u w + ∇u · ∇w)` construct the massive wave generator and its
semigroup through Lax–Milgram and Hille–Yosida theory. The source `u - f(u)`
cancels the auxiliary mass. Iterated Picard estimates give infinite forward
lifetime. Linear weak-wave uniqueness identifies every energy solution with
this mild evolution, so fixed-point uniqueness yields PDE uniqueness.

The data need no smallness, sign, compact support, or additional regularity.
The condition `f 0 = 0` makes composition preserve L² on the infinite-measure
whole space. Negative-time values are a continuous extension used for integrals.
The energy theorem neither assumes nor concludes higher Sobolev or classical regularity; those
are separate results.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2, equation (1) and the definition of a weak solution;
  §12.2.1, Theorem 1; §6.2.1, Theorem 1 (Lax–Milgram); §7.4.2, Theorem 4 (Hille–Yosida).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : ℝ → ℝ} {L : NNReal}

/-- The acceleration is exactly the spatial distribution `Δu - f(u)`, tested
against an arbitrary H¹ function. -/
theorem acceleration_apply (hf : LipschitzWith L f) (hf0 : f 0 = 0) (u w : H¹(ℝ^n)) :
    acceleration hf hf0 u w = -((∑ i : Fin n, ⟪u.val (singleDerivIndex n i),
      w.val (singleDerivIndex n i)⟫_ℝ) + ⟪hf.compLp hf0 ((energyTriple n).inclusion u),
      (energyTriple n).inclusion w⟫_ℝ) := by
  simp only [acceleration, sub_apply, neg_apply, GelfandTriple.pivotToDual_apply,
    gradientForm_apply]
  abel

/-- Every finite restriction has the standard Bochner weak-wave formulation,
with the nonlinear load, displacement, velocity, acceleration, and initial data
all identified. This is a weak PDE statement in the whole-space Gelfand triple. -/
theorem IsEnergySolution.weakWave_on {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0 x u) {b : ℝ} (hb : 0 < b) :
    ∃ (ell : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 b)))
      (q : Lp H¹(ℝ^n) 2 (volume.restrict (Ioc 0 b)))
      (p : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc 0 b)))
      (a : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 b))),
      (ell : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 b)]
        (fun t ↦ -(energyTriple n).pivotToDual
          (hf.compLp hf0 ((energyTriple n).inclusion (u t).1))) ∧
      (q : ℝ → H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).1) ∧
      (p : ℝ → DerivLp n 2 univ) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).2) ∧
      (a : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 b)]
        (fun t ↦ acceleration hf hf0 (u t).1) ∧
      IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ gradientForm n)
        ell q p a x.1 x.2 := by
  have hcomp := hf.lipschitzWith_compLp hf0 (μ := domainMeasure n univ) (p := 2)
  have hell : Continuous fun z : H¹(ℝ^n) × DerivLp n 2 univ ↦
      -(energyTriple n).pivotToDual (hf.compLp hf0 ((energyTriple n).inclusion z.1)) :=
    ((energyTriple n).pivotToDual.continuous.comp
      (hcomp.continuous.comp ((energyTriple n).inclusion.continuous.comp continuous_fst))).neg
  exact IsEnergySolutionOn.weakWave_on h hell (fun _ ↦ rfl) hb

/-- The weak semilinear PDE against every spatial H¹ test and every endpoint
time test. The gradient and scalar reaction are explicit, and the initial
velocity occurs in the boundary term. The displacement trace and the identity
`u_t = v` are recorded by `IsEnergySolution.initial` and `.displacement`. -/
theorem IsEnergySolution.weak_pde {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0 x u) {b : ℝ} (hb : 0 ≤ b) (w : H¹(ℝ^n)) (τ : TimeTest 0 b) :
    -(∫ t in (0 : ℝ)..b, ⟪(u t).2, (energyTriple n).inclusion w⟫_ℝ *
        τ.derivFun t) +
      (∫ t in (0 : ℝ)..b,
        ((∑ i : Fin n,
            ⟪(u t).1.val (singleDerivIndex n i),
              w.val (singleDerivIndex n i)⟫_ℝ) +
          ⟪hf.compLp hf0 ((energyTriple n).inclusion (u t).1),
            (energyTriple n).inclusion w⟫_ℝ) * τ.toFun t) =
      ⟪x.2, (energyTriple n).inclusion w⟫_ℝ * τ.toFun 0 := by
  have hid := IsEnergySolutionOn.weak_pde h
    ((continuous_acceleration hf hf0).comp continuous_fst) hb w τ
  simp only [acceleration_apply, neg_mul, intervalIntegral.integral_neg] at hid
  linarith

end PDE.Hyperbolic.NonlinearWave.Cauchy
