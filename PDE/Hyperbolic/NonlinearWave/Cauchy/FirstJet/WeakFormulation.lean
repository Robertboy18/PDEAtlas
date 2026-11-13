/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.EnergySolution

/-!
# Weak PDE and time derivatives for first-jet nonlinear waves

For the global energy solution, the velocity is the L² time derivative
of the displacement, with a right derivative at zero
(`IsEnergySolutionOn.hasDerivWithinAt_displacement`). Its derivative in the
H¹ dual is `Δu - f(Du,u_t,u)`. On every finite interval the same curve satisfies
the Bochner weak-wave formulation, with both Cauchy traces and the
first-derivative load. Spatial tests pair with the Sobolev weak gradient.

The data are whole-space energy data (Evans, §12.2.1, Theorem 1(i)), and the Bochner
formulation is the whole-space form of the weak solution Evans defines at the start of §12.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2, definition of a weak solution; §12.2.1, Theorem 1(i).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert Interval Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- The acceleration is exactly the spatial distribution `Δu - f(Du,v,u)`, tested
against an arbitrary H¹ function. -/
theorem acceleration_apply (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) (w : H¹(ℝ^n)) :
    acceleration hf hf0 z w = -((∑ i : Fin n, ⟪z.1.val (singleDerivIndex n i), w.val
      (singleDerivIndex n i)⟫_ℝ) + ⟪reaction hf hf0 z, (energyTriple n).inclusion w⟫_ℝ) := by
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
          (reaction hf hf0 (u t))) ∧
      (q : ℝ → H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).1) ∧
      (p : ℝ → DerivLp n 2 univ) =ᵐ[volume.restrict (Ioc 0 b)] (fun t ↦ (u t).2) ∧
      (a : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 b)]
        (fun t ↦ acceleration hf hf0 (u t)) ∧
      IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ gradientForm n)
        ell q p a x.1 x.2 := by
  have hell : Continuous fun z : H¹(ℝ^n) × DerivLp n 2 univ ↦
      -(energyTriple n).pivotToDual (reaction hf hf0 z) :=
    ((energyTriple n).pivotToDual.continuous.comp (reaction_lipschitz hf hf0).continuous).neg
  exact IsEnergySolutionOn.weakWave_on h hell (fun _ ↦ rfl) hb

/-- The weak semilinear PDE against every spatial H¹ test and every endpoint
time test. The gradient and first-jet reaction are explicit, and the initial
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
          ⟪reaction hf hf0 (u t),
            (energyTriple n).inclusion w⟫_ℝ) * τ.toFun t) =
      ⟪x.2, (energyTriple n).inclusion w⟫_ℝ * τ.toFun 0 := by
  have hid := IsEnergySolutionOn.weak_pde h (continuous_acceleration hf hf0) hb w τ
  simp only [acceleration_apply, neg_mul, intervalIntegral.integral_neg] at hid
  linarith

variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}
variable {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ}

/-- The integrated PDE gives the H¹-dual acceleration, including at zero. This is
`IsEnergySolutionOn.hasDerivWithinAt_velocity` for the continuous first-jet acceleration. -/
theorem IsEnergySolution.hasDerivWithinAt_velocity (h : IsEnergySolution hf hf0 x u)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s ↦ (energyTriple n).pivotToDual (u s).2)
      (acceleration hf hf0 (u t)) (Ici 0) t :=
  IsEnergySolutionOn.hasDerivWithinAt_velocity h (continuous_acceleration hf hf0) ht

/-- At every positive time the velocity is differentiable in the H¹ dual. This is
`IsEnergySolutionOn.hasDerivAt_velocity` for the continuous first-jet acceleration. -/
theorem IsEnergySolution.hasDerivAt_velocity (h : IsEnergySolution hf hf0 x u)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ (energyTriple n).pivotToDual (u s).2) (acceleration hf hf0 (u t)) t :=
  IsEnergySolutionOn.hasDerivAt_velocity h (continuous_acceleration hf hf0) ht

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
