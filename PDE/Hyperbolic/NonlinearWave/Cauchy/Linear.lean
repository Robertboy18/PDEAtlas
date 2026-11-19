/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Spaces
public import PDE.Hyperbolic.NonlinearWave.Cauchy.ObservedEvolution
public import PDE.Hyperbolic.WeakWave.IntegratedTrajectory

/-!
# Constructed whole-space linear wave evolution

Lax–Milgram and Hille–Yosida construct the evolution for `u_tt - Δu + u = f`
on the full space `H¹(ℝ^n) × L²(ℝ^n)`. Its generator graph contains exactly the
two weak first-order equations. The observation argument extends those equations
to every energy datum and every continuous L² force.

The mass term is retained here to use the full coercive H¹ norm. The semilinear
construction cancels it in the forcing. Neither a bounded-domain spectrum nor an
externally supplied solution operator enters this construction.

`linearSemigroup` is the semigroup of Evans, §7.4.3, Theorem 6, for `L = -Δ + 1` on `ℝⁿ`, with
`H¹(ℝⁿ) × L²(ℝⁿ)` in place of `H¹₀(U) × L²(U)`. It is `waveContractionSemigroup` for the form
`B(u, w) = ∫ (u w + ∇u · ∇w)`, which is coercive on `H¹(ℝⁿ)` as (35) requires.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.3, Theorem 6; §7.4.2, Theorem 4 (Hille–Yosida);
  §6.2.1, Theorem 1 (Lax–Milgram).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ}

/-- Displacement and velocity with the Hilbert norm
`(‖u‖²_H¹ + ‖v‖²_L²)^(1/2)`, equivalent to the ordinary product norm. -/
abbrev EnergyState (n : ℕ) :=
  WaveEnergySpace (H := DerivLp n 2 univ) (massForm n)
    (massForm_coercive n) massForm_symmetric

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The whole-space massive wave semigroup constructed from its weak generator,
using the resolvent furnished by Lax–Milgram. -/
def linearSemigroup (n : ℕ) : StronglyContinuousSemigroup (EnergyState n) :=
  waveContractionSemigroup (energyTriple n) (massForm n)
    (massForm_coercive n) massForm_symmetric

/-- The constructed generator has exactly the kinematic and weak acceleration
equations, including its domain. -/
theorem linearSemigroup_generator {x y : EnergyState n}
    (h : (linearSemigroup n).HasGeneratorAt x y) :
    (energyTriple n).inclusion (C y).1 = (C x).2 ∧
      massForm n (C x).1 = -(energyTriple n).pivotToDual (C y).2 := by
  have hg := ((linearSemigroup n).hasGeneratorAt_iff_mem_generatorPMap_graph x y).mp h
  change (x, y) ∈ (waveContractionSemigroup (energyTriple n) (massForm n)
    (massForm_coercive n) massForm_symmetric).generatorPMap.graph at hg
  rw [generatorPMap_waveContractionSemigroup] at hg
  exact (mem_waveOperator_graph_iff _ _ _ _ x y).mp hg

/-- The generator domain is dense in the whole energy space. -/
theorem linearSemigroup_dense_domain (n : ℕ) :
    Dense ((linearSemigroup n).generatorPMap.domain : Set (EnergyState n)) := by
  change Dense ((waveContractionSemigroup (energyTriple n) (massForm n)
    (massForm_coercive n) massForm_symmetric).generatorPMap.domain : Set (EnergyState n))
  rw [generatorPMap_waveContractionSemigroup]
  exact dense_waveOperator_domain _ _ _ _

/-- Arbitrary energy data and continuous L² forcing satisfy both integrated
whole-space equations. In particular, velocity is the time derivative of
displacement in L², and acceleration is `f - (1 - Δ)u` in the H¹ dual. -/
theorem linear_forced_integral {f : ℝ → DerivLp n 2 univ} (hf : Continuous f) (x : EnergyState n)
    {t : ℝ} (ht : 0 ≤ t) :
    let z := fun s ↦ (linearSemigroup n).realOrbit x s +
      (linearSemigroup n).duhamel (fun r ↦ (C).symm (0, f r)) s
    (∫ s in (0 : ℝ)..t, (C (z s)).2) =
        (energyTriple n).inclusion (C (z t)).1 - (energyTriple n).inclusion (C x).1 ∧
      (∫ s in (0 : ℝ)..t,
        (energyTriple n).pivotToDual (f s) - massForm n (C (z s)).1) =
        (energyTriple n).pivotToDual (C (z t)).2 -
          (energyTriple n).pivotToDual (C x).2 := by
  let P : EnergyState n →L[ℝ] H¹(ℝ^n) :=
    (ContinuousLinearMap.fst ℝ _ _).comp (C).toContinuousLinearMap
  let V : EnergyState n →L[ℝ] DerivLp n 2 univ :=
    (ContinuousLinearMap.snd ℝ _ _).comp (C).toContinuousLinearMap
  have hforce : Continuous (fun r ↦ (C).symm (0, f r)) :=
    (C).symm.continuous.comp (continuous_const.prodMk hf)
  have hq := observed_forced_integral (linearSemigroup n)
    ((energyTriple n).inclusion.comp P) V (linearSemigroup_dense_domain n)
    (fun a b h ↦ (linearSemigroup_generator h).1) hforce x ht
  have hp := observed_forced_integral (linearSemigroup n)
    ((energyTriple n).pivotToDual.comp V) (-(massForm n).comp P) (linearSemigroup_dense_domain n)
    (fun a b h ↦ by
      have h' := (linearSemigroup_generator h).2
      change (energyTriple n).pivotToDual (C b).2 = -(massForm n (C a).1)
      exact neg_eq_iff_eq_neg.mp h'.symm) hforce x ht
  constructor
  · simpa only [P, V, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, map_zero, add_zero] using hq
  · simpa only [P, V, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, neg_apply, neg_add_eq_sub] using hp

end PDE.Hyperbolic.NonlinearWave.Cauchy
