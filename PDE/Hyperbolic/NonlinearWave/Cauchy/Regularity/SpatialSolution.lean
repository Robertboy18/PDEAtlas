/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.EllipticResolvent
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.StrongSolution

/-!
# Global H² × H¹ solutions of the whole-space semilinear wave equation

For H² displacement and H¹ velocity data, the already constructed global
energy solution has displacement continuous in H², velocity continuous in H¹,
and acceleration continuous in L². The equation holds in spatial L² at every
nonnegative time, and the displacement is C² in time with values in L² on
positive times.

The assumptions are a C¹ globally Lipschitz scalar nonlinearity with `f(0) = 0`,
in arbitrary spatial dimension. Spatial H² continuity is derived by applying
the constructed continuous inverse of `1 - Δ` to `u - f(u) - u_tt`.

These are strong Sobolev solutions. Higher spatial propagation and pointwise
classical regularity require further results; smoothness of the initial data
alone is not used to claim those conclusions here.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n : ℕ} {f : ℝ → ℝ} {L : NNReal}
  {hf : LipschitzWith L f} {hf0 : f 0 = 0}
  {x : H¹(ℝ^n) × DerivLp n 2 univ}
  {u d : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}

/-- The displacement of a strong energy solution has a continuous H² lift.
Its Laplacian is the L² acceleration plus the nonlinear reaction. -/
theorem IsStrongEnergySolution.exists_continuous_h2
    (h : IsStrongEnergySolution hf hf0 x u d) :
    ∃ U : C(ℝ, W^{2,2}(ℝ^n)), ∀ t : ℝ, 0 ≤ t →
      lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (u t).1 ∧
        (d t).2 = Δ (U t) - hf.compLp hf0 (wkpBaseCoordinateCLM (U t)) := by
  let b : C(ℝ, DerivLp n 2 univ) := ⟨fun t ↦ source hf hf0 (u t).1 - (d t).2,
      ((source_lipschitz hf hf0).continuous.comp u.continuous.fst).sub d.continuous.snd⟩
  let U : C(ℝ, W^{2,2}(ℝ^n)) := ⟨fun t ↦ (massiveLaplacianEquiv n).symm (b t),
      (massiveLaplacianEquiv n).symm.continuous.comp b.continuous⟩
  refine ⟨U, fun t ht ↦ ?_⟩
  have hm : massForm n (u t).1 = (energyTriple n).pivotToDual (b t) := by
    have heq := h.acceleration_eq t ht
    rw [← source_sub_massForm] at heq
    change massForm n (u t).1 = (energyTriple n).pivotToDual (source hf hf0 (u t).1 - (d t).2)
    rw [map_sub, heq]
    abel
  have hlow : lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (u t).1 :=
    lowerOrder_massiveLaplacianEquiv_symm (u t).1 (b t) hm
  refine ⟨hlow, ?_⟩
  have hbase : wkpBaseCoordinateCLM (U t) = (energyTriple n).inclusion (u t).1 :=
    congrArg (energyTriple n).inclusion hlow
  have hres : wkpBaseCoordinateCLM (U t) - Δ (U t) = b t :=
    (massiveLaplacianEquiv n).apply_symm_apply (b t)
  change wkpBaseCoordinateCLM (U t) - Δ (U t) = (energyTriple n).inclusion (u t).1 -
      hf.compLp hf0 ((energyTriple n).inclusion (u t).1) - (d t).2 at hres
  rw [hbase] at hres ⊢
  rw [sub_sub] at hres
  have hsum := sub_right_inj.mp hres
  rw [hsum]
  abel

/-- H² × H¹ data give a global solution with continuous H² displacement,
continuous H¹ velocity and continuous L² acceleration. The spatial equation
holds in L², and uniqueness holds among all natural energy solutions.
All regularity is derived from the initial data and the scalar nonlinearity. -/
theorem exists_unique_h2EnergySolution (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (hreg : ContDiff ℝ 1 f) (u₀ : W^{2,2}(ℝ^n)) (v₀ : H¹(ℝ^n)) :
    ∃ u d : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      ∃ U : C(ℝ, W^{2,2}(ℝ^n)),
        IsStrongEnergySolution hf hf0
          (lowerOrderCLM (by decide : 1 ≤ 2) u₀, (energyTriple n).inclusion v₀) u d ∧
        U 0 = u₀ ∧
        (∀ t : ℝ, 0 ≤ t →
          lowerOrderCLM (by decide : 1 ≤ 2) (U t) = (u t).1 ∧
            (d t).2 = Δ (U t) - hf.compLp hf0 (wkpBaseCoordinateCLM (U t))) ∧
        ∀ v : ℝ → H¹(ℝ^n) × DerivLp n 2 univ,
          IsEnergySolution hf hf0
            (lowerOrderCLM (by decide : 1 ≤ 2) u₀, (energyTriple n).inclusion v₀) v →
              EqOn u v (Ici 0) := by
  obtain ⟨u, d, h, huniq⟩ := exists_unique_strongEnergySolution hf hf0 hreg u₀ v₀
  obtain ⟨U, hU⟩ := h.exists_continuous_h2
  refine ⟨u, d, U, h, ?_, hU, huniq⟩
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  have hlow := (hU 0 le_rfl).1
  rw [h.initial] at hlow
  exact congrArg (energyTriple n).inclusion hlow

end PDE.Hyperbolic.NonlinearWave.Cauchy
