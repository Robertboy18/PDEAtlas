/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Composition
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.InitialDomain
public import PDE.Hyperbolic.NonlinearWave.Cauchy.WeakFormulation

/-!
# Strong time regularity of the nonlinear wave energy solution

H² × H¹ initial data and a globally Lipschitz `C¹` nonlinearity fixing zero
give a continuous time derivative in H¹ × L². The regularity is derived for
every energy solution, using its mild representation and the H¹ chain rule.
In particular, the constructed global energy solution has H¹ velocity and L²
acceleration at every nonnegative time.

This is a strong Sobolev time-regularity statement in arbitrary dimension.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology Interval Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : ℝ → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The global energy equation determines the constructed mild trajectory at each
nonnegative time. This uses only energy continuity and the integrated weak PDE: it is
`IsEnergySolutionOn.mild_eq` on `[0, t + 1]` for the force `u - f(u)`. -/
theorem IsEnergySolution.mild_eq {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0 x u) {t : ℝ} (ht : 0 ≤ t) :
    (C).symm (u t) = (linearSemigroup n).realOrbit ((C).symm x) t +
      (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, source hf hf0 (u s).1)) t :=
  IsEnergySolutionOn.mild_eq (F := fun z ↦ source hf hf0 z.1) (b := t + 1)
    (h.mono Icc_subset_Ici_self) ((source_lipschitz hf hf0).continuous.comp continuous_fst)
    (fun z ↦ source_sub_massForm hf hf0 z.1) (add_pos_of_nonneg_of_pos ht zero_lt_one)
    ⟨ht, le_add_of_nonneg_right zero_le_one⟩

/-- Regular initial data force a continuous strong derivative of every energy
solution. The derivative satisfies both the kinematic equation in L² and the
nonlinear acceleration equation in the H¹ dual. -/
theorem IsEnergySolution.exists_continuous_derivative
    {hf : LipschitzWith L f} {hf0 : f 0 = 0} (hreg : ContDiff ℝ 1 f)
    (u₀ : W^{2,2}(ℝ^n)) (v₀ : H¹(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0
      (lowerOrderCLM (by decide : 1 ≤ 2) u₀, (energyTriple n).inclusion v₀) u) :
    ∃ d : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ),
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (d t) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → HasDerivAt u (d t) t) ∧
      (∀ t : ℝ, 0 ≤ t → (energyTriple n).inclusion (d t).1 = (u t).2) ∧
      (∀ t : ℝ, 0 ≤ t →
        (energyTriple n).pivotToDual (d t).2 = acceleration hf hf0 (u t).1) := by
  let x := (C).symm
    (lowerOrderCLM (by decide : 1 ≤ 2) u₀, (energyTriple n).inclusion v₀)
  let Ax := (C).symm (v₀, Δ u₀ - wkpBaseCoordinateCLM u₀)
  let F := fun s ↦ (C).symm (0, source hf hf0 (u s).1)
  let AF := fun s ↦ (C).symm (sourceH1 hf hf0 hreg (u s).1, 0)
  have hF : Continuous F := (C).symm.continuous.comp
    (continuous_const.prodMk ((source_lipschitz hf hf0).continuous.comp u.continuous.fst))
  have hAF : Continuous AF := (C).symm.continuous.comp
    (((continuous_sourceH1 hf hf0 hreg).comp u.continuous.fst).prodMk continuous_const)
  have hgraph (s : ℝ) : (linearSemigroup n).HasGeneratorAt (F s) (AF s) := by
    have hg := hasGeneratorAt_velocity (sourceH1 hf hf0 hreg (u s).1)
    rwa [inclusion_sourceH1] at hg
  have hx : (linearSemigroup n).HasGeneratorAt x Ax := hasGeneratorAt_h2 u₀ v₀
  let z := fun s ↦ (linearSemigroup n).realOrbit x s + (linearSemigroup n).duhamel F s
  let Az := fun s ↦ (linearSemigroup n).realOrbit Ax s + (linearSemigroup n).duhamel AF s
  have hAz : Continuous Az := ((linearSemigroup n).continuous_realOrbit Ax).add
      ((linearSemigroup n).continuous_duhamel hAF)
  let d : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ) :=
    ⟨fun s ↦ C (Az s + F s), (C).continuous.comp (hAz.add hF)⟩
  have heq (t : ℝ) (ht : 0 ≤ t) : u t = C (z t) := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using congrArg C (h.mild_eq ht)
  have hg (t : ℝ) (ht : 0 ≤ t) : (energyTriple n).inclusion (C (Az t)).1 = (u t).2 ∧
        massForm n (u t).1 = -(energyTriple n).pivotToDual (C (Az t)).2 := by
    have hh := linearSemigroup_generator
      ((linearSemigroup n).hasGeneratorAt_orbit_add_duhamel hx hF hAF (fun s _ ↦ hgraph s) (t := t))
    change (energyTriple n).inclusion (C (Az t)).1 = (C (z t)).2 ∧
      massForm n (C (z t)).1 = -(energyTriple n).pivotToDual (C (Az t)).2 at hh
    rwa [← heq t ht] at hh
  have hdval (t : ℝ) :
      d t = ((C (Az t)).1, (C (Az t)).2 + source hf hf0 (u t).1) := by
    change C (Az t + (C).symm (0, source hf hf0 (u t).1)) = _
    rw [map_add, ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext (add_zero _) rfl
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have hd := (C).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t
      ((linearSemigroup n).hasDerivWithinAt_orbit_add_duhamel hx hF hAF ht (fun s _ ↦ hgraph s))
    exact hd.congr_of_mem (fun s hs ↦ heq s (ht.trans hs)) le_rfl
  · intro t ht
    have hd := (C).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      ((linearSemigroup n).hasDerivAt_orbit_add_duhamel hx hF hAF
        (show t ∈ Ioo 0 (t + 1) from ⟨ht, lt_add_one t⟩) (fun s _ ↦ hgraph s))
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs using heq s hs.le
  · intro t ht
    rw [hdval]
    exact (hg t ht).1
  · intro t ht
    rw [hdval, map_add, ← source_sub_massForm]
    have hm := (hg t ht).2
    change (energyTriple n).pivotToDual (C (Az t)).2 +
      (energyTriple n).pivotToDual (source hf hf0 (u t).1) =
        (energyTriple n).pivotToDual (source hf hf0 (u t).1) - massForm n (u t).1
    rw [hm, sub_neg_eq_add, add_comm]

end PDE.Hyperbolic.NonlinearWave.Cauchy
