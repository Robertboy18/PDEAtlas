/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.HigherReaction
public import PDE.Hyperbolic.NonlinearWave.Cauchy.LinearUniqueness

/-!
# The weak PDE for smooth first-jet waves at the sharp Sobolev order

Projection of the constructed higher evolution satisfies both integrated wave
equations in spatial L² and the H¹ dual. Conversely, linear weak-wave uniqueness
identifies any continuous higher curve satisfying these equations with its mild
trajectory. The Sobolev order is the strict threshold: data in `H^(k+1) × H^k` with
`n < 2k`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Hyperbolic.Variational

variable {n k : ℕ}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The natural energy coordinates of a higher Sobolev wave state. -/
def higherCoordinatesCLM : (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ]
    (H¹(ℝ^n) × DerivLp n 2 univ) :=
  (lowerOrderCLM (by omega : 1 ≤ k + 1)).prodMap wkpBaseCoordinateCLM

/-- The coordinate projection is the higher-energy inclusion. -/
theorem higherCoordinatesCLM_eq_coordinates (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    higherCoordinatesCLM z = C (higherEnergyInclusionCLM n k z) :=
  (coordinates_higherEnergyInclusionCLM n k z).symm

variable [NeZero n] {f : (ℝ^n × ℝ × ℝ) → ℝ}

/-- Distributional acceleration for the sharp higher first-jet state. -/
def higherAcceleration (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) : StrongDual ℝ H¹(ℝ^n) :=
  -(energyTriple n).pivotToDual (wkpBaseCoordinateCLM (higherReaction hk hf hf0 z)) -
    gradientForm n (higherCoordinatesCLM z).1

/-- The mass term in the higher source cancels in the weak wave equation. -/
theorem higherSource_sub_massForm (hk : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (higherMap hk hf hf0 z).2) -
      massForm n (higherCoordinatesCLM z).1 = higherAcceleration hk hf hf0 z := by
  change (energyTriple n).pivotToDual (wkpBaseCoordinateCLM
    (lowerOrderCLM (Nat.le_succ k) z.1 - higherReaction hk hf hf0 z)) - _ = _
  rw [map_sub, map_sub]
  unfold higherAcceleration gradientForm
  change _ - _ - _ = -_ - (_ - (energyTriple n).pivotToDual
    ((energyTriple n).inclusion (higherCoordinatesCLM z).1))
  have hb : wkpBaseCoordinateCLM (lowerOrderCLM (Nat.le_succ k) z.1) =
      (energyTriple n).inclusion (higherCoordinatesCLM z).1 := rfl
  rw [hb]
  abel

/-- The higher Duhamel curve has the lower-energy forced representation. -/
theorem higher_forced_projection (hk : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    (u : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))) (t : ℝ) :
    higherCoordinatesCLM ((higherLinearSemigroup n k).realOrbit x t +
      (higherLinearSemigroup n k).duhamel (fun s ↦ higherMap hk hf hf0 (u s)) t) =
    C ((linearSemigroup n).realOrbit (higherEnergyInclusionCLM n k x) t +
      (linearSemigroup n).duhamel
        (fun s ↦ (C).symm (0, wkpBaseCoordinateCLM (higherMap hk hf hf0 (u s)).2)) t) := by
  have hF : Continuous (fun s ↦ higherMap hk hf hf0 (u s)) :=
    (higherMap hk hf hf0).continuous.comp u.continuous
  rw [higherCoordinatesCLM_eq_coordinates, higherEnergyInclusionCLM_forced n k x hF]
  congr 2

/-- Both integrated weak PDE equations for a continuous higher Sobolev curve
on a finite time interval. Spatial derivatives are the graph-space weak
partials and the reaction is identified pointwise by `higherReaction_ae`. -/
structure IsHigherWeakSolutionOn (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) (τ : NNReal)
    (u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))) : Prop where
  initial : u ⟨0, le_rfl, τ.coe_nonneg⟩ = x
  displacement : ∀ t ∈ Icc (0 : ℝ) (τ : ℝ),
    (∫ s in (0 : ℝ)..t, wkpBaseCoordinateCLM (IccExtend τ.coe_nonneg u s).2) =
      wkpBaseCoordinateCLM (IccExtend τ.coe_nonneg u t).1 - wkpBaseCoordinateCLM x.1
  velocity : ∀ t ∈ Icc (0 : ℝ) (τ : ℝ),
    (∫ s in (0 : ℝ)..t, higherAcceleration hk hf hf0 (IccExtend τ.coe_nonneg u s)) =
      (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (IccExtend τ.coe_nonneg u t).2) -
        (energyTriple n).pivotToDual (wkpBaseCoordinateCLM x.2)

/-- Every sharp higher mild trajectory satisfies the integrated weak PDE. -/
theorem isHigherWeakSolutionOn_of_mild (hk : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))}
    (hu : (higherLinearSemigroup n k).IsMildSolutionOn (higherMap hk hf hf0) x τ u) :
    IsHigherWeakSolutionOn hk hf hf0 x τ u := by
  let U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
    ⟨IccExtend τ.coe_nonneg u, u.continuous.Icc_extend'⟩
  let g := fun s ↦ wkpBaseCoordinateCLM (higherMap hk hf hf0 (U s)).2
  have hg : Continuous g := wkpBaseCoordinateCLM.continuous.comp
    ((higherMap hk hf hf0).continuous.comp U.continuous).snd
  let w := fun t ↦ C ((linearSemigroup n).realOrbit (higherEnergyInclusionCLM n k x) t +
    (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, g s)) t)
  have huw (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (τ : ℝ)) : higherCoordinatesCLM (U t) = w t := by
    have h := congrArg higherCoordinatesCLM (hu ⟨t, ht⟩)
    rw [← IccExtend_of_mem τ.coe_nonneg u ht] at h
    exact h.trans (higher_forced_projection hk hf hf0 x U t)
  refine ⟨hu.initial_value, ?_, ?_⟩
  · intro t ht
    have h := (linear_forced_integral hg (higherEnergyInclusionCLM n k x) ht.1).1
    change (∫ s in (0 : ℝ)..t, (w s).2) = (energyTriple n).inclusion (w t).1 - _ at h
    rw [← huw t ht, coordinates_higherEnergyInclusionCLM] at h
    refine Eq.trans ?_ h
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact congrArg Prod.snd (huw s ⟨hs.1, hs.2.trans ht.2⟩)
  · intro t ht
    have h := (linear_forced_integral hg (higherEnergyInclusionCLM n k x) ht.1).2
    change (∫ s in (0 : ℝ)..t, (energyTriple n).pivotToDual (g s) - massForm n (w s).1) =
      (energyTriple n).pivotToDual (w t).2 - _ at h
    rw [← huw t ht, coordinates_higherEnergyInclusionCLM] at h
    refine Eq.trans ?_ h
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change higherAcceleration hk hf hf0 (U s) =
      (energyTriple n).pivotToDual (g s) - massForm n (w s).1
    rw [← huw s ⟨hs.1, hs.2.trans ht.2⟩]
    exact (higherSource_sub_massForm hk hf hf0 (U s)).symm

/-- Weak PDE identification recovers the higher mild equation without
assuming it of the competing continuous Sobolev trajectory. -/
theorem IsHigherWeakSolutionOn.isMildSolutionOn {hk : (n : ℝ) < 2 * (k : ℝ)}
    {hf : ContDiff ℝ (⊤ : ℕ∞) f} {hf0 : f 0 = 0} {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))}
    (hu : IsHigherWeakSolutionOn hk hf hf0 x τ u) (hτ : 0 < (τ : ℝ)) :
    (higherLinearSemigroup n k).IsMildSolutionOn (higherMap hk hf hf0) x τ u := by
  let U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
    ⟨IccExtend τ.coe_nonneg u, u.continuous.Icc_extend'⟩
  let g := fun s ↦ wkpBaseCoordinateCLM (higherMap hk hf hf0 (U s)).2
  have hg : Continuous g := wkpBaseCoordinateCLM.continuous.comp
    ((higherMap hk hf hf0).continuous.comp U.continuous).snd
  have heq := linear_integral_identification hg (higherCoordinatesCLM.continuous.comp U.continuous)
    (higherEnergyInclusionCLM n k x) hτ
    (fun t ht ↦ by
      rw [coordinates_higherEnergyInclusionCLM]
      exact hu.displacement t ht)
    (fun t ht ↦ by
      rw [coordinates_higherEnergyInclusionCLM]
      change (∫ s in (0 : ℝ)..t,
        (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (higherMap hk hf hf0 (U s)).2) -
          massForm n (higherCoordinatesCLM (U s)).1) = _
      simp only [higherSource_sub_massForm]
      exact hu.velocity t ht)
  intro t
  apply higherEnergyInclusionCLM_injective n k
  apply (C).injective
  rw [← higherCoordinatesCLM_eq_coordinates, ← higherCoordinatesCLM_eq_coordinates]
  have h := (heq t.property).trans (higher_forced_projection hk hf hf0 x U t).symm
  simp only [U, ContinuousMap.coe_mk, Function.comp_def, IccExtend_val,
    StronglyContinuousSemigroup.realOrbit] at h
  convert h using 1
  rfl

/-- Arbitrary data at the exact threshold yield a unique continuous higher
weak solution on a positive interval, bounded in the same Sobolev norm. -/
theorem exists_unique_higher_weak (hk : (n : ℝ) < 2 * (k : ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    ∃ τ : NNReal, 0 < τ ∧ ∃ u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)),
      IsHigherWeakSolutionOn hk hf hf0 x τ u ∧ (∃ B : ℝ, ∀ t, ‖u t‖ ≤ B) ∧ ∀ v,
      IsHigherWeakSolutionOn hk hf hf0 x τ v → v = u := by
  obtain ⟨τ, hτ, u, hu, huniq⟩ := exists_unique_higher_mild hk hf hf0 x
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn u.continuous.continuousOn
  exact ⟨τ, hτ, u, isHigherWeakSolutionOn_of_mild hk hf hf0 hu,
    ⟨B, fun t ↦ hB t (mem_univ t)⟩, fun v hv ↦ huniq v (hv.isMildSolutionOn hτ)⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
