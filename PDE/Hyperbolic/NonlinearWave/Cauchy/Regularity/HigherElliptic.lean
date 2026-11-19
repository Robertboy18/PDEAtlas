/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.EllipticResolvent
public import PDE.DistributionTheory.TemperedDistribution.EllipticBootstrap
public import PDE.Spaces.Sobolev.Fractional.Integer.RealPart.AllOrder

/-!
# Arbitrary integer regularity of the whole-space wave resolvent

The H¹ variational solution of `(1 - Δ)u = g` has two more weak derivatives
than its load. This identifies the massive Laplacian as an isomorphism
from Hᵏ⁺² to Hᵏ for every integer `k`, in every dimension. The inverse is
constructed from the variational solution and Bessel regularity.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace TemperedDistribution
open scoped Sobolev SobolevSpace.WholeSpaceHilbert SchwartzMap Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ}

/-- The variational resolvent gains two orders in the Bessel scale. -/
theorem memSobolev_complexifyL2_of_massForm_eq (k : ℕ) (u : H¹(ℝ^n)) (g : W^{k,2}(ℝ^n))
    (h : massForm n u = (energyTriple n).pivotToDual (wkpBaseCoordinateCLM g)) :
    MemSobolev ((k + 2 : ℕ) : ℝ) 2
      (Fractional.complexifyL2CLM n ((energyTriple n).inclusion u) : 𝓢'(ℝ^n, ℂ)) := by
  let z := Fractional.complexifyL2CLM n ((energyTriple n).inclusion u)
  let T : DerivLp n 2 univ →L[ℝ] 𝓢'(ℝ^n, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Fractional.complexifyL2CLM n)
  have hgrad : gradientForm n u = -(energyTriple n).pivotToDual
      ((energyTriple n).inclusion u - wkpBaseCoordinateCLM g) := by
    change massForm n u - (energyTriple n).energyToDual u = _
    rw [h, map_sub]
    change (energyTriple n).pivotToDual (wkpBaseCoordinateCLM g) -
      (energyTriple n).pivotToDual ((energyTriple n).inclusion u) = _
    abel
  have hΔ := laplacian_complexifyL2_inclusion u _ hgrad
  have heq : (z : 𝓢'(ℝ^n, ℂ)) - Δ (z : 𝓢'(ℝ^n, ℂ)) =
      (Fractional.baseL2 g : 𝓢'(ℝ^n, ℂ)) := by
    rw [hΔ]
    change T ((energyTriple n).inclusion u) -
      T ((energyTriple n).inclusion u - wkpBaseCoordinateCLM g) = _
    rw [map_sub, sub_sub_cancel]
    change (Fractional.complexifyL2CLM n (wkpBaseCoordinateCLM g) : 𝓢'(ℝ^n, ℂ)) = _
    rw [Fractional.complexifyL2CLM_base]
  have hz0 : MemSobolev 0 2 (z : 𝓢'(ℝ^n, ℂ)) := memSobolev_zero_iff.mpr ⟨z, rfl⟩
  have hg : MemSobolev (k : ℝ) 2
      ((z : 𝓢'(ℝ^n, ℂ)) - Δ (z : 𝓢'(ℝ^n, ℂ))) := by
    rw [heq]
    exact Fractional.memSobolev_baseL2 g
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hz0.add_two_of_sub_laplacian k hg

/-- An Hᵏ elliptic load gives Hᵏ⁺² regularity of its H¹ variational solution.
The conclusion retains both the original solution and the full higher-order equation. -/
theorem exists_higherOrder_of_massForm_eq (k : ℕ)
    (u : H¹(ℝ^n)) (g : W^{k,2}(ℝ^n))
    (h : massForm n u = (energyTriple n).pivotToDual (wkpBaseCoordinateCLM g)) :
    ∃ U : W^{k + 2,2}(ℝ^n),
      lowerOrderCLM (by omega : 1 ≤ k + 2) U = u ∧
      lowerOrderCLM (by omega : k ≤ k + 2) U -
        higherOrderLaplacianCLM le_rfl U = g := by
  let z := Fractional.complexifyL2CLM n ((energyTriple n).inclusion u)
  have hzk := memSobolev_complexifyL2_of_massForm_eq k u g h
  obtain ⟨U, hU⟩ := Fractional.exists_wkpSpaceOn_re_of_memSobolev z hzk
  have hlow : lowerOrderCLM (by omega : 1 ≤ k + 2) U = u := by
    apply (energyTriple n).injective
    apply Lp.ext
    simp only [domainMeasure, Measure.restrict_univ]
    filter_upwards [hU, Fractional.complexifyL2CLM_ae ((energyTriple n).inclusion u)] with x hx hy
    exact hx.trans (congrArg Complex.re hy)
  refine ⟨U, hlow, ?_⟩
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  rw [map_sub, higherOrderLaplacianCLM_base]
  apply (energyTriple n).pivotToDual_injective
  have hm := massForm_h2 (lowerOrderCLM (by omega : 2 ≤ k + 2) U)
  rw [lowerOrderCLM_trans_apply, hlow, h] at hm
  simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex] using hm.symm

/-- The massive Laplacian retaining all derivatives through order `k`. -/
def higherMassiveLaplacianCLM (n k : ℕ) :
    W^{k + 2,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  lowerOrderCLM (by omega) - higherOrderLaplacianCLM le_rfl

/-- The higher-order massive Laplacian is bijective at every integer order. -/
theorem bijective_higherMassiveLaplacianCLM (n k : ℕ) :
    Function.Bijective (higherMassiveLaplacianCLM n k) := by
  constructor
  · intro U V h
    have hb := congrArg wkpBaseCoordinateCLM h
    change wkpBaseCoordinateCLM (lowerOrderCLM _ U - higherOrderLaplacianCLM _ U) =
      wkpBaseCoordinateCLM (lowerOrderCLM _ V - higherOrderLaplacianCLM _ V) at hb
    simp only [map_sub, higherOrderLaplacianCLM_base] at hb
    have htwo : lowerOrderCLM (by omega : 2 ≤ k + 2) U =
        lowerOrderCLM (by omega : 2 ≤ k + 2) V := bijective_massiveLaplacian.injective hb
    apply wkpBaseCoordinateCLM_injective isOpen_univ
    exact congrArg (wkpBaseCoordinateCLM (m := 2)) htwo
  · intro g
    let u := (InnerProductSpace.toDual ℝ H¹(ℝ^n)).symm
      ((energyTriple n).pivotToDual (wkpBaseCoordinateCLM g))
    have h : massForm n u = (energyTriple n).pivotToDual (wkpBaseCoordinateCLM g) :=
      (InnerProductSpace.toDual ℝ H¹(ℝ^n)).apply_symm_apply _
    obtain ⟨U, _, hU⟩ := exists_higherOrder_of_massForm_eq k u g h
    exact ⟨U, hU⟩

/-- The continuous inverse of `1 - Δ : Hᵏ⁺² → Hᵏ`, constructed from
variational solvability and all-order elliptic regularity. -/
def higherMassiveLaplacianEquiv (n k : ℕ) :
    W^{k + 2,2}(ℝ^n) ≃L[ℝ] W^{k,2}(ℝ^n) :=
  ContinuousLinearEquiv.ofBijective (higherMassiveLaplacianCLM n k)
    (LinearMap.ker_eq_bot.mpr (bijective_higherMassiveLaplacianCLM n k).injective)
    (LinearMap.range_eq_top.mpr (bijective_higherMassiveLaplacianCLM n k).surjective)

end PDE.Hyperbolic.NonlinearWave.Cauchy
