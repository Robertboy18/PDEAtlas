/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Global
public import PDE.Analysis.MeasureTheory.Lp.EuclideanCoordinates

/-!
# Simultaneous approximation of a finite Sobolev family

A common tail of smooth approximants has coordinate norms at most the target
norm plus one. Finite-dimensional L² assembly preserves convergence.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Composition

open GraphSpace

variable {n k m : ℕ}

/-- A finite tuple of compactly supported functions is compactly supported. -/
theorem hasCompactSupport_finite_family {v : ℝ^n → Fin m → ℝ}
    (hv : ∀ i, HasCompactSupport (fun x ↦ v x i)) : HasCompactSupport v := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have he := Filter.eventually_all.mpr (fun i ↦ hasCompactSupport_iff_eventuallyEq.mp (hv i))
  filter_upwards [he] with x hx
  exact funext hx

/-- Simultaneous smooth approximation with a uniform bound on each coordinate. -/
theorem exists_finite_smooth_approximation (U : Fin m → W^{k,2}(ℝ^n)) :
    ∃ v : ℕ → ℝ^n → Fin m → ℝ,
      ∃ hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j),
      ∃ hc : ∀ j, HasCompactSupport (v j),
      (∀ j i, ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
        (fun x ↦ v j x i) ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp (hv j))
        ((hc j).comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl)‖ ≤ ‖U i‖ + 1) ∧
      ∀ i, Tendsto (fun j ↦ mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
        (fun x ↦ v j x i) ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp (hv j))
        ((hc j).comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl)) atTop (𝓝 (U i)) := by
  classical
  have ha (i : Fin m) := globalApproximation_WkpSpace (Approximation.standardMollifier n)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) k (U i)
  choose v hv hc hlim using ha
  let V (i : Fin m) (j : ℕ) : W^{k,2}(ℝ^n) :=
    mkWkpSpaceOnOfContDiff (v i j) (hv i j) (hc i j)
  have hV (i : Fin m) : Tendsto (V i) atTop (𝓝 (U i)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (hlim i)
  have he : ∀ᶠ j in atTop, ∀ i, ‖V i j‖ ≤ ‖U i‖ + 1 :=
    Filter.eventually_all.mpr fun i ↦ ((hV i).norm.eventually
      (gt_mem_nhds (lt_add_one ‖U i‖))).mono fun _ hj ↦ hj.le
  obtain ⟨M, hM⟩ := eventually_atTop.mp he
  let w (j : ℕ) (x : ℝ^n) (i : Fin m) := v i (j + M) x
  have hw (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (w j) := contDiff_pi.mpr fun i ↦ hv i (j + M)
  have hwc (j : ℕ) : HasCompactSupport (w j) := hasCompactSupport_finite_family
    (fun i ↦ hc i (j + M))
  refine ⟨w, hw, hwc, ?_, ?_⟩
  · intro j i
    exact hM (j + M) (Nat.le_add_left M j) i
  · intro i
    exact (hV i).comp (tendsto_add_atTop_nat M)

/-- Assemble finite scalar `L²` coordinates with the usual finite-product norm
on the value space. -/
def finiteTupleL2 {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    (Fin m → Lp ℝ 2 μ) →L[ℝ] Lp (Fin m → ℝ) 2 μ :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).toContinuousLinearMap).compLpL 2 μ).comp
    Lp.euclideanTuple

theorem finiteTupleL2_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (U : Fin m → Lp ℝ 2 μ) :
    finiteTupleL2 μ U =ᵐ[μ] fun x i ↦ U i x := by
  filter_upwards [(PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin m ↦ ℝ)).toContinuousLinearMap.coeFn_compLpL
    (Lp.euclideanTuple U), Lp.euclideanTuple_apply_ae U] with x hx hy
  exact hx.trans (funext hy)

end SobolevSpace.Composition
