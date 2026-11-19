/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.WeakH2Transport
public import PDE.Fluid.DeGregorio.Iteration.Transport
import CAS.ExactTactic

/-!
# H² output closure on the common characteristic interval

The characteristic construction produces the coefficient, flow, Eulerian
field and continuous L² curve. The weak H² slice theorem gives a uniformly
bounded H² graph for that same L² output at every time in the closed interval.
The initial data and the explicit support enclosure are preserved.

The explicit norm bound depends on the input budget and time through
their product. `Iteration.InvariantBall` uses this dependence to choose
a radius and a positive time for which the output stays in the input ball.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- A bounded weak H² input curve constructs a characteristic
transport whose continuous L² output has uniformly bounded weak H² graphs
on the same closed interval. The graph bound and support enclosure depend
only on the input budget, interval, and initial datum. -/
theorem exists_hkCurve_transport_with_h2_output
    {A : Set (ℝ^1)} {B : NNReal} {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    (W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀)
    (hW₀ : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] w₀)
    (hsupp₀ : ∀ x, S < |x| → w₀ x = 0) :
    let M := Real.exp (2 * (B : ℝ) * T)
    let N := 2 * (B : ℝ) * T * Real.exp (4 * (B : ℝ) * T)
    let C := Real.sqrt M *
      ((M + (2 * (B : ℝ) * T + 1) * Real.exp (4 * (B : ℝ) * T)) * B)
    let K := (succOrderAssemblyNormBound 1 1 *
      (Real.sqrt M * (1 + 2 * (M + N * M ^ 3 + M * M)))) *
      (succOrderAssemblyNormBound 1 1 * ((2 * M + N) * (2 + 6 * T * C)))
    ∃ c X Y w : ℝ → ℝ → ℝ,
      HkTransportData hT f w₀ c X Y w ∧
      (∀ y t, t ∈ Icc (0 : ℝ) T →
        S * Real.exp (2 * (B : ℝ) * T) < |y| → w y t = 0) ∧
      ∃ F : C(Icc (0 : ℝ) T, Lp ℝ 2 volume),
        (∀ t, (F t : ℝ → ℝ) =ᵐ[volume] fun y ↦ w y t) ∧
        ∀ t, ∃ W : W^{2,2}((Set.univ : Set (ℝ^1))),
          oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) = F t ∧
          ‖W‖ ≤ K * ‖W₀‖ := by
  dsimp only
  obtain ⟨c, X, Y, w, htransport⟩ :=
    exists_hkCurve_transport_along_characteristics hT hS f hw₀ hsupp₀
  obtain ⟨F, hF⟩ := htransport.representative
  refine ⟨c, X, Y, w, htransport.toHkTransportData, htransport.support, F, hF, ?_⟩
  intro t
  obtain ⟨W, hWbase, hWnorm⟩ := exists_h2_hkCurve_eulerian_slice hT f
    htransport.toHkCharacteristics W₀ hw₀ hW₀ t.property
  refine ⟨W, ?_, ?_⟩
  · apply Lp.ext
    have hformula : (fun y ↦ w₀ (Y y t) *
        Real.exp (∫ s in 0..(t : ℝ), c (X (Y y t) s) s)) = fun y ↦ w y t := by
      funext y
      rw [← htransport.formula (Y y t) t t.property, htransport.flow_inverse y t t.property]
    exact hWbase.trans ((Filter.EventuallyEq.of_eq hformula).trans (hF t).symm)
  · let M := Real.exp (2 * (B : ℝ) * T)
    let N := 2 * (B : ℝ) * T * Real.exp (4 * (B : ℝ) * T)
    let C := Real.sqrt M *
      ((M + (2 * (B : ℝ) * T + 1) * Real.exp (4 * (B : ℝ) * T)) * B)
    let Q := succOrderAssemblyNormBound 1 1 *
      (Real.sqrt M * (1 + 2 * (M + N * M ^ 3 + M * M)))
    have hM : 0 ≤ M := Real.exp_nonneg _
    have hN : 0 ≤ N := by dsimp only [N]; positivity
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    have ha : 0 ≤ succOrderAssemblyNormBound 1 1 := succOrderAssemblyNormBound_nonneg
    have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
    change ‖W‖ ≤ (Q * (succOrderAssemblyNormBound 1 1 *
      ((2 * M + N) * (2 + 6 * T * C)))) * ‖W₀‖
    calc
      ‖W‖ ≤ Q * (succOrderAssemblyNormBound 1 1 *
          ((2 * M + N) * (2 + 6 * (t : ℝ) * C) * ‖W₀‖)) := hWnorm
      _ ≤ Q * (succOrderAssemblyNormBound 1 1 *
          ((2 * M + N) * (2 + 6 * T * C) * ‖W₀‖)) := by
        gcongr
        exact t.property.2
      _ = _ := by cas

end DeGregorio.Iteration
