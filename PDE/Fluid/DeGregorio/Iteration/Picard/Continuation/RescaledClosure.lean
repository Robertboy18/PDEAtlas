/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.RescaledSplice
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.TerminalClosure

/-!
# Terminal filling and spatial traces for rescaled splicing

Changing only the missing terminal slice preserves the interior coupled PDE.
Spatial differentiation commutes with concatenating closed time slabs.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace DeGregorio

namespace Iteration

/-- Fill the two coupled fields at the missing terminal slice. -/
def closeTimeFields (T : ℝ) (fields : Fields) (v u : ℝ → ℝ) : Fields :=
  ⟨closeTimeSlice T fields.vorticity v, closeTimeSlice T fields.velocity u⟩

/-- Spatial differentiation acts separately on the two time slabs. -/
theorem deriv_joinTimeSlabs {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (w z : ℝ → ℝ → ℝ) (t : ℝ) :
    deriv (fun x ↦ joinTimeSlabs hT hS w z x t) =
      fun x ↦ joinTimeSlabs hT hS
        (fun y s ↦ deriv (fun q ↦ w q s) y)
        (fun y s ↦ deriv (fun q ↦ z q s) y) x t := by
  by_cases ht : t ≤ T <;> simp only [joinTimeSlabs, ht, ↓reduceIte]

/-- Joint continuity of both spatial derivative traces passes to their join. -/
theorem continuous_deriv_joinTimeSlabs {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    {w z : ℝ → ℝ → ℝ}
    (hw : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ deriv (fun x ↦ w x p.2) p.1))
    (hz : Continuous (fun p : ℝ × Icc (0 : ℝ) S ↦ deriv (fun x ↦ z x p.2) p.1))
    (hmatch : (fun x ↦ w x T) = fun x ↦ z x 0) :
    Continuous (fun p : ℝ × ℝ ↦
      deriv (fun x ↦ joinTimeSlabs hT hS w z x p.2) p.1) := by
  simpa only [deriv_joinTimeSlabs, Function.uncurry_def] using
    continuous_joinTimeSlabs hT hS hw hz (fun x ↦ congrFun (congrArg deriv hmatch) x)

end Iteration

/-- Changing the fields and the rate at the terminal time `T` leaves the rescaled
equation on `(a, T)` unchanged. -/
theorem IsClassicalRescaledSolutionOn.close_terminal
    {fields : Fields} {ρ : ℝ → ℝ} {a T : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields ρ ρ (Ioo a T))
    (v u : ℝ → ℝ) (r : ℝ) :
    IsClassicalRescaledSolutionOn 1 (Iteration.closeTimeFields T fields v u)
      (Function.update ρ T r) (Function.update ρ T r) (Ioo a T) := by
  classical
  have hω (t : ℝ) (ht : t < T) :
      (fun x ↦ (Iteration.closeTimeFields T fields v u).vorticity x t) =
        fun x ↦ fields.vorticity x t :=
    funext fun x ↦ Iteration.closeTimeSlice_of_ne _ _ x ht.ne
  have hu (t : ℝ) (ht : t < T) :
      (fun x ↦ (Iteration.closeTimeFields T fields v u).velocity x t) =
        fun x ↦ fields.velocity x t :=
    funext fun x ↦ Iteration.closeTimeSlice_of_ne _ _ x ht.ne
  have htime (x t : ℝ) (ht : t < T) :
      (Iteration.closeTimeFields T fields v u).vorticity x =ᶠ[𝓝 t]
        fields.vorticity x := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact congrFun (hω s hs) x
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x t ht
    apply (hsol.regularity.vorticity_differentiableAt ht).congr_of_eventuallyEq
    filter_upwards [(continuous_snd.tendsto (x, t)) (Iio_mem_nhds ht.2)] with p hp
    exact congrFun (hω p.2 hp) p.1
  · intro x t ht
    rw [hu t ht.2]
    exact hsol.regularity.velocity_differentiableAt ht
  · intro x t ht
    change deriv ((Iteration.closeTimeFields T fields v u).vorticity x) t +
        (Function.update ρ T r t * x +
          1 * (Iteration.closeTimeFields T fields v u).velocity x t) *
          deriv (fun y ↦ (Iteration.closeTimeFields T fields v u).vorticity y t) x =
      (Function.update ρ T r t +
        deriv (fun y ↦ (Iteration.closeTimeFields T fields v u).velocity y t) x) *
          (Iteration.closeTimeFields T fields v u).vorticity x t
    rw [(htime x t ht.2).deriv_eq, hω t ht.2, hu t ht.2,
      Function.update_of_ne ht.2.ne, congrFun (hω t ht.2) x, congrFun (hu t ht.2) x]
    exact hsol.transport ht
  · intro t ht
    rw [hω t ht.2, hu t ht.2]
    exact hsol.biotSavart ht

end DeGregorio
