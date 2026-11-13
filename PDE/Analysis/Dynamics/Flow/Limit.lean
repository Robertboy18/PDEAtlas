/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Dynamics.Flow
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Limits of flow orbits

An orbit limit at either end of time is fixed by every flow map. Continuity
transports the orbit limit through a fixed time map, while translation of time
leaves the limiting filter unchanged.
-/

public section

open Filter
open scoped Topology

namespace Flow

variable {τ X : Type*} [AddCommGroup τ] [LinearOrder τ] [IsOrderedAddMonoid τ]
  [TopologicalSpace τ] [TopologicalSpace X] [T2Space X]

/-- A forward orbit limit is fixed by every time map. -/
theorem map_eq_of_tendsto_atTop (Φ : Flow τ X) {x y : X}
    (h : Tendsto (fun t ↦ Φ t x) atTop (𝓝 y)) (s : τ) : Φ s y = y := by
  have hshift : Tendsto (fun t : τ ↦ s + t) atTop atTop := by
    change Filter.map (fun t : τ ↦ s + t) atTop ≤ atTop
    simpa only [add_comm s] using (Filter.map_add_atTop_eq s).le
  have htranslated := h.comp hshift
  exact tendsto_nhds_unique ((Φ.continuous_toFun s).continuousAt.tendsto.comp h)
    (by simpa only [Function.comp_def, Φ.map_add] using htranslated)

/-- A backward orbit limit is fixed by every time map. -/
theorem map_eq_of_tendsto_atBot (Φ : Flow τ X) {x y : X}
    (h : Tendsto (fun t ↦ Φ t x) atBot (𝓝 y)) (s : τ) : Φ s y = y :=
  map_eq_of_tendsto_atTop (τ := τᵒᵈ) Φ h s

end Flow
