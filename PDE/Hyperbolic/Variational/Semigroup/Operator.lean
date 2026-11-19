/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.Semigroup.EnergySpace
public import PDE.Analysis.Evolution.Gelfand.Triple
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The partial wave operator

For an energy inclusion `J : V → H` and its dual inclusion `K`, the graph is
`Jw = v`, `Bu = -Kr`. Thus the state `(u,v)` has image `(w,r)`.
The two injective inclusions make this a single-valued partial linear map.
For the Dirichlet problem on a `C²` domain, elliptic regularity identifies its displacement
domain with `H² ∩ H¹₀` (`PDE.Hyperbolic.Variational.Semigroup.ClassicalDomain`).
-/

@[expose] public section

noncomputable section

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution
open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : GelfandTriple (V := V) (H := H))
  (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
  (hsymm : ∀ u v, B u v = B v u)

local notation "W" => WaveEnergySpace (H := H) B hB hsymm
local notation "C" => WaveEnergySpace.coordinates (H := H) B hB hsymm

/-- The weak wave graph in the energy space. -/
def waveGraph : Submodule ℝ (W × W) where
  carrier := {p | T.inclusion (C p.2).1 = (C p.1).2 ∧
    B (C p.1).1 = -T.pivotToDual (C p.2).2}
  zero_mem' := by simp
  add_mem' := by
    rintro p q ⟨hp, hBp⟩ ⟨hq, hBq⟩
    constructor
    · simpa using congrArg₂ (· + ·) hp hq
    · simpa [map_add, neg_add, add_comm] using congrArg₂ (· + ·) hBp hBq
  smul_mem' := by
    rintro a p ⟨hp, hBp⟩
    constructor
    · simpa using congrArg (a • ·) hp
    · simpa using congrArg (a • ·) hBp

/-- A zero input has only the zero output in the wave graph. -/
theorem waveGraph_zero (p : W × W) (hp : p ∈ waveGraph T B hB hsymm)
    (hzero : p.1 = 0) : p.2 = 0 := by
  obtain ⟨hw, hr⟩ := hp
  have hwzero : (C p.2).1 = 0 := T.injective (by simpa [hzero] using hw)
  have hrzero : (C p.2).2 = 0 := by
    apply T.pivotToDual_injective
    simpa using (neg_eq_zero.mp (by simpa [hzero] using hr.symm))
  apply (C).injective
  change C p.2 = C 0
  rw [map_zero]
  exact Prod.ext hwzero hrzero

/-- The autonomous wave operator as Mathlib's partial linear map. -/
def waveOperator : W →ₗ.[ℝ] W :=
  (waveGraph T B hB hsymm).toLinearPMap

/-- The partial operator has exactly the specified weak graph. -/
theorem waveOperator_graph :
    (waveOperator T B hB hsymm).graph = waveGraph T B hB hsymm :=
  Submodule.toLinearPMap_graph_eq _ (waveGraph_zero T B hB hsymm)

/-- Graph membership gives both equations, with no assumed domain identification. -/
theorem mem_waveOperator_graph_iff (x y : W) :
    (x, y) ∈ (waveOperator T B hB hsymm).graph ↔
      T.inclusion (C y).1 = (C x).2 ∧ B (C x).1 = -T.pivotToDual (C y).2 := by
  rw [waveOperator_graph]
  rfl

/-- The wave generator is skew on the diagonal of the full energy inner product. -/
theorem inner_waveOperator_self (x : (waveOperator T B hB hsymm).domain) :
    ⟪waveOperator T B hB hsymm x, (x : W)⟫_ℝ = 0 := by
  obtain ⟨hw, hr⟩ := (mem_waveOperator_graph_iff T B hB hsymm _ _).mp
    ((waveOperator T B hB hsymm).mem_graph x)
  have hpair := DFunLike.congr_fun hr (C (waveOperator T B hB hsymm x)).1
  change B (C (x : W)).1 (C (waveOperator T B hB hsymm x)).1 =
    -⟪(C (waveOperator T B hB hsymm x)).2,
      T.inclusion (C (waveOperator T B hB hsymm x)).1⟫_ℝ at hpair
  rw [hw] at hpair
  rw [WaveEnergySpace.inner_eq, hsymm, hpair, neg_add_cancel]

end Hyperbolic.Variational
