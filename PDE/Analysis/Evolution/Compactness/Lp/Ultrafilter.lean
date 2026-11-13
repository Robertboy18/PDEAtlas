/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Topology.ContinuousMap.Bounded.Basic -- shake: keep
import PDE.Analysis.WeakCompactness

/-!
# Common ultrafilter weak limits in Bochner L²

Finite families of bounded Bochner `L²` sequences in one Hilbert space have
weak limits along a common ultrafilter. Families involving different
Hilbert spaces are assembled by repeatedly applying the general one-sequence
refinement theorem in `PDE.Analysis.WeakCompactness`. Exact
continuous-linear relations between approximating sequences pass to their
weak limits.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
A finite family of bounded sequences in one real Hilbert space has a common
weakly convergent ultrafilter refinement.

The family is compactified once as a finite Hilbert product. Projecting the
single product limit gives every coordinate limit along the same filter.
-/
theorem exists_ultrafilter_weak_limits_finite
    {ι κ H : Type*} [Finite κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (l : Filter ι) [l.NeBot]
    (x : κ → ι → H)
    (hx : ∀ r, Bornology.IsBounded (Set.range (x r))) :
    ∃ (xLimit : κ → H) (U : Ultrafilter ι),
      (U : Filter ι) ≤ l ∧
      ∀ r, Filter.Tendsto
        (fun i ↦ toWeakSpace ℝ H (x r i)) U
        (nhds (toWeakSpace ℝ H (xLimit r))) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let e := PiLp.continuousLinearEquiv
    (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (β := fun _ : κ ↦ H)
  let xPi : ι → PiLp 2 (fun _ : κ ↦ H) :=
    fun i ↦ e.symm (fun r ↦ x r i)
  have hPi :
      Bornology.IsBounded
        (Set.pi Set.univ fun r ↦ Set.range (x r)) :=
    Bornology.IsBounded.pi hx
  have hRange :
      Bornology.IsBounded (Set.range (fun i ↦ fun r ↦ x r i)) := by
    apply hPi.subset
    rintro y ⟨i, rfl⟩ r -
    exact ⟨i, rfl⟩
  have hRangePi : Bornology.IsBounded (Set.range xPi) := by
    refine (hRange.image e.symm.toContinuousLinearMap).subset ?_
    rintro y ⟨i, rfl⟩
    exact ⟨(fun r ↦ x r i), ⟨i, rfl⟩, rfl⟩
  obtain ⟨w, U, hUl, hw⟩ :=
    PDE.Analysis.WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter
      l xPi hRangePi
  let wPi : PiLp 2 (fun _ : κ ↦ H) :=
    (toWeakSpace ℝ (PiLp 2 (fun _ : κ ↦ H))).symm w
  let xLimit : κ → H := fun r ↦
    PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (β := fun _ : κ ↦ H) r wPi
  refine ⟨xLimit, U, hUl, fun r ↦ ?_⟩
  let Q : PiLp 2 (fun _ : κ ↦ H) →L[ℝ] H :=
    PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (β := fun _ : κ ↦ H) r
  have hmap :
      Filter.Tendsto
        (fun i ↦ toWeakSpace ℝ H (Q (xPi i))) U
        (nhds (toWeakSpace ℝ H (Q wPi))) := by
    have hraw :=
      (WeakSpace.map Q).continuous.continuousAt.tendsto.comp hw
    change Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ H (Q (xPi i))) U
      (nhds (toWeakSpace ℝ H
        (Q ((toWeakSpace ℝ (PiLp 2 (fun _ : κ ↦ H))).symm w)))) at hraw
    simpa only [wPi] using hraw
  simpa [Q, xPi, e, xLimit] using hmap

omit [CompleteSpace E] in
/-- An exact continuous-linear relation between two Galerkin sequences
survives simultaneous weak `L²` convergence. -/
theorem compLpL_eq_of_tendsto_weak
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (L : E →L[ℝ] F)
    (x : ι → Lp E 2 μ) (y : ι → Lp F 2 μ)
    (xLimit : Lp E 2 μ) (yLimit : Lp F 2 μ)
    (hx : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (x i)) l
      (nhds (toWeakSpace ℝ _ xLimit)))
    (hy : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (y i)) l
      (nhds (toWeakSpace ℝ _ yLimit)))
    (hxy : ∀ i, L.compLpL 2 μ (x i) = y i) :
    L.compLpL 2 μ xLimit = yLimit := by
  let Q : Lp E 2 μ →L[ℝ] Lp F 2 μ := L.compLpL 2 μ
  have hmap :
      Filter.Tendsto
        (fun i ↦ toWeakSpace ℝ _ (Q (x i))) l
        (nhds (toWeakSpace ℝ _ (Q xLimit))) := by
    have hraw :=
      (WeakSpace.map Q).continuous.continuousAt.tendsto.comp hx
    change Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ _ (Q (x i))) l
      (nhds (toWeakSpace ℝ _ (Q xLimit))) at hraw
    exact hraw
  have hmapAsY :
      Filter.Tendsto
        (fun i ↦ toWeakSpace ℝ _ (y i)) l
        (nhds (toWeakSpace ℝ _ (Q xLimit))) := by
    apply hmap.congr'
    exact Filter.Eventually.of_forall fun i ↦ by
      exact congrArg (toWeakSpace ℝ (Lp F 2 μ))
        (by simpa [Q] using hxy i)
  have hweak :
      toWeakSpace ℝ _ (Q xLimit) =
        toWeakSpace ℝ _ yLimit :=
    tendsto_nhds_unique hmapAsY hy
  exact (toWeakSpace ℝ _).injective hweak

end PDE.Analysis.Evolution
