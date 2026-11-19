/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Differentiation
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Periodic Sobolev graph space

The periodic `H¹` space is the closure of the graph of continuous periodic
potentials with continuous coordinate derivatives. The ambient space carries the
Hilbert norm of the value and gradient together. The mean-zero subspace fixes the
additive constant in a periodic potential.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace

namespace SobolevSpace.Periodic

/-- The value and gradient coordinates, with their Hilbert product norm. -/
abbrev AmbientSpace (n : ℕ) :=
  WithLp 2 (Lp ℝ 2 (cellMeasure n) × Lp (ℝ^n) 2 (cellMeasure n))

/-- The graph of continuous coordinate gradients on the unit torus. -/
def continuousGraph (n : ℕ) : Submodule ℝ (AmbientSpace n) where
  carrier := {v | ∃ (u : C(UnitAddTorus (Fin n), ℝ))
    (g : C(UnitAddTorus (Fin n), ℝ^n)),
    (∀ x i t, HasDerivAt (fun s ↦ u (x + coordinateShift i s))
      (g (x + coordinateShift i t) i) t) ∧
    v = WithLp.toLp 2
      (ContinuousMap.toLp 2 (cellMeasure n) ℝ u,
        ContinuousMap.toLp 2 (cellMeasure n) ℝ g)}
  zero_mem' := by
    refine ⟨0, 0, fun x i t ↦ ?_, ?_⟩
    · simpa using hasDerivAt_const t (0 : ℝ)
    · simp only [map_zero]
      rfl
  add_mem' := by
    rintro v w ⟨u, g, hg, rfl⟩ ⟨u', g', hg', rfl⟩
    refine ⟨u + u', g + g', fun x i t ↦ (hg x i t).add (hg' x i t), ?_⟩
    simp [← WithLp.toLp_add]
  smul_mem' := by
    rintro c v ⟨u, g, hg, rfl⟩
    refine ⟨c • u, c • g, fun x i t ↦ (hg x i t).const_smul c, ?_⟩
    simp [← WithLp.toLp_smul]

/-- Periodic Sobolev functions, represented by their value and gradient in `L²`. -/
def h1Space (n : ℕ) : Submodule ℝ (AmbientSpace n) :=
  (continuousGraph n).topologicalClosure

/-- The periodic Sobolev space is complete in the graph norm. -/
instance h1Space_complete (n : ℕ) : CompleteSpace (h1Space n) :=
  (continuousGraph n).isClosed_topologicalClosure.completeSpace_coe

/-- The value coordinate of a periodic Sobolev function. -/
def valueCLM (n : ℕ) : h1Space n →L[ℝ] Lp ℝ 2 (cellMeasure n) :=
  (WithLp.fstL 2 ℝ _ _).comp (h1Space n).subtypeL

/-- The gradient coordinate of a periodic Sobolev function. -/
def gradientCLM (n : ℕ) : h1Space n →L[ℝ] Lp (ℝ^n) 2 (cellMeasure n) :=
  (WithLp.sndL 2 ℝ _ _).comp (h1Space n).subtypeL

/-- The mean of a real `L²` function on the periodic cell. -/
def meanCLM (n : ℕ) : Lp ℝ 2 (cellMeasure n) →L[ℝ] ℝ :=
  innerSL ℝ (Lp.const 2 (cellMeasure n) (1 : ℝ))

/-- The mean functional is the integral against normalized Haar measure. -/
theorem meanCLM_apply {n : ℕ} (u : Lp ℝ 2 (cellMeasure n)) :
    meanCLM n u = ∫ x, u x ∂cellMeasure n := by
  change ⟪Lp.const 2 (cellMeasure n) (1 : ℝ), u⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (cellMeasure n) (1 : ℝ)] with x hx
  change u x * Lp.const 2 (cellMeasure n) (1 : ℝ) x = u x
  rw [hx]
  exact mul_one _

/-- Periodic Sobolev functions with integral zero. -/
def meanZeroSpace (n : ℕ) : Submodule ℝ (h1Space n) :=
  ((meanCLM n).comp (valueCLM n)).ker

/-- Fixing the mean defines a closed Hilbert subspace. -/
instance meanZeroSpace_complete (n : ℕ) : CompleteSpace (meanZeroSpace n) :=
  ((meanCLM n).comp (valueCLM n)).isClosed_ker.completeSpace_coe

/-- The gradient on the mean-zero periodic Sobolev space. -/
def meanZeroGradientCLM (n : ℕ) :
    meanZeroSpace n →L[ℝ] Lp (ℝ^n) 2 (cellMeasure n) :=
  (gradientCLM n).comp (meanZeroSpace n).subtypeL

/-- The value of a mean-zero periodic Sobolev function has integral zero. -/
theorem integral_value_eq_zero {n : ℕ} (u : meanZeroSpace n) :
    (∫ x, valueCLM n u.val x ∂cellMeasure n) = 0 := by
  rw [← meanCLM_apply]
  exact u.property

/-- A continuous periodic potential defines an element of the Sobolev graph. -/
def ofContinuous {n : ℕ}
    (u : C(UnitAddTorus (Fin n), ℝ)) (g : C(UnitAddTorus (Fin n), ℝ^n))
    (hd : ∀ x i t, HasDerivAt (fun s ↦ u (x + coordinateShift i s))
      (g (x + coordinateShift i t) i) t) : h1Space n :=
  ⟨WithLp.toLp 2 (ContinuousMap.toLp 2 (cellMeasure n) ℝ u,
    ContinuousMap.toLp 2 (cellMeasure n) ℝ g),
    (continuousGraph n).le_topologicalClosure ⟨u, g, hd, rfl⟩⟩

end SobolevSpace.Periodic
