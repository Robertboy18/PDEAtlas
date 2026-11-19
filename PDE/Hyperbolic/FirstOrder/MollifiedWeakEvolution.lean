/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.MollifiedTesting
public import PDE.Analysis.Evolution.Integrated.IdentityRegularity

/-!
# Time regularity of a spatially mollified weak solution

Start with a Bochner L² state satisfying the original transport equation
against fixed H¹ spatial tests and the endpoint time tests.

Testing on mollified H¹ vectors identifies the mollified velocity in
L². The Hilbert-space weak-equation theorem constructs an absolutely continuous L²
representative and recovers the mollified initial datum from the boundary
term. Coefficient values are continuous in L∞ only on the closed interval;
their indicated spatial derivatives need only be uniformly bounded.

This is the fixed-scale regularity step in the uniqueness argument. Symmetry
enters only the later spatial energy estimate.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- Recover the time derivative and initial trace after spatial
mollification of a Bochner L² weak solution. The prescribed initial value
enters only through the original weak equation's boundary term. -/
theorem exists_mollified_absolutelyContinuous_of_weak_equation {ε : ℝ} (hε : 0 < ε)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    (u f : Lp H 2 ν) (x : H)
    (hweak : ∀ (φ : V) (τ : TimeTest a b), -(∫ t, ⟪u t, transportBaseCLM φ⟫_ℝ * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
      (∫ t, ⟪f t, transportBaseCLM φ⟫_ℝ * τ.toFun t ∂ν) + ⟪x, transportBaseCLM φ⟫_ℝ * τ.toFun a) :
    let S : H →L[ℝ] V := mollifierProductH1CLM (standardMollifier n) hε;
    let J : H →L[ℝ] H := transportBaseCLM.comp S;
    ∃ w : ℝ → H,
      ContinuousOn w (Icc a b) ∧
      w =ᵐ[ν] (fun t ↦ J (u t)) ∧
      w a = J x ∧
      AbsolutelyContinuousOnInterval w a b ∧
      ∀ᵐ t ∂ν,
        HasDerivAt w
          (mollifiedTransportDrift (standardMollifier n) hε (A t) (u t) + J (f t)) t := by
  classical
  intro S J
  let : MeasurableSpace H := borel _
  let : BorelSpace H := ⟨rfl⟩
  let d : ℝ → H := fun t ↦ mollifiedTransportDrift (standardMollifier n) hε (A t) (u t)
  have hd : MemLp d 2 ν :=
    memLp_mollifiedTransportDrift (standardMollifier n) hε hab.le A hA L hL (Lp.memLp u)
  have hJf : MemLp (fun t ↦ J (f t)) 2 ν := J.comp_memLp f
  let velocity : ℝ → H := fun t ↦ d t + J (f t)
  have hvelocity : MemLp velocity 2 ν := hd.add hJf
  let g : Lp H 2 ν := hvelocity.toLp velocity
  let v : Lp H 2 ν := J.compLpL 2 ν u
  have hg : (g : ℝ → H) =ᵐ[ν] velocity := hvelocity.coeFn_toLp
  have hv : (v : ℝ → H) =ᵐ[ν] fun t ↦ J (u t) := J.coeFn_compLpL u
  have hself (y z : H) : ⟪J y, z⟫_ℝ = ⟪y, J z⟫_ℝ :=
    inner_transportBase_mollifierProductH1CLM_left hε y z
  have htimeTest (z : H) (τ : TimeTest a b) : -(∫ t, ⟪v t, z⟫_ℝ * τ.derivFun t ∂ν) =
        (∫ t, ⟪g t, z⟫_ℝ * τ.toFun t ∂ν) + ⟪J x, z⟫_ℝ * τ.toFun a := by
    have htime : (∫ t, ⟪v t, z⟫_ℝ * τ.derivFun t ∂ν) =
          ∫ t, ⟪u t, transportBaseCLM (S z)⟫_ℝ * τ.derivFun t ∂ν := by
      apply integral_congr_ae
      filter_upwards [hv] with t ht
      rw [ht, hself]
      rfl
    have hdrift : (∫ t, ⟪d t, z⟫_ℝ * τ.toFun t ∂ν) =
          ∫ t, transportTestFunctional (A t) (S z) (u t) * τ.toFun t ∂ν := by
      apply integral_congr_ae
      filter_upwards with t
      rw [inner_mollifiedTransportDrift]
    have hforce : (∫ t, ⟪J (f t), z⟫_ℝ * τ.toFun t ∂ν) =
          ∫ t, ⟪f t, transportBaseCLM (S z)⟫_ℝ * τ.toFun t ∂ν := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hself]
      rfl
    have hload : (∫ t, ⟪g t, z⟫_ℝ * τ.toFun t ∂ν) = (∫ t, ⟪d t, z⟫_ℝ * τ.toFun t ∂ν) +
            ∫ t, ⟪J (f t), z⟫_ℝ * τ.toFun t ∂ν := by
      calc
        _ = ∫ t, (⟪d t, z⟫_ℝ * τ.toFun t + ⟪J (f t), z⟫_ℝ * τ.toFun t) ∂ν := by
          apply integral_congr_ae
          filter_upwards [hg] with t ht
          rw [ht]
          change ⟪d t + J (f t), z⟫_ℝ * τ.toFun t = _
          rw [inner_add_left, add_mul]
        _ = _ := integral_add ((hd.inner_const z).integrable_mul τ.memLp)
          ((hJf.inner_const z).integrable_mul τ.memLp)
    rw [htime, hload, hdrift, hforce, hself]
    exact hweak (S z) τ
  obtain ⟨w, hwcont, hwae, hwx, hwac, hwderiv, _hwenergy⟩ :=
    exists_absolutelyContinuous_representative_of_timeTest hab v g (J x) htimeTest
  refine ⟨w, hwcont, hwae.trans hv, hwx, hwac, ?_⟩
  filter_upwards [hwderiv, hg] with t ht hgt
  simpa only [hgt] using ht

end PDE.Hyperbolic.FirstOrder
