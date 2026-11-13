/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.MollifiedWeakEvolution
public import PDE.Analysis.Evolution.Time.MovingTests

/-!
# Moving tests for the spatially mollified weak equation

The separated weak equation constructs an absolutely continuous representative after
spatial mollification. Pairing that representative with a C¹ L²-valued test gives the
moving-test identity below. Self-adjointness of the standard mollifier moves it back
onto the test in each term, including the prescribed initial datum.

The input state and forcing are only Bochner L² classes. The coefficient base rows are
continuous on the time interval and the indicated weak spatial derivative rows have a
uniform bound.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- The separated weak equation admits every C¹ L²-valued moving test after spatial
mollification. The test vanishes at `b`; its value at `a` retains the initial term.
Absolute continuity is constructed for the mollified state. -/
theorem integral_mollified_moving_test_of_weak_equation {ε : ℝ} (hε : 0 < ε)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b) (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    (u f : Lp H 2 ν) (x : H)
    (hweak : ∀ (φ : V) (τ : TimeTest a b), -(∫ t, inner ℝ (u t) (transportBaseCLM φ) *
      τ.derivFun t ∂ν) = (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
      (∫ t, inner ℝ (f t) (transportBaseCLM φ) * τ.toFun t ∂ν) + inner ℝ x (transportBaseCLM φ) *
      τ.toFun a)
    (y dy : ℝ → H) (hdy : ContinuousOn dy (Icc a b)) (hy : ∀ t ∈ Icc a b, HasDerivAt y (dy t) t)
    (hyb : y b = 0) :
    let S : H →L[ℝ] V := mollifierProductH1CLM (standardMollifier n) hε;
    let J : H →L[ℝ] H := transportBaseCLM.comp S;
    -(∫ t, inner ℝ (u t) (J (dy t)) ∂ν) =
      (∫ t, transportTestFunctional (A t) (S (y t)) (u t) ∂ν) +
      (∫ t, inner ℝ (f t) (J (y t)) ∂ν) + inner ℝ x (J (y a)) := by
  intro S J
  obtain ⟨w, _hwcont, hwae, hwx, hwac, hwderiv⟩ :=
    exists_mollified_absolutelyContinuous_of_weak_equation hε A hA hab L hL u f x hweak
  have hself (v z : H) : inner ℝ (J v) z = inner ℝ v (J z) :=
    inner_transportBase_mollifierProductH1CLM_left hε v z
  have hyac : AbsolutelyContinuousOnInterval y a b :=
    absolutelyContinuousOnInterval_of_continuous_derivative
      (by simpa only [uIcc_of_le hab.le] using hdy)
      (by simpa only [uIcc_of_le hab.le] using hy)
  have hyderiv : ∀ᵐ t ∂volume.restrict (uIoc a b), HasDerivAt y (dy t) t := by
    rw [uIoc_of_le hab.le]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ hy t (Ioc_subset_Icc_self ht)
  have hwLp : MemLp w 2 ν := MemLp.ae_eq hwae.symm (J.comp_memLp' (Lp.memLp u))
  have hyLp := memLp_restrict_Ioc_of_continuousOn
    fun t ht ↦ (hy t ht).continuousAt.continuousWithinAt
  have hitime : Integrable (fun t ↦ inner ℝ (w t) (dy t)) ν :=
    memLp_one_iff_integrable.mp ((innerSL ℝ (E := H)).memLp_of_bilin 1 hwLp
      (memLp_restrict_Ioc_of_continuousOn hdy))
  have hidrift : Integrable (fun t ↦
      inner ℝ (mollifiedTransportDrift (standardMollifier n) hε (A t) (u t)) (y t)) ν :=
    memLp_one_iff_integrable.mp ((innerSL ℝ (E := H)).memLp_of_bilin 1
      (memLp_mollifiedTransportDrift (standardMollifier n) hε hab.le A hA L hL (Lp.memLp u)) hyLp)
  have hiforce : Integrable (fun t ↦ inner ℝ (J (f t)) (y t)) ν :=
    memLp_one_iff_integrable.mp ((innerSL ℝ (E := H)).memLp_of_bilin 1
      (J.comp_memLp' (Lp.memLp f)) hyLp)
  have hprod := integrated_inner_product_of_ae_hasDerivAt hwac hyac
    (by simpa only [uIoc_of_le hab.le] using hwderiv) hyderiv
  rw [hyb, inner_zero_right, zero_sub, intervalIntegral.integral_of_le hab.le] at hprod
  simp only [inner_add_left] at hprod
  change -inner ℝ (w a) (y a) = (∫ t, inner ℝ (w t) (dy t) +
      (inner ℝ (mollifiedTransportDrift (standardMollifier n) hε (A t) (u t)) (y t) +
        inner ℝ (J (f t)) (y t)) ∂ν) at hprod
  have htime : (∫ t, inner ℝ (w t) (dy t) ∂ν) = ∫ t, inner ℝ (u t) (J (dy t)) ∂ν :=
    integral_congr_ae (hwae.mono fun t ht ↦
      (congrArg (inner ℝ · (dy t)) ht).trans (hself (u t) (dy t)))
  have hdrift : (∫ t, inner ℝ
      (mollifiedTransportDrift (standardMollifier n) hε (A t) (u t)) (y t) ∂ν) =
      ∫ t, transportTestFunctional (A t) (S (y t)) (u t) ∂ν :=
    integral_congr_ae (ae_of_all _ fun t ↦ inner_mollifiedTransportDrift hε (A t) (u t) (y t))
  rw [integral_add hitime (hidrift.fun_add hiforce), integral_add hidrift hiforce, htime, hdrift,
    show w a = J x from hwx] at hprod
  simp only [hself] at hprod
  linarith only [hprod]

end PDE.Hyperbolic.FirstOrder
