/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.Definitions
public import PDE.Spaces.Sobolev.Periodic.ClassicalLift
public import PDE.Analysis.Integration.PeriodicAveraging.LocalMeasure
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Closure
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Locality
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder

/-!
# Periodic Sobolev functions as local Euclidean Sobolev functions

The cell pullback preserves `L²` convergence. Closedness of the
Euclidean weak-derivative relation therefore passes the classical identity to
the completed periodic graph. Locality then joins overlapping cells on all of
Euclidean space.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Periodic

/-- The periodic graph gradient lifts to a weak derivative on every unit cell. -/
theorem hasWeakDerivativeOn_unitCell {n : ℕ} (u : h1Space n)
    (a : Fin n → ℝ) (i : Fin n) :
    HasWeakDerivativeOn (unitCell a) [i]
      (fun x ↦ valueCLM n u (toTorus n x))
      (fun x ↦ gradientCLM n u (toTorus n x) i) := by
  let D := (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (cellMeasure n)
  let V : AmbientSpace n →L[ℝ] Lp ℝ 2 (domainMeasure n (unitCell a)) :=
    (liftLp 2 a).toContinuousLinearMap.comp (WithLp.fstL 2 ℝ _ _)
  let G : AmbientSpace n →L[ℝ] Lp ℝ 2 (domainMeasure n (unitCell a)) :=
    (liftLp 2 a).toContinuousLinearMap.comp (D.comp (WithLp.sndL 2 ℝ _ _))
  have hV (v : AmbientSpace n) :
      V v =ᵐ[domainMeasure n (unitCell a)] fun x ↦ v.fst (toTorus n x) :=
    liftLp_ae a v.fst
  have hG (v : AmbientSpace n) :
      G v =ᵐ[domainMeasure n (unitCell a)] fun x ↦ v.snd (toTorus n x) i := by
    filter_upwards [liftLp_ae a (D v.snd),
      (measurePreserving_toTorus a).quasiMeasurePreserving.ae_eq_comp
        ((EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL v.snd)] with x hx hy
    exact hx.trans hy
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp u.property
  have hweak (k : ℕ) :
      HasWeakDerivativeOn (unitCell a) [i] (V (v k)) (G (v k)) := by
    obtain ⟨b, g, hd, he⟩ := hv k
    let gi : C(UnitAddTorus (Fin n), ℝ) :=
      ⟨fun x ↦ g x i, (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp g.continuous⟩
    have hw := (hasWeakDerivativeOn_toTorus_of_continuous b gi i
      (fun x t ↦ hd x i t)).mono (measurableSet_unitCell a) (subset_univ _)
    apply hw.congr_ae
    · have h := hV (v k)
      rw [he] at h
      have h' := h.trans
        ((measurePreserving_toTorus a).quasiMeasurePreserving.ae_eq_comp
          (ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) b))
      rw [he]
      convert! h'.symm using 1
    · filter_upwards [hG (v k),
        (measurePreserving_toTorus a).quasiMeasurePreserving.ae_eq_comp
          (ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) g)]
        with x hx hy
      rw [he] at hx
      rw [he]
      convert! (hx.trans (congrArg (fun z : ℝ^n ↦ z i) hy)).symm using 1
  have hw := WeakChangeOfVariables.hasWeakDerivativeOn_of_tendsto_eLpNorm
    (fun k ↦ Lp.memLp (V (v k))) (fun k ↦ Lp.memLp (G (v k)))
    (Lp.memLp (V u.val)) (Lp.memLp (G u.val)) hweak
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp ((V.continuous.tendsto u.val).comp ht))
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp ((G.continuous.tendsto u.val).comp ht))
  exact hw.congr_ae (hV u.val) (hG u.val)

/-- The periodic Sobolev lift has the canonical weak derivative on Euclidean space. -/
theorem hasWeakDerivativeOn_toTorus {n : ℕ} (u : h1Space n) (i : Fin n) :
    HasWeakDerivativeOn univ [i]
      (fun x ↦ valueCLM n u (toTorus n x))
      (fun x ↦ gradientCLM n u (toTorus n x) i) := by
  refine hasWeakDerivativeOn_single_of_open_cover openUnitCell isOpen_openUnitCell ?_ i ?_
  · rw [iUnion_openUnitCell]
  · intro a
    exact (hasWeakDerivativeOn_unitCell u a i).mono
      (isOpen_openUnitCell a).measurableSet (openUnitCell_subset_unitCell a)

/-- On a unit cell the lift is an element of the Euclidean Sobolev space. -/
theorem exists_unitCell_sobolev {n : ℕ} (u : h1Space n) (a : Fin n → ℝ) :
    ∃ U : W^{1,2}(unitCell a),
      GraphSpace.baseRepresentative U =ᵐ[domainMeasure n (unitCell a)]
        (fun x ↦ valueCLM n u (toTorus n x)) ∧
      (GraphSpace.wkpGradientCLM U : ℝ^n → ℝ^n) =ᵐ[domainMeasure n (unitCell a)]
        (fun x ↦ gradientCLM n u (toTorus n x)) :=
  GraphSpace.exists_of_weakGradient
    (memLp_comp_toTorus a (valueCLM n u)) (memLp_comp_toTorus a (gradientCLM n u))
    (hasWeakDerivativeOn_unitCell u a)

/-- The value determines a periodic Sobolev function and its weak gradient. -/
theorem valueCLM_injective (n : ℕ) : Function.Injective (valueCLM n) := by
  intro u v huv
  have hi (i : Fin n) :
      (fun x ↦ gradientCLM n u (toTorus n x) i) =ᵐ[volume]
        (fun x ↦ gradientCLM n v (toTorus n x) i) := by
    have hu := hasWeakDerivativeOn_toTorus u i
    rw [huv] at hu
    simpa only [domainMeasure, Measure.restrict_univ] using
      hu.unique_ae isOpen_univ (hasWeakDerivativeOn_toTorus v i)
  have hg : gradientCLM n u = gradientCLM n v := by
    apply (liftLp 2 (fun _ : Fin n ↦ (0 : ℝ))).injective
    apply Lp.ext
    filter_upwards [liftLp_ae (fun _ ↦ (0 : ℝ)) (gradientCLM n u),
      liftLp_ae (fun _ ↦ (0 : ℝ)) (gradientCLM n v),
      ae_restrict_of_ae (ae_all_iff.mpr hi)] with x hxu hxv hx
    rw [hxu, hxv]
    ext i
    exact hx i
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext huv hg

end SobolevSpace.Periodic
