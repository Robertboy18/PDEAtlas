/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.TimeDerivative.ClosedSlab
public import PDE.Hyperbolic.FirstOrder.Coefficients.SpaceTime
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Transport.Coefficients
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# Differentiating matrix transport in time

The transport operator depends linearly and boundedly on its L∞ matrix
coefficients. Bounded joint C² coefficients on a closed slab therefore give
a continuously differentiable H¹-to-L² operator curve. Its derivative is
transport with the time derivatives of the matrices, with the same
negative sign as the evolution drift. The W¹,∞ coefficient curves need not
be differentiable in W¹,∞ norm.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal NNReal SobolevSpace.WholeSpaceHilbert

attribute [local instance] transportOperatorNormedAddCommGroup transportOperatorNormedSpace

namespace PDE.Hyperbolic.FirstOrder

variable {n m : ℕ} {a b : ℝ}

/-- Bounded joint C² matrices give the time derivative of matrix
transport in H¹-to-L² operator norm, including within derivatives at both
endpoints. The coefficient curve only identifies the L∞ classes of the given field. -/
theorem exists_vectorTransportCLM_timeDerivative (hab : a < b)
    (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ j p q, ContDiffOn ℝ 2 (fun y ↦ B j y p q) {y | y 0 ∈ Icc a b}) (M : ℝ≥0)
    (hone : ∀ j p q y, y 0 ∈ Icc a b →
      ‖fderivWithin ℝ (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b} y‖ ≤ M)
    (htwo : ∀ j p q y, y 0 ∈ Icc a b →
      ‖iteratedFDerivWithin ℝ 2 (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b} y‖ ≤ M)
    (A : ℝ → Fin n → Fin m → Fin m → DerivLp n ∞ univ)
    (hA : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : ℝ^n → ℝ) =ᵐ[volume] fun x ↦
      B j (timeSpaceCons t x) p q) :
    ∃ D : ℝ → Fin n → Fin m → Fin m → DerivLp n ∞ univ,
      ContinuousOn D (Icc a b) ∧
      (∀ t ∈ Icc a b, ∀ j p q, ‖D t j p q‖ ≤ M) ∧
      (∀ t ∈ Icc a b, ∀ j p q, (D t j p q : ℝ^n → ℝ) =ᵐ[volume] fun x ↦
        fderivWithin ℝ (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b}
          (timeSpaceCons t x) (EuclideanSpace.single 0 1)) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt A (D t) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt (fun s ↦ vectorTransportCLM (A s))
        (vectorTransportCLM (D t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ‖vectorTransportCLM (D t)‖ ≤
        ‖vectorTransportCoefficientCLM (n := n) (m := m) (Ω := univ)‖ * M) := by
  have hrep (j : Fin n) (p q : Fin m) (t : ℝ) (ht : t ∈ Icc a b) :
      (A t j p q : ℝ^n → ℝ) =ᵐ[domainMeasure n univ]
        fun x ↦ B j (timeSpaceCons t x) p q := by
    simpa only [domainMeasure, Measure.restrict_univ] using hA t ht j p q
  choose D hDcont hDbound hDrep hDderiv using fun j p q ↦
    exists_lp_top_timeDerivative_of_contDiffOn hab (hB j p q) M (hone j p q)
      (htwo j p q) (fun t ↦ A t j p q) (hrep j p q)
  let D' (t : ℝ) (j : Fin n) (p q : Fin m) := D j p q t
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) : HasDerivWithinAt A (D' t) (Icc a b) t :=
    hasDerivWithinAt_pi.mpr fun j ↦ hasDerivWithinAt_pi.mpr fun p ↦
      hasDerivWithinAt_pi.mpr fun q ↦ hDderiv j p q t ht
  refine ⟨D', ?_, ?_, ?_, hderiv, ?_, ?_⟩
  · exact continuousOn_pi.mpr fun j ↦ continuousOn_pi.mpr fun p ↦
      continuousOn_pi.mpr fun q ↦ (hDcont j p q).continuousOn
  · exact fun t ht j p q ↦ hDbound j p q t ht
  · intro t ht j p q
    simpa only [domainMeasure, Measure.restrict_univ] using hDrep j p q t ht
  · intro t ht
    have hL := (vectorTransportCoefficientCLM (n := n) (m := m) (Ω := univ)).hasFDerivAt (x := A t)
    exact hL.comp_hasDerivWithinAt t (hderiv t ht)
  · exact fun t ht ↦ norm_vectorTransportCLM_le_of_entry_bound _ M.coe_nonneg
      (fun j p q ↦ hDbound j p q t ht)

/-- The transport curve on finite Hilbert products has a continuous,
uniformly bounded time derivative for bounded joint C² matrices. Any
W¹,∞ realization of the coefficient slices may be used. The final formula
identifies the derivative with the negative matrix contraction against the
weak spatial gradient, using the time derivative within the slab.
The bound precedes, and is independent of, every state and forcing datum. -/
theorem exists_vectorTransportPiLpCLM_timeDerivative (hab : a < b)
    (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ j p q, ContDiffOn ℝ 2 (fun y ↦ B j y p q) {y | y 0 ∈ Icc a b}) (M : ℝ≥0)
    (hone : ∀ j p q y, y 0 ∈ Icc a b →
      ‖fderivWithin ℝ (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b} y‖ ≤ M)
    (htwo : ∀ j p q y, y 0 ∈ Icc a b →
      ‖iteratedFDerivWithin ℝ 2 (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b} y‖ ≤ M)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hbase : ∀ t ∈ Icc a b, ∀ j p q, (wkpBaseCoordinateCLM (A t j p q) : ℝ^n → ℝ) =ᵐ[volume] fun x ↦
      B j (timeSpaceCons t x) p q) :
    let C := fun t ↦ vectorTransportPiLpCLM (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q))
    ∃ dC : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ]
        PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ),
      ContinuousOn C (Icc a b) ∧
      ContinuousOn dC (Icc a b) ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt C (dC t) (Icc a b) t) ∧
      (∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ‖dC t‖ ≤ K) ∧
      (∀ t ∈ Icc a b, ∀ U : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)),
        ∀ᵐ x ∂volume, ∀ p, dC t U p x = -(∑ j, ∑ q,
          fderivWithin ℝ (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b}
            (timeSpaceCons t x) (EuclideanSpace.single 0 1) *
              wkpCoordinateCLM (singleDerivIndex n j) (U q) x)) := by
  let A₀ (t : ℝ) (j : Fin n) (p q : Fin m) := wkpBaseCoordinateCLM (A t j p q)
  obtain ⟨D, hDcont, _hDbound, hDrep, _hDderiv, hCderiv, _hCbound⟩ :=
    exists_vectorTransportCLM_timeDerivative hab B hB M hone htwo A₀ hbase
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ W^{1,2}(ℝ^n))).toContinuousLinearMap
  let f := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin m ↦ DerivLp n 2 univ)).symm.toContinuousLinearMap
  let dC (t : ℝ) := vectorTransportPiLpCLM (D t)
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s ↦ vectorTransportPiLpCLM (A₀ s)) (dC t) (Icc a b) t := by
    have hright := (hCderiv t ht).clm_comp (hasDerivWithinAt_const t (Icc a b) e)
    have hleft := (hasDerivWithinAt_const t (Icc a b) f).clm_comp hright
    simpa only [vectorTransportPiLpCLM, dC, e, f, ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.zero_comp, add_zero, zero_add] using hleft
  have hdcont : ContinuousOn dC (Icc a b) := by
    have h : ContinuousOn (fun t ↦ vectorTransportCLM (D t)) (Icc a b) :=
      continuous_vectorTransportCLM.comp_continuousOn hDcont
    have hr : ContinuousOn (fun t ↦ (vectorTransportCLM (D t)).comp e) (Icc a b) :=
      h.clm_comp continuousOn_const
    have hl : ContinuousOn (fun t ↦ f.comp ((vectorTransportCLM (D t)).comp e)) (Icc a b) :=
      continuousOn_const.clm_comp hr
    exact hl
  refine ⟨dC, fun t ht ↦ (hderiv t ht).continuousWithinAt, hdcont, hderiv, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hdcont
    exact ⟨max K 0, le_max_right _ _, fun t ht ↦ (hK t ht).trans (le_max_left _ _)⟩
  · intro t ht U
    have htransport := vectorTransportCLM_apply_ae (D t) (fun q ↦ U q)
    simp only [domainMeasure, Measure.restrict_univ] at htransport
    have hcoef : ∀ᵐ x ∂volume, ∀ j p q, D t j p q x =
        fderivWithin ℝ (fun z ↦ B j z p q) {z | z 0 ∈ Icc a b}
          (timeSpaceCons t x) (EuclideanSpace.single 0 1) :=
      ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun p ↦ ae_all_iff.mpr fun q ↦ hDrep t ht j p q
    filter_upwards [htransport, hcoef] with x hx hdx
    intro p
    simpa only [dC, vectorTransportPiLpCLM_apply, hdx] using hx p

end PDE.Hyperbolic.FirstOrder
