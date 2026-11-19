/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.IdentityEvolution
public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# A product representative from component identity-triple evolutions

A stronger-space Bochner trajectory may be given through finitely many bounded coordinate
maps into a Hilbert space. If each coordinate has an identity-triple evolution with its
initial trace, those component representatives assemble into one absolutely continuous
product curve with the prescribed strong derivative and initial value.

The proof uses the integrated derivative of each component. The stronger space need not be
complete or an inner product space.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis.Evolution

/-- Assemble the component evolutions of bounded images of one Bochner trajectory.
The resulting curve represents all coordinates almost everywhere, has their L2 velocities
as its strong derivative, and takes the prescribed product value at the initial time. -/
theorem exists_absolutelyContinuous_product_of_identity_evolutions
    {S H ι : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Fintype ι]
    {a b : ℝ} (hab : a < b) (J : ι → S →L[ℝ] H)
    (u : Lp S 2 (volume.restrict (Ioc a b)))
    (g : ι → Lp H 2 (volume.restrict (Ioc a b))) (u₀ : S)
    (hE : ∀ i, ∃ E : ContinuousPivotEvolutionOn (GelfandTriple.identity H)
      (fun t ↦ (J i).compLpL 2 (volume.restrict (Ioc a b)) u t)
      (fun t ↦ (GelfandTriple.identity H).pivotToDual.compLpL
        2 (volume.restrict (Ioc a b)) (g i) t) a b,
      E.representative a = J i u₀) :
    ∃ z : ℝ → PiLp 2 (fun _ : ι ↦ H),
      AbsolutelyContinuousOnInterval z a b ∧
      (z =ᵐ[volume.restrict (Ioc a b)]
        fun t ↦ WithLp.toLp 2 (fun i ↦ J i (u t))) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b),
        HasDerivAt z (WithLp.toLp 2 (fun i ↦ g i t)) t) ∧
      z a = WithLp.toLp 2 (fun i ↦ J i u₀) := by
  classical
  choose E hEa using hE
  let L : (ι → H) →L[ℝ] PiLp 2 (fun _ : ι ↦ H) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ H)).symm.toContinuousLinearMap
  let I (i : ι) : H →L[ℝ] PiLp 2 (fun _ : ι ↦ H) :=
    L.comp (ContinuousLinearMap.single ℝ (fun _ : ι ↦ H) i)
  let z : ℝ → PiLp 2 (fun _ : ι ↦ H) :=
    fun t ↦ ∑ i, I i ((E i).representative t)
  have hsum (w : ι → H) :
      (∑ i, I i (w i)) = WithLp.toLp 2 w :=
    ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι ↦ H) L w
  have hAC : AbsolutelyContinuousOnInterval z a b := by
    apply AbsolutelyContinuousOnInterval.finset_sum (Finset.univ : Finset ι)
    intro i _
    exact (I i).lipschitzWith.comp_absolutelyContinuousOnInterval
      (E i).integratedDerivative.absolutelyContinuousOnInterval_identity
  have hrep (i : ι) :
      (E i).representative =ᵐ[volume.restrict (Ioc a b)] fun t ↦ J i (u t) := by
    have hi := (E i).ae_eq_inclusion
    rw [uIcc_of_le hab.le, ← restrict_Ioc_eq_restrict_Icc] at hi
    have hj := (J i).coeFn_compLpL u
    filter_upwards [hi, hj] with t ht hJt
    simpa only [GelfandTriple.identity_inclusion_apply, hJt] using ht
  have hderiv (i : ι) : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt (E i).representative (g i t) t :=
    (E i).integratedDerivative.ae_hasDerivAt_identity_of_ae_eq hab
      ((GelfandTriple.identity H).pivotToDual.coeFn_compLpL (g i))
  refine ⟨z, hAC, ?_, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr hrep] with t ht
    change (∑ i, I i ((E i).representative t)) = _
    simp_rw [ht]
    exact hsum _
  · filter_upwards [ae_all_iff.mpr hderiv] with t ht
    have hsumDeriv : HasDerivAt z (∑ i, I i (g i t)) t := by
      exact HasDerivAt.fun_sum fun i _ ↦
        (I i).hasFDerivAt.comp_hasDerivAt t (ht i)
    simpa only [hsum] using hsumDeriv
  · change (∑ i, I i ((E i).representative a)) = _
    simp_rw [hEa]
    exact hsum _

end PDE.Analysis.Evolution
