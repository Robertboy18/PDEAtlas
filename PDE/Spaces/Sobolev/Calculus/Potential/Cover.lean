/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Potential.Overlap
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Locality
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Centering
import PDE.Analysis.MeasureTheory.Function.Gluing.Constants
import PDE.Analysis.MeasureTheory.Function.LocalL2

/-!
# Gluing Sobolev potentials

On a simply connected domain, H¹ potentials on a countable connected
open cover can be shifted by constants and glued. Connected overlaps make
their differences constant. The resulting measurable potential is locally L²
and satisfies the weak derivative identities on the entire domain.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {ι : Type*} [Countable ι] {Ω : Set (ℝ^n)}
    [SimplyConnectedSpace Ω] [LocallyPathConnectedSpace Ω]

/-- Compatible local potentials give one locally L² weak potential.
The additive constants are derived from simple connectedness. The potential
need not be globally L² or normalized. -/
theorem exists_weak_potential_of_native_cover
    (hΩ : IsOpen Ω) (U : ι → Set (ℝ^n))
    (hopen : ∀ i, IsOpen (U i)) (hconn : ∀ i, IsPreconnected (U i))
    (hoverlap : ∀ i j, IsPreconnected (U i ∩ U j))
    (hb : ∀ i, Bornology.IsBounded (U i))
    (hsub : ∀ i, U i ⊆ Ω) (hcover : Ω ⊆ ⋃ i, U i)
    (w : ∀ i, W^{1,2}(U i)) (F : ℝ^n → ℝ^n)
    (hgrad : ∀ i, (∇ (w i) : ℝ^n → ℝ^n)
      =ᵐ[domainMeasure n (U i)] F) :
    ∃ p : ℝ^n → ℝ, AEStronglyMeasurable p (domainMeasure n Ω) ∧
      (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
        MemLp p 2 (domainMeasure n K)) ∧
      ∀ j : Fin n, HasWeakDerivativeOn Ω [j] p (fun x ↦ F x j) := by
  have hpair (i j : ι) : ∃ c : ℝ,
      (fun x ↦ baseRepresentative (w i) x - baseRepresentative (w j) x)
        =ᵐ[volume.restrict (U i ∩ U j)] fun _ ↦ c := by
    apply exists_ae_eq_const_sub_of_gradient_eq (w i) (w j)
      ((hopen i).inter (hopen j)) (hoverlap i j) ((hb i).subset inter_subset_left)
      inter_subset_left inter_subset_right
    have hi : (∇ (w i) : ℝ^n → ℝ^n)
        =ᵐ[domainMeasure n (U i ∩ U j)] F :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hgrad i)
    have hj : (∇ (w j) : ℝ^n → ℝ^n)
        =ᵐ[domainMeasure n (U i ∩ U j)] F :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hgrad j)
    exact hi.trans hj.symm
  obtain ⟨a, p, hp, hpw⟩ := exists_aestronglyMeasurable_add_constants
    hΩ U hopen hconn hsub hcover (fun i ↦ baseRepresentative (w i))
    (fun i ↦ (Lp.memLp (wkpBaseCoordinateCLM (w i))).aestronglyMeasurable) hpair
  have (i : ι) : IsFiniteMeasure (domainMeasure n (U i)) :=
    isFiniteMeasure_domainMeasure_of_isBounded (hb i)
  let W (i : ι) : W^{1,2}(U i) := w i + wkpConstant (a i)
  have hbase (i : ι) : baseRepresentative (W i) =ᵐ[domainMeasure n (U i)] p := by
    have hsum :
        baseRepresentative (W i) =ᵐ[domainMeasure n (U i)]
          fun x ↦ baseRepresentative (w i) x + a i := by
      change (wkpBaseCoordinateCLM (W i) : ℝ^n → ℝ) =ᵐ[domainMeasure n (U i)] _
      dsimp only [W]
      rw [map_add]
      filter_upwards [Lp.coeFn_add (wkpBaseCoordinateCLM (w i))
        (wkpBaseCoordinateCLM (wkpConstant (p := 2) (Ω := U i) (a i))),
        wkpConstant_base_ae (p := 2) (Ω := U i) (a i)] with x hx hc
      rw [hx, Pi.add_apply, hc]
      rfl
    exact hsum.trans (hpw i).symm
  have hWG (i : ι) :
      (∇ (W i) : ℝ^n → ℝ^n) =ᵐ[domainMeasure n (U i)] F := by
    simpa only [W, map_add, wkpGradientCLM_constant, add_zero] using hgrad i
  have hmem (i : ι) : MemLp p 2 (domainMeasure n (U i)) :=
    (memLp_congr_ae (hbase i)).mp (Lp.memLp (wkpBaseCoordinateCLM (W i)))
  refine ⟨p, hp, ?_, ?_⟩
  · intro K hK hKΩ
    exact memLp_two_on_compact_of_open_cover U hopen hcover hmem hK hKΩ
  · intro j
    apply hasWeakDerivativeOn_single_of_open_cover U hopen hcover j
    intro i
    exact (hasWeakDerivativeOn_wkpGradientCLM (W i) j).congr_ae (hbase i)
      ((hWG i).mono fun _ hx ↦ congrArg (fun z : ℝ^n ↦ z j) hx)

end SobolevSpace.GraphSpace
