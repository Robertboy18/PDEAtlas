/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ConvolutionL2
public import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing
public import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions

/-!
# Vector L² pairings in Sobolev coordinates

Almost-everywhere coordinate identities identify the energy of a Euclidean-valued L² field
with the sum of its scalar coordinate energies. For an L∞ field of bounded operators,
entrywise identification similarly expresses its L² multiplication pairing as a finite
matrix pairing. No derivatives or symmetry of the coefficients are required here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Convolution ENNReal Topology

namespace SobolevSpace.GraphSpace

open scoped InnerProductSpace

variable {n m : ℕ}

/-- The sum of the component L2 energies is the vector-valued L2 energy.
Almost-everywhere identities suffice, including for Sobolev representatives. -/
theorem sum_norm_sq_eq_of_ae_coordinates
    (v : Fin m → DerivLp n 2 Set.univ)
    (w : Lp (ℝ^m) 2 (volume : Measure (ℝ^n)))
    (hv : ∀ p, (v p : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ w x p) :
    ∑ p, ‖v p‖ ^ 2 = ‖w‖ ^ 2 := by
  classical
  have hInt (p : Fin m) : Integrable (fun x ↦ inner ℝ (v p x) (v p x)) volume := by
    simpa only [domainMeasure, Measure.restrict_univ] using L2.integrable_inner (v p) (v p)
  simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [domainMeasure, Measure.restrict_univ]
  rw [← integral_finsetSum Finset.univ (fun p _ ↦ hInt p)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hv] with x hx
  simp only [hx, PiLp.inner_apply]

/-- A bounded linear map on Euclidean space acts by its coordinate matrix. -/
theorem continuousLinearMap_apply_coordinate (T : ℝ^m →L[ℝ] ℝ^m)
    (v : ℝ^m) (p : Fin m) :
    T v p = ∑ q, (T (EuclideanSpace.single q 1) p) * v q := by
  classical
  have hrepr := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  have hT := congrArg (fun w : ℝ^m ↦ T w p) hrepr
  simpa only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, smul_eq_mul,
    mul_comm] using hT.symm

/-- The L-infinity operator multiplication pairing equals the scalar matrix pairing
when the coefficient entries and vector components have the stated representatives. -/
theorem inner_multiplicationL2CLM_eq_sum_of_ae_coordinates
    (B : Lp (ℝ^m →L[ℝ] ℝ^m) ∞ (volume : Measure (ℝ^n)))
    (a : Fin m → Fin m → DerivLp n ∞ Set.univ)
    (d v : Fin m → DerivLp n 2 Set.univ)
    (D V : Lp (ℝ^m) 2 (volume : Measure (ℝ^n)))
    (hB : ∀ p q, (fun x ↦ B x (EuclideanSpace.single q 1) p)
      =ᵐ[volume] (a p q : ℝ^n → ℝ))
    (hd : ∀ p, (d p : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ D x p)
    (hv : ∀ p, (v p : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ V x p) :
    ⟪PDE.Analysis.multiplicationL2CLM B D, V⟫_ℝ =
      ∑ p, ∑ q, ⟪a p q • d q, v p⟫_ℝ := by
  classical
  let f : Fin m → Fin m → ℝ^n → ℝ := fun p q x ↦
    inner ℝ ((a p q • d q : DerivLp n 2 Set.univ) x) (v p x)
  have hInt (p q : Fin m) : Integrable (f p q) volume := by
    simpa only [f, domainMeasure, Measure.restrict_univ] using
      L2.integrable_inner (a p q • d q) (v p)
  have hMul (p q : Fin m) :
      (fun x ↦ (a p q • d q : DerivLp n 2 Set.univ) x) =ᵐ[volume]
        fun x ↦ a p q x * d q x := by
    have h := Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (a p q) (d q)
    simp only [domainMeasure, Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    exact hx
  have hpoint : (fun x ↦ inner ℝ (PDE.Analysis.multiplicationL2CLM B D x) (V x))
      =ᵐ[volume] fun x ↦ ∑ p, ∑ q, f p q x := by
    filter_upwards [PDE.Analysis.multiplicationL2CLM_ae_eq B D,
      ae_all_iff.mpr (fun p ↦ ae_all_iff.mpr (hB p)),
      ae_all_iff.mpr hd, ae_all_iff.mpr hv,
      ae_all_iff.mpr (fun p ↦ ae_all_iff.mpr (hMul p))]
      with x hBD hBx hdx hvx hMx
    rw [hBD, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro p _
    rw [continuousLinearMap_apply_coordinate]
    simp only [f, hMx, Real.inner_apply, ← hdx, ← hvx,
      hBx, Finset.sum_mul, mul_assoc]
  rw [L2.inner_def, integral_congr_ae hpoint,
    integral_finsetSum Finset.univ (fun p _ ↦
      integrable_finsetSum Finset.univ (fun q _ ↦ hInt p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum Finset.univ (fun q _ ↦ hInt p q)]
  apply Finset.sum_congr rfl
  intro q _
  simp only [f, L2.inner_def, domainMeasure, Measure.restrict_univ]

end SobolevSpace.GraphSpace
