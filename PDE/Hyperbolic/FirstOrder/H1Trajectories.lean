/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.TransportTesting
public import PDE.Hyperbolic.FirstOrder.MollifiedH1
import PDE.Hyperbolic.FirstOrder.SymmetricCauchy
import PDE.Hyperbolic.FirstOrder.Stability
import PDE.Analysis.Evolution.LionsMagenes.Basic.ProductEvolution

/-!
# L2 trajectories of the constructed H1 solutions

The symmetric H1 construction supplies the original a.e. equations and component
identity-triple evolutions. Their product is an absolutely continuous L2 trajectory.
The velocity is assembled from the component L2 classes.

The difference estimate uses the L2 data and loads, with exponent `C + 1`. The full spatial
gradient bound remains an existence hypothesis inherited from the H1 approximation step.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- Construct an absolutely continuous product L2 trajectory from H1 initial data and
a Bochner L2 load with values in H1. Its velocity is L2 in time and agrees almost everywhere
with the original spatial drift plus forcing. -/
theorem exists_h1_transport_trajectory (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L) (F : Lp V 2 ν) (X : V) :
    ∃ (U : Lp V 2 ν) (z g : ℝ → H),
      AbsolutelyContinuousOnInterval z a b ∧
      z =ᵐ[ν] (fun t ↦ transportBaseCLM (U t)) ∧
      MemLp g 2 ν ∧
      (∀ᵐ t ∂ν, HasDerivAt z (g t) t) ∧
      (g =ᵐ[ν] fun t ↦ transportDrift (A t) (U t) +
        (transportBaseCLM.compLpL 2 ν F) t) ∧
      z a = transportBaseCLM X := by
  classical
  have hF : MemLp (F : ℝ → V) 2 (volume.restrict (Icc a b)) := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact Lp.memLp F
  obtain ⟨U, g, heq, hE, _⟩ :=
    exists_symmetric_cauchy_with_h1_energy A hA hab hsym hC hL hdiv hgrad F hF X
  obtain ⟨z, hz, hzU, hzg, hzX⟩ := exists_absolutelyContinuous_product_of_identity_evolutions hab
      (fun p ↦ (wkpCoordinateCLM (baseIndex n 1)).comp
        (PiLp.proj 2 (fun _ : Fin m ↦ H¹(ℝ^n)) p)) U g X hE
  let I (p : Fin m) : D →L[ℝ] H :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ D) p)
  have hsum (w : Fin m → D) : (∑ p, I p (w p)) = WithLp.toLp 2 w :=
    ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin m ↦ D)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ D)).symm.toContinuousLinearMap w
  have hG : MemLp (fun t ↦ WithLp.toLp 2 (fun p ↦ g p t)) 2 ν := by
    have h := memLp_finsetSum (Finset.univ : Finset (Fin m)) (fun p _ ↦ (I p).comp_memLp (g p))
    simpa only [Function.comp_apply, hsum] using h
  refine ⟨U, z, fun t ↦ WithLp.toLp 2 (fun p ↦ g p t), hz, hzU, hG, hzg, ?_, hzX⟩
  filter_upwards [ae_all_iff.mpr heq, transportBaseCLM.coeFn_compLpL F] with t ht hFt
  rw [hFt]
  exact PiLp.ext fun p ↦ ht p

/-- The original-system stability estimate expressed in the norms of its Bochner L2 loads.
This form can be used directly to complete trajectories in the uniform norm. -/
theorem h1_transport_trajectory_stability
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n)))) (hab : a ≤ b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C : ℝ} (hC : 0 ≤ C) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C) {U V' : ℝ → V}
    {z w : ℝ → H} (f g : Lp H 2 ν) (hz : AbsolutelyContinuousOnInterval z a b)
    (hw : AbsolutelyContinuousOnInterval w a b) (hzU : z =ᵐ[ν] fun t ↦ transportBaseCLM (U t))
    (hwV : w =ᵐ[ν] fun t ↦ transportBaseCLM (V' t))
    (hez : ∀ᵐ t ∂ν, HasDerivAt z (transportDrift (A t) (U t) + f t) t)
    (hew : ∀ᵐ t ∂ν, HasDerivAt w (transportDrift (A t) (V' t) + g t) t) :
    ∀ t ∈ Icc a b, ‖z t - w t‖ ^ 2 ≤
      (‖z a - w a‖ ^ 2 + ‖f - g‖ ^ 2) * Real.exp ((C + 1) * (t - a)) := by
  have hs : ∀ᵐ t ∂ν, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
        (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hsym t ⟨ht.1.le, ht.2⟩
  have hd : ∀ᵐ t ∂ν, coefficientDerivativeBound (A t) ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hdiv t ⟨ht.1.le, ht.2⟩
  have h := norm_sub_sq_le_exp_of_symmetric_transport hab A hs hC hd hz hw
    ((Lp.memLp f).sub (Lp.memLp g)) hzU hwV hez hew
  have hint : (∫ s in a..b, ‖f s - g s‖ ^ 2) = ‖f - g‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab, Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with t ht
    rw [ht, Pi.sub_apply]
  simpa only [hint] using h

/-- The zero solution in the difference estimate gives a bound involving only L2 data.
The H1 norms used to construct the trajectory do not occur in the conclusion. -/
theorem h1_transport_trajectory_energy (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hab : a ≤ b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C : ℝ} (hC : 0 ≤ C) (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C) {U : ℝ → V}
    {z : ℝ → H} (f : Lp H 2 ν) (hz : AbsolutelyContinuousOnInterval z a b)
    (hzU : z =ᵐ[ν] fun t ↦ transportBaseCLM (U t))
    (hez : ∀ᵐ t ∂ν, HasDerivAt z (transportDrift (A t) (U t) + f t) t) :
    ∀ t ∈ Icc a b, ‖z t‖ ^ 2 ≤ (‖z a‖ ^ 2 + ‖f‖ ^ 2) * Real.exp ((C + 1) * (t - a)) := by
  have hzero : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ (0 : H)) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hbase : (fun _ : ℝ ↦ (0 : H)) =ᵐ[ν]
      fun t ↦ transportBaseCLM (0 : V) := Eventually.of_forall fun _ ↦ (map_zero _).symm
  have hzderiv : ∀ᵐ t ∂ν, HasDerivAt (fun _ : ℝ ↦ (0 : H))
      (transportDrift (A t) (0 : V) + (0 : Lp H 2 ν) t) t := by
    filter_upwards [Lp.coeFn_zero (E := H) (p := 2) (μ := ν)] with t ht
    rw [transportDrift_zero, ht, Pi.zero_apply, add_zero]
    exact hasDerivAt_const t (0 : H)
  simpa only [sub_zero] using h1_transport_trajectory_stability A hab hsym hC hdiv
    f 0 hz hzero hzU hbase hez hzderiv

end PDE.Hyperbolic.FirstOrder
