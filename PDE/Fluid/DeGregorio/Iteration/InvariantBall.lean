/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.H2Output
import CAS.ExactTactic

/-!
# An invariant supported H² ball for frozen transport

The amplitude and inverse-flow estimates depend on the input budget and
time only through their product. Bounding that product by one gives a fixed
finite amplification factor. A larger initial radius therefore closes the
H² ball even with the coarse assembly estimate.

The output curve carries the inherited L² topology. Its Sobolev graphs
come from the log-Jacobian integral, product, and pullback construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Common
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The explicit amplification factor for the constructed H² graph, written
as a function of the dimensionless product of input budget and time. -/
def hkTransportH2Bound (q : ℝ) : ℝ :=
  let M := Real.exp (2 * q)
  let N := 2 * q * Real.exp (4 * q)
  let D := Real.sqrt M * (M + (2 * q + 1) * Real.exp (4 * q))
  (succOrderAssemblyNormBound 1 1 *
    (Real.sqrt M * (1 + 2 * (M + N * M ^ 3 + M * M)))) *
    (succOrderAssemblyNormBound 1 1 * ((2 * M + N) * (2 + 6 * q * D)))

/-- The H² amplification bound is nonnegative for forward time. -/
theorem hkTransportH2Bound_nonneg {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ hkTransportH2Bound q := by
  have ha : 0 ≤ succOrderAssemblyNormBound 1 1 := succOrderAssemblyNormBound_nonneg
  dsimp only [hkTransportH2Bound]
  positivity

/-- Increasing the product of budget and time increases the graph estimate. -/
theorem hkTransportH2Bound_le {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) :
    hkTransportH2Bound q ≤ hkTransportH2Bound r := by
  have ha : 0 ≤ succOrderAssemblyNormBound 1 1 := succOrderAssemblyNormBound_nonneg
  have hr : 0 ≤ r := hq.trans hqr
  dsimp only [hkTransportH2Bound]
  gcongr

/-- An explicit radius and positive time satisfy the numerical conditions
for the invariant ball; every shorter nonnegative interval also does. -/
theorem hkTransportH2Bound_explicit_budget (W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))) :
    let B := hkTransportH2Bound 1 * ‖W₀‖ + 1
    0 < B ∧ 0 < 1 / (B + 1) ∧ hkTransportH2Bound 1 * ‖W₀‖ ≤ B ∧
      ∀ T : ℝ, 0 ≤ T → T ≤ 1 / (B + 1) → B * T ≤ 1 := by
  dsimp only
  have hK := hkTransportH2Bound_nonneg (q := 1) (by norm_num)
  have hB : 0 < hkTransportH2Bound 1 * ‖W₀‖ + 1 := by positivity
  refine ⟨hB, by positivity, le_add_of_nonneg_right (by norm_num), ?_⟩
  intro T _hT htime
  apply (mul_le_mul_of_nonneg_left htime hB.le).trans
  rw [mul_one_div]
  rw [div_le_iff₀ (show 0 < hkTransportH2Bound 1 * ‖W₀‖ + 1 + 1 by positivity),
    one_mul]
  exact le_add_of_nonneg_right (by norm_num)

/-- The constructed transport remains in the supported H² ball and has the
prescribed weak initial trace. The characteristic data refer to the same field. -/
structure HkInvariantOutput {B : NNReal} {T R : ℝ} (hT : 0 ≤ T)
    (f G : C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B))
    (W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))) (w₀ : ℝ → ℝ) (c X Y w : ℝ → ℝ → ℝ) : Prop
    extends HkTransportData hT f w₀ c X Y w where
  /-- The fixed support enclosure holds on the closed interval. -/
  support : ∀ y t, t ∈ Icc (0 : ℝ) T → R < |y| → w y t = 0
  /-- The field represents the continuous curve in the invariant ball. -/
  representative : ∀ t,
    (oneDimensionalPushforwardL2 (G t).val : ℝ → ℝ) =ᵐ[volume] fun y ↦ w y t
  /-- The initial L² coordinate is the prescribed Sobolev datum. -/
  initial_base : (G ⟨0, le_rfl, hT⟩).val = wkpBaseCoordinateCLM W₀

/-- Every input curve in the supported H² ball constructs an output curve
in that same ball, with the initial datum and characteristic equation.
The numerical hypotheses concern only the input budget, time, and datum. -/
theorem exists_hkCurve_transport_in_h2_ball
    {B : NNReal} {T S R : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hBT : (B : ℝ) * T ≤ 1) (hR : S * Real.exp 2 ≤ R)
    (f : C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B))
    (W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀)
    (hW₀ : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] w₀)
    (hsupp₀ : ∀ x, S < |x| → w₀ x = 0)
    (hbudget : hkTransportH2Bound 1 * ‖W₀‖ ≤ B) :
    ∃ (c X Y w : ℝ → ℝ → ℝ)
      (G : C(Icc (0 : ℝ) T,
        supportedHkBaseBall 1 2 univ
          (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)),
      HkInvariantOutput hT f G W₀ w₀ c X Y w := by
  obtain ⟨c, X, Y, w, htransport, hwsupp, F, hF, hgraphs⟩ :=
    exists_hkCurve_transport_with_h2_output hT hS f W₀ hw₀ hW₀ hsupp₀
  have hsupport (y t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (hy : R < |y|) :
      w y t = 0 := by
    apply hwsupp y t ht
    apply lt_of_le_of_lt _ hy
    apply le_trans _ hR
    apply mul_le_mul_of_nonneg_left _ hS
    apply Real.exp_le_exp.mpr
    calc
      2 * (B : ℝ) * T = 2 * ((B : ℝ) * T) := by cas
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hBT (by norm_num)
      _ = 2 := by norm_num
  have hmem (t : Icc (0 : ℝ) T) : oneDimensionalPullbackL2 (F t) ∈
      supportedHkBaseBall 1 2 univ
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B := by
    apply (mem_supportedHkBaseBall_iff
      (measurableSet_Icc.preimage
        (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).continuous.measurable) _).mpr
    constructor
    · obtain ⟨W, hWbase, hWnorm⟩ := hgraphs t
      have hWq : ‖W‖ ≤ hkTransportH2Bound ((B : ℝ) * T) * ‖W₀‖ := by
        convert hWnorm using 1
        dsimp only [hkTransportH2Bound]
        simp only [mul_assoc]
        cas
      refine ⟨W, hWq.trans ((mul_le_mul_of_nonneg_right
        (hkTransportH2Bound_le (mul_nonneg B.coe_nonneg hT) hBT)
          (norm_nonneg W₀)).trans hbudget), ?_⟩
      simpa only [oneDimensionalPullbackL2_pushforward] using
        congrArg oneDimensionalPullbackL2 hWbase
    · have hm : MemLp (fun y ↦ w y t) 2 volume := (Lp.memLp (F t)).ae_eq (hF t)
      have hto : hm.toLp (fun y ↦ w y t) = F t :=
        Lp.ext (hm.coeFn_toLp.trans (hF t).symm)
      have hrep := oneDimensionalPullbackL2_toLp_ae hm
      rw [hto] at hrep
      filter_upwards [hrep] with x hx
      intro houtside
      rw [hx]
      exact hsupport ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) x) t t.property
        (lt_of_not_ge fun h ↦ houtside (abs_le.mp h))
  let G : C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B) :=
    ⟨fun t ↦ ⟨oneDimensionalPullbackL2 (F t), hmem t⟩,
      (oneDimensionalPullbackL2.continuous.comp F.continuous).subtype_mk _⟩
  have hG (t : Icc (0 : ℝ) T) :
      (oneDimensionalPushforwardL2 (G t).val : ℝ → ℝ) =ᵐ[volume] fun y ↦ w y t := by
    simpa only [G, ContinuousMap.coe_mk, oneDimensionalPushforwardL2_pullback] using hF t
  refine ⟨c, X, Y, w, G, {
    toHkTransportData := htransport
    support := hsupport
    representative := hG
    initial_base := ?_ }⟩
  apply oneDimensionalPushforwardL2.injective
  apply Lp.ext
  exact (hG ⟨0, le_rfl, hT⟩).trans
    ((Filter.EventuallyEq.of_eq (funext htransport.initial)).trans hW₀.symm)

end DeGregorio.Iteration
