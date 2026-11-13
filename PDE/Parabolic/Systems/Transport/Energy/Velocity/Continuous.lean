/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Solution.Velocity
public import PDE.Analysis.Evolution.LionsMagenes.Dissipation
import PDE.Analysis.Evolution.Bochner.OperatorForcing


/-!
# A closed-time velocity estimate for strong solutions

The differentiated equation and its initial trace are derived from the original
transport-diffusion solution. The forcing produced by coefficient differentiation
is bounded using the state in H¹. No H¹ velocity bound enters the constant.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace Sobolev Laplacian
open scoped SobolevSpace.WholeSpaceHilbert

namespace PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution

variable {n m : ℕ} {ε a b : ℝ}

variable {B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ}
  {f : Fin m → ℝ × ℝ^n → ℝ} {q : (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))}
  {U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2 (volume.restrict (Ioc a b))}
  {G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2 (volume.restrict (Ioc a b))}
  {z : ℝ → (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))}

/-- An H² initial state and an H¹ state bound give a closed-time L² velocity
estimate. The initial velocity and differentiated weak equation are conclusions
of the original PDE, not additional assumptions. The displayed Laplacian term
can subsequently be bounded uniformly for mollified H¹ data. -/
theorem exists_velocity_bound
    (h : IsStrongTransportDiffusionSolution ε a b B f q U G z)
    (hab : a < b) (hε : 0 ≤ ε)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hB : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (F : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2 (volume.restrict (Ioc a b)))
    (hf : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F t p) x = f p (t, x))
    (dF : Lp (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) 2 (volume.restrict (Ioc a b)))
    (hF : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦
      (vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion (F t)) dF)
    (C dC : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ]
      PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ))
    (hC : ∀ t ∈ Icc a b, ∀ v : (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))), ∀ p,
      C t v p = vectorTransportCLM
        (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q)) (fun q ↦ v q) p)
    (hdC : ContinuousOn dC (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt C (dC t) (Icc a b) t)
    {K Kd Z : ℝ} (hK : 0 ≤ K) (hKd : 0 ≤ Kd) (hZ : 0 ≤ Z)
    (henergy : ∀ t ∈ Icc a b, ∀ v : (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))),
      2 * ⟪C t v, (vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion v⟫_ℝ
        ≤ K * ‖(vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion v‖ ^ 2)
    (hdBound : ∀ t ∈ Icc a b, ‖dC t‖ ≤ Kd)
    (hz : ∀ t ∈ Icc a b, ‖z t‖ ≤ Z)
    (Q : PiLp 2 (fun _ : Fin m ↦ W^{2,2}(ℝ^n)))
    (hq : ContinuousLinearMap.piLpMap 2
      (fun _ : Fin m ↦ lowerOrderCLM (by decide : 1 ≤ 2)) Q = q) :
    ∃ v : ℝ → (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)), ContinuousOn v (Icc a b) ∧
      (v =ᵐ[(volume.restrict (Ioc a b))] fun t ↦
        (vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion (G t)) ∧
      ∀ t ∈ Icc a b, ‖v t‖ ≤ Real.exp ((K + 1) * (b - a)) *
        (ε * ‖WithLp.toLp 2 (fun p ↦ Δ (Q p))‖ + ‖C a‖ * ‖q‖ +
          (((b - a)⁻¹ + 1) * max 1 (b - a)) *
            (‖(vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion.compLpL
              2 (volume.restrict (Ioc a b)) F‖ + ‖dF‖) +
          ‖dF‖ + Kd * ((measureUnivNNReal (volume.restrict (Ioc a b)) : ℝ) ^
            ((2 : ENNReal).toReal⁻¹) * Z)) := by
  let triple := vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ
  obtain ⟨Fc, g, E, _hFc, _hFcAE, hFcBound, hEquation, hInitial⟩ :=
    h.exists_velocityEvolution hab A hB F hf dF hF C dC hC hdC hderiv
  have hLap : vectorWeakLaplacianCLM q =
      triple.pivotToDual (WithLp.toLp 2 (fun p ↦ Δ (Q p))) := by
    rw [← hq]
    exact vectorWeakLaplacianCLM_lowerOrder_univ Q
  have hvInitial : E.representative a =
      ε • WithLp.toLp 2 (fun p ↦ Δ (Q p)) + (C a q + Fc a) := by
    apply triple.pivotToDual_injective
    rw [hInitial, hLap]
    simp only [triple, map_add, map_smul]
  have hInitialBound : ‖E.representative a‖ ≤
      ε * ‖WithLp.toLp 2 (fun p ↦ Δ (Q p))‖ + ‖C a‖ * ‖q‖ +
        (((b - a)⁻¹ + 1) * max 1 (b - a)) *
          (‖triple.inclusion.compLpL 2 (volume.restrict (Ioc a b)) F‖ + ‖dF‖) := by
    rw [hvInitial, ← add_assoc]
    refine norm_add₃_le.trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε]
    exact add_le_add_three le_rfl ((C a).le_opNorm q) (hFcBound a ⟨le_rfl, hab.le⟩)
  have hzLp : MemLp z 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn h.continuousOn
  let u := hzLp.toLp z
  have hu : (fun t ↦ u t) =ᵐ[(volume.restrict (Ioc a b))] z := hzLp.coeFn_toLp
  have huBound : ‖u‖ ≤ (measureUnivNNReal (volume.restrict (Ioc a b)) : ℝ) ^
      ((2 : ENNReal).toReal⁻¹) * Z := by
    refine Lp.norm_le_of_ae_bound hZ ?_
    filter_upwards [hu, ae_restrict_mem measurableSet_Ioc] with t hut ht
    exact hut ▸ hz t (Ioc_subset_Icc_self ht)
  have hrLp : MemLp (fun t ↦ dC t (z t)) 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn (hdC.clm_apply h.continuousOn)
  let r := hrLp.toLp (fun t ↦ dC t (z t))
  let R := dF + r
  have hr : (fun t ↦ r t) =ᵐ[(volume.restrict (Ioc a b))] fun t ↦ dC t (z t) := hrLp.coeFn_toLp
  have hR : (fun t ↦ R t) =ᵐ[(volume.restrict (Ioc a b))] fun t ↦ dF t + dC t (z t) := by
    filter_upwards [Lp.coeFn_add dF r, hr] with t ht hrt
    simpa only [R, Pi.add_apply, hrt] using ht
  have hRBound : ‖R‖ ≤ ‖dF‖ +
      Kd * ((measureUnivNNReal (volume.restrict (Ioc a b)) : ℝ) ^
            ((2 : ENNReal).toReal⁻¹) * Z) := by
    apply (norm_le_add_mul_of_ae_eq_add_clm u R dF dC ?_ ?_).trans
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left huBound hKd))
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hdBound t (Ioc_subset_Icc_self ht)
    · filter_upwards [hR, hu] with t hRt hut
      simpa only [hut] using hRt
  have hEq : ∀ᵐ t ∂(volume.restrict (Ioc a b)), g t = ε • vectorWeakLaplacianCLM (G t) +
      triple.pivotToDual (R t + C t (G t)) := by
    filter_upwards [hEquation, hR] with t hEt hRt
    rw [hEt, hRt]
    congr 2
    abel
  let : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) :=
    SobolevSpace.WholeSpaceHilbert.piH1InnerProductSpace
  have hEBound := E.norm_le_exp_mul_of_dissipative_equation hab.le hε hK G g R
    vectorWeakLaplacianCLM C vectorWeakLaplacianCLM_apply_self_nonpos
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact henergy t (Ioc_subset_Icc_self ht)) hEq
  refine ⟨E.representative, ?_, ?_, ?_⟩
  · simpa only [uIcc_of_le hab.le] using E.continuousOn
  · have he := E.ae_eq_inclusion
    rwa [uIcc_of_le hab.le, ← Measure.restrict_congr_set Ioc_ae_eq_Icc] at he
  · exact fun t ht ↦ (hEBound t ht).trans (mul_le_mul_of_nonneg_left
      ((add_le_add hInitialBound hRBound).trans_eq (by ring)) (Real.exp_nonneg _))

end PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution
