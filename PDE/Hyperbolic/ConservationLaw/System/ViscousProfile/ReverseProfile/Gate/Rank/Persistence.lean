/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.FirstOrder

import PDE.Analysis.Calculus.Prod.SliceDerivative
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Full.Existence
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.State
import CAS.ExactTactic

/-!
# Persistence of gate determinants and nonzero tangent coefficients

The time, full flow, signed gate family, feedback thresholds, and two indices are
fixed. The physical speed variation is the derivative of that full flow.
Joint smoothness gives continuity of the flux and variation; the ordinary
state derivative of the gate is handled by the product-slice calculus theorem.

On the strict upper gate and inner feedback plateau, the normalized
right eigenvectors have two nonconstant rational entries. The concrete scalar
slope bounds keep their denominators positive even at zero delta. Two nonzero
base determinants therefore persist on one open parameter neighborhood. The
nonzero tangent expansion supplied by the full gate-rank theorem persists on that
same neighborhood: its coefficients are explicit continuous functions of the
flux and the triangular normalized eigenvectors.
-/

@[expose] public noncomputable section

open Filter Set
open PDE.Analysis
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- Two fixed nonzero gate determinants persist for the same supplied smooth full
flow. The neighborhood retains the strict gate and fast margins, and the concrete
flux is strictly hyperbolic there. Both determinant functions are proved continuous.
Assuming a nonzero base expansion, as supplied by the full gate-rank theorem, the coefficients
in the same normalized eigenvectors stay nonzero throughout the neighborhood. -/
theorem exists_prescribed_clock_gate_determinants_ne_zero_nhds
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3} {b : (Fin 3 → ℝ) × ℝ → ℝ} {A B t : ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hb : ContDiff ℝ ∞ b)
    (hsupport : ∀ c, tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10)) (c0 : Fin 3 → ℝ)
    (hab : A ^ 2 < B ^ 2) (hy : Ψ (t, ((0, c0), (0, 0))) 1 ∈ Ioo (205 : ℝ) (2051 / 10))
    (hz : 2 < Ψ (t, ((0, c0), (0, 0))) 2) (hzA : (Ψ (t, ((0, c0), (0, 0))) 2) ^ 2 < A ^ 2)
    (i j : Fin 3) (hij : i ≠ j) :
    let γ : (ℝ × (Fin 3 → ℝ)) → ℝ^3 := fun σ ↦ Ψ (t, (σ, (0, 0)))
    let v : (ℝ × (Fin 3 → ℝ)) → ℝ^3 := fun σ ↦
      concreteGatedFlux σ.1 (clockFeedback A B) (fun y ↦ b (σ.2, y)) (γ σ)
    let r : (ℝ × (Fin 3 → ℝ)) → Fin 3 → ℝ^3 := fun σ ↦
      GatedFlux.rightEigenvector (fastLogCosh σ.1) MiddleClock.g cutoff
        (clockFeedback A B) (fun y ↦ b (σ.2, y)) (γ σ)
    let W : (ℝ × (Fin 3 → ℝ)) → ℝ^3 := fun σ ↦
      prescribedClockFullVariation Ψ σ (1, 0) t
    let d : Fin 3 → (ℝ × (Fin 3 → ℝ)) → ℝ := fun k σ ↦
      Matrix.det ![⇑(v σ), ⇑(r σ k), ⇑(W σ)]
    d i (0, c0) ≠ 0 → d j (0, c0) ≠ 0 →
    (∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ v (0, c0) = ∑ k, a k • r (0, c0) k) →
      ∃ S : Set (ℝ × (Fin 3 → ℝ)), IsOpen S ∧ (0, c0) ∈ S ∧
        ContinuousOn (d i) S ∧ ContinuousOn (d j) S ∧
        ∀ σ ∈ S,
          γ σ 1 ∈ Ioo (205 : ℝ) (2051 / 10) ∧ 2 < γ σ 2 ∧ (γ σ 2) ^ 2 < A ^ 2 ∧
          |σ.1| < 1 / 4 ∧
          IsStrictlyHyperbolicAt
            (concreteGatedFlux σ.1 (clockFeedback A B) (fun y ↦ b (σ.2, y))) (γ σ) ∧
          i ≠ j ∧ d i σ ≠ 0 ∧ d j σ ≠ 0 ∧
          ∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ v σ = ∑ k, a k • r σ k := by
  intro γ v r W d hi hj hbasecoeff
  have hγ : ContDiff ℝ ∞ γ := hΨ.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hcoord (k : Fin 3) : Continuous (fun σ : ℝ × (Fin 3 → ℝ) ↦ γ σ k) :=
    ((show ContDiff ℝ ∞ (fun q : ℝ^3 ↦ q k) from
      contDiff_piLp_apply (2 : ENNReal)).comp hγ).continuous
  have hv : ContDiff ℝ ∞ v := by
    have hembed : ContDiff ℝ ∞ (fun σ : ℝ × (Fin 3 → ℝ) ↦ ((σ, (0 : ℝ)), γ σ)) :=
      (contDiff_id.prodMk contDiff_const).prodMk hγ
    simpa only [v, Function.comp_def, zero_smul, sub_zero] using
      (contDiff_prescribed_clock_full_field A B hb).comp hembed
  have hW : ContDiff ℝ ∞ W := by
    have hembed : ContDiff ℝ ∞ (fun σ : ℝ × (Fin 3 → ℝ) ↦ (t, σ)) :=
      contDiff_const.prodMk contDiff_id
    simpa only [W, Function.comp_def] using
      (contDiff_prescribedClockFullVariation hΨ (1, 0)).comp hembed
  have hbder : Continuous (fun u : (Fin 3 → ℝ) × ℝ ↦ deriv (fun y ↦ b (u.1, y)) u.2) :=
    (contDiff_deriv_prod_snd (m := 0) (f := b) (hb.of_le (by simp))).continuous
  have hkder : Continuous (fun u : ℝ × ℝ ↦ deriv (fastLogCosh u.1) u.2) :=
    (contDiff_deriv_prod_snd (m := 0) (f := fun u : ℝ × ℝ ↦ fastLogCosh u.1 u.2)
      (contDiff_fastLogCosh_joint.of_le (by simp))).continuous
  let O : Set (ℝ × (Fin 3 → ℝ)) := {σ | γ σ 1 ∈ Ioo (205 : ℝ) (2051 / 10) ∧
      2 < γ σ 2 ∧ (γ σ 2) ^ 2 < A ^ 2 ∧ |σ.1| < 1 / 4}
  have hOopen : IsOpen O := (isOpen_Ioo.preimage (hcoord 1)).inter
      ((isOpen_lt continuous_const (hcoord 2)).inter
        ((isOpen_lt ((hcoord 2).pow 2) continuous_const).inter
          (isOpen_lt continuous_fst.abs continuous_const)))
  have hO0 : ((0 : ℝ), c0) ∈ O := ⟨hy, hz, hzA, by simp only [abs_zero]; cas⟩
  have hgap (σ : ℝ × (Fin 3 → ℝ)) (hσ : σ ∈ O) :
      -deriv (fastLogCosh σ.1) (γ σ 0) < deriv MiddleClock.g (γ σ 1) ∧
        deriv MiddleClock.g (γ σ 1) < deriv (fastLogCosh σ.1) (γ σ 2) := by
    have hk0 := seven_fourths_lt_deriv_fastLogCosh hσ.2.2.2 (γ σ 0)
    have hk2 := seven_fourths_lt_deriv_fastLogCosh hσ.2.2.2 (γ σ 2)
    rcases abs_le.mp (MiddleClock.abs_deriv_g_le (γ σ 1)) with ⟨hglo, hghi⟩
    have hlo : (-(7 / 4) : ℝ) < deriv MiddleClock.g (γ σ 1) :=
      lt_of_lt_of_le (by cas) hglo
    have hhi : deriv MiddleClock.g (γ σ 1) < (7 / 4 : ℝ) :=
      lt_of_le_of_lt hghi (by cas)
    exact ⟨(neg_lt_neg hk0).trans hlo, hhi.trans hk2⟩
  have hbSlice (c : Fin 3 → ℝ) : ContDiff ℝ ∞ (fun y : ℝ ↦ b (c, y)) :=
    hb.comp (contDiff_const.prodMk contDiff_id)
  have hstate (σ : ℝ × (Fin 3 → ℝ)) (hσ : σ ∈ O) :=
    concreteGatedFlux_upward_gate_state_general (δ := σ.1) (q := γ σ)
      hab ((hbSlice σ.2).differentiable (by simp) (γ σ 1)) (hsupport σ.2) hσ.1.1 hσ.2.1 hσ.2.2.1
  have hbval : Continuous (fun σ : ℝ × (Fin 3 → ℝ) ↦ b (σ.2, γ σ 1)) :=
    hb.continuous.comp (continuous_snd.prodMk (hcoord 1))
  have hbslope : Continuous (fun σ : ℝ × (Fin 3 → ℝ) ↦ deriv (fun y ↦ b (σ.2, y)) (γ σ 1)) :=
    hbder.comp (continuous_snd.prodMk (hcoord 1))
  have hkslope (k : Fin 3) : Continuous
      (fun σ : ℝ × (Fin 3 → ℝ) ↦ deriv (fastLogCosh σ.1) (γ σ k)) :=
    hkder.comp (continuous_fst.prodMk (hcoord k))
  have hgslope : Continuous (fun σ : ℝ × (Fin 3 → ℝ) ↦ deriv MiddleClock.g (γ σ 1)) :=
    (MiddleClock.contDiff_g.continuous_deriv (by simp)).comp (hcoord 1)
  have hrone : ContinuousOn (fun σ : ℝ × (Fin 3 → ℝ) ↦ deriv (fun y ↦ b (σ.2, y)) (γ σ 1) * γ σ 2 /
        (deriv MiddleClock.g (γ σ 1) + deriv (fastLogCosh σ.1) (γ σ 0))) O := by
    refine (hbslope.mul (hcoord 2)).continuousOn.div₀ (hgslope.add (hkslope 0)).continuousOn ?_
    intro σ hσ
    apply ne_of_gt
    simpa only [sub_neg_eq_add] using sub_pos.mpr (hgap σ hσ).1
  have hrtwo : ContinuousOn (fun σ : ℝ × (Fin 3 → ℝ) ↦ b (σ.2, γ σ 1) /
        (deriv (fastLogCosh σ.1) (γ σ 2) + deriv (fastLogCosh σ.1) (γ σ 0))) O := by
    refine hbval.continuousOn.div₀ ((hkslope 2).add (hkslope 0)).continuousOn ?_
    intro σ hσ
    apply ne_of_gt
    simpa only [sub_neg_eq_add] using sub_pos.mpr ((hgap σ hσ).1.trans (hgap σ hσ).2)
  have hr (k : Fin 3) : ContinuousOn (fun σ ↦ r σ k) O := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun σ : O ↦ r σ k)
    have heq : (fun σ : O ↦ r σ k) = (fun σ : O ↦ ![!₂[1, 0, 0],
          !₂[deriv (fun y ↦ b (σ.val.2, y)) (γ σ 1) * γ σ 2 /
            (deriv MiddleClock.g (γ σ 1) + deriv (fastLogCosh σ.val.1) (γ σ 0)), 1, 0],
          !₂[b (σ.val.2, γ σ 1) / (deriv (fastLogCosh σ.val.1) (γ σ 2) +
            deriv (fastLogCosh σ.val.1) (γ σ 0)), 0, 1]] k) := by
      funext σ
      exact congrFun (hstate σ σ.property).2.2.1 k
    rw [heq]
    fin_cases k
    · exact continuous_const
    · exact (PiLp.continuous_toLp (2 : ENNReal) _).comp
        (hrone.domRestrict.matrixVecCons continuous_const)
    · exact (PiLp.continuous_toLp (2 : ENNReal) _).comp
        (hrtwo.domRestrict.matrixVecCons continuous_const)
  -- Extract the inverse triangular coordinates without another gate-state reduction.
  let a : (ℝ × (Fin 3 → ℝ)) → Fin 3 → ℝ := fun σ ↦
    ![v σ 0 - (r σ 1) 0 * v σ 1 - (r σ 2) 0 * v σ 2, v σ 1, v σ 2]
  have hsum (σ : ℝ × (Fin 3 → ℝ)) (hσ : σ ∈ O) (e : Fin 3 → ℝ) : (∑ k, e k • r σ k : ℝ^3) =
        !₂[e 0 + e 1 * (r σ 1) 0 + e 2 * (r σ 2) 0, e 1, e 2] := by
    rw [Fin.sum_univ_three]
    have heq := (hstate σ hσ).2.2.1
    change r σ = _ at heq
    rw [heq]
    ext k
    fin_cases k <;> simp
  have haDecomp (σ : ℝ × (Fin 3 → ℝ)) (hσ : σ ∈ O) :
      v σ = ∑ k, a σ k • r σ k := by
    rw [hsum σ hσ (a σ)]
    ext k
    fin_cases k
    · change v σ 0 = (v σ 0 - (r σ 1) 0 * v σ 1 - (r σ 2) 0 * v σ 2) +
        v σ 1 * (r σ 1) 0 + v σ 2 * (r σ 2) 0
      ring
    all_goals rfl
  obtain ⟨a0, ha0, hbaseexp⟩ := hbasecoeff
  rw [hsum _ hO0 a0] at hbaseexp
  have hbase1 : v (0, c0) 1 = a0 1 := by simpa using congrArg (· 1) hbaseexp
  have hbase2 : v (0, c0) 2 = a0 2 := by simpa using congrArg (· 2) hbaseexp
  have haBase : a (0, c0) = a0 := by
    funext k
    fin_cases k
    · change v _ 0 - (r _ 1) 0 * v _ 1 - (r _ 2) 0 * v _ 2 = a0 0
      rw [congrArg (· 0) hbaseexp, hbase1, hbase2]
      simp only [Matrix.cons_val_zero]
      ring
    · exact hbase1
    · exact hbase2
  have hvcoord (k : Fin 3) : Continuous (fun σ : ℝ × (Fin 3 → ℝ) ↦ v σ k) :=
    (show Continuous (fun q : ℝ^3 ↦ q k) from
      PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin 3 ↦ ℝ) k).comp hv.continuous
  have hrcoord (k l : Fin 3) : ContinuousOn (fun σ ↦ r σ k l) O :=
    (show Continuous (fun q : ℝ^3 ↦ q l) from
      PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin 3 ↦ ℝ) l).comp_continuousOn' (hr k)
  have haCont (k : Fin 3) : ContinuousOn (fun σ ↦ a σ k) O := by
    fin_cases k
    · exact ((hvcoord 0).continuousOn.sub ((hrcoord 1 0).mul (hvcoord 1).continuousOn)).sub
        ((hrcoord 2 0).mul (hvcoord 2).continuousOn)
    · exact (hvcoord 1).continuousOn
    · exact (hvcoord 2).continuousOn
  have haNear : ∀ᶠ σ in 𝓝 (0, c0), ∀ k : Fin 3, a σ k ≠ 0 := by
    refine Filter.eventually_all.mpr fun k ↦ ?_
    apply ((haCont k).continuousAt (hOopen.mem_nhds hO0)).eventually_ne
    simpa only [haBase] using ha0 k
  have hd (k : Fin 3) : ContinuousOn (d k) O := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    refine Continuous.matrix_det (continuous_pi fun l ↦ ?_)
    fin_cases l
    · exact (PiLp.continuous_ofLp (2 : ENNReal) (fun _ : Fin 3 ↦ ℝ)).comp
        (hv.continuous.comp continuous_subtype_val)
    · exact (PiLp.continuous_ofLp (2 : ENNReal) (fun _ : Fin 3 ↦ ℝ)).comp (hr k).domRestrict
    · exact (PiLp.continuous_ofLp (2 : ENNReal) (fun _ : Fin 3 ↦ ℝ)).comp
        (hW.continuous.comp continuous_subtype_val)
  have hgood : {σ | σ ∈ O ∧ d i σ ≠ 0 ∧ d j σ ≠ 0 ∧ ∀ k : Fin 3, a σ k ≠ 0} ∈ 𝓝 (0, c0) :=
    inter_mem (hOopen.mem_nhds hO0)
      ((((hd i).continuousAt (hOopen.mem_nhds hO0)).eventually_ne hi).and
        ((((hd j).continuousAt (hOopen.mem_nhds hO0)).eventually_ne hj).and haNear))
  obtain ⟨S, hSsub, hSopen, hS0⟩ := mem_nhds_iff.mp hgood
  have hSO : S ⊆ O := fun σ hσ ↦ (hSsub hσ).1
  refine ⟨S, hSopen, hS0, (hd i).mono hSO, (hd j).mono hSO, fun σ hσ ↦ ?_⟩
  have hσO := hSO hσ
  have hspectral : IsStrictlyHyperbolicAt
      (concreteGatedFlux σ.1 (clockFeedback A B) (fun y ↦ b (σ.2, y))) (γ σ) := by
    unfold concreteGatedFlux
    refine GatedFlux.isStrictlyHyperbolicAt (a := 100) (d := 205) (e := 2051 / 10)
      ((contDiff_fastLogCosh σ.1).differentiable (by simp))
      (MiddleClock.contDiff_g.differentiable (by simp))
      (contDiff_cutoff.differentiable (by simp))
      ((contDiff_clockFeedback A B).differentiable (by simp))
      ((hbSlice σ.2).differentiable (by simp)) (by cas) (by cas)
      (fun s hs ↦ cutoff_of_le hs) (fun s hs ↦ cutoff_of_ge hs) (hsupport σ.2) ?_ ?_
    · rw [(hstate σ hσO).2.1]
      exact (hgap σ hσO).1
    · rw [(hstate σ hσO).2.1]
      exact (hgap σ hσO).2
  exact ⟨hσO.1, hσO.2.1, hσO.2.2.1, hσO.2.2.2, hspectral, hij,
    (hSsub hσ).2.1, (hSsub hσ).2.2.1, a σ, (hSsub hσ).2.2.2, haDecomp σ hσO⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
