/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Interpolation.Strip.Rank
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Retained.Branches

import PDE.Analysis.Matrix.Determinant.Derivative

/-!
# Rank of the phase-aligned strip

The outgoing branch keeps the first speed derivative of the selected flow. A
translation by its moving event adds a multiple of the base tangent to that
variation. The incoming strip has the same first jet because its difference
from the outgoing strip has a smooth cubic factor. Consequently, blending the
two strips does not change their differential at zero speed.

The time interval is chosen from the retained determinant before the transition
function is supplied. The last theorem gives the derivative hypothesis of
`exists_smooth_compact_strip_state_chart` on that entire interval.

The input cubic strip must contain the selected gate time. The first-variation
and cubic identities are used on that common time interval; they do not extend
the domain on which either branch is known to satisfy its differential equation.
-/

@[expose] public noncomputable section

open Filter Function Set
open PDE.Analysis.ODE.StripRank
open scoped BigOperators ContDiff Matrix Matrix.Norms.Elementwise Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- Rank on an open arc and a compact subinterval, chosen before the transition.

`F` is the corrected outgoing family returned by the retained moving-event theorem;
`hretained` is its first-variation conclusion relative to the same selected `Ψ`.
`U,V,A` and `hphase,hcubic` are the phase-strip outputs on a gate-containing
interval. The normal vector is the fixed selected basis vector `rStar i`.

The only rank input is the nonvanishing determinant `hdet` at the selected time `tStar`. The cubic
strip's time coverage is stated explicitly because the phase theorem's interval need not contain
`tStar`. -/
theorem exists_selected_actual_strip_rank_arc {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hΨ : ContDiff ℝ ∞ Ψ) (σ : ℝ × (Fin 3 → ℝ)) {f : (ℝ^3) → ℝ^3} {q : ℝ → ℝ^3}
    (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q) (hqode : ∀ t, HasDerivAt q (f (q t)) t)
    {F U V : ℝ → ℝ → ℝ^3} {A : ℝ × ℝ → ℝ^3} {τ : ℝ → ℝ} {J : Set ℝ} {lo hi e tStar : ℝ}
    (hF : ContDiff ℝ ∞ F.uncurry) (hU : ContDiff ℝ ∞ U.uncurry) (hV : ContDiff ℝ ∞ V.uncurry)
    (hA : ContDiff ℝ ∞ A) (hτ : DifferentiableAt ℝ τ 0) (hτzero : τ 0 = e) (hJ : IsOpen J)
    (hzero : (0 : ℝ) ∈ J) (hFbase : EqOn (fun t ↦ F t 0) q (Icc lo hi))
    (hretained :
      EqOn (fun t ↦ deriv (F t) 0) (fun t ↦ deriv (retainedOutgoingBranch Ψ σ t) 0) (Icc lo hi))
    (hphase : ∀ μ ∈ J, ∀ t, U t μ = F (t + τ μ - e) μ)
    (hcubic : ∀ t ∈ Icc lo hi, ∀ μ ∈ J, V t μ - U t μ = μ ^ 3 • A (t, μ))
    (htStar : tStar ∈ Ioo lo hi) (rStar : Module.Basis (Fin 3) ℝ (ℝ^3)) (i : Fin 3)
    (hdet : Matrix.det
      ![⇑(f (q tStar)), ⇑(rStar i), ⇑(prescribedClockFullVariation Ψ σ (1, 0) tStar)] ≠ 0) :
    let W := prescribedClockFullVariation Ψ σ (1, 0)
    let ν := rStar i
    ∃ (O : Set ℝ) (a b : ℝ), IsOpen O ∧ tStar ∈ Ioo a b ∧
      Icc a b ⊆ O ∧ O ⊆ Ioo lo hi ∧
      (∀ t ∈ O, Matrix.det ![⇑(f (q t)), ⇑ν, ⇑(W t)] ≠ 0) ∧
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ →
        ContDiff ℝ ∞ (blendedStrip U V θ) ∧
        EqOn (fun t ↦ blendedStrip U V θ (t, 0)) q O ∧
        ∀ t ∈ O,
          HasFDerivAt
            (fun z : (ℝ × ℝ) × ℝ ↦ blendedStrip U V θ z.1 + z.2 • ν)
            (stripDifferential (f (q t)) (W t + deriv τ 0 • f (q t)) ν) ((t, 0), 0) ∧
          Matrix.det ![⇑(f (q t)), ⇑(W t + deriv τ 0 • f (q t)), ⇑ν] =
            -Matrix.det ![⇑(f (q t)), ⇑ν, ⇑(W t)] ∧
          ∃ D : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ℝ^3,
            (D : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ^3) =
              stripDifferential (f (q t)) (W t + deriv τ 0 • f (q t)) ν := by
  classical
  let W := prescribedClockFullVariation Ψ σ (1, 0)
  let ν := rStar i
  let v := fun t ↦ f (q t)
  have hW : ContDiff ℝ ∞ W := (contDiff_prescribedClockFullVariation hΨ (1, 0)).comp
      (contDiff_id.prodMk contDiff_const)
  have hv : ContDiff ℝ ∞ v := hf.comp hq
  have hdetContinuous : Continuous (fun t ↦ Matrix.det ![⇑(v t), ⇑ν, ⇑(W t)]) := by fun_prop
  let O := Ioo lo hi ∩ {t | Matrix.det ![⇑(v t), ⇑ν, ⇑(W t)] ≠ 0}
  have hO : IsOpen O := isOpen_Ioo.inter (isOpen_ne.preimage hdetContinuous)
  obtain ⟨a, b, _, hab, hcompact⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (hO.mem_nhds (⟨htStar, hdet⟩ : tStar ∈ O))
  -- These witnesses are fixed before θ occurs in the proof.
  refine ⟨O, a, b, hO, Icc_mem_nhds_iff.mp hab, hcompact, (fun t ht ↦ ht.1),
    (fun t ht ↦ ht.2), fun θ hθ ↦ ?_⟩
  have hw : ContDiff ℝ ∞ (blendedStrip U V θ) := hU.add ((hθ.comp contDiff_fst).smul (hV.sub hU))
  have hUzero (t : ℝ) (ht : t ∈ Icc lo hi) : U t 0 = q t := by
    rw [hphase 0 hzero t, hτzero, add_sub_cancel_right]
    exact hFbase ht
  have hjets (t : ℝ) (ht : t ∈ Icc lo hi) : V t 0 = U t 0 ∧ deriv (V t) 0 = deriv (U t) 0 :=
    firstJet_eq_of_cubic_difference hU hV hA hJ hzero (hcubic t ht)
  have hwzero : EqOn (fun t ↦ blendedStrip U V θ (t, 0)) q (Ioo lo hi) := fun t ht ↦ by
    simp only [blendedStrip, (hjets t (Ioo_subset_Icc_self ht)).1,
      sub_self, smul_zero, add_zero, hUzero t (Ioo_subset_Icc_self ht)]
  refine ⟨hw, hwzero.mono (fun t ht ↦ ht.1), fun t ht ↦ ?_⟩
  have htclosed : t ∈ Icc lo hi := Ioo_subset_Icc_self ht.1
  have hFtime : HasDerivAt (fun s ↦ F s 0) (v t) t := (hqode t).congr_of_eventuallyEq
    (eventually_of_mem (isOpen_Ioo.mem_nhds ht.1) fun s hs ↦ hFbase (Ioo_subset_Icc_self hs))
  have hFspeed : deriv (F t) 0 = W t :=
    (hretained htclosed).trans (hasDerivAt_retainedOutgoingBranch_speed hΨ σ t).deriv
  have hUspeed : HasDerivAt (U t) (W t + deriv τ 0 • v t) 0 :=
    hasDerivAt_phase_speed hF hτ hτzero hFtime hFspeed
      (eventually_of_mem (hJ.mem_nhds hzero) fun μ hμ ↦ hphase μ hμ t)
  have hVspeed : HasDerivAt (V t) (W t + deriv τ 0 • v t) 0 := by
    have hd : HasDerivAt (V t) (deriv (V t) 0) 0 :=
      ((hV.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) 0).hasDerivAt
    simpa only [(hjets t htclosed).2, hUspeed.deriv] using hd
  have hwspeed : HasDerivAt (fun μ ↦ blendedStrip U V θ (t, μ))
      (W t + deriv τ 0 • v t) 0 := by
    simpa only [blendedStrip, Pi.smul_apply, sub_self, smul_zero, add_zero] using
      hUspeed.fun_add ((hVspeed.fun_sub hUspeed).const_smul (θ t))
  have hwtime : HasDerivAt (fun s ↦ blendedStrip U V θ (s, 0)) (v t) t :=
    (hqode t).congr_of_eventuallyEq (eventually_of_mem (isOpen_Ioo.mem_nhds ht.1) hwzero)
  have hplane := hasFDerivAt_of_time_speed (U := fun s μ ↦ blendedStrip U V θ (s, μ))
    (hw.differentiable (by simp) (t, 0)) hwtime hwspeed
  have hfst : HasFDerivAt (fun z : (ℝ × ℝ) × ℝ ↦ z.1)
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) ((t, 0), 0) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun z : (ℝ × ℝ) × ℝ ↦ z.2)
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) ((t, 0), 0) := hasFDerivAt_snd
  have hfull := (hplane.comp ((t, 0), 0) hfst).fun_add (hsnd.smul_const ν)
  exact ⟨by simpa only [stripDifferential, Function.comp_def, uncurry] using hfull,
    det_phase_columns (v t) ν (W t) (deriv τ 0),
    exists_equiv_stripDifferential _ _ _ (by rw [det_phase_columns]; exact neg_ne_zero.mpr ht.2)⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
