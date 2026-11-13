/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ImplicitFunction.RegularLevel
public import PDE.Common.Euclidean

import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Analysis.Calculus.Prod.SliceDerivative

/-!
# The moving zero section of the full prescribed flow

The full flow retains its supplied reference on a closed time slab. A transverse
zero of the reference's middle coordinate at an interior time therefore gives a
smooth moving zero of that same full flow. The regular-level theorem
supplies the event and its local uniqueness on one parameter neighborhood.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- An interior transverse zero of the retained reference gives a smooth zero
section of the same full flow. Parameters are `((δ,c),(μ,a))`. The event stays
inside the supplied slab and flow neighborhood; uniqueness is a germ at the
base parameter and time. -/
theorem exists_prescribed_clock_full_event {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))} {cStar : Fin 3 → ℝ} {γ : ℝ → ℝ^3} {H τ0 v : ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hN : IsOpen N) (hbase : ((0, cStar), (0, 0)) ∈ N)
    (hτ : τ0 ∈ Ioo (0 : ℝ) H) (href : EqOn (fun t ↦ Ψ (t, ((0, cStar), (0, 0)))) γ (Icc (0 : ℝ) H))
    (hsection : γ τ0 1 = 0) (htransverse : HasDerivAt (fun t ↦ γ t 1) v τ0) (hv : v ≠ 0) :
    ∃ (T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ)
      (V : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))),
      IsOpen V ∧ ((0, cStar), (0, 0)) ∈ V ∧ V ⊆ N ∧ ContDiffOn ℝ ∞ T V ∧
      T ((0, cStar), (0, 0)) = τ0 ∧
      (∀ p ∈ V, T p ∈ Ioo (0 : ℝ) H ∧ Ψ (T p, p) 1 = 0) ∧
      ∀ᶠ q in 𝓝 (((0, cStar), (0, 0)), τ0),
        Ψ (q.2, q.1) 1 = 0 ↔ T q.1 = q.2 := by
  let θ₀ : (ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ) := ((0, cStar), (0, 0))
  let Y : (((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) × ℝ) → ℝ := fun q ↦ Ψ (q.2, q.1) 1
  have hY : ContDiff ℝ ∞ Y := (show ContDiff ℝ ∞ (fun u : ℝ^3 ↦ u 1) from
      contDiff_piLp_apply (2 : ENNReal)).comp (hΨ.comp (contDiff_snd.prodMk contDiff_fst))
  have hYbase : Y (θ₀, τ0) = 0 :=
    (congrArg (fun u : ℝ^3 ↦ u 1) (href (Ioo_subset_Icc_self hτ))).trans hsection
  have hsame : (fun t ↦ Y (θ₀, t)) =ᶠ[𝓝 τ0] (fun t ↦ γ t 1) := by
    filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with t ht using congrArg (fun u : ℝ^3 ↦ u 1) (href ht)
  have htime : HasDerivAt (fun t ↦ Y (θ₀, t)) v τ0 := htransverse.congr_of_eventuallyEq hsame
  have hpartial : fderiv ℝ Y (θ₀, τ0) (0, 1) ≠ 0 := by
    have heq : fderiv ℝ Y (θ₀, τ0) (0, 1) = v :=
      (deriv_prod_timeSlice Y θ₀ τ0 ((hY.differentiable (by simp)) (θ₀, τ0))).symm.trans htime.deriv
    exact fun hzero ↦ hv (heq.symm.trans hzero)
  have hYon : ContDiffOn ℝ (⊤ : ℕ∞) Y (N ×ˢ Ioo (0 : ℝ) H) := hY.contDiffOn
  obtain ⟨T, V, hV, hbaseV, hT, hTbase, hgraph, hunique⟩ :=
    hYon.exists_implicitFunction_of_fderiv_snd_ne_zero (hN.prod isOpen_Ioo) (by simp)
      (show (θ₀, τ0) ∈ N ×ˢ Ioo (0 : ℝ) H from ⟨hbase, hτ⟩) hpartial
  refine ⟨T, V, hV, hbaseV, fun p hp ↦ (hgraph p hp).1.1, hT, hTbase, ?_, ?_⟩
  · exact fun p hp ↦ ⟨(hgraph p hp).1.2, (hgraph p hp).2.trans hYbase⟩
  · change ∀ᶠ q in 𝓝 (θ₀, τ0), Y q = 0 ↔ T q.1 = q.2
    simpa only [hYbase] using hunique

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
