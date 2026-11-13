/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Rarefaction
public import PDE.Analysis.ODE.SmoothDependence.Local

/-!
# Normalized flows of linearly degenerate characteristic fields

The ordered operator frame constructs a local eigenfield normalized by a fixed
base coordinate. The ODE constructor supplies its integral curve.
Linear degeneracy gives constant characteristic speed and Rankine–Hugoniot, while
the normalization makes the coordinate of the displacement exactly the time.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped ContDiff Topology

/-- Construct a normalized characteristic integral curve of a linearly
degenerate family from the flux. The coordinate, constant-speed and jump
identities are proved along the constructed trajectory. -/
theorem exists_normalized_linearly_degenerate_flow {m : ℕ} {flux : ℝ^m → ℝ^m} {u₀ : ℝ^m} {k : Fin m}
    (hflux : ContDiff ℝ 2 flux) (hhyper : IsStrictlyHyperbolicAt flux u₀)
    (hld : IsLinearlyDegenerateFamily flux k) (b : Module.Basis (Fin m) ℝ (ℝ^m))
    (heigen : ∀ j, fderiv ℝ flux u₀ (b j) = characteristicSpeed flux j u₀ • b j) :
    ∃ r : ℝ^m → ℝ^m, ∃ R : ℝ → ℝ^m, ∃ V : Set (ℝ^m), ∃ ε : ℝ,
      IsOpen V ∧ u₀ ∈ V ∧ 0 < ε ∧
      ContDiffOn ℝ 1 r V ∧ r u₀ = b k ∧ R 0 = u₀ ∧
      ContDiffOn ℝ 1 R (Ioo (-ε) ε) ∧
      (∀ u ∈ V,
        Module.End.HasEigenvector (fderiv ℝ flux u).toLinearMap
          (characteristicSpeed flux k u) (r u) ∧ b.equivFun (r u) k = 1) ∧
      ∀ s ∈ Ioo (-ε) ε,
        R s ∈ V ∧ HasDerivAt R (r (R s)) s ∧ b.equivFun (R s - u₀) k = s ∧
        characteristicSpeed flux k (R s) = characteristicSpeed flux k u₀ ∧
        RankineHugoniot flux u₀ (R s) (characteristicSpeed flux k u₀) := by
  obtain ⟨ψ, hbase, W, hW, hAW, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame
      b (fderiv ℝ flux u₀) (fun j ↦ characteristicSpeed flux j u₀)
      heigen (characteristicSpeed_spec hhyper).1
  let r : ℝ^m → ℝ^m := fun u ↦ (ψ k (fderiv ℝ flux u)).1
  have hD : ContDiff ℝ 1 (fderiv ℝ flux) := hflux.fderiv_right le_rfl
  let V : Set (ℝ^m) := fderiv ℝ flux ⁻¹' W
  have hV : IsOpen V := hW.preimage hD.continuous
  have huV : u₀ ∈ V := hAW
  have hr : ContDiffOn ℝ 1 r V := fun u hu ↦
    ((((hframe _ hu).2.1 k).1.of_le (by simp)).comp u hD.contDiffAt).fst.contDiffWithinAt
  have hr₀ : r u₀ = b k := congrArg Prod.fst (hbase k)
  have hfield (u : ℝ^m) (hu : u ∈ V) : Module.End.HasEigenvector (fderiv ℝ flux u).toLinearMap
        (characteristicSpeed flux k u) (r u) ∧ b.equivFun (r u) k = 1 := by
    obtain ⟨hord, hvec, c, hc⟩ := hframe _ hu
    have hcanonical := congrFun (characteristicSpeed_eq_of_eigenbasis c hord
      (fun j ↦ by rw [hc j]; exact (hvec j).2.1.apply_eq_smul)) k
    exact ⟨hcanonical.symm ▸ (hvec k).2.1, (hvec k).2.2⟩
  obtain ⟨flow, hflow₀, hflowreg, hflowzero, hflow⟩ :=
    PDE.Analysis.ODE.exists_local_flow_of_contDiffAt (hr.contDiffAt (hV.mem_nhds huV))
  have hdeg : ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℝ (characteristicSpeed flux k) u ∧
      fderiv ℝ (characteristicSpeed flux k) u (r u) = 0 ∧
      fderiv ℝ flux u (r u) = characteristicSpeed flux k u • r u :=
    eventually_of_mem (hV.mem_nhds huV) fun u hu ↦
      ⟨(hld u).1, (hld u).2 (r u) (hfield u hu).1, (hfield u hu).1.apply_eq_smul⟩
  obtain ⟨δ, hδ, hcontact⟩ := exists_uniform_contact_of_local_flow
    (hflux.differentiable (by norm_num)) hflowreg.continuousAt
    (hflowzero.mono fun _ h ↦ h.1) hflow hdeg
  let R : ℝ → ℝ^m := fun s ↦ flow (s, u₀)
  have hR₀ : R 0 = u₀ := hflow₀
  have hRreg : ContDiffAt ℝ 1 R 0 := hflowreg.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hRflow : ∀ᶠ s in 𝓝 0, HasDerivAt R (r (R s)) s :=
    (continuousAt_id.prodMk continuousAt_const).tendsto.eventually hflow
  have hRV : ∀ᶠ s in 𝓝 0, R s ∈ V := hRreg.continuousAt (hR₀.symm ▸ hV.mem_nhds huV)
  have hgood : ∀ᶠ s in 𝓝 0, ContDiffAt ℝ 1 R s ∧ R s ∈ V ∧ HasDerivAt R (r (R s)) s ∧
      characteristicSpeed flux k (R s) = characteristicSpeed flux k u₀ ∧
      RankineHugoniot flux u₀ (R s) (characteristicSpeed flux k u₀) := by
    have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
    filter_upwards [hRreg.eventually (by simp), hRV, hRflow, isOpen_Ioo.mem_nhds hzero]
      with s hs hsV hsflow hsδ using ⟨hs, hsV, hsflow, hcontact u₀ (mem_ball_self hδ) s hsδ⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hinterval {s : ℝ} (hs : s ∈ Ioo (-ε) ε) :
      ContDiffAt ℝ 1 R s ∧ R s ∈ V ∧ HasDerivAt R (r (R s)) s ∧
      characteristicSpeed flux k (R s) = characteristicSpeed flux k u₀ ∧
      RankineHugoniot flux u₀ (R s) (characteristicSpeed flux k u₀) :=
    hball (Real.ball_zero_eq_Ioo ε ▸ hs)
  let c : ℝ^m →L[ℝ] ℝ := (ContinuousLinearMap.proj k).comp b.equivFunL.toContinuousLinearMap
  have hcoord {s : ℝ} (hs : s ∈ Ioo (-ε) ε) : c (R s - u₀) = s := by
    have hderiv (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
        HasDerivAt (fun a ↦ c (R a - u₀) - a) 0 t := by
      have hd := c.hasFDerivAt.comp_hasDerivAt t ((hinterval ht).2.2.1.sub_const u₀)
      have hc : c (r (R t)) = 1 := (hfield _ (hinterval ht).2.1).2
      simpa only [Function.comp_def, Pi.sub_def, id, hc, sub_self] using hd.sub (hasDerivAt_id t)
    have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
    have heq := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun t ht ↦ (hderiv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (hderiv t ht).deriv) hs hzero
    simpa only [hR₀, sub_self, map_zero, sub_zero, sub_eq_zero] using heq
  exact ⟨r, R, V, ε, hV, huV, hε, hr, hr₀, hR₀, fun s hs ↦ (hinterval hs).1.contDiffWithinAt,
    hfield, fun s hs ↦ ⟨(hinterval hs).2.1, (hinterval hs).2.2.1, hcoord hs, (hinterval hs).2.2.2⟩⟩

end PDE.Hyperbolic.ConservationLaw.System
