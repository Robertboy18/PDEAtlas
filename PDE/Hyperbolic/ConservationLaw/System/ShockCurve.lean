/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ImplicitRay
public import PDE.Hyperbolic.ConservationLaw.System.AveragedSpectralFrame

/-!
# Local Rankine–Hugoniot curves

For a `C²` flux near a strictly hyperbolic state `u₀`, write the flux increment as
the averaged Jacobian applied to the displacement. Its ordered `C¹` eigenvectors
give the implicit equations `u - u₀ = s • rₖ(u)`. The state derivative at `s = 0`
is the identity, so these equations construct `C¹` curves with the expected tangents.

Every sufficiently small nonzero Rankine–Hugoniot jump lies on one of these curves.
Indeed, its displacement is an eigenvector of the averaged Jacobian. Expansion in
the nearby eigenbasis leaves only one nonzero coordinate; the implicit equation then
identifies the state. The parameter is the corresponding base-basis coordinate of
the displacement.

This is Theorem 2 (i)-(ii) of Evans, §11.2.3, the structure of the shock set, at the finite
regularity needed for the curves and speed limits; the expansion (iii) is in
`ShockCurve.Speed`. Evans constructs the curves from the equations (20), which use left
eigenvectors, and then derives the form (24), `φₖ(t) = z₀ + μ(t) r̂ₖ(φₖ(t))`; we solve this
equation, `u - u₀ = s • rₖ(u)`, directly. At zero displacement the Rankine–Hugoniot equation
holds for every speed, so speed classification is stated only for nonzero jumps.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, Theorem 2 and its proof, steps 1-5,
  equations (15)-(26).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Set
open scoped ContDiff Topology

/-- Construct and locally classify the Rankine–Hugoniot curves of a locally `C²`
flux strictly hyperbolic at `u₀`. Their tangents form an ordered eigenbasis of `Df u₀`.
The parameter equals a fixed linear coordinate of the displacement, and each speed
is `C¹` with base value the corresponding characteristic speed.

The state neighborhood classifies all nonzero jumps, with no prior bound on their
speed. Curve points in the common parameter neighborhood remain in the original
regularity domain. -/
theorem exists_local_shock_curves {m : ℕ} {flux : ℝ^m → ℝ^m} {U : Set (ℝ^m)} {u₀ : ℝ^m}
    (hU : IsOpen U) (hu₀ : u₀ ∈ U) (hflux : ContDiffOn ℝ 2 flux U)
    (hhyper : IsStrictlyHyperbolicAt flux u₀) :
    ∃ b : Module.Basis (Fin m) ℝ (ℝ^m),
    ∃ eig : Fin m → ℝ,
    ∃ S : Fin m → ℝ → ℝ^m,
    ∃ speed : Fin m → ℝ → ℝ,
    ∃ I : Set ℝ, ∃ V : Set (ℝ^m),
      StrictMono eig ∧
      (∀ k, fderiv ℝ flux u₀ (b k) = eig k • b k) ∧
      IsOpen I ∧ 0 ∈ I ∧ IsOpen V ∧ u₀ ∈ V ∧ V ⊆ U ∧
      (∀ k,
        S k 0 = u₀ ∧ speed k 0 = eig k ∧
        ContDiffOn ℝ 1 (S k) I ∧ ContDiffOn ℝ 1 (speed k) I ∧
        HasDerivAt (S k) (b k) 0 ∧
        ∀ s ∈ I, S k s ∈ U ∧
          RankineHugoniot flux u₀ (S k s) (speed k s) ∧
          b.equivFun (S k s - u₀) k = s) ∧
      ∀ u ∈ V, ∀ a : ℝ, u ≠ u₀ →
        (RankineHugoniot flux u₀ u a ↔
          ∃ k s, s ∈ I ∧ s ≠ 0 ∧ u = S k s ∧ a = speed k s) := by
  classical
  obtain ⟨b, eig, ψ, W, horder, hW, huW, hWU, hbase, hψ, hframe⟩ :=
    exists_local_averaged_spectral_frame (n := 1) hU hu₀ hflux hhyper
  let B := PDE.Analysis.averagedFDeriv flux u₀
  let c (k : Fin m) : ℝ^m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj k).comp b.equivFunL.toContinuousLinearMap
  have hbranches (k : Fin m) := PDE.Analysis.exists_implicit_ray
      ((hψ k).contDiffAt (hW.mem_nhds huW)).fst
  choose S hS0 hS htan heq hlocal using hbranches
  let speed : Fin m → ℝ → ℝ := fun k s ↦ (ψ k (S k s)).2
  have hspeed0 (k : Fin m) : speed k 0 = eig k := by
    simp only [speed, hS0 k, hbase k]
  have hspeed (k : Fin m) : ContDiffAt ℝ 1 (speed k) 0 := by
    have hp : ContDiffAt ℝ 1 (ψ k) (S k 0) := by
      simpa only [show ((1 : ℕ) : ℕ∞ω) = 1 from rfl, hS0 k] using
        (hψ k).contDiffAt (hW.mem_nhds huW)
    exact (hp.comp 0 (hS k)).snd
  have hgood (k : Fin m) : ∀ᶠ s in 𝓝 0, ContDiffAt ℝ 1 (S k) s ∧ ContDiffAt ℝ 1 (speed k) s ∧
        S k s ∈ W ∧ RankineHugoniot flux u₀ (S k s) (speed k s) ∧
        c k (S k s - u₀) = s := by
    have hST : Tendsto (S k) (𝓝 0) (𝓝 u₀) := by
      simpa only [ContinuousAt, hS0 k] using (hS k).continuousAt
    filter_upwards [(hS k).eventually (by simp), (hspeed k).eventually (by simp),
      hST (hW.mem_nhds huW), heq k] with s hs hσs hsW hray
    have heigen := ((hframe (S k s) hsW).2.2.1 k).1.apply_eq_smul
    simp only [ContinuousLinearMap.coe_coe] at heigen
    have hnorm := ((hframe (S k s) hsW).2.2.1 k).2
    refine ⟨hs, hσs, hsW, ?_, ?_⟩
    · change flux (S k s) - flux u₀ = (ψ k (S k s)).2 • (S k s - u₀)
      rw [← (hframe (S k s) hsW).1, hray, map_smul, heigen, smul_comm]
    · rw [hray, map_smul]
      change s * b.equivFun (ψ k (S k s)).1 k = s
      rw [hnorm, mul_one]
  obtain ⟨I, hIsub, hI, h0I⟩ := _root_.mem_nhds_iff.mp (Filter.eventually_all.mpr hgood)
  have hclass (k : Fin m) : ∀ᶠ u in 𝓝 u₀, c k (u - u₀) ∈ I ∧
        (u - u₀ = c k (u - u₀) • (ψ k u).1 ↔ S k (c k (u - u₀)) = u) := by
    have hc : ContinuousAt (fun u ↦ c k (u - u₀)) u₀ :=
      (c k).continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    have ht : Tendsto (fun u ↦ (c k (u - u₀), u)) (𝓝 u₀) (𝓝 (0, u₀)) := by
      simpa only [ContinuousAt, id, sub_self, map_zero] using hc.prodMk continuousAt_id
    have hInear : ∀ᶠ u in 𝓝 u₀, c k (u - u₀) ∈ I :=
      hc (by simpa only [sub_self, map_zero] using hI.mem_nhds h0I)
    exact hInear.and (ht.eventually (hlocal k))
  have hWnear : ∀ᶠ u in 𝓝 u₀, u ∈ W := hW.mem_nhds huW
  obtain ⟨V, hVsub, hV, huV⟩ :=
    _root_.mem_nhds_iff.mp (hWnear.and (Filter.eventually_all.mpr hclass))
  refine ⟨b, eig, S, speed, I, V, horder, fun k ↦ by
      simpa only [ContinuousLinearMap.coe_coe, PDE.Analysis.averagedFDeriv_self, hbase k] using
        ((hframe u₀ huW).2.2.1 k).1.apply_eq_smul, hI, h0I, hV, huV,
    fun u hu ↦ hWU (hVsub hu).1, fun k ↦ ⟨hS0 k, hspeed0 k,
      fun s hs ↦ ((hIsub hs k).1).contDiffWithinAt, fun s hs ↦ ((hIsub hs k).2.1).contDiffWithinAt,
      by simpa only [hbase k] using htan k,
      fun s hs ↦ ⟨hWU (hIsub hs k).2.2.1, (hIsub hs k).2.2.2.1, (hIsub hs k).2.2.2.2⟩⟩,
    fun u hu a hune ↦ ⟨fun hRH ↦ ?_, ?_⟩⟩
  · obtain ⟨bu, hbu⟩ := (hframe u (hVsub hu).1).2.2.2
    have hdiag (j : Fin m) : B u (bu j) = (ψ j u).2 • bu j := by
      rw [hbu j]
      simpa only [ContinuousLinearMap.coe_coe] using
        ((hframe u (hVsub hu).1).2.2.1 j).1.apply_eq_smul
    have hjump : B u (u - u₀) = a • (u - u₀) := (hframe u (hVsub hu).1).1.trans hRH
    obtain ⟨k, ha, hline⟩ := bu.exists_eq_smul_of_apply_eq_smul
      (B u).toLinearMap (fun j ↦ (ψ j u).2)
      (hframe u (hVsub hu).1).2.1.injective hdiag (sub_ne_zero.mpr hune) hjump
    have hc : c k (u - u₀) = bu.equivFun (u - u₀) k := by
      rw [congrArg (c k) hline, map_smul, hbu k]
      change bu.equivFun (u - u₀) k * b.equivFun (ψ k u).1 k = _
      rw [((hframe u (hVsub hu).1).2.2.1 k).2, mul_one]
    have hray : u - u₀ = c k (u - u₀) • (ψ k u).1 := by rw [hc, ← hbu k]; exact hline
    have hstate : S k (c k (u - u₀)) = u := ((hVsub hu).2 k).2.mp hray
    exact ⟨k, c k (u - u₀), ((hVsub hu).2 k).1,
      fun hz ↦ (sub_ne_zero.mpr hune) (by rw [hray, hz, zero_smul]), hstate.symm,
      by simpa only [speed, hstate] using ha⟩
  · rintro ⟨k, s, hs, _hsne, rfl, rfl⟩
    exact (hIsub hs k).2.2.2.1

end PDE.Hyperbolic.ConservationLaw.System
