/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Field
public import PDE.Analysis.Calculus.ImplicitRay

/-!
# Rarefaction profiles from local characteristic flows

Invert the speed along a characteristic trajectory jointly with its initial
state, then compose the inverse with the vector trajectory. The resulting
vector profile has speed equal to the similarity variable and satisfies the
self-similar conservation equation. Both inverse identities hold on product
neighborhoods, so endpoints and nearby initial states use the same inverse.

In the notation of the proof of Evans, §11.2.2, Theorem 1, `P (ξ, q)` is `v(G_k(ξ))`, where
`v` solves (6) with `v(0) = q` and `G_k = (F_k')^{-1}` inverts the speed `F_k'(w) = λ_k(v(w))`
of (8)-(9). We need `Dλ_k · r_k ≠ 0` only at `q₀`, the genuine nonlinearity (11) of §11.2.1 at
that state. The profile equation `DF(P) ∂_ξ P = ξ ∂_ξ P` makes `P (x/t, q)` a solution inside
the rarefaction fan.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equations (6)-(11); §11.2.2, Theorem 1 and its
  proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter
open Metric Set
open scoped Topology

/-- A transverse characteristic flow gives a local vector profile.
The profile remains jointly `C¹` in speed and initial state. Its conservation
identity follows from the eigenvector equation along the flow. -/
theorem exists_local_rarefaction_profile {m : ℕ} {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux)
    {R : ℝ × ℝ^m → ℝ^m} {q₀ : ℝ^m} (heig : ContDiffAt ℝ 1 C.speed q₀)
    (hR : ContDiffAt ℝ 1 R (0, q₀)) (hR₀ : R (0, q₀) = q₀)
    (hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      HasDerivAt (fun t ↦ R (t, p.2)) (C.rightEigenvector (R p)) p.1)
    (hκ : fderiv ℝ C.speed q₀ (C.rightEigenvector q₀) ≠ 0) :
    ∃ P : ℝ × ℝ^m → ℝ^m,
      P (C.speed q₀, q₀) = q₀ ∧ ContDiffAt ℝ 1 P (C.speed q₀, q₀) ∧
      (∀ᶠ p in 𝓝 (C.speed q₀, q₀),
        ContDiffAt ℝ 1 P p ∧ C.speed (P p) = p.1 ∧
        fderiv ℝ flux (P p) (deriv (fun ξ ↦ P (ξ, p.2)) p.1) =
          p.1 • deriv (fun ξ ↦ P (ξ, p.2)) p.1) ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ), q₀), P (C.speed (R p), p.2) = R p) := by
  let f : ℝ × ℝ^m → ℝ := fun p ↦ C.speed (R p)
  have heigR : ContDiffAt ℝ 1 C.speed (R (0, q₀)) := by
    simpa only [hR₀] using heig
  have hf : ContDiffAt ℝ 1 f (0, q₀) := heigR.comp (0, q₀) hR
  have hd : HasDerivAt (fun s ↦ f (s, q₀))
      (fderiv ℝ C.speed q₀ (C.rightEigenvector q₀)) 0 := by
    simpa only [Function.comp_def, hR₀] using
      heigR.differentiableAt_one.hasFDerivAt.comp_hasDerivAt 0 hflow.self_of_nhds
  obtain ⟨inverse, hi₀, hi, hright, hleft⟩ := PDE.Analysis.exists_implicit_inverse_family hf hd hκ
  have hf₀ : f (0, q₀) = C.speed q₀ := congrArg C.speed hR₀
  rw [hf₀] at hi₀ hi hright
  let parameter : ℝ × ℝ^m → ℝ × ℝ^m := fun p ↦ (inverse p, p.2)
  have hp₀ : parameter (C.speed q₀, q₀) = (0, q₀) := by
    simp only [parameter, hi₀]
  have hparam : ContDiffAt ℝ 1 parameter (C.speed q₀, q₀) := hi.prodMk contDiffAt_snd
  let P : ℝ × ℝ^m → ℝ^m := R ∘ parameter
  have hP₀ : P (C.speed q₀, q₀) = q₀ := by
    simp only [P, Function.comp_def, hp₀, hR₀]
  have hP : ContDiffAt ℝ 1 P (C.speed q₀, q₀) :=
    (show ContDiffAt ℝ 1 R (parameter (C.speed q₀, q₀)) from hp₀ ▸ hR).comp _ hparam
  have ht : Tendsto parameter (𝓝 (C.speed q₀, q₀)) (𝓝 (0, q₀)) := by
    simpa only [ContinuousAt, hp₀] using hparam.continuousAt
  refine ⟨P, hP₀, hP, ?_, ?_⟩
  · filter_upwards [hP.eventually (by simp), hi.eventually (by simp),
      ht.eventually hflow, hright] with p hPp hip hRp hspeed
    have hdi : HasDerivAt (fun ξ ↦ inverse (ξ, p.2)) (deriv (fun ξ ↦ inverse (ξ, p.2)) p.1) p.1 :=
      (hip.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt_one.hasDerivAt
    have hdP : HasDerivAt (fun ξ ↦ P (ξ, p.2))
        (deriv (fun ξ ↦ inverse (ξ, p.2)) p.1 • C.rightEigenvector (P p)) p.1 := hRp.scomp p.1 hdi
    have heigen : fderiv ℝ flux (P p) (C.rightEigenvector (P p)) =
        C.speed (P p) • C.rightEigenvector (P p) := (C.eigenvector (P p)).apply_eq_smul
    refine ⟨hPp, hspeed, ?_⟩
    rw [hdP.deriv, map_smul, heigen, show C.speed (P p) = p.1 from hspeed, smul_comm]
  · filter_upwards [hleft] with p hp
    change R (inverse (f p, p.2), p.2) = R p
    rw [hp]

/-- On a single neighborhood of zero strength and the base state, every closed
speed interval has the correct endpoint states, a regular conservative vector
profile and one norm bound fixed before choosing the two endpoint states. -/
theorem exists_uniform_rarefaction_profile {m : ℕ} {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux)
    {R : ℝ × ℝ^m → ℝ^m} {q₀ : ℝ^m} (heig : ContDiffAt ℝ 1 C.speed q₀)
    (hR : ContDiffAt ℝ 1 R (0, q₀)) (hzero : ∀ᶠ q in 𝓝 q₀, R (0, q) = q)
    (hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      HasDerivAt (fun t ↦ R (t, p.2)) (C.rightEigenvector (R p)) p.1)
    (hκ : fderiv ℝ C.speed q₀ (C.rightEigenvector q₀) ≠ 0) :
    ∃ P : ℝ × ℝ^m → ℝ^m, ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      P (C.speed p.2, p.2) = p.2 ∧ P (C.speed (R p), p.2) = R p ∧
      ∀ ξ ∈ uIcc (C.speed p.2) (C.speed (R p)),
        ContDiffAt ℝ 1 (fun η ↦ P (η, p.2)) ξ ∧
        C.speed (P (ξ, p.2)) = ξ ∧
        fderiv ℝ flux (P (ξ, p.2)) (deriv (fun η ↦ P (η, p.2)) ξ) =
          ξ • deriv (fun η ↦ P (η, p.2)) ξ ∧
        ‖P (ξ, p.2)‖ ≤ ‖q₀‖ + 1 := by
  have hR₀ := hzero.self_of_nhds
  obtain ⟨P, hP₀, hP, hprofile, hinverse⟩ := exists_local_rarefaction_profile C heig hR hR₀ hflow hκ
  have hbound : ∀ᶠ p in 𝓝 (C.speed q₀, q₀), ‖P p‖ < ‖q₀‖ + 1 := hP.continuousAt.norm
      (Iio_mem_nhds (by simpa only [hP₀] using lt_add_one ‖q₀‖))
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp (hprofile.and hbound)
  have hstate : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), p.2 ∈ ball q₀ η :=
    continuousAt_snd (ball_mem_nhds q₀ hη)
  have hfirst : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), C.speed p.2 ∈ ball (C.speed q₀) η :=
    (heig.continuousAt.comp continuousAt_snd) (ball_mem_nhds _ hη)
  have hsecond : ∀ᶠ p in 𝓝 (0, q₀), C.speed (R p) ∈ ball (C.speed q₀) η :=
    ((show ContinuousAt C.speed (R (0, q₀)) by simpa only [hR₀] using heig.continuousAt).comp
      hR.continuousAt) (by simpa only [Function.comp_def, hR₀] using ball_mem_nhds _ hη)
  have ht : Tendsto (fun p : ℝ × ℝ^m ↦ ((0 : ℝ), p.2))
      (𝓝 (0, q₀)) (𝓝 (0, q₀)) := continuousAt_const.prodMk continuousAt_snd
  have hz : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), R (0, p.2) = p.2 := (continuousAt_snd :
      ContinuousAt (Prod.snd : ℝ × ℝ^m → ℝ^m) (0, q₀)).tendsto.eventually hzero
  refine ⟨P, ?_⟩
  filter_upwards [hstate, hfirst, hsecond, hinverse, ht.eventually hinverse, hz]
    with p hq ha hb hi hi₀ hzp
  refine ⟨by simpa only [hzp] using hi₀, hi, fun ξ hξ ↦ ?_⟩
  obtain ⟨⟨hreg, hspeed, heq⟩, hnorm⟩ := hball (show (ξ, p.2) ∈ ball (C.speed q₀, q₀) η by
    rw [← ball_prod_same]
    exact ⟨(convex_ball (C.speed q₀) η).ordConnected.uIcc_subset ha hb hξ, hq⟩)
  exact ⟨hreg.comp ξ (contDiffAt_id.prodMk contDiffAt_const), hspeed, heq, hnorm.le⟩

end PDE.Hyperbolic.ConservationLaw.System
