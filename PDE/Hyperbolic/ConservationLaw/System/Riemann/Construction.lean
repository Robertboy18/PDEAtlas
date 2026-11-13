/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Riemann.ElementaryChain
public import PDE.Hyperbolic.ConservationLaw.System.Riemann.WeakSolution
import PDE.Hyperbolic.ConservationLaw.System.Rarefaction.Fan
import PDE.Hyperbolic.ConservationLaw.System.PlanarShock

/-!
# Weak Riemann solutions from local wave curves

The characteristic construction supplies shock curves and integral
curves. Their local regularity gives bounded weak elementary waves in fixed
speed intervals. Local strength inversion keeps all prefix states inside the
same construction neighborhoods; separated-wave gluing then constructs the
weak solution from the flux and characteristic-family hypotheses.

`exists_local_riemann_wave_decomposition` follows the proof of Evans, §11.2.4, Theorem 4: the
states `state k` are the `z_k` of (44)-(45), each joined to the next by a wave of family `k`,
and the speed windows `(lo k, hi k)` are ordered and disjoint, as in step 4 of that proof.
`exists_local_riemann_weak_solution` is Theorem 4 for the weak equation on `t > 0`;
`exists_local_riemann_initialValue_solution` adds the Riemann datum as initial trace.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.4, Theorem 4 and its proof, equations (44)-(49).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

private theorem exists_bounded_weak_shock {m : ℕ} {flux : ℝ^m → ℝ^m} {left right : ℝ^m}
    {σ lo hi K : ℝ} (hRH : RankineHugoniot flux left right σ) (hlo : lo ≤ σ) (hhi : σ ≤ hi)
    (hleft : ‖left‖ ≤ K) (hright : ‖right‖ ≤ K) :
    ∃ u : ℝ^2 → ℝ^m,
      IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
      (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
      (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
      (∀ p : ℝ^2, 0 < p 0 → p 1 < lo * p 0 → u p = left) ∧
      (∀ p : ℝ^2, 0 < p 0 → hi * p 0 ≤ p 1 → u p = right) := by
  refine ⟨planarShock left right σ, hRH.isWeakSolution_planarShock.mono_domain le_top,
    measurable_planarShock left right σ,
    fun p _ ↦ (norm_planarShock_le_max left right σ p).trans (max_le hleft hright),
    fun _ hc p ↦ planarShock_smul_of_pos hc left right σ p,
    fun p ht hp ↦ planarShock_apply_of_mem (hp.trans_le (mul_le_mul_of_nonneg_right hlo ht.le)),
    fun p ht hp ↦ planarShock_apply_of_not_mem
      (not_lt.mpr ((mul_le_mul_of_nonneg_right hhi ht.le).trans hp))⟩

/-- Local shock and characteristic-flow equations produce uniformly bounded
weak waves in every speed interval containing the base characteristic speed. -/
theorem eventually_exists_bounded_weak_wave {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 1 flux)
    (C : CharacteristicField flux) (gn : Prop) [Decidable gn] {S R T : ℝ × ℝ^m → ℝ^m}
    {speed : ℝ × ℝ^m → ℝ} {q₀ : ℝ^m} {lo hi : ℝ} (heig : ContDiffAt ℝ 1 C.speed q₀)
    (hS : ContDiffAt ℝ 1 S (0, q₀)) (hR : ContDiffAt ℝ 1 R (0, q₀))
    (hspeed : ContDiffAt ℝ 1 speed (0, q₀))
    (hzero : ∀ᶠ q in 𝓝 q₀, S (0, q) = q ∧ R (0, q) = q ∧ speed (0, q) = C.speed q)
    (hbranch : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), T p = (if gn then if p.1 ≤ 0 then S p else R p else R p))
    (hRH : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), RankineHugoniot flux p.2 (S p) (speed p))
    (hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      HasDerivAt (fun t ↦ R (t, p.2)) (C.rightEigenvector (R p)) p.1)
    (hpositive : gn → 0 < fderiv ℝ C.speed q₀ (C.rightEigenvector q₀))
    (hdegenerate : ¬gn → C.IsLinearlyDegenerate) (hwindow : C.speed q₀ ∈ Ioo lo hi) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∃ u : ℝ^2 → ℝ^m,
      IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
      (∀ z : ℝ^2, 0 < z 0 → ‖u z‖ ≤ ‖q₀‖ + 1) ∧
      (∀ c : ℝ, 0 < c → ∀ z, u (c • z) = u z) ∧
      (∀ z : ℝ^2, 0 < z 0 → z 1 < lo * z 0 → u z = p.2) ∧
      (∀ z : ℝ^2, 0 < z 0 → hi * z 0 ≤ z 1 → u z = T p) := by
  have hz := hzero.self_of_nhds
  have hSnorm : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ‖S p‖ ≤ ‖q₀‖ + 1 := Eventually.mono
    (hS.continuousAt.norm (Iio_mem_nhds (by simpa only [hz.1] using lt_add_one ‖q₀‖)))
    fun _ h ↦ le_of_lt h
  have hRnorm : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ‖R p‖ ≤ ‖q₀‖ + 1 := Eventually.mono
    (hR.continuousAt.norm (Iio_mem_nhds (by simpa only [hz.2.1] using lt_add_one ‖q₀‖)))
    fun _ h ↦ le_of_lt h
  have hqnorm : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), ‖p.2‖ ≤ ‖q₀‖ + 1 := Eventually.mono
    (continuousAt_snd.norm (Iio_mem_nhds (lt_add_one ‖q₀‖))) fun _ h ↦ le_of_lt h
  have hspeedLeft : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), C.speed p.2 ∈ Ioo lo hi :=
    (heig.continuousAt.comp continuousAt_snd) (Ioo_mem_nhds hwindow.1 hwindow.2)
  have hspeedRight : ∀ᶠ p in 𝓝 (0, q₀), C.speed (R p) ∈ Ioo lo hi := by
    have heigR : ContinuousAt C.speed (R (0, q₀)) := by
      simpa only [hz.2.1] using heig.continuousAt
    exact (heigR.comp hR.continuousAt) (by
      simpa only [Function.comp_def, hz.2.1] using Ioo_mem_nhds hwindow.1 hwindow.2)
  have hσ : ∀ᶠ p in 𝓝 (0, q₀), speed p ∈ Ioo lo hi :=
    hspeed.continuousAt (by
      simpa only [hz.2.2] using Ioo_mem_nhds hwindow.1 hwindow.2)
  by_cases hgn : gn
  · obtain ⟨P, hP⟩ := exists_uniform_rarefaction_profile C heig hR
      (hzero.mono fun _ h ↦ h.2.1) hflow (hpositive hgn).ne'
    have htan : HasDerivAt (fun t ↦ R (t, q₀)) (C.rightEigenvector q₀) 0 := by
      simpa only [hz.2.1] using hflow.self_of_nhds
    obtain ⟨δ, hδ, hmono⟩ := exists_uniform_speed_expansion heig hR hz.2.1 htan (hpositive hgn)
    have hzeroP : ∀ᶠ p : ℝ × ℝ^m in 𝓝 (0, q₀), R (0, p.2) = p.2 :=
      (continuousAt_snd : ContinuousAt (Prod.snd : ℝ × ℝ^m → ℝ^m)
        (0, q₀)).tendsto.eventually (hzero.mono fun _ h ↦ h.2.1)
    filter_upwards [hbranch, hRH, hP, hSnorm, hqnorm, hspeedLeft, hspeedRight, hσ, hzeroP,
      ball_mem_nhds ((0 : ℝ), q₀) hδ]
      with p hT hjump hPp hSp hqp hspeedLeftp hspeedRightp hσp hzp hp
    by_cases hs : p.1 ≤ 0
    · rw [ite_eq_left hgn, ite_eq_left hs] at hT
      rw [hT]
      exact exists_bounded_weak_shock hjump hσp.1.le hσp.2.le hqp hSp
    · rw [ite_eq_left hgn, ite_eq_right hs] at hT
      rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hp
      have horder : C.speed p.2 ≤ C.speed (R p) := by
        simpa only [hzp] using (hmono p.2 hp.2 ⟨neg_lt_zero.mpr hδ, hδ⟩ hp.1 (lt_of_not_ge hs)).le
      obtain ⟨u, hu, hmu, hbu, hsu, hlu, hru, _hinside⟩ :=
        exists_bounded_weak_rarefaction hflux horder (fun ξ hξ ↦ (hPp.2.2 ξ (Icc_subset_uIcc hξ)).1)
          (fun ξ hξ ↦ (hPp.2.2 ξ (Icc_subset_uIcc hξ)).2.2.1)
          hPp.1 hPp.2.1 (fun ξ hξ ↦ (hPp.2.2 ξ (Icc_subset_uIcc hξ)).2.2.2)
      refine ⟨u, hu, hmu, hbu, hsu,
        fun z ht hx ↦ hlu z (hx.trans_le (mul_le_mul_of_nonneg_right hspeedLeftp.1.le ht.le)),
        fun z ht hx ↦ ?_⟩
      rw [hT]
      exact hru z ht ((mul_le_mul_of_nonneg_right hspeedRightp.2.le ht.le).trans hx)
  · have hld := hdegenerate hgn
    obtain ⟨δ, hδ, hcontact⟩ := exists_uniform_contact_of_local_flow
      C.flux_differentiable hR.continuousAt (hzero.mono fun _ h ↦ h.2.1)
      hflow (Eventually.of_forall fun q ↦ ⟨hld.1 q, hld.2 q, (C.eigenvector q).apply_eq_smul⟩)
    filter_upwards [hbranch, hRnorm, hqnorm, hspeedLeft,
      ball_mem_nhds ((0 : ℝ), q₀) hδ] with p hT hRp hqp hspeedLeftp hp
    rw [ite_eq_right hgn] at hT
    rw [hT]
    rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hp
    exact exists_bounded_weak_shock (hcontact p.2 hp.2 p.1 hp.1).2
      hspeedLeftp.1.le hspeedLeftp.2.le hqp hRp

/-- Hyperbolicity and the family alternatives construct ordered elementary
states, weak waves in separated speed windows, and their finite gluing.
The radius and bounds precede the right state. The finite-sum identity ties the
solution to these same waves, including in the zero-family case.

`IsElementaryConnection` describes the successive endpoint states. The conclusions
about each `wave k` give its weak equation, bounds, self-similarity and outer states;
they do not identify its profile with the shock or rarefaction witnessing that
connection. -/
theorem exists_local_riemann_wave_decomposition {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 2 flux) (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hfamilies : ∀ k, IsGenuinelyNonlinearFamily flux k ∨ IsLinearlyDegenerateFamily flux k)
    (left : ℝ^m) :
    ∃ δ K M : ℝ, 0 < δ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ right : ℝ^m, ‖right - left‖ < δ →
      ∃ (fields : Fin m → CharacteristicField flux) (state : ℕ → ℝ^m)
        (lo hi : Fin m → ℝ) (wave : Fin m → ℝ^2 → ℝ^m) (u : ℝ^2 → ℝ^m),
        (∀ k, (fields k).speed = characteristicSpeed flux k) ∧
        state 0 = left ∧ state m = right ∧
        (∀ k, IsElementaryConnection fields k (state k) (state (k + 1))) ∧
        (∀ k, lo k < hi k) ∧
        (∀ i j, i < j → hi i < lo j) ∧
        (∀ k, -M ≤ lo k ∧ hi k ≤ M) ∧
        (∀ k, IsWeakSolution flux forwardHalfSpace (wave k) ∧
          Measurable (wave k) ∧
          (∀ p : ℝ^2, 0 < p 0 → ‖wave k p‖ ≤ K) ∧
          (∀ c : ℝ, 0 < c → ∀ p, wave k (c • p) = wave k p) ∧
          (∀ p : ℝ^2, 0 < p 0 → p 1 < lo k * p 0 → wave k p = state k) ∧
          (∀ p : ℝ^2, 0 < p 0 → hi k * p 0 ≤ p 1 → wave k p = state (k + 1))) ∧
        IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
        (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
        (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
        (∀ p : ℝ^2, 0 < p 0 → p 1 < -M * p 0 → u p = left) ∧
        (∀ p : ℝ^2, 0 < p 0 → M * p 0 ≤ p 1 → u p = right) ∧
        (∀ p, u p = left + ∑ k : Fin m, (wave k p - state k)) := by
  classical
  obtain ⟨fields, hcanonical, states, _hopen, hleft, W, hW, basis, hbasis,
    S, speed, R, hreg, hzero, hequations, hpositive⟩ :=
    exists_local_elementary_wave_family hflux hhyper hfamilies left
  let eig (k : Fin m) := (fields k).speed left
  have horder : StrictMono eig := by
    simpa only [eig, hcanonical] using (characteristicSpeed_spec (hhyper left)).1
  have hsep : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i j : Fin m,
      i < j → eig i + ε < eig j - ε := eventually_all.mpr fun i ↦ eventually_all.mpr fun j ↦ by
    by_cases hij : i < j
    · exact ((continuousAt_const.add continuousAt_id).eventually_lt
        (continuousAt_const.sub continuousAt_id) (show eig i + (0 : ℝ) < eig j - 0 by
          simpa only [add_zero, sub_zero] using horder hij)).mono fun _ h _ ↦ h
    · exact Eventually.of_forall fun _ h ↦ (hij h).elim
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨η, hη, hsepη⟩ := (hpos.and (hsep.filter_mono nhdsWithin_le_nhds)).exists
  let lo (k : Fin m) := eig k - η
  let hi (k : Fin m) := eig k + η
  have hwaves (k : Fin m) :=
    eventually_exists_bounded_weak_wave (hflux.of_le (by norm_num)) (fields k)
      (IsGenuinelyNonlinearFamily flux k) (T := fun p ↦ W.curve k p.1 p.2)
      (hcanonical k ▸ contDiffAt_characteristicSpeed hflux (hhyper left) k)
      (hreg k).1 (hreg k).2.2.1 (hreg k).2.1 (hzero.mono fun _ h ↦ h k)
      (hequations.mono fun _ h ↦ (h k).1) (hequations.mono fun _ h ↦ (h k).2.1)
      (hequations.mono fun _ h ↦ (h k).2.2) (hpositive k)
      (fun hgn ↦ (isLinearlyDegenerateFamily_iff hhyper k (fields k)
        (hcanonical k)).mp ((hfamilies k).resolve_left hgn))
      (lo := lo k) (hi := hi k) ⟨sub_lt_self _ hη, lt_add_of_pos_right _ hη⟩
  have hb : ∀ k, (fields k).rightEigenvector left = basis k := fun k ↦ (hbasis k).symm
  obtain ⟨δ, hδ, hδball⟩ := eventually_nhds_iff_ball.mp
    ((W.eventually_localRiemann_steps left hleft basis hb (eventually_all.mpr hwaves)).and
      ((W.localRiemannHomeomorph left hleft basis hb).open_target.mem_nhds
        (W.left_mem_localRiemannHomeomorph_target left hleft basis hb)))
  let M := η + ∑ k : Fin m, |eig k|
  have hsum (k : Fin m) : |eig k| ≤ ∑ j : Fin m, |eig j| :=
    Finset.single_le_sum (fun j _ ↦ abs_nonneg (eig j)) (Finset.mem_univ k)
  have hlo (k : Fin m) : -M ≤ lo k := by
    simp only [M, lo]; linarith [hsum k, neg_abs_le (eig k)]
  have hhi (k : Fin m) : hi k ≤ M := by
    simp only [M, hi]; linarith [hsum k, le_abs_self (eig k)]
  refine ⟨δ, ‖left‖ + 1, M, hδ, by positivity,
    add_nonneg hη.le (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _), fun right hright ↦ ?_⟩
  obtain ⟨hw, ht⟩ := hδball right (by simpa only [mem_ball, dist_eq_norm] using hright)
  choose wave hweak hmeas hbound hscale hwl hwr using hw
  let state := W.localRiemannState left hleft basis hb right
  have hlast : state m = right := W.localRiemannState_eq_right left hleft basis hb ht
  have hfirst : state 0 = left := W.localRiemannState_zero left hleft basis hb right
  have hwright (k : Fin m) (p : ℝ^2) (hp : 0 < p 0) (hx : hi k * p 0 ≤ p 1) :
      wave k p = state (k + 1) := (hwr k p hp hx).trans (W.intermediateState_succ left
      (W.localRiemannStrength left hleft basis hb right) k).symm
  obtain ⟨u, hu, hmu, hbu, hsu, hlu, hru, hformula⟩ :=
    exists_weakSolution_of_separated_waves state wave lo hi
      (K := ‖left‖ + 1) (by rw [hfirst]; exact (lt_add_one ‖left‖).le)
      (fun i j hij ↦ (hsepη i j hij).le) hweak hmeas hbound hscale hwl hwright
  refine ⟨fields, state, lo, hi, wave, u, hcanonical, hfirst, hlast,
    W.isElementaryConnection_localRiemannState hW left hleft basis hb right,
    fun k ↦ show eig k - η < eig k + η by linarith, hsepη, fun k ↦ ⟨hlo k, hhi k⟩,
    fun k ↦ ⟨hweak k, hmeas k, hbound k, hscale k, hwl k, hwright k⟩, hu, hmu, hbu, hsu,
    fun p hp hx ↦ (hlu (-M) hlo p hp hx).trans hfirst,
    fun p hp hx ↦ (hru M hhi p hp hx).trans hlast,
    fun p ↦ (hformula p).trans (by rw [hfirst])⟩

/-- A `C²` strictly hyperbolic system with genuinely nonlinear or linearly
degenerate characteristic families admits bounded self-similar weak solutions
for all sufficiently small Riemann jumps. The neighborhood, state bound, and
propagation speed are chosen before the right state. Initial-value identities
follow separately from the finite propagation cone. -/
theorem exists_local_riemann_weak_solution {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 2 flux)
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hfamilies : ∀ k, IsGenuinelyNonlinearFamily flux k ∨ IsLinearlyDegenerateFamily flux k)
    (left : ℝ^m) :
    ∃ δ K M : ℝ, 0 < δ ∧ 0 ≤ K ∧ 0 ≤ M ∧
      ∀ right : ℝ^m, ‖right - left‖ < δ →
      ∃ u : ℝ^2 → ℝ^m,
        IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
        (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
        (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
        (∀ p : ℝ^2, 0 < p 0 → p 1 < -M * p 0 → u p = left) ∧
        (∀ p : ℝ^2, 0 < p 0 → M * p 0 ≤ p 1 → u p = right) := by
  obtain ⟨δ, K, M, hδ, hK, hM, hsolve⟩ :=
    exists_local_riemann_wave_decomposition hflux hhyper hfamilies left
  refine ⟨δ, K, M, hδ, hK, hM, fun right hright ↦ ?_⟩
  obtain ⟨_fields, _state, _lo, _hi, _wave, u, _hcanonical, _hfirst, _hlast, _hchain,
    _hwindow, _hsep, _hcone, _hwaves, hu, hmu, hbu, hsu, hlu, hru, _hformula⟩ := hsolve right hright
  exact ⟨u, hu, hmu, hbu, hsu, hlu, hru⟩

end PDE.Hyperbolic.ConservationLaw.System
