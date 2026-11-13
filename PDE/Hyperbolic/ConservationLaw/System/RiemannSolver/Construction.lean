/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.LocalWave
public import PDE.Hyperbolic.ConservationLaw.System.Riemann.ElementaryChain
public import PDE.Hyperbolic.ConservationLaw.System.Riemann.WeakSolution
import PDE.Hyperbolic.ConservationLaw.System.IntegralCurveFamily

/-!
# Local Riemann solutions with realized elementary waves

The local wave family and its inverse strength map are the
constructions from strict hyperbolicity and the characteristic-family
alternatives. Each selected transformation is realized by its
Lax shock, contact, or characteristic rarefaction. Finite weak gluing retains
these witnesses and the uniform propagation cone.

The conclusion is local in the size of the initial jump and global for
positive time by self-similarity. It asserts elementary admissibility. This is Theorem 4 of
Evans, §11.2.4, with each wave realized by a spacetime profile.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.4, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

/-- Construct a local self-similar Riemann solution from a `C²` strictly
hyperbolic flux with genuinely nonlinear or linearly degenerate families.
Every component profile realizes the elementary connection between its
successive states. The radius and bounds are fixed before the right state. -/
theorem exists_local_riemann_elementary_decomposition {m : ℕ} {flux : ℝ^m → ℝ^m}
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
        (∀ k, IsElementaryWave fields k (state k) (state (k + 1)) (wave k) ∧
          IsWeakSolution flux forwardHalfSpace (wave k) ∧
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
    _S, _speed, _R, hreg, hzero, hequations, hpositive⟩ :=
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
    eventually_exists_bounded_elementary_wave (hflux.of_le (by norm_num)) fields k
      (IsGenuinelyNonlinearFamily flux k) (T := fun p ↦ W.curve k p.1 p.2)
      (hcanonical k ▸ contDiffAt_characteristicSpeed hflux (hhyper left) k)
      (hreg k).2.2.2 (hreg k).2.2.1 (W.curve_zero k) (hzero.mono fun _ h ↦ (h k).2.1)
      (W.hasDerivAt_curve_zero k left hleft) (fun p ↦ hW k p.1 p.2)
      (hequations.mono fun p hp h ↦ by
        rw [(hp k).1]
        rcases h with hn | hs
        · simp [hn]
        · simp [not_le_of_gt hs]) (hequations.mono fun _ h ↦ (h k).2.2) (hpositive k)
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
  choose wave helem hweak hmeas hbound hscale hwl hwr using hw
  let state := W.localRiemannState left hleft basis hb right
  have hlast : state m = right := W.localRiemannState_eq_right left hleft basis hb ht
  have hfirst : state 0 = left := W.localRiemannState_zero left hleft basis hb right
  have hwright (k : Fin m) (p : ℝ^2) (hp : 0 < p 0) (hx : hi k * p 0 ≤ p 1) :
      wave k p = state (k + 1) := (hwr k p hp hx).trans (W.intermediateState_succ left
      (W.localRiemannStrength left hleft basis hb right) k).symm
  have helementary (k : Fin m) :
      IsElementaryWave fields k (state k) (state (k + 1)) (wave k) := by
    change IsElementaryWave fields k _ (W.intermediateState left
      (W.localRiemannStrength left hleft basis hb right) (k + 1)) _
    rw [W.intermediateState_succ left (W.localRiemannStrength left hleft basis hb right) k]
    exact helem k
  obtain ⟨u, hu, hmu, hbu, hsu, hlu, hru, hformula⟩ :=
    exists_weakSolution_of_separated_waves state wave lo hi
      (K := ‖left‖ + 1) (by rw [hfirst]; exact (lt_add_one ‖left‖).le)
      (fun i j hij ↦ (hsepη i j hij).le) hweak hmeas hbound hscale hwl hwright
  refine ⟨fields, state, lo, hi, wave, u, hcanonical, hfirst, hlast,
    fun k ↦ (helementary k).isElementaryConnection,
    fun k ↦ show eig k - η < eig k + η by linarith, hsepη, fun k ↦ ⟨hlo k, hhi k⟩,
    fun k ↦ ⟨helementary k, hweak k, hmeas k, hbound k, hscale k, hwl k, hwright k⟩,
    hu, hmu, hbu, hsu, fun p hp hx ↦ (hlu (-M) hlo p hp hx).trans hfirst,
    fun p hp hx ↦ (hru M hhi p hp hx).trans hlast,
    fun p ↦ (hformula p).trans (by rw [hfirst])⟩

end PDE.Hyperbolic.ConservationLaw.System
