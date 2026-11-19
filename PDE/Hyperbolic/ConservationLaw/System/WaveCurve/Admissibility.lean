/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Compression
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Rarefaction

/-!
# Local admissible wave transformations

The characteristic branches are used only near zero strength and the fixed left
state. Outside their construction neighborhood the carrier is the identity.
This totalization preserves the full local derivative, and its remaining
connections are the no-jump elementary wave.

For a genuinely nonlinear family the joined curve, the shock curve for `s ≤ 0` and the
rarefaction curve for `s > 0`, traces `T_k(z₀) = R_k^+(z₀) ∪ {z₀} ∪ S_k^-(z₀)` of Evans,
§11.2.4, near `z₀`. `eventually_isElementaryConnection_joined` shows that each of its points
is joined to `z₀` by a `k`-shock wave (36)-(37) of §11.2.3 or a `k`-rarefaction wave of
§11.2.2, Theorem 1, and `LocalWaveFamily.exists_of_local_curves` collects the curves of all
families, with derivative `r_k` at zero strength, for the map `Φ` of steps 2-3 of the proof
of Theorem 4 there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.2, Theorem 1; §11.2.3, equations (36)-(37) and (42);
  §11.2.4, the definition of `T_k(z₀)` and steps 2-3 of the proof of Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

/-- Matching shock and flow branches with positive characteristic derivative
give admissible elementary connections on a full product neighborhood. The
compression inequalities follow from the half-speed derivative. Positive
strengths use the local integral curve, including its whole parameter
segment. -/
theorem eventually_isElementaryConnection_joined {m : ℕ} {flux : ℝ^m → ℝ^m}
    {fields : Fin m → CharacteristicField flux} {k : Fin m} {q₀ v : ℝ^m} {S R : ℝ × ℝ^m → ℝ^m}
    {speed : ℝ × ℝ^m → ℝ} (heig : ContDiffAt ℝ 1 (fields k).speed q₀)
    (hS : ContDiffAt ℝ 1 S (0, q₀)) (hR : ContDiffAt ℝ 1 R (0, q₀))
    (hspeed : ContDiffAt ℝ 1 speed (0, q₀))
    (hzero : ∀ᶠ q in 𝓝 q₀, S (0, q) = q ∧ R (0, q) = q ∧ speed (0, q) = (fields k).speed q)
    (htanS : HasDerivAt (fun s ↦ S (s, q₀)) v 0) (htanR : HasDerivAt (fun s ↦ R (s, q₀)) v 0)
    (hhalf : HasDerivAt (fun s ↦ speed (s, q₀)) ((1 / 2 : ℝ) * fderiv ℝ (fields k).speed q₀ v) 0)
    (hpos : 0 < fderiv ℝ (fields k).speed q₀ v)
    (hRH : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), RankineHugoniot flux p.2 (S p) (speed p))
    (hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      HasDerivAt (fun t ↦ R (t, p.2)) ((fields k).rightEigenvector (R p)) p.1)
    (hsep : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), (∀ j, j < k → (fields j).speed p.2 < speed p) ∧
      (∀ j, k < j → speed p < (fields j).speed (S p))) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      IsElementaryConnection fields k p.2 (if p.1 ≤ 0 then S p else R p) := by
  obtain ⟨δ₁, hδ₁, hmono⟩ := exists_uniform_speed_expansion
    heig hR hzero.self_of_nhds.2.1 htanR hpos
  obtain ⟨δ₂, hδ₂, hcompress⟩ := exists_uniform_shock_compression
    heig hS hspeed (hzero.mono fun _ h ↦ ⟨h.1, h.2.2⟩) htanS hhalf hpos
  have hz := (continuousAt_snd :
    ContinuousAt (Prod.snd : ℝ × ℝ^m → ℝ^m) (0, q₀)).tendsto.eventually hzero
  obtain ⟨δ₀, hδ₀, hlocal⟩ := Metric.mem_nhds_iff.mp
    (hRH.and (hflow.and (hsep.and (hz.and (hR.eventually (by simp))))))
  let δ := min δ₀ (min δ₁ δ₂)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hle₀ : δ ≤ δ₀ := min_le_left _ _
  have hle₁ : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hle₂ : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  filter_upwards [ball_mem_nhds ((0 : ℝ), q₀) hδ] with p hp
  have hlocalP := hlocal (ball_subset_ball hle₀ hp)
  rw [← ball_prod_same, Real.ball_zero_eq_Ioo] at hp
  have hmem {s : ℝ} (hs : s ∈ Ioo (-δ) δ) : (s, p.2) ∈ ball ((0 : ℝ), q₀) δ₀ := by
    refine ball_subset_ball hle₀ ?_
    rw [← ball_prod_same, Real.ball_zero_eq_Ioo]
    exact ⟨hs, hp.2⟩
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  rcases lt_trichotomy p.1 0 with hs | hs | hs
  · rw [ite_eq_left hs.le]
    obtain ⟨hlo, hhi⟩ := hcompress p.2 (ball_subset_ball hle₂ hp.2) p.1
      ⟨lt_of_le_of_lt (neg_le_neg hle₂) hp.1.1, hs⟩
    exact .shock (speed p) ⟨hlocalP.1, hlo, hhi, hlocalP.2.2.1⟩
  · have hp₀ : p = (0, p.2) := Prod.ext hs rfl
    rw [ite_eq_left hs.le, hp₀, (hlocal (hmem h0)).2.2.2.1.1]
    exact .same p.2
  · rw [ite_eq_right (not_le.mpr hs)]
    exact .rarefaction (IsRarefactionConnection.of_local_flow (fields k)
      (curve := fun s ↦ R (s, p.2)) (s := p.1) (hlocal (hmem h0)).2.2.2.1.2.1
      (fun s hs ↦ ((hlocal (hmem hs)).2.2.2.2.comp s
        (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt)
      (fun s hs ↦ (hlocal (hmem hs)).2.1)
      ((hmono p.2 (ball_subset_ball hle₁ hp.2)).mono (Ioo_subset_Ioo (neg_le_neg hle₁) hle₁))
      hs hp.1.2)

/-- Local elementary curves with the prescribed strict derivatives give the
wave-family structure on an open state neighborhood. The carrier agrees
with the original curves on one full product neighborhood. -/
theorem LocalWaveFamily.exists_of_local_curves {m : ℕ} {flux : ℝ^m → ℝ^m}
    {fields : Fin m → CharacteristicField flux} {T : Fin m → ℝ × ℝ^m → ℝ^m} {q₀ : ℝ^m}
    (hzero : ∀ᶠ q in 𝓝 q₀, ∀ k, T k (0, q) = q)
    (hderiv : ∀ᶠ q in 𝓝 q₀, ∀ k,
      HasStrictFDerivAt (T k) (waveStepDerivative ((fields k).rightEigenvector q)) (0, q))
    (helem : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k, IsElementaryConnection fields k p.2 (T k p)) :
    ∃ states : Set (ℝ^m), IsOpen states ∧ q₀ ∈ states ∧ ∃ W : LocalWaveFamily flux fields states,
      W.IsElementary ∧ ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k, W.curve k p.1 p.2 = T k p := by
  classical
  obtain ⟨D, hDsub, hDopen, hD₀⟩ := _root_.eventually_nhds_iff.mp helem
  let curve (k : Fin m) (s : ℝ) (q : ℝ^m) :=
    if s = 0 then q else if (s, q) ∈ D then T k (s, q) else q
  have heq : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k, curve k p.1 p.2 = T k p := by
    have hz := (continuousAt_snd :
      ContinuousAt (Prod.snd : ℝ × ℝ^m → ℝ^m) (0, q₀)).tendsto.eventually hzero
    filter_upwards [hDopen.mem_nhds hD₀, hz] with p hp hz k
    by_cases hs : p.1 = 0
    · have hp₀ : p = (0, p.2) := Prod.ext hs rfl
      simp only [curve, ite_eq_left hs]
      exact (hz k).symm.trans (congrArg (T k) hp₀.symm)
    · simp only [curve, ite_eq_right hs, Prod.mk.eta, ite_eq_left hp]
  have hnear : ∀ᶠ q in 𝓝 q₀, ∀ k, HasStrictFDerivAt (fun p : ℝ × ℝ^m ↦ curve k p.1 p.2)
        (waveStepDerivative ((fields k).rightEigenvector q)) (0, q) := by
    have heqNear := (continuousAt_const.prodMk continuousAt_id :
      ContinuousAt (fun q : ℝ^m ↦ ((0 : ℝ), q)) q₀).tendsto.eventually heq.eventually_nhds
    filter_upwards [hderiv, heqNear] with q hq heqQ k
    exact (hq k).congr_of_eventuallyEq (heqQ.mono fun _ hp ↦ (hp k).symm)
  obtain ⟨states, hstates, hopen, hq₀⟩ := _root_.eventually_nhds_iff.mp hnear
  let W : LocalWaveFamily flux fields states :=
    { curve := curve
      curve_zero := fun _ _ ↦ ite_eq_left rfl
      hasStrictFDerivAt_zero := fun k q hq ↦ hstates q hq k }
  refine ⟨states, hopen, hq₀, W, fun k s q ↦ ?_, heq⟩
  change IsElementaryConnection fields k q (curve k s q)
  dsimp only [curve]
  split_ifs with hs hD
  exacts [.same q, hDsub (s, q) hD k, .same q]

end PDE.Hyperbolic.ConservationLaw.System
