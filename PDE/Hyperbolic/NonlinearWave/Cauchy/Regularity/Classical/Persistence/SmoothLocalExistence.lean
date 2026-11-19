/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothDataAllOrders
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiniteForwardUniqueness
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.TraceOperator

/-!
# Smooth local Cauchy waves in three dimensions

Smooth compact data and an arbitrary smooth scalar reaction fixing zero give a jointly smooth local
wave. The initial face is included in the regularity conclusion. Finite-cone uniqueness compares
every classical competitor having interior C² regularity and C¹ regularity at the initial face.

This is Evans, §12.3.2, Theorem 2(i), under the standing hypotheses of §12.3.2: `f` is smooth with
`f(0) = 0`, and `g, h ∈ C_c^∞(ℝ³)`. Uniqueness holds in the larger class of classical competitors
described above.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.2, standing hypotheses and Theorem 2(i).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter PDE.Common Set
open scoped Laplacian Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open WaveEquation

/-- Smooth compact data give a unique local smooth wave in three dimensions.
The reaction is not assumed globally Lipschitz. -/
theorem exists_unique_smooth_local_of_smoothCompact {f : ℝ → ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf0 : f 0 = 0) (g h : ℝ^3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ^4 → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) u {p | p 0 ∈ Ico 0 T} ∧
      (∀ x, u (timeSpaceCons 0 x) = g x ∧
        HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) ∧
      (∀ t ∈ Ioo 0 T, ∀ x,
        waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0) ∧
      ∀ v : ℝ^4 → ℝ,
        ContDiffOn ℝ 2 v {p | p 0 ∈ Ioo 0 T} →
        ContDiffOn ℝ 1 v {p | p 0 ∈ Ico 0 T} →
        (∀ t ∈ Ioo 0 T, ∀ x,
          waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0) →
        (∀ x, v (timeSpaceCons 0 x) = g x) →
        (∀ x, derivWithin (fun t ↦ v (timeSpaceCons t x)) (Ici 0) 0 = h x) →
        ∀ t ∈ Ico 0 T, ∀ x, v (timeSpaceCons t x) = u (timeSpaceCons t x) := by
  obtain ⟨T, hT, q, hq, hzero, hfield⟩ :=
    exists_smooth_localReaction_of_smoothCompact (by norm_num : 3 < 4) hs hf0 g h hg hh hgc hhc
  let u : ℝ^4 → ℝ := fun p ↦ q (timeSpaceContinuousLinearEquiv 3 p)
  have hslice (t : ℝ) (x : ℝ^3) : u (timeSpaceCons t x) = q (t, x) :=
    congrArg q ((timeSpaceContinuousLinearEquiv 3).apply_symm_apply (t, x))
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) u {p | p 0 ∈ Ico 0 T} :=
    hq.comp (timeSpaceContinuousLinearEquiv 3).contDiff.contDiffOn (fun p hp ↦ ⟨hp, mem_univ _⟩)
  have hui : ContDiffOn ℝ 2 u {p | p 0 ∈ Ioo 0 T} :=
    (hu.of_le (by simp)).mono (fun _ hp ↦ ⟨hp.1.le, hp.2⟩)
  have hu0 (x : ℝ^3) : u (timeSpaceCons 0 x) = g x ∧
      HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0 := by
    constructor
    · exact (hslice 0 x).trans (hzero x).1
    · simp only [hslice]
      exact (hzero x).2.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hT)
  have hwave (t : ℝ) (ht : t ∈ Ioo 0 T) (x : ℝ^3) :
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0 := by
    have hopen : IsOpen {p : ℝ^4 | p 0 ∈ Ioo 0 T} :=
      isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous
    have hat : ContDiffAt ℝ 2 u (timeSpaceCons t x) := (hui _ ht).contDiffAt (hopen.mem_nhds ht)
    rw [waveOperator_timeSpaceCons_of_contDiffAt hat]
    simp only [hslice]
    exact hfield t ht x
  refine ⟨T, hT, u, hu, hu0, hwave, fun v hv hv0 hvwave hvpos hvvel ↦ ?_⟩
  exact eq_on_finite_forward_strip ((hs.of_le (by simp)).locallyLipschitz)
    hv hui hv0 (hu.of_le (by simp)) hvwave hwave (fun x ↦ (hvpos x).trans (hu0 x).1.symm)
    (fun x ↦ (hvvel x).trans ((hu0 x).2.derivWithin (uniqueDiffWithinAt_Ici 0)).symm)

end PDE.Hyperbolic.NonlinearWave.Cauchy
