/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Primitive.Parametric
public import PDE.DistributionTheory.TestFunction.CompactCutoff
public import PDE.DistributionTheory.TestFunction.Derivative.Commutation

/-!
# Compact backward tests at an initial time

A backward time primitive of a compact test need not have compact support:
it can remain nonzero as time tends to minus infinity. Multiplication by a
smooth cutoff repairs that support while retaining the primitive at every
nonnegative time. Thus its time derivative there is the negative of
the original test, and its initial value is the time integral of that test.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions Topology

namespace TestFunction

/-- A smooth compact backward test, with its values and time
derivative on the forward half-plane. The terminal time and all support
properties are constructed from the original test. -/
theorem exists_backwardPrimitive
    (φ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ)) :
    ∃ R : ℝ, 0 < R ∧ ∃ ψ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ),
      (∀ p : ℝ × ℝ, R ≤ p.1 → φ p = 0) ∧
      (∀ p : ℝ × ℝ, 0 ≤ p.1 →
        ψ p = PDE.Analysis.backwardPrimitive φ R p) ∧
      (∀ p : ℝ × ℝ, 0 < p.1 →
        (lineDerivCLM (k := ⊤) ℝ (1, 0) ψ) p = -φ p) := by
  obtain ⟨R, hR, hbound⟩ := φ.hasCompactSupport.isBounded.exists_pos_norm_lt
  have hzero (p : ℝ × ℝ) (hp : R ≤ p.1) : φ p = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hfirst : p.1 ≤ ‖p‖ :=
      (le_abs_self p.1).trans (by simp [Prod.norm_def])
    exact (not_lt_of_ge (hp.trans hfirst)) (hbound p hs)
  obtain ⟨χ, _, hχ, _, _⟩ :=
    exists_eq_one_on_compact_finiteDimensional isOpen_univ
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) R)) (subset_univ _)
  let K : Set ℝ := Prod.snd '' tsupport (φ : ℝ × ℝ → ℝ)
  have hK : IsCompact K := φ.hasCompactSupport.image continuous_snd
  let W := PDE.Analysis.backwardPrimitive (φ : ℝ × ℝ → ℝ) R
  let w : ℝ × ℝ → ℝ := fun p ↦ χ p.1 * W p
  have hw : ContDiff ℝ (⊤ : ℕ∞) w :=
    (χ.contDiff.comp contDiff_fst).mul
      (PDE.Analysis.contDiff_backwardPrimitive φ.contDiff R)
  have hwcompact : HasCompactSupport w := by
    apply HasCompactSupport.intro (χ.hasCompactSupport.prod hK)
    intro p hp
    by_cases ht : p.1 ∈ tsupport (χ : ℝ → ℝ)
    · have hx : p.2 ∉ K := fun hx ↦ hp ⟨ht, hx⟩
      have hz : W p = 0 :=
        PDE.Analysis.backwardPrimitive_eq_zero_of_fiber φ R p.1 p.2 fun s ↦
          image_eq_zero_of_notMem_tsupport (fun hs ↦ hx ⟨(s, p.2), hs, rfl⟩)
      simp [w, hz]
    · simp [w, image_eq_zero_of_notMem_tsupport ht]
  let ψ : 𝓓((⊤ : Opens (ℝ × ℝ)), ℝ) :=
    .mk w hw hwcompact (subset_univ _)
  have heq (p : ℝ × ℝ) (hp : 0 ≤ p.1) : ψ p = W p := by
    by_cases ht : p.1 ≤ R
    · have hc : χ p.1 = 1 := hχ p.1 ⟨hp, ht⟩
      change χ p.1 * W p = W p
      rw [hc, one_mul]
    · have hz : W p = 0 :=
        PDE.Analysis.backwardPrimitive_eq_zero_of_le φ R p.1 p.2
          (le_of_not_ge ht) (fun s hs ↦ hzero (s, p.2) hs)
      change χ p.1 * W p = W p
      rw [hz, mul_zero]
  refine ⟨R, hR, ψ, hzero, heq, ?_⟩
  intro p hp
  have hnear : (ψ : ℝ × ℝ → ℝ) =ᶠ[𝓝 p] W := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with y hy
    exact heq y hy.le
  rw [lineDerivCLM_apply_eq_fderiv, hnear.fderiv_eq]
  exact PDE.Analysis.fderiv_backwardPrimitive_time (φ.contDiff.of_le (by simp)) R p

end TestFunction
