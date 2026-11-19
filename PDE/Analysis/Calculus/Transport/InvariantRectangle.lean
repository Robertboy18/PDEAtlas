/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Transport.BackwardCone
public import PDE.Analysis.Calculus.Transport.FirstContact
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Invariant rectangles for diagonal transport

Compact backward cones give range bounds without assuming characteristic curves
or any global bound on the unknown solution. The transport speeds need only be
bounded on a slightly enlarged rectangle in the state space. Strictly moving
barriers reduce the argument to the first-contact theorem.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis.Transport

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] [Finite ι]

/-- Strict barriers for transport remain negative on a compact backward cone.
Only the velocities at possible first contacts must be bounded. -/
theorem lt_zero_on_backwardCone
    {x : E} {T r M : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r) (hM : 0 ≤ M)
    {f : ι → ℝ × E → ℝ}
    (hcont : ∀ i, ContinuousOn (f i) (backwardCone x T r M))
    (hinit : ∀ p ∈ backwardCone x T r M, p.1 = 0 → ∀ i, f i p < 0)
    (htransport : ∀ p ∈ backwardCone x T r M, 0 < p.1 →
      (∀ j, f j p ≤ 0) → ∀ i, f i p = 0 →
        ∃ b : E, ‖b‖ ≤ M ∧ ∃ L : (ℝ × E) →L[ℝ] ℝ,
          HasFDerivWithinAt (f i) L (backwardCone x T r M) p ∧ L (1, b) < 0) :
    ∀ p ∈ backwardCone x T r M, ∀ i, f i p < 0 := by
  refine strict_invariant_of_first_contact (clock := ContinuousLinearMap.fst ℝ ℝ E)
    (isCompact_backwardCone x T r M hM) (convex_backwardCone x T r M)
    (fun _ hp ↦ hp.1) ?_ hcont hinit ?_
  · refine ⟨(0, x), ⟨le_rfl, hT, ?_⟩, rfl⟩
    simpa using add_nonneg hr (mul_nonneg hM hT)
  · intro p hp htp hall i hi
    obtain ⟨b, hb, L, hL, hneg⟩ := htransport p hp htp hall i hi
    refine ⟨L, hL, (0, p.2 - p.1 • b) - p,
      initial_shift_sub_mem_posTangentConeAt hp hb, ?_⟩
    have hvec : (0, p.2 - p.1 • b) - p = (-p.1) • (1, b) := by
      apply Prod.ext
      · simp
      · change p.2 - p.1 • b - p.2 = (-p.1) • b
        rw [neg_smul]
        abel
    rw [hvec, map_smul, smul_eq_mul]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos htp) hneg

/-- Strictly expanded initial bounds persist on a cone. The equation is the
actual differential of each component in its transport direction. -/
theorem expanded_rectangle_on_backwardCone
    {x : E} {T r M ε : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hε : 0 < ε) (hεT : ε * (1 + T) < 1)
    {lo hi : ι → ℝ} {v : ℝ × E → ι → ℝ} {B : ι → (ι → ℝ) → E}
    (hbound : ∀ z : ι → ℝ, (∀ j, lo j - 1 ≤ z j ∧ z j ≤ hi j + 1) →
      ∀ i, ‖B i z‖ ≤ M)
    (hcont : ∀ i, ContinuousOn (fun p ↦ v p i) (backwardCone x T r M))
    (hinit : ∀ p ∈ backwardCone x T r M, p.1 = 0 →
      ∀ i, lo i ≤ v p i ∧ v p i ≤ hi i)
    (hpde : ∀ p ∈ backwardCone x T r M, 0 < p.1 → ∀ i,
      ∃ L : (ℝ × E) →L[ℝ] ℝ, HasFDerivAt (fun q ↦ v q i) L p ∧
        L (1, B i (v p)) = 0) :
    ∀ p ∈ backwardCone x T r M, ∀ i,
      lo i - ε * (1 + p.1) < v p i ∧ v p i < hi i + ε * (1 + p.1) := by
  classical
  let f : (ι × Bool) → ℝ × E → ℝ := fun j p ↦
    (if j.2 then v p j.1 - hi j.1 else lo j.1 - v p j.1) - ε * (1 + p.1)
  have hfcont : ∀ j, ContinuousOn (f j) (backwardCone x T r M) := by
    rintro ⟨i, b⟩
    cases b <;> dsimp [f]
    · exact (continuousOn_const.sub (hcont i)).sub
        (continuousOn_const.mul (continuousOn_const.add continuous_fst.continuousOn))
    · exact ((hcont i).sub continuousOn_const).sub
        (continuousOn_const.mul (continuousOn_const.add continuous_fst.continuousOn))
  have hfinit : ∀ p ∈ backwardCone x T r M, p.1 = 0 → ∀ j, f j p < 0 := by
    intro p hp ht j
    obtain ⟨hl, hh⟩ := hinit p hp ht j.1
    cases hj : j.2 <;> simp only [f, hj, Bool.false_eq_true, ↓reduceIte, ht,
      add_zero, mul_one] <;> linarith
  have hftransport : ∀ p ∈ backwardCone x T r M, 0 < p.1 →
      (∀ j, f j p ≤ 0) → ∀ i, f i p = 0 →
        ∃ b : E, ‖b‖ ≤ M ∧ ∃ L : (ℝ × E) →L[ℝ] ℝ,
          HasFDerivWithinAt (f i) L (backwardCone x T r M) p ∧ L (1, b) < 0 := by
    intro p hp htp hall j _
    have hsmall : ε * (1 + p.1) < 1 :=
      (mul_le_mul_of_nonneg_left (by linarith [hp.2.1]) hε.le).trans_lt hεT
    have hbox : ∀ i, lo i - 1 ≤ v p i ∧ v p i ≤ hi i + 1 := by
      intro i
      have hl := hall (i, false)
      have hh := hall (i, true)
      simp only [f, Bool.false_eq_true, ↓reduceIte] at hl hh
      constructor <;> linarith
    obtain ⟨L, hL, hzero⟩ := hpde p hp htp j.1
    refine ⟨B j.1 (v p), hbound _ hbox j.1, ?_⟩
    have htime : HasFDerivAt (fun q : ℝ × E ↦ ε * (1 + q.1))
        (ε • ContinuousLinearMap.fst ℝ ℝ E) p := by
      simpa using ((hasFDerivAt_const (1 : ℝ) p).fun_add
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).const_mul ε
    cases hj : j.2
    · refine ⟨-L - ε • ContinuousLinearMap.fst ℝ ℝ E, ?_, ?_⟩
      · simpa only [f, hj, Bool.false_eq_true, ↓reduceIte, zero_sub] using
          (((hasFDerivAt_const (lo j.1) p).fun_sub hL).fun_sub htime).hasFDerivWithinAt
      · simpa [hzero] using neg_neg_of_pos hε
    · refine ⟨L - ε • ContinuousLinearMap.fst ℝ ℝ E, ?_, ?_⟩
      · simpa only [f, hj, ↓reduceIte, sub_zero] using
          ((hL.fun_sub (hasFDerivAt_const (hi j.1) p)).fun_sub htime).hasFDerivWithinAt
      · simpa [hzero] using neg_neg_of_pos hε
  have hf := lt_zero_on_backwardCone hT hr hM hfcont hfinit hftransport
  intro p hp i
  have hl := hf p hp (i, false)
  have hh := hf p hp (i, true)
  simp only [f, Bool.false_eq_true, ↓reduceIte] at hl hh
  constructor <;> linarith

/-- The initial closed rectangle is invariant. A coefficient bound on its
unit enlargement suffices; boundedness of the solution is a conclusion. -/
theorem rectangle_on_backwardCone
    {x : E} {T r M : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r) (hM : 0 ≤ M)
    {lo hi : ι → ℝ} {v : ℝ × E → ι → ℝ} {B : ι → (ι → ℝ) → E}
    (hbound : ∀ z : ι → ℝ, (∀ j, lo j - 1 ≤ z j ∧ z j ≤ hi j + 1) →
      ∀ i, ‖B i z‖ ≤ M)
    (hcont : ∀ i, ContinuousOn (fun p ↦ v p i) (backwardCone x T r M))
    (hinit : ∀ p ∈ backwardCone x T r M, p.1 = 0 →
      ∀ i, lo i ≤ v p i ∧ v p i ≤ hi i)
    (hpde : ∀ p ∈ backwardCone x T r M, 0 < p.1 → ∀ i,
      ∃ L : (ℝ × E) →L[ℝ] ℝ, HasFDerivAt (fun q ↦ v q i) L p ∧
        L (1, B i (v p)) = 0) :
    ∀ p ∈ backwardCone x T r M, ∀ i, lo i ≤ v p i ∧ v p i ≤ hi i := by
  intro p hp i
  have happrox : ∀ δ : ℝ, 0 < δ → lo i - δ < v p i ∧ v p i < hi i + δ := by
    intro δ hδ
    let ε := min δ 1 / (2 * (1 + T))
    have hden : 0 < 2 * (1 + T) := by positivity
    have hε : 0 < ε := div_pos (lt_min hδ zero_lt_one) hden
    have heq : ε * (1 + T) = min δ 1 / 2 := by
      dsimp [ε]
      field_simp
    have hsmall : ε * (1 + T) < δ ∧ ε * (1 + T) < 1 := by
      rw [heq]
      constructor <;> linarith [min_le_left δ 1, min_le_right δ 1]
    obtain ⟨hl, hh⟩ := expanded_rectangle_on_backwardCone hT hr hM hε hsmall.2
      hbound hcont hinit hpde p hp i
    have ht : ε * (1 + p.1) ≤ ε * (1 + T) :=
      mul_le_mul_of_nonneg_left (by linarith [hp.2.1]) hε.le
    constructor <;> linarith [hsmall.1]
  constructor
  · by_contra h
    have hδ : 0 < (lo i - v p i) / 2 := by linarith
    have hsmall := (happrox _ hδ).1
    linarith
  · by_contra h
    have hδ : 0 < (v p i - hi i) / 2 := by linarith
    have hsmall := (happrox _ hδ).2
    linarith

/-- Continuous state-dependent velocities preserve every initial rectangle on a
closed finite slab. The equation is required only at interior times, and no
bound or growth condition is imposed on the unknown solution. -/
theorem rectangle_on_timeSlab
    {T : ℝ} (hT : 0 < T) {lo hi : ι → ℝ}
    {B : ι → (ι → ℝ) → E} (hB : ∀ i, Continuous (B i))
    {v : ℝ × E → ι → ℝ}
    (hcont : ∀ i, ContinuousOn (fun p ↦ v p i) (Icc (0 : ℝ) T ×ˢ univ))
    (hinit : ∀ x i, lo i ≤ v (0, x) i ∧ v (0, x) i ≤ hi i)
    (hpde : ∀ p : ℝ × E, p.1 ∈ Ioo 0 T → ∀ i,
      ∃ L : (ℝ × E) →L[ℝ] ℝ, HasFDerivAt (fun q ↦ v q i) L p ∧
        L (1, B i (v p)) = 0) :
    ∀ p : ℝ × E, p.1 ∈ Icc 0 T → ∀ i, lo i ≤ v p i ∧ v p i ≤ hi i := by
  classical
  let := Fintype.ofFinite ι
  let K := Icc (fun i ↦ lo i - 1) (fun i ↦ hi i + 1)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact K).exists_bound_of_continuousOn
    (f := fun z i ↦ B i z) ((continuous_pi (fun i ↦ hB i)).continuousOn)
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ z : ι → ℝ, (∀ j, lo j - 1 ≤ z j ∧ z j ≤ hi j + 1) →
      ∀ i, ‖B i z‖ ≤ M := by
    intro z hz i
    exact (norm_le_pi_norm (fun j ↦ B j z) i).trans
      ((hC z ⟨fun j ↦ (hz j).1, fun j ↦ (hz j).2⟩).trans (le_max_left _ _))
  have hinterior : ∀ p : ℝ × E, p.1 ∈ Ioo 0 T →
      ∀ i, lo i ≤ v p i ∧ v p i ≤ hi i := by
    intro p hp i
    have hsub : backwardCone p.2 p.1 0 M ⊆ Icc (0 : ℝ) T ×ˢ univ := by
      intro q hq
      exact ⟨⟨hq.1, hq.2.1.trans hp.2.le⟩, mem_univ _⟩
    apply rectangle_on_backwardCone hp.1.le le_rfl hM hbound
      (fun j ↦ (hcont j).mono hsub) _ _ p _ i
    · intro q hq ht j
      simpa only [← ht] using hinit q.2 j
    · intro q hq ht j
      exact hpde q ⟨ht, hq.2.1.trans_lt hp.2⟩ j
    · exact ⟨hp.1.le, le_rfl, by simp⟩
  intro p hp i
  have hc : ContinuousOn (fun t ↦ v (t, p.2) i) (Icc (0 : ℝ) T) :=
    (hcont i).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ht ↦ ⟨ht, mem_univ _⟩)
  have hclosure : closure (Ioo (0 : ℝ) T) = Icc 0 T := closure_Ioo hT.ne
  have hpclosure : p.1 ∈ closure (Ioo (0 : ℝ) T) := hclosure ▸ hp
  constructor
  · exact le_on_closure (fun t ht ↦ (hinterior (t, p.2) ht i).1)
      continuousOn_const (hclosure.symm ▸ hc) hpclosure
  · exact le_on_closure (fun t ht ↦ (hinterior (t, p.2) ht i).2)
      (hclosure.symm ▸ hc) continuousOn_const hpclosure

end PDE.Analysis.Transport
