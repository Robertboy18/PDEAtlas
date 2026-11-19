/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Smoothness.Tower
import PDE.Analysis.Calculus.Deriv.ContDiffOne

/-!
# Persistence of smoothness for coupled De Gregorio outputs

A coupled H² output `w` of the De Gregorio equation on `[0, T]` with smooth compactly supported
initial datum has derivative towers of every height (`IsDerivTower`). Each step is linear:
the `n`-th derivative satisfies an affine characteristic equation whose coefficients and forcing
involve only `w` and its first `n - 1` derivatives, all bounded in H², so it is solved on the
whole interval and identified with the derivative by H¹ uniqueness (`exists_h2_deriv`). The
intervals never shrink, and every slice `w (·, t)`, `t ∈ [0, T]`, is `C^∞`.

## Main results

* `IsHkFrozenOutput.exists_derivTower`: towers of every height.
* `IsHkFrozenOutput.contDiff_vorticity`: every closed-time slice is `C^∞`.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology Sobolev ContDiff
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {T : ℝ} {B : NNReal} {R : ℝ} {hT : 0 ≤ T}
  {F : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}(ℝ^1)} {w₀ : ℝ → ℝ} {c w X Y : ℝ → ℝ → ℝ}

/-- The representatives of a tower are the iterated derivatives of the slices. -/
theorem IsDerivTower.realLineRepresentative_eq {q : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1)}
    {n : ℕ} (htower : IsDerivTower hT X q n)
    (hq0 : ∀ t, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q 0 t)) =
      fun x ↦ w x t) :
    ∀ j ≤ n, ∀ t, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q j t)) =
      deriv^[j] (fun x ↦ w x t) := by
  intro j
  induction j with
  | zero => intro _ t; exact hq0 t
  | succ j ih =>
    intro hj t
    rw [← htower.deriv_eq j (by omega) t, ← deriv_realLineRepresentative_lowerOrder,
      ih (by omega) t, Function.iterate_succ_apply']

/-- The slices of a tower of height `n` are `C^{n+1}`. -/
theorem IsDerivTower.contDiff {q : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} {n : ℕ}
    (htower : IsDerivTower hT X q n)
    (hq0 : ∀ t, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q 0 t)) =
      fun x ↦ w x t) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ (n + 1 : ℕ) (fun x ↦ w x t) := by
  rw [← hq0 t]
  apply PDE.contDiff_of_hasDerivAt_chain
    (r := fun j ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q j t)))
  · intro j hj x
    rw [← htower.deriv_eq j hj t]
    exact hasDerivAt_realLineRepresentative_lowerOrder _ x
  · apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x ↦ (hasDerivAt_realLineRepresentative_lowerOrder (q n t) x).differentiableAt,
      ?_⟩
    rw [deriv_realLineRepresentative_lowerOrder]
    exact continuous_realLineRepresentative _

/-- The product rule for the representatives of `B (A, Q)`, in terms of weak derivatives. -/
theorem realLineRepresentative_partialDeriv_firstDerivativeSource (A Q : W^{2,2}(ℝ^1))
    (x : ℝ) :
    realLineRepresentative (∂[0] (firstDerivativeSourceH2CLM A Q)) x =
      realLineRepresentative (∂[0] A) x *
          realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) Q)) x +
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) A) x *
          realLineRepresentative (realHilbertH1 (∂[0] Q)) x :=
  (hasDerivAt_realLineRepresentative_lowerOrder _ x).unique (hasDerivAt_firstDerivativeSource A Q x)

/-- Smooth compact data give the derivative tower of height one. -/
theorem IsHkFrozenOutput.exists_derivTower_one
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hchar : HkCharacteristics hT F c X Y)
    {W : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hW : StronglyMeasurable W) (hWb : ∀ t, ‖W t‖ ≤ B)
    (hWrep : ∀ t, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) =
      fun x ↦ w x t)
    (hc : ∀ (t : Icc (0 : ℝ) T) x, c x t =
      realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))) x)
    (hw₀ : ContDiff ℝ ∞ w₀) (hc₀ : HasCompactSupport w₀) :
    ∃ q : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1), q 0 = W ∧ IsDerivTower hT X q 1 := by
  set k := 36 * succOrderAssemblyNormBound 1 1 with hk
  have hk0 : 0 ≤ k := mul_nonneg (by norm_num) succOrderAssemblyNormBound_nonneg
  let K := max (B : ℝ) (k * B * B)
  have hBK : (B : ℝ) ≤ K := le_max_left _ _
  have hK : 0 ≤ K := B.coe_nonneg.trans hBK
  have hVm : StronglyMeasurable (fun t ↦ firstDerivativeSourceH2CLM (W t) (W t)) :=
    firstDerivativeSourceH2CLM.continuous₂.comp_stronglyMeasurable (hW.prodMk hW)
  have hVb (t : Icc (0 : ℝ) T) : ‖firstDerivativeSourceH2CLM (W t) (W t)‖ ≤ K := by
    have := hWb t
    exact (norm_firstDerivativeSourceH2CLM_apply_le _ _).trans
      (le_trans (by gcongr) (le_max_right _ _))
  obtain ⟨Q₀, hQ₀⟩ := exists_h2_of_contDiff (hw₀.iterate_deriv 1) (by simpa using hc₀.deriv)
  have hQ₀' : realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) Q₀) =
      realLineRepresentative (∂[0] (W ⟨0, le_rfl, hT⟩)) := by
    rw [hQ₀, ← deriv_realLineRepresentative_lowerOrder, hWrep]
    simp only [Function.iterate_one]
    congr 1
    funext x
    exact (h.initial x).symm
  obtain ⟨q₁, hq₁, ⟨C₁, _, hq₁b⟩, hid, hE⟩ := hchar.exists_h2_deriv hW hK
    (fun t ↦ (hWb t).trans hBK) hc (Φ := W)
    (V := fun t ↦ firstDerivativeSourceH2CLM (W t) (W t)) (g := fun _ ↦ 0) hW
    (fun t ↦ (hWb t).trans hBK) hVm hVb stronglyMeasurable_const (fun _ ↦ by simpa using hK) 0
    (fun t x ↦ by
      rw [realLineRepresentative_partialDeriv_firstDerivativeSource, ← hc]
      simp only [map_zero, realLineRepresentative_zero, Pi.zero_apply]
      ring)
    (h.integral_eq_source hchar hWrep hc) Q₀ hQ₀'
  refine ⟨fun j ↦ if j = 1 then q₁ else W, by simp, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro j hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · simpa using hW
    · simpa using hq₁
  · refine ⟨max B C₁, fun j hj t ↦ ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · simpa using (hWb t).trans (le_max_left _ _)
    · simpa using (hq₁b t).trans (le_max_right _ _)
  · intro j hj t
    obtain rfl : j = 0 := by omega
    simpa using hid t
  · intro a t
    simp only [↓reduceIte]
    rw [hE a t]
    refine congrArg _ (intervalIntegral.integral_congr fun s _ ↦ ?_)
    simp only [levelSource, forcingList, sourceSum_nil, zero_ne_one, ↓reduceIte, Nat.cast_one,
      sub_self, zero_smul, add_zero]

/-- A tower of height `n ≥ 1` extends to height `n + 1`. -/
theorem IsHkFrozenOutput.exists_derivTower_succ
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hchar : HkCharacteristics hT F c X Y)
    {W : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hW : StronglyMeasurable W) (hWb : ∀ t, ‖W t‖ ≤ B)
    (hWrep : ∀ t, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) =
      fun x ↦ w x t)
    (hc : ∀ (t : Icc (0 : ℝ) T) x, c x t =
      realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))) x)
    (hw₀ : ContDiff ℝ ∞ w₀) (hc₀ : HasCompactSupport w₀)
    {q : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hq0 : q 0 = W) {m : ℕ}
    (htower : IsDerivTower hT X q (m + 1)) :
    ∃ q' : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1), q' 0 = W ∧ IsDerivTower hT X q' (m + 2) := by
  set k := 36 * succOrderAssemblyNormBound 1 1 with hk
  set n := m + 1 with hn
  obtain ⟨C, hC⟩ := htower.bounded
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by omega) ⟨0, le_rfl, hT⟩)
  have hmeas := htower.measurable
  have hlist (l : ℕ) (hl : l ≤ n + 1) {e : ℕ × ℕ × ℝ} (he : e ∈ forcingList l) :
      e.1 < l ∧ e.2.1 < l := by
    have := mem_forcingList he
    omega
  -- The level integrand and the next forcing.
  let V : Icc (0 : ℝ) T → W^{2,2}(ℝ^1) := levelSource q n
  let g : Icc (0 : ℝ) T → W^{2,2}(ℝ^1) := fun t ↦ sourceSum (fun j ↦ q j t) (forcingList (n + 1))
  have hVm : StronglyMeasurable V := by
    have h1 := firstDerivativeSourceH2CLM.continuous₂.comp_stronglyMeasurable
      ((hmeas 0 (by omega)).prodMk (hmeas n le_rfl))
    have h2 := firstDerivativeSourceH2CLM.continuous₂.comp_stronglyMeasurable
      ((hmeas n le_rfl).prodMk (hmeas 0 (by omega)))
    have h3 := stronglyMeasurable_sourceSum (q := q) (l := forcingList n) fun e he ↦
      ⟨hmeas _ (hlist n (by omega) he).1.le, hmeas _ (hlist n (by omega) he).2.le⟩
    exact (h1.add (h2.const_smul (1 - (n : ℝ)))).add h3
  have hgm : StronglyMeasurable g :=
    stronglyMeasurable_sourceSum (q := q) (l := forcingList (n + 1)) fun e he ↦
      ⟨hmeas _ (by have := hlist (n + 1) le_rfl he; omega),
        hmeas _ (by have := hlist (n + 1) le_rfl he; omega)⟩
  obtain ⟨D₁, hD₁⟩ := exists_norm_sourceSum_le (q := q) (l := forcingList n) (C := C)
    fun e he t ↦ ⟨hC _ (hlist n (by omega) he).1.le t, hC _ (hlist n (by omega) he).2.le t⟩
  obtain ⟨D₂, hD₂⟩ := exists_norm_sourceSum_le (q := q) (l := forcingList (n + 1)) (C := C)
    fun e he t ↦ ⟨hC _ (by have := hlist (n + 1) le_rfl he; omega) t,
      hC _ (by have := hlist (n + 1) le_rfl he; omega) t⟩
  have hk0 : 0 ≤ k := mul_nonneg (by norm_num) succOrderAssemblyNormBound_nonneg
  let K := max (max (B : ℝ) C) (max (k * C * C + |1 - (n : ℝ)| * (k * C * C) + D₁) D₂)
  have hK : 0 ≤ K := hC0.trans ((le_max_right _ _).trans (le_max_left _ _))
  have hWK (t : Icc (0 : ℝ) T) : ‖W t‖ ≤ K :=
    (hWb t).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hqK (t : Icc (0 : ℝ) T) : ‖q n t‖ ≤ K :=
    (hC n le_rfl t).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hVK (t : Icc (0 : ℝ) T) : ‖V t‖ ≤ K := by
    have h0 := hC 0 (by omega) t
    have hn' := hC n le_rfl t
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
    simp only [V, levelSource]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_firstDerivativeSourceH2CLM_apply_le _ _).trans (by gcongr)) ?_)) (hD₁ t))
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    exact (norm_firstDerivativeSourceH2CLM_apply_le _ _).trans (by gcongr)
  have hgK (t : Icc (0 : ℝ) T) : ‖g t‖ ≤ K :=
    (hD₂ t).trans ((le_max_right _ _).trans (le_max_right _ _))
  -- The initial derivative.
  have hrep := htower.realLineRepresentative_eq (w := w) (by rw [hq0]; exact hWrep)
  obtain ⟨Q₀, hQ₀⟩ := exists_h2_of_contDiff (hw₀.iterate_deriv (n + 1))
    (by rw [← iteratedDeriv_eq_iterate, iteratedDeriv_eq_equiv_comp]
        exact (hc₀.iteratedFDeriv (n + 1)).comp_left (map_zero _))
  have hQ₀' : realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) Q₀) =
      realLineRepresentative (∂[0] (q n ⟨0, le_rfl, hT⟩)) := by
    rw [hQ₀, ← deriv_realLineRepresentative_lowerOrder, hrep n le_rfl,
      Function.iterate_succ_apply']
    congr 2
    funext x
    exact (h.initial x).symm
  -- The derivative of the level integrand.
  have hd0 (t : Icc (0 : ℝ) T) : ∂[0] (q 0 t) = lowerOrderCLM (by decide : 1 ≤ 2) (q 1 t) :=
    htower.deriv_eq 0 (by omega) t
  have hder (t : Icc (0 : ℝ) T) (x : ℝ) : realLineRepresentative (∂[0] (V t)) x =
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) x *
          realLineRepresentative (realHilbertH1 (∂[0] (q n t))) x +
        (-(n : ℝ)) * (c x t * realLineRepresentative (∂[0] (q n t)) x) +
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (g t)) x +
        c x t * realLineRepresentative (∂[0] (q n t)) x := by
    have hs := hasDerivAt_sourceSum (q := fun j ↦ q j t) (l := forcingList n) (fun e he ↦
      ⟨htower.deriv_eq _ (hlist n (by omega) he).1 t,
        htower.deriv_eq _ (hlist n (by omega) he).2 t⟩) x
    have hfull := ((hasDerivAt_firstDerivativeSource (q 0 t) (q n t) x).add
      ((hasDerivAt_firstDerivativeSource (q n t) (q 0 t) x).const_mul (1 - (n : ℝ)))).add hs
    have hV : realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (V t)) =
        fun y ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
            (firstDerivativeSourceH2CLM (q 0 t) (q n t))) y +
          (1 - (n : ℝ)) * realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
            (firstDerivativeSourceH2CLM (q n t) (q 0 t))) y +
          realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
            (sourceSum (fun j ↦ q j t) (forcingList n))) y := by
      funext y
      simp only [V, levelSource, map_add, map_smul, realLineRepresentative_add,
        realLineRepresentative_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hfull' := hfull.congr_of_eventuallyEq (f₁ := realLineRepresentative
      (lowerOrderCLM (by decide : 1 ≤ 2) (V t))) (Filter.Eventually.of_forall fun y ↦ by
        rw [hV]
        rfl)
    rw [(hasDerivAt_realLineRepresentative_lowerOrder _ x).unique hfull']
    have hg : g t = (1 : ℝ) • firstDerivativeSourceH2CLM (q 1 t) (q n t) +
        (-(m : ℝ)) • firstDerivativeSourceH2CLM (q n t) (q 1 t) +
          sourceSum (fun j ↦ q j t) (sourceDeriv (forcingList n)) := by
      simp only [g, hn, forcingList, sourceSum_cons]
      abel
    rw [hg, hc t x, ← hq0, hd0]
    simp only [map_add, map_smul, realLineRepresentative_add, realLineRepresentative_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, realLineRepresentative_firstDerivativeSourceH2CLM]
    rw [hn]
    push_cast
    ring
  have hE := htower.integral_eq
  obtain ⟨q', hq', ⟨C', _, hq'b⟩, hid, hE'⟩ := hchar.exists_h2_deriv hW hK hWK hc (Φ := q n)
    (V := V) (g := g) (hmeas n le_rfl) hqK hVm hVK hgm hgK (-(n : ℝ)) hder
    (fun a t ↦ hE a t) Q₀ hQ₀'
  -- The extended tower.
  let qq : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1) := Function.update q (n + 1) q'
  have hqq_lt (j : ℕ) (hj : j ≤ n) : qq j = q j := Function.update_of_ne (by omega) _ _
  have hqq_top : qq (n + 1) = q' := Function.update_self _ _ _
  refine ⟨qq, by rw [hqq_lt 0 (by omega), hq0], ⟨?_, ?_, ?_, ?_⟩⟩
  · intro j hj
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact hqq_lt j (by omega) ▸ hmeas j (by omega)
    · obtain rfl : j = n + 1 := by omega
      exact hqq_top ▸ hq'
  · refine ⟨max C C', fun j hj t ↦ ?_⟩
    rcases Nat.lt_or_ge j (n + 1) with hlt | hge
    · exact hqq_lt j (by omega) ▸ (hC j (by omega) t).trans (le_max_left _ _)
    · obtain rfl : j = n + 1 := by omega
      exact hqq_top ▸ (hq'b t).trans (le_max_right _ _)
  · intro j hj t
    rcases Nat.lt_or_ge j n with hlt | hge
    · rw [hqq_lt j (by omega), hqq_lt (j + 1) (by omega)]
      exact htower.deriv_eq j hlt t
    · obtain rfl : j = n := by omega
      rw [hqq_lt n le_rfl, hqq_top]
      exact hid t
  · intro a t
    have hsum (s : Icc (0 : ℝ) T) :
        sourceSum (fun j ↦ qq j s) (forcingList (n + 1)) = g s :=
      sourceSum_congr fun e he ↦ have := hlist (n + 1) le_rfl he
        ⟨congrFun (hqq_lt _ (by omega)) s, congrFun (hqq_lt _ (by omega)) s⟩
    rw [hqq_top, hE' a t]
    refine congrArg _ (intervalIntegral.integral_congr fun s _ ↦ ?_)
    have hlev : levelSource qq (m + 2) (projIcc 0 T hT s) =
        firstDerivativeSourceH2CLM (W (projIcc 0 T hT s)) (q' (projIcc 0 T hT s)) +
          (-(n : ℝ)) • firstDerivativeSourceH2CLM (q' (projIcc 0 T hT s)) (W (projIcc 0 T hT s)) +
            g (projIcc 0 T hT s) := by
      change levelSource qq (n + 1) _ = _
      simp only [levelSource, hqq_top, hsum, hqq_lt 0 (by omega), hq0]
      congr 3
      push_cast
      ring
    rw [hlev]

/-- A coupled output with smooth compact initial datum has derivative towers of every height,
with the vorticity graphs `W` at the base. -/
theorem IsHkFrozenOutput.exists_derivTower
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hchar : HkCharacteristics hT F c X Y)
    {W : Icc (0 : ℝ) T → W^{2,2}(ℝ^1)} (hW : StronglyMeasurable W) (hWb : ∀ t, ‖W t‖ ≤ B)
    (hWrep : ∀ t, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (W t)) =
      fun x ↦ w x t)
    (hc : ∀ (t : Icc (0 : ℝ) T) x, c x t =
      realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) (W t))) x)
    (hw₀ : ContDiff ℝ ∞ w₀) (hc₀ : HasCompactSupport w₀) (n : ℕ) :
    ∃ q : ℕ → Icc (0 : ℝ) T → W^{2,2}(ℝ^1), q 0 = W ∧ IsDerivTower hT X q (n + 1) := by
  induction n with
  | zero => exact h.exists_derivTower_one hchar hW hWb hWrep hc hw₀ hc₀
  | succ m ih =>
    obtain ⟨q, hq0, htower⟩ := ih
    exact h.exists_derivTower_succ hchar hW hWb hWrep hc hw₀ hc₀ hq0 htower

/-- Persistence of smoothness: every closed-time slice of a coupled H² output of the De Gregorio
equation with smooth compactly supported initial datum is `C^∞`. -/
theorem IsHkFrozenOutput.contDiff_vorticity (h : IsHkFrozenOutput hT F F W₀ w₀ c w)
    (hw₀ : ContDiff ℝ ∞ w₀) (hc₀ : HasCompactSupport w₀) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ ∞ (fun x ↦ w x t) := by
  obtain ⟨W, hW, hWb, hWbase, hWrep⟩ := h.exists_measurable_h2_graph
  obtain ⟨X, Y, hX₀, hX', hXc, hYc, hYX, hXY, hYLip, _⟩ :=
    exists_hkCurve_hilbert_eulerian_coordinates hT F
  have hchar : HkCharacteristics hT F c X Y :=
    ⟨⟨h.coefficient_continuous, h.hilbert_pair, h.velocity_derivative,
      h.coefficient_bound, hX₀, hX', hXc⟩, hYc, hYX, hXY, hYLip⟩
  have hc := h.coefficient_eq_realHilbertH1 hWbase
  apply contDiff_infty.mpr
  intro n
  obtain ⟨q, hq0, htower⟩ := h.exists_derivTower hchar hW hWb hWrep hc hw₀ hc₀ n
  have hrep (s : Icc (0 : ℝ) T) :
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (q 0 s)) = fun x ↦ w x s := by
    rw [hq0]
    exact hWrep s
  exact (htower.contDiff hrep ⟨t, ht⟩).of_le (by exact_mod_cast (by omega : n ≤ n + 1 + 1))

end DeGregorio.Iteration
