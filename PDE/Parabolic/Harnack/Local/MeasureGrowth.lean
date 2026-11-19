/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Local.ForwardGrowth
public import PDE.Analysis.Geometry.SpaceTime.Superlevels
import CAS.ExactTactic

/-!
# A later lower bound from a positive superlevel fraction

A positive fraction of an early parabolic box lies above a given level.
Finite forward-cover iteration finds a dense full-sized slice at a lower
level. Contact growth then gives a lower bound on a later spatial ball.
Every scale and level constant is chosen before the coefficients and solution.

This local result uses joint C² regularity. `Local.Classical` passes to continuous
spatial second derivatives and a continuous first time derivative by approximation.
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum BoxIntegral Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

variable {n : ℕ}

/-- Stretching a parabolic box in time leaves its spatial cylinder unchanged and
multiplies its duration by the stretch factor. -/
private theorem mapsTo_time_stretch_cylinder
    (I : Box (Fin (n + 1))) (j : Fin (n + 1)) {r ε L R D : ℝ}
    (hr : 0 ≤ r) (hL : 0 < L) (hR : (n : ℝ) + 1 ≤ R) (hD : L * ε ≤ D)
    (hside : ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r)
    (htime : I.upper j - I.lower j = ε * r ^ 2) :
    MapsTo (fun x : Fin (n + 1) → ℝ ↦
      (WithLp.toLp 2 (fun i ↦ x (j.succAbove i)), x j))
      (I.forwardExtension j (-1) L hL).Icc
      (closedBall (euclideanBoxCenter (I.face j)) (r * R) ×ˢ
        Icc (I.lower j) (I.lower j + r ^ 2 * D)) := by
  simpa only [Box.face_forwardExtension, Box.lower_forwardExtension_neg_one] using
    mapsTo_box_space_time_cylinder (I.forwardExtension j (-1) L hL) j hr hR hD
      (by simpa only [Box.face_forwardExtension] using hside)
      (by rw [Box.upper_sub_lower_forwardExtension, htime, mul_assoc])

/-- A positive early superlevel fraction forces a uniform lower bound on a
later ball. The spatial dimension may be zero, and all constants precede
the coefficients, scale, solution, and level. -/
theorem exists_later_ball_lower_bound_of_superlevel_fraction
    {α τ B : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hB : 0 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∀ β : ℝ, 0 < β →
      ∃ D C : ℝ, 1 < D ∧ 0 < C ∧
      ∀ (I : Box (Fin (n + 1))) (j : Fin (n + 1)) (r : ℝ),
        0 < r → r ≤ 1 →
        (∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r) →
        I.upper j - I.lower j = ε * r ^ 2 →
        ∀ (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (d : ℝ^n → ℝ → ℝ^n),
          let z := euclideanBoxCenter (I.face j)
          let s := I.lower j
          let Q := closedBall z (r * (17 * ((n : ℝ) + 1))) ×ˢ
            Icc s (s + r ^ 2 * D)
          (∀ p ∈ Q, (a p.1 p.2).PosSemidef) →
          (∀ p ∈ Q, ∀ v : ℝ^n, α * ‖v‖ ^ 2 ≤ ⟪v, (a p.1 p.2).toEuclideanLin v⟫) →
          (∀ p ∈ Q, (a p.1 p.2).trace ≤ τ) →
          (∀ p ∈ Q, ‖d p.1 p.2‖ ≤ B) →
          ∀ (u : ℝ^n → ℝ → ℝ) (ℓ : ℝ), 0 < ℓ →
            (∀ p ∈ Q, ContDiffAt ℝ 2 (Function.uncurry u) p) →
            (∀ p ∈ Q, 0 ≤ u p.1 p.2) →
            (∀ p ∈ Q, 0 ≤ matrixParabolicOperator a d (fun _ _ ↦ 0) u p.1 p.2) →
            β * volume.real (I : Set (Fin (n + 1) → ℝ)) ≤
              (volume.restrict {x : Fin (n + 1) → ℝ |
                ℓ < u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j)}).real I →
            ∃ z' ∈ closedBall z (((n : ℝ) + 1) * r),
              ∃ q ∈ Icc (s + r ^ 2) (s + r ^ 2 * D),
                ∀ x ∈ closedBall z' r, ℓ / C < u x q := by
  let R := 16 * ((n : ℝ) + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hR : 0 < R := by dsimp only [R]; positivity
  have hRbox : (n : ℝ) + 1 ≤ R := by dsimp only [R]; nlinarith
  have hshort : (1 : ℝ) < R ^ 2 / 8 := by dsimp only [R]; nlinarith
  have hRsum : R + ((n : ℝ) + 1) = 17 * ((n : ℝ) + 1) := by
    dsimp only [R]
    clear * - n
    cas
  obtain ⟨δ, ε, hδ, hδ₁, hε, hεquarter, hpersistent⟩ :=
    exists_box_persistent_growth (n := n) hRbox hα hτ hB hshort
  obtain ⟨lag, m, H, hm, hlag, hlagtime, hfactor, hHdef, hH⟩ :=
    exists_forward_parameters hδ₁ hε
  obtain ⟨M, hM, hgrowth⟩ := hpersistent H hH
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  refine ⟨ε, hε, hεquarter, ?_⟩
  intro β hβ
  obtain ⟨S, hS⟩ := exists_nat_gt (lag + m)
  obtain ⟨N, _, hbudget⟩ := Prepartition.exists_geometric_affine_lt
    (show 0 ≤ δ * (1 + (lag + 1) / m) by positivity) hfactor hβ 1 (S : ℝ)
  let A := 1 + (N : ℝ) * S
  let D := A * ε + (1 + H)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hD : 1 < D := by dsimp only [D]; linarith [mul_pos hA hε]
  refine ⟨D, M ^ (N + 1), hD, pow_pos hMpos _, ?_⟩
  intro I j r hr hr₁ hside htime a d
  dsimp only
  intro ha hell htrace hdrift u ℓ hℓ hreg hnonneg hsuper hinitial
  let z := euclideanBoxCenter (I.face j)
  let s := I.lower j
  let Q := closedBall z (r * (17 * ((n : ℝ) + 1))) ×ˢ Icc s (s + r ^ 2 * D)
  let v := fun x : Fin (n + 1) → ℝ ↦
    u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j)
  let t := fun k : ℕ ↦ ℓ / M ^ k
  let W := fun k : ℕ ↦ I.forwardExtension j (-1) (1 + (k : ℝ) * S) (by positivity)
  have htpos (k : ℕ) : 0 < t k := div_pos hℓ (pow_pos hMpos k)
  have hlevel (k : ℕ) : M * t (k + 1) = t k := by
    dsimp only [t]
    rw [pow_succ]
    clear * - M ℓ k hMpos
    cas using hMpos.ne' (pow_ne_zero k hMpos.ne')
  have htdec (k : ℕ) : t (k + 1) < t k := by nlinarith only [hlevel k, hM, htpos (k + 1)]
  have htmono : Antitone t := antitone_nat_of_succ_le (fun k ↦ (htdec k).le)
  have hWmono {k l : ℕ} (hkl : k ≤ l) : W k ≤ W l :=
    I.forwardExtension_mono j (-1) (by positivity) (by positivity)
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkl) (Nat.cast_nonneg S)))
  have hcyl (K : Box (Fin (n + 1))) (rK : ℝ) (hrK : 0 ≤ rK) (hrKr : rK ≤ r)
      (hK : K ≤ W N) :
      closedBall (euclideanBoxCenter (K.face j)) (rK * R) ×ˢ
          Icc (K.lower j) (K.lower j + rK ^ 2 * (1 + H)) ⊆ Q := by
    simpa only [hRsum, Q, z, s, D, A] using
      subbox_cylinder_subset_time_stretch_cylinder j hrK hrKr hA hR.le
        (by positivity : 0 ≤ 1 + H) hK hside htime
  have hgrowthQ (K : Box (Fin (n + 1))) (rK : ℝ) (k : ℕ) (hrK : 0 < rK) (hrKr : rK ≤ r)
      (hK : K ≤ W N) (hKside : ∀ i, (K.face j).upper i - (K.face j).lower i = 2 * rK)
      (hKtime : K.upper j - K.lower j = ε * rK ^ 2)
      (hdense : δ * volume.real (K : Set (Fin (n + 1) → ℝ)) <
        (volume.restrict {x | t k < v x}).real K) :
      ∀ q ∈ Icc (K.lower j + rK ^ 2) ((K.lower j + rK ^ 2) + rK ^ 2 * H),
        ∀ x ∈ closedBall (euclideanBoxCenter (K.face j)) (rK * (R / 2) / 2),
          t (k + 1) < u x q := by
    have hclosed := hcyl K rK hrK.le hrKr hK
    have hopen := (prod_mono ball_subset_closedBall Ioc_subset_Icc_self).trans hclosed
    exact hgrowth K j rK hrK (hrKr.trans hr₁) hKside hKtime a d
      (fun p hp ↦ ha p (hopen hp)) (fun p hp w ↦ hell p (hopen hp) w)
      (fun p hp ↦ htrace p (hopen hp)) (fun p hp ↦ hdrift p (hopen hp))
      u (t (k + 1)) (htpos _) (fun p hp ↦ hreg p (hclosed hp))
      (fun p hp ↦ hnonneg p (hclosed hp)) (fun p hp ↦ hsuper p (hopen hp))
      (by simpa only [hlevel] using hdense)
  have hWmap : MapsTo (fun x : Fin (n + 1) → ℝ ↦
      (WithLp.toLp 2 (fun i ↦ x (j.succAbove i)), x j)) (W N).Icc Q :=
    mapsTo_time_stretch_cylinder I j hr.le hA
      (by nlinarith : (n : ℝ) + 1 ≤ 17 * ((n : ℝ) + 1))
      (by dsimp only [D]; linarith : A * ε ≤ D) hside htime
  have hv : ContinuousOn v (W N).Icc :=
    ContinuousOn.comp (fun p hp ↦ (hreg p hp).continuousAt.continuousWithinAt)
      (by fun_prop) hWmap
  obtain ⟨k, hk, J, hJW, hJside, hJtime, hdense⟩ :=
    exists_dense_time_slice_of_forward_growth I j hr hε hδ.le hlag hm hside htime
      N S hS.le t (fun k _ ↦ htdec k) hv
      (fun k hk J hJW rJ hrJ hrJr hJside hJtime K hK hdense x hx ↦ by
        obtain ⟨hKside, hKtime⟩ :=
          parabolic_sides_of_mem_splitCenterTwiceAt j hJside hJtime hK
        have hxcyl := forwardExtension_subset_child_cylinder j hK (half_pos hrJ).le hm
          hKside hKtime hlagtime hHdef hx
        apply hgrowthQ K (rJ / 2) k (half_pos hrJ) ((half_le_self hrJ.le).trans hrJr)
          (((Prepartition.splitCenterTwiceAt J j).le_of_mem hK).trans
            (hJW.trans (hWmono hk.le))) hKside hKtime hdense (x j) hxcyl.2
        convert hxcyl.1 using 1
        dsimp only [R]
        clear * - n rJ
        cas)
      (by simpa only [t, pow_zero, div_one] using hinitial) hbudget
  have hJN : J ≤ W N := hJW.trans (hWmono hk.le)
  have hclosed := hcyl J r hr.le le_rfl hJN
  have hface : J.face j ≤ I.face j := by
    simpa only [W, Box.face_forwardExtension] using Box.face_mono hJN j
  have hz' : euclideanBoxCenter (J.face j) ∈ closedBall z (((n : ℝ) + 1) * r) := by
    rw [mem_closedBall, dist_eq_norm]
    exact norm_sub_euclideanBoxCenter_le (I.face j) hr.le hside
      (x := euclideanBoxCenter (J.face j))
      ((Box.le_iff_Icc.mp hface) (euclideanBoxCenter_mem_Icc (J.face j)))
  have hlower : I.lower j ≤ J.lower j := by
    simpa only [W, Box.lower_forwardExtension_neg_one] using Box.antitone_lower hJN j
  have hq : (euclideanBoxCenter (J.face j), J.lower j + r ^ 2) ∈ Q :=
    hclosed ⟨mem_closedBall_self (mul_nonneg hr.le hR.le),
      by linarith only [sq_nonneg r], by nlinarith only [hH, sq_nonneg r]⟩
  refine ⟨euclideanBoxCenter (J.face j), hz', J.lower j + r ^ 2,
    ⟨by linarith only [hlower], hq.2.2⟩, fun x hx ↦ ?_⟩
  refine (htmono (Nat.succ_le_succ hk.le)).trans_lt (hgrowthQ J r k hr le_rfl hJN hJside hJtime
    hdense _ ⟨le_rfl, by nlinarith only [hH, sq_nonneg r]⟩ x ?_)
  exact closedBall_subset_closedBall (show r ≤ r * (R / 2) / 2 by
    dsimp only [R]
    nlinarith only [hr, hn]) hx

end ParabolicHarnack
