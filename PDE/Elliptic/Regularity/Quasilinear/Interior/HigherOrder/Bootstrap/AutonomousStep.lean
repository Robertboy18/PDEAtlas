/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.LocalRegularity
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.JetEquation

/-!
# One nonlinear regularity step

For a finite family satisfying diagonal elliptic equations with the same
principal matrix, smooth dependence on the values suffices to improve C¹ to
C². First Schauder gives Hölder first derivatives. The explicit commutator
is then Hölder because it is a smooth function of this first derivative field.
Second Schauder supplies the new derivative.
-/

@[expose] public noncomputable section

open Set Metric SobolevSpace
open PDE.Elliptic.Regularity.Schauder
open scoped ENNReal NNReal

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} [Fact (0 < n)] {I : Type*} [Fintype I] {Ω : Set ℝ^n}

/-- Smooth autonomous coefficients and forcing improve a C¹ weak solution
family to C². No regularity of the differentiated forcing is assumed. -/
theorem contDiffOn_two_of_autonomous_system
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω)
    {a : Fin n → Fin n → (I → ℝ) → ℝ}
    {f : I → Fin n → (I → ℝ) → ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hf : ∀ l i, ContDiff ℝ (⊤ : ℕ∞) (f l i))
    {v : ℝ^n → I → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    {θ Λ : ℝ} (hθ : 0 < θ) (hΛ : 0 ≤ Λ)
    (hbound : ∀ x ∈ Ω, ∀ i j, ‖a i j (v x)‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, a i j (v x) * ξ j * ξ i)
    (heq : ∀ l, HasZeroWeakDivergenceOn Ω (fun i x ↦
      (∑ j, a i j (v x) * (∂[j] (fun y ↦ v y l)) x) - f l i (v x))) :
    ContDiffOn ℝ 2 v Ω := by
  classical
  have hac (i j : Fin n) : ContDiffOn ℝ 1 (fun x ↦ a i j (v x)) Ω :=
    ((ha i j).of_le (by simp)).comp_contDiffOn hv
  have hfc (l : I) (i : Fin n) : ContDiffOn ℝ 1 (fun x ↦ f l i (v x)) Ω :=
    ((hf l i).of_le (by simp)).comp_contDiffOn hv
  apply contDiffOn_pi.mpr
  intro l z hz
  have : Nonempty I := ⟨l⟩
  obtain ⟨R, hR, hc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz)
  choose r hr hsub hder using fun t : I ↦
    exists_holder_partialDeriv_of_local_flux hq2 hq hΩ hac (hfc t)
      (contDiffOn_pi.mp hv t) hθ hΛ hbound hell (heq t)
      (γ := (1 / 2 : ℝ≥0)) (by norm_num) (by norm_num) hz
  let ρ := min R (Finset.univ.inf' Finset.univ_nonempty r)
  have hρ : 0 < ρ :=
    lt_min hR ((Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun t _ ↦ hr t)
  have hρR : ρ ≤ R := min_le_left _ _
  have hρr (t : I) : ρ ≤ r t :=
    (min_le_right _ _).trans (Finset.inf'_le r (Finset.mem_univ t))
  have hs : 0 < ρ / 2 := by positivity
  have hcΩ : closedBall z (ρ / 2) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ R)).trans hc
  have hcr (t : I) : closedBall z (ρ / 2) ⊆ ball z (r t) :=
    closedBall_subset_ball (by have := hρr t; linarith)
  obtain ⟨K, hK⟩ := exists_holder_pi (f := firstJet v)
    (s := closedBall z (ρ / 2)) (γ := (1 / 2 : ℝ≥0)) (fun t ↦ by
      cases t with
      | inl t =>
        exact exists_holderOnWith_of_contDiffOn (isCompact_closedBall z (ρ / 2))
          (convex_closedBall z (ρ / 2)) ((contDiffOn_pi.mp hv t).mono hcΩ) (by norm_num)
      | inr tk =>
        obtain ⟨N, hN⟩ := hder tk.1 tk.2
        exact ⟨N, hN.mono (hcr tk.1)⟩)
  have hjetc : ContinuousOn (firstJet v) (closedBall z (ρ / 2)) :=
    hK.continuousOn (by norm_num)
  obtain ⟨M, hM⟩ := exists_common_holder_constant (fun p : Fin n × Fin n ↦
    exists_holderOnWith_comp_of_contDiff (isCompact_closedBall z (ρ / 2)) hjetc hK
      ((contDiff_prolongedForcing ha hf (.inr (l, p.1)) p.2).of_le (by simp)))
  have hcomm (k i : Fin n) : HolderOnWith M (1 / 2 : ℝ≥0)
      (fun x ↦ (∂[k] (fun y ↦ f l i (v y))) x -
        ∑ j, (∂[k] (fun y ↦ a i j (v y))) x *
          (∂[j] (fun y ↦ v y l)) x) (ball z (ρ / 2)) := by
    intro x hx y hy
    have he (w : ℝ^n) (hw : w ∈ Ω) :=
      prolongedForcing_comp_firstJet
        ((hv.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by norm_num))
        (fun i j ↦ (ha i j).differentiable (by simp) _)
        (fun l i ↦ (hf l i).differentiable (by simp) _) l k i
    simpa only [Function.comp_apply, he x (hcΩ (ball_subset_closedBall hx)),
      he y (hcΩ (ball_subset_closedBall hy))] using
      hM (k, i) x (ball_subset_closedBall hx) y (ball_subset_closedBall hy)
  have hbΩ : ball z (ρ / 2) ⊆ Ω := ball_subset_closedBall.trans hcΩ
  have hreg := contDiffOn_two_of_local_flux_holder_commutator hq2 hq isOpen_ball
    (fun i j ↦ (hac i j).mono hbΩ) (fun i ↦ (hfc l i).mono hbΩ)
    ((contDiffOn_pi.mp hv l).mono hbΩ) hθ hΛ
    (fun x hx ↦ hbound x (hbΩ hx)) (fun x hx ↦ hell x (hbΩ hx))
    ((heq l).mono hbΩ) (by norm_num : 0 < (1 / 2 : ℝ≥0))
    (by norm_num : (1 / 2 : ℝ≥0) < 1) hcomm
  exact (hreg.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hs))).contDiffWithinAt

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
