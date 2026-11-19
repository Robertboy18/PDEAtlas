/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.LocalData
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.SecondDerivatives
import PDE.Spaces.Sobolev.Calculus.Differentiation.Representative

/-!
# The two local Schauder applications

The first application gives Hölder first derivatives of a C¹ solution.
The second applies to its differentiated equation. Interior H² regularity
supplies the weak derivatives used in that equation, rather than assuming
that the classical first derivatives already belong to H¹.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace
open PDE.Elliptic.Regularity.Schauder
open scoped Sobolev ENNReal NNReal InnerProductSpace

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}

/-- C¹ coefficients and forcing give Hölder first derivatives locally,
with any prescribed exponent strictly between zero and one. -/
theorem exists_holder_partialDeriv_of_local_flux
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω) {a : Fin n → Fin n → ℝ^n → ℝ}
    {f : Fin n → ℝ^n → ℝ} {v : ℝ^n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) Ω) (hv : ContDiffOn ℝ 1 v Ω)
    {θ Λ : ℝ} (hθ : 0 < θ) (hΛ : 0 ≤ Λ)
    (hbound : ∀ x ∈ Ω, ∀ i j, ‖a i j x‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, a i j x * ξ j * ξ i)
    (heq : HasZeroWeakDivergenceOn Ω
      (fun i x ↦ (∑ j, a i j x * (∂[j] v) x) - f i x))
    {γ : ℝ≥0} (hγ0 : 0 < γ) (hγ1 : γ < 1) {z : ℝ^n} (hz : z ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ Ω ∧
      ∀ i, ∃ K, HolderOnWith K γ (∂[i] v) (ball z r) := by
  obtain ⟨R, hR, hc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz)
  have hcl : IsCompact (closure (ball z R)) := by
    rw [closure_ball z hR.ne']
    exact isCompact_closedBall z R
  have hc' : closure (ball z R) ⊆ Ω := by rwa [closure_ball z hR.ne']
  obtain ⟨A, F, u, hA, hF, hu, he⟩ :=
    exists_sobolev_realization_of_local_flux hΩ ha hf hv heq isOpen_ball hcl hc'
  obtain ⟨K, hK⟩ := exists_common_holder_constant (fun p : Fin n × Fin n ↦
    exists_holderOnWith_of_contDiffOn (isCompact_closedBall z R) (convex_closedBall z R)
      ((ha p.1 p.2).mono hc) hγ1.le)
  obtain ⟨M, hM⟩ := exists_common_holder_constant (fun i : Fin n ↦
    exists_holderOnWith_of_contDiffOn (isCompact_closedBall z R) (convex_closedBall z R)
      ((hf i).mono hc) hγ1.le)
  have hb : ball z R ⊆ Ω := ball_subset_closedBall.trans hc
  obtain ⟨r, hr, hrR, hreg⟩ :=
    exists_holder_partialDeriv_of_holder_coefficients hq2 hq hθ hΛ isOpen_ball
      (fun i j ↦ wkpBaseCoordinateCLM (A i j)) a hγ0 hγ1
      (fun i j ↦ (hK (i, j)).mono ball_subset_closedBall) hA
      (fun x hx ↦ hbound x (hb hx)) (fun x hx ↦ hell x (hb hx))
      u (fun i ↦ wkpBaseCoordinateCLM (F i)) f
      (fun i ↦ (hM i).mono ball_subset_closedBall) hF he
      (hv.mono hb) hu.symm hR Subset.rfl
  exact ⟨r, hr, (closedBall_subset_closedBall (by linarith : r ≤ R)).trans hc, hreg⟩

/-- A Hölder commutator gives C² regularity locally. Its Sobolev equation
and H² state are constructed from the original C¹ weak solution. -/
theorem contDiffOn_two_of_local_flux_holder_commutator
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω) {a : Fin n → Fin n → ℝ^n → ℝ}
    {f : Fin n → ℝ^n → ℝ} {v : ℝ^n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) Ω) (hv : ContDiffOn ℝ 1 v Ω)
    {θ Λ : ℝ} (hθ : 0 < θ) (hΛ : 0 ≤ Λ)
    (hbound : ∀ x ∈ Ω, ∀ i j, ‖a i j x‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, a i j x * ξ j * ξ i)
    (heq : HasZeroWeakDivergenceOn Ω
      (fun i x ↦ (∑ j, a i j x * (∂[j] v) x) - f i x))
    {M γ : ℝ≥0} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hcomm : ∀ k i, HolderOnWith M γ
      (fun x ↦ (∂[k] (f i)) x - ∑ j, (∂[k] (a i j)) x * (∂[j] v) x) Ω) :
    ContDiffOn ℝ 2 v Ω := by
  intro z hz
  obtain ⟨R, hR, hc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz)
  have hcl : IsCompact (closure (ball z R)) := by
    rw [closure_ball z hR.ne']
    exact isCompact_closedBall z R
  have hc' : closure (ball z R) ⊆ Ω := by rwa [closure_ball z hR.ne']
  have hb : ball z R ⊆ Ω := ball_subset_closedBall.trans hc
  obtain ⟨A, F, u, hA, _, hu, he⟩ :=
    exists_sobolev_realization_of_local_flux hΩ ha hf hv heq isOpen_ball hcl hc'
  have hr : 0 < R / 2 := by positivity
  have hsmall : closure (ball z (R / 2)) ⊆ ball z R := by
    rw [closure_ball z hr.ne']
    exact closedBall_subset_ball (by linarith)
  have hsmallc : IsCompact (closure (ball z (R / 2))) := by
    rw [closure_ball z hr.ne']
    exact isCompact_closedBall z (R / 2)
  obtain ⟨W, hW⟩ := exists_interior_h2_of_divergence_forcing isOpen_ball
    (fun i j ↦ wkpBaseCoordinateCLM (A i j)) a
    (fun i j ↦ ((ha i j).mono hb).locallyLipschitzOn (convex_ball z R)) hA
    (aeUniformlyElliptic_of_representatives isOpen_ball hA hθ
      (fun x hx ↦ hell x (hb hx))) u F he isOpen_ball hsmallc hsmall
  have hsΩ : closure (ball z (R / 2)) ⊆ Ω := hsmall.trans hb
  have hs : ball z (R / 2) ⊆ Ω := subset_closure.trans hsΩ
  obtain ⟨B, G, _, hB, hG, _, _⟩ :=
    exists_sobolev_realization_of_local_flux hΩ ha hf hv heq isOpen_ball hsmallc hsΩ
  have hWv : (wkpBaseCoordinateCLM W : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball z (R / 2))] v := by
    rw [hW]
    exact (restrictDerivLp_apply_ae (subset_closure.trans hsmall) _).trans
      (ae_mono (domainMeasure_le (subset_closure.trans hsmall)) hu)
  let U : H¹(ball z (R / 2)) := lowerOrderCLM (by omega : 1 ≤ 2) W
  have hUv : (wkpBaseCoordinateCLM U : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball z (R / 2))] v := hWv
  have hweak := interiorVariableCoeffForm_eq_of_local_flux
    (fun i j ↦ wkpBaseCoordinateCLM (B i j)) U
    (fun i ↦ wkpBaseCoordinateCLM (G i)) a f v hB hG
    (wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn isOpen_ball U (hv.mono hs) hUv)
    (heq.mono hs)
  obtain ⟨K, hK⟩ := exists_common_holder_constant (fun p : Fin n × Fin n ↦
    exists_holderOnWith_of_contDiffOn (isCompact_closedBall z R) (convex_closedBall z R)
      ((ha p.1 p.2).mono hc) hγ1.le)
  have hsR : ball z (R / 2) ⊆ closedBall z R :=
    (subset_closure.trans hsmall).trans ball_subset_closedBall
  have hreg := contDiffOn_two_of_holder_commutator hq2 hq isOpen_ball B a
    (fun i j ↦ (ha i j).mono hs) hB hθ hΛ
    (fun x hx ↦ hbound x (hs hx)) (fun x hx ↦ hell x (hs hx))
    W G f (fun i ↦ (hf i).mono hs) hG hweak (hv.mono hs) hWv.symm hγ0 hγ1
    (fun i j ↦ (hK (i, j)).mono hsR) (fun k i ↦ (hcomm k i).mono hs)
  exact (hreg.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).contDiffWithinAt

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
