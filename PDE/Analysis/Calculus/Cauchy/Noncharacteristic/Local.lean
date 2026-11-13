/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Cauchy.Noncharacteristic.Determination
public import PDE.Analysis.Calculus.LocalExtension

/-!
# Cauchy jets for solutions smooth only near the hypersurface

Local smooth representatives permit the intrinsic jet induction to be used on
an arbitrary open neighborhood. The representatives are constructed by a bump
function and disappear from the conclusion, which concerns the original
functions and their ordinary derivatives.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace PDE.Analysis.Cauchy

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Local smoothness, normal Cauchy data and a nonzero principal symbol
determine every jet of the original solutions along the hypersurface. -/
theorem iteratedFDeriv_eq_on_of_normal_data_contDiffOn
    {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {k : ℕ} (d : ∀ j, ι j → Fin j → ℝ^n)
    (a : ι k → ℝ^n × (∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] ℝ) → ℝ)
    (b : ℝ^n × (∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] ℝ) → ℝ)
    {Γ Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) (hΓΩ : Γ ⊆ Ω)
    (ha : ∀ α, ∀ x ∈ Γ, ∀ p, ContDiffAt ℝ ∞ (a α) (x, p))
    (hb : ∀ x ∈ Γ, ∀ p, ContDiffAt ℝ ∞ b (x, p))
    {ℓ : ℝ^n → ℝ^n →ₗ[ℝ] ℝ}
    (hΓ : HasConormalParametrizations H Γ ℓ)
    (e : ℝ^n → ℝ^n) (he : ∀ x ∈ Γ, ℓ x (e x) = 1)
    (hdetect : ∀ j, 0 < j → j < k → ∀ x ∈ Γ,
      ∃ α, (∏ i, ℓ x (d j α i)) ≠ 0)
    {u v : ℝ^n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (hvalue : EqOn u v Γ)
    (hdata : ∀ j, 0 < j → j < k → ∀ x ∈ Γ,
      ∑ α, iteratedFDeriv ℝ j u x (d j α) * ∏ i, ℓ x (d j α i) =
        ∑ α, iteratedFDeriv ℝ j v x (d j α) * ∏ i, ℓ x (d j α i))
    (hPu : ∀ x ∈ Γ, ∀ᶠ y in 𝓝 x,
      ∑ α, a α (y, jetLT ℝ k u y) * iteratedFDeriv ℝ k u y (d k α) =
        b (y, jetLT ℝ k u y))
    (hPv : ∀ x ∈ Γ, ∀ᶠ y in 𝓝 x,
      ∑ α, a α (y, jetLT ℝ k v y) * iteratedFDeriv ℝ k v y (d k α) =
        b (y, jetLT ℝ k v y))
    (hsymbol : ∀ x ∈ Γ,
      ∑ α, a α (x, jetLT ℝ k u x) * ∏ i, ℓ x (d k α i) ≠ 0) :
    ∀ j, EqOn (iteratedFDeriv ℝ j u) (iteratedFDeriv ℝ j v) Γ := by
  classical
  intro j x hx
  obtain ⟨U, hU, -, huU⟩ :=
    hu.exists_contDiff_compactSupport_eventuallyEq hΩ (hΓΩ hx)
  obtain ⟨V, hV, -, hvV⟩ :=
    hv.exists_contDiff_compactSupport_eventuallyEq hΩ (hΓΩ hx)
  obtain ⟨s, hs, hopen, hxs⟩ := mem_nhds_iff.mp (huU.and hvV)
  have hujet (i : ℕ) {y : ℝ^n} (hy : y ∈ s) :
      iteratedFDeriv ℝ i u y = iteratedFDeriv ℝ i U y :=
    (((show EqOn u U s from fun _ hz ↦ (hs hz).1).eventuallyEq_of_mem
      (hopen.mem_nhds hy)).iteratedFDeriv ℝ i).self_of_nhds
  have hvjet (i : ℕ) {y : ℝ^n} (hy : y ∈ s) :
      iteratedFDeriv ℝ i v y = iteratedFDeriv ℝ i V y :=
    (((show EqOn v V s from fun _ hz ↦ (hs hz).2).eventuallyEq_of_mem
      (hopen.mem_nhds hy)).iteratedFDeriv ℝ i).self_of_nhds
  have hujets {y : ℝ^n} (hy : y ∈ s) : jetLT ℝ k u y = jetLT ℝ k U y :=
    funext fun i ↦ hujet i hy
  have hvjets {y : ℝ^n} (hy : y ∈ s) : jetLT ℝ k v y = jetLT ℝ k V y :=
    funext fun i ↦ hvjet i hy
  have hsame := iteratedFDeriv_eq_on_of_normal_data d a b
    (fun α y hy ↦ ha α y hy.1) (fun y hy ↦ hb y hy.1)
    (hΓ.inter_open hopen) e (fun y hy ↦ he y hy.1)
    (fun i hi hik y hy ↦ hdetect i hi hik y hy.1) hU hV
    (fun y hy ↦ ((hs hy.2).1.symm.trans (hvalue hy.1)).trans (hs hy.2).2)
    (fun i hi hik y hy ↦ by
      simpa only [← hujet i hy.2, ← hvjet i hy.2] using hdata i hi hik y hy.1)
    (fun y hy ↦ by
      filter_upwards [hPu y hy.1, hopen.mem_nhds hy.2] with z hz hzs
      simpa only [← hujet k hzs, ← hujets hzs] using hz)
    (fun y hy ↦ by
      filter_upwards [hPv y hy.1, hopen.mem_nhds hy.2] with z hz hzs
      simpa only [← hvjet k hzs, ← hvjets hzs] using hz)
    (fun y hy ↦ by
      simpa only [← hujets hy.2] using hsymbol y hy.1)
  exact (hujet j hxs).trans ((hsame j ⟨hx, hxs⟩).trans (hvjet j hxs).symm)

end PDE.Analysis.Cauchy
