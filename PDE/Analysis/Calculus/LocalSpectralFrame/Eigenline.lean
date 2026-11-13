/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalSpectralFrame
public import PDE.LinearAlgebra.Eigenbasis

/-!
# Identifying a continuous eigenvalue branch

Near a simple real spectrum, a continuous eigenvalue with prescribed base value
cannot switch to a different ordered branch. A corresponding eigenvector whose
fixed base coordinate is the parameter is therefore that parameter times the
normalized spectral vector. At parameter zero the vector vanishes; no nonzero
eigenvector assertion is made there.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Calculus.SimpleEigenpair

open Filter Set
open scoped Topology

/-- A continuous eigenvalue selects one simple spectral branch, and a fixed
coordinate identifies the associated vector even as it vanishes at zero. -/
theorem eventually_eq_normalized_eigenline
    {ι E Z : Type*} [Finite ι] [LinearOrder ι] [TopologicalSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b : Module.Basis ι ℝ E} {B : Z → E →L[ℝ] E} {z₀ : Z} {eig : ι → ℝ}
    {ψ : ι → Z → E × ℝ} {U : Set Z}
    (hbase : ∀ j, ψ j z₀ = (b j, eig j))
    (horder : StrictMono eig) (hU : U ∈ 𝓝 z₀)
    (hψ : ∀ j, ContinuousAt (ψ j) z₀)
    (hframe : ∀ z ∈ U,
      StrictMono (fun j ↦ (ψ j z).2) ∧
      (∀ j, Module.End.HasEigenvector (B z).toLinearMap (ψ j z).2 (ψ j z).1 ∧
        b.equivFun (ψ j z).1 j = 1) ∧
      ∃ bB : Module.Basis ι ℝ E, ∀ j, bB j = (ψ j z).1)
    {T : ℝ → Z} {w : ℝ → E} {a : ℝ → ℝ} {k : ι}
    (hT : ContinuousAt T 0) (hT₀ : T 0 = z₀)
    (ha : ContinuousAt a 0) (ha₀ : a 0 = eig k)
    (hnear : ∀ᶠ s in 𝓝 0,
      B (T s) (w s) = a s • w s ∧ b.equivFun (w s) k = s) :
    ∀ᶠ s in 𝓝 0, w s = s • (ψ k (T s)).1 ∧ a s = (ψ k (T s)).2 := by
  have hother (j : ι) :
      ∀ᶠ s in 𝓝 0, j ≠ k → a s ≠ (ψ j (T s)).2 := by
    by_cases hj : j = k
    · exact Filter.Eventually.of_forall fun _ h ↦ (h hj).elim
    · have hcomp : ContinuousAt (fun s ↦ (ψ j (T s)).2) 0 :=
        ((hT₀.symm ▸ hψ j).comp hT).snd
      have hne : a 0 ≠ (ψ j (T 0)).2 := by
        simpa only [ha₀, hT₀, hbase j] using horder.injective.ne (Ne.symm hj)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (ha.eventually_lt hcomp hlt).mono fun _ h _ ↦ h.ne
      · exact (hcomp.eventually_lt ha hgt).mono fun _ h _ ↦ h.ne.symm
  have hTU : ∀ᶠ s in 𝓝 0, T s ∈ U := hT (hT₀.symm ▸ hU)
  filter_upwards [hnear, hTU, Filter.eventually_all.mpr hother] with s hs hsU hsep
  by_cases hw : w s = 0
  · have hs₀ : s = 0 := by simpa only [hw, map_zero, Pi.zero_apply] using hs.2.symm
    subst s
    simp only [hw, hT₀, ha₀, hbase k, zero_smul, and_self]
  · obtain ⟨hord, hvec, bB, hbB⟩ := hframe (T s) hsU
    have hdiag (j : ι) : B (T s) (bB j) = (ψ j (T s)).2 • bB j := by
      rw [hbB j]
      exact (hvec j).1.apply_eq_smul
    obtain ⟨j, hj, hline⟩ := bB.exists_eq_smul_of_apply_eq_smul
      (B (T s)).toLinearMap (fun j ↦ (ψ j (T s)).2) hord.injective hdiag hw hs.1
    have hjk : j = k := by
      by_contra h
      exact hsep j h hj
    subst j
    have hcoord : bB.equivFun (w s) k = s := by
      calc
        bB.equivFun (w s) k = b.equivFun
            (bB.equivFun (w s) k • bB k) k := by
          rw [map_smul, Pi.smul_apply, hbB k, (hvec k).2, smul_eq_mul, mul_one]
        _ = b.equivFun (w s) k := congrArg (fun v ↦ b.equivFun v k) hline.symm
        _ = s := hs.2
    exact ⟨by simpa only [hcoord, hbB k] using hline, hj⟩

end PDE.Analysis.Calculus.SimpleEigenpair
