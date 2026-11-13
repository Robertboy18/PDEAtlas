/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalSpectralFrame
public import PDE.Analysis.Calculus.AveragedFDeriv
public import PDE.Hyperbolic.ConservationLaw.System.Basic
public import PDE.LinearAlgebra.Eigenbasis

/-!
# Ordered spectral branches of the averaged flux derivative

For a flux of class `C^(n+1)` near a strictly hyperbolic state, the averaged derivative
has one common `C^n`, strictly ordered eigenbasis neighborhood. The basis and branches
are constructed from strict hyperbolicity at that state. The same averaged operator
recovers the flux increment, so a Rankine–Hugoniot jump is an eigenvector equation
for these operators.

In particular, a locally `C²` flux gives `C¹` eigenfields. The vectors have
base-coordinate normalization, rather than unit norm. This is the input to the
implicit equation for local shock curves.

These are steps 1 and 2 of the proof of Theorem 2 in Evans, §11.2.3: the averaged Jacobian
`B(z)` with (15)-(16), and its smooth eigenpairs (18) near the base state. Evans takes a smooth
flux and unit eigenvectors; our regularity is finite and local to an open neighborhood of the
base state.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, proof of Theorem 2, steps 1-2, equations
  (15)-(19).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Set
open scoped ContDiff Topology

/-- Extend a prescribed ordered eigenbasis to the averaged Jacobian. Keeping
that basis fixes the normalization used by a given shock curve. Finite and
infinite regularity hold on one common neighborhood. -/
theorem exists_local_averaged_spectral_frame_of_basis
    {m : ℕ} {n : ℕ∞} {flux : ℝ^m → ℝ^m} {U : Set (ℝ^m)} {u₀ : ℝ^m}
    (hU : IsOpen U) (hu₀ : u₀ ∈ U) (hflux : ContDiffOn ℝ ((n : ℕ∞ω) + 1) flux U)
    (b : Module.Basis (Fin m) ℝ (ℝ^m)) (eig : Fin m → ℝ)
    (horder : StrictMono eig) (heigen : ∀ k, fderiv ℝ flux u₀ (b k) = eig k • b k) :
    ∃ ψ : Fin m → ℝ^m → ℝ^m × ℝ,
    ∃ V : Set (ℝ^m),
      IsOpen V ∧ u₀ ∈ V ∧ V ⊆ U ∧
      (∀ k, ψ k u₀ = (b k, eig k)) ∧
      (∀ k, ContDiffOn ℝ n (ψ k) V) ∧
      ∀ u ∈ V,
        PDE.Analysis.averagedFDeriv flux u₀ u (u - u₀) = flux u - flux u₀ ∧
        StrictMono (fun k ↦ (ψ k u).2) ∧
        (∀ k, Module.End.HasEigenvector
          (PDE.Analysis.averagedFDeriv flux u₀ u).toLinearMap
          (ψ k u).2 (ψ k u).1 ∧ b.equivFun (ψ k u).1 k = 1) ∧
        ∃ bu : Module.Basis (Fin m) ℝ (ℝ^m),
          ∀ k, bu k = (ψ k u).1 := by
  obtain ⟨χ, hχbase, W, hW, hAW, hχ⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame
      b (fderiv ℝ flux u₀) eig heigen horder
  obtain ⟨V₀, hV₀, huV₀, hV₀U, hB, hinc⟩ :=
    PDE.Analysis.exists_local_contDiff_averagedFDeriv (n := n) hU hu₀ hflux
  let B := PDE.Analysis.averagedFDeriv flux u₀
  have hBbase : B u₀ = fderiv ℝ flux u₀ := PDE.Analysis.averagedFDeriv_self flux u₀
  have hBW : W ∈ 𝓝 (B u₀) := by
    rw [hBbase]
    exact hW.mem_nhds hAW
  have hcont : ContinuousAt B u₀ := (hB.contDiffAt (hV₀.mem_nhds huV₀)).continuousAt
  have hnear : B ⁻¹' W ∈ 𝓝 u₀ := hcont hBW
  have hboth : V₀ ∩ B ⁻¹' W ∈ 𝓝 u₀ := Filter.inter_mem (hV₀.mem_nhds huV₀) hnear
  obtain ⟨V, hVsub, hVopen, huV⟩ := _root_.mem_nhds_iff.mp hboth
  refine ⟨fun k u ↦ χ k (B u), V, hVopen, huV, fun _ hu ↦ hV₀U (hVsub hu).1, ?_, ?_, ?_⟩
  · intro k
    change χ k (B u₀) = (b k, eig k)
    rw [hBbase, hχbase k]
  · intro k u hu
    have hregB := hB.contDiffAt (hV₀.mem_nhds (hVsub hu).1)
    have hregχ := ((hχ (B u) (hVsub hu).2).2.1 k).1
    exact ((hregχ.of_le (by simp)).comp u hregB).contDiffWithinAt
  · intro u hu
    obtain ⟨hord, hvec, hbasis⟩ := hχ (B u) (hVsub hu).2
    exact ⟨hinc u (hVsub hu).1, hord, fun k ↦ (hvec k).2, hbasis⟩

/-- A locally `C^(n+1)` flux, strictly hyperbolic at one state, has a `C^n` ordered
spectral frame for its averaged Jacobian near that state. The output includes the
exact flux-increment identity and a basis at each nearby state. The case `n = 1`
provides the `C¹` eigenfields used to construct shock curves from a `C²` flux. -/
theorem exists_local_averaged_spectral_frame {m n : ℕ} {flux : ℝ^m → ℝ^m} {U : Set (ℝ^m)} {u₀ : ℝ^m}
    (hU : IsOpen U) (hu₀ : u₀ ∈ U) (hflux : ContDiffOn ℝ (n + 1 : ℕ) flux U)
    (hhyper : IsStrictlyHyperbolicAt flux u₀) :
    ∃ b : Module.Basis (Fin m) ℝ (ℝ^m),
    ∃ eig : Fin m → ℝ,
    ∃ ψ : Fin m → ℝ^m → ℝ^m × ℝ,
    ∃ V : Set (ℝ^m),
      StrictMono eig ∧ IsOpen V ∧ u₀ ∈ V ∧ V ⊆ U ∧
      (∀ k, ψ k u₀ = (b k, eig k)) ∧
      (∀ k, ContDiffOn ℝ n (ψ k) V) ∧
      ∀ u ∈ V,
        PDE.Analysis.averagedFDeriv flux u₀ u (u - u₀) = flux u - flux u₀ ∧
        StrictMono (fun k ↦ (ψ k u).2) ∧
        (∀ k, Module.End.HasEigenvector
          (PDE.Analysis.averagedFDeriv flux u₀ u).toLinearMap
          (ψ k u).2 (ψ k u).1 ∧ b.equivFun (ψ k u).1 k = 1) ∧
        ∃ bu : Module.Basis (Fin m) ℝ (ℝ^m),
          ∀ k, bu k = (ψ k u).1 := by
  obtain ⟨_hdiff, b₀, eig₀, hinj, heigen₀⟩ := hhyper
  obtain ⟨b, eig, horder, heigen⟩ :=
    b₀.exists_ordered_eigenbasis (fderiv ℝ flux u₀).toLinearMap eig₀ hinj
      (fun k ↦ (heigen₀ k).apply_eq_smul)
  obtain ⟨ψ, V, hV, huV, hVU, hbase, hψ, hframe⟩ :=
    exists_local_averaged_spectral_frame_of_basis (n := n)
      hU hu₀ (by simpa using hflux) b eig horder heigen
  exact ⟨b, eig, ψ, V, horder, hV, huV, hVU, hbase, hψ, hframe⟩

end PDE.Hyperbolic.ConservationLaw.System
