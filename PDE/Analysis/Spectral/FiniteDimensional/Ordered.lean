/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalSpectralFrame
public import PDE.LinearAlgebra.Eigenbasis

/-!
# Ordered simple real spectra

A complete real eigenbasis with strictly increasing eigenvalues determines its
eigenvalue list uniquely. Local analytic eigenpairs then give the regularity of
that list under any smooth parameterization of the operator.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace ContinuousLinearMap

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- A complete eigenbasis with a simple increasing real spectrum. -/
def HasOrderedEigenbasis (n : ℕ) (A : E →L[ℝ] E) : Prop :=
  ∃ a : Fin n → ℝ, StrictMono a ∧ ∃ b : Module.Basis (Fin n) ℝ E,
    ∀ k, A (b k) = a k • b k

/-- The increasing eigenvalues of a simple real spectrum; zero otherwise. -/
def orderedEigenvalue (n : ℕ) (A : E →L[ℝ] E) (k : Fin n) : ℝ := by
  classical
  exact if h : HasOrderedEigenbasis n A then h.choose k else 0

theorem orderedEigenvalue_spec {A : E →L[ℝ] E} (h : HasOrderedEigenbasis n A) :
    StrictMono (orderedEigenvalue n A) ∧ ∃ b : Module.Basis (Fin n) ℝ E,
      ∀ k, A (b k) = orderedEigenvalue n A k • b k := by
  unfold orderedEigenvalue
  simpa only [dite_eq_left h] using h.choose_spec

/-- Ordering makes the eigenvalue list independent of every choice of basis. -/
theorem orderedEigenvalue_eq_of_eigenbasis
    {A : E →L[ℝ] E} (b : Module.Basis (Fin n) ℝ E) {a : Fin n → ℝ}
    (ha : StrictMono a) (hb : ∀ k, A (b k) = a k • b k) :
    orderedEigenvalue n A = a := by
  obtain ⟨hc, c, hAc⟩ := orderedEigenvalue_spec (⟨a, ha, b, hb⟩ : HasOrderedEigenbasis n A)
  exact c.eq_eigenvalues_of_strictMono b A.toLinearMap hc ha hAc hb

/-- Any selection agreeing with complete increasing eigenvalue lists inherits
the regularity of the operator. Only the spectrum at the base point is assumed. -/
theorem contDiffAt_of_eq_ordered_eigenvalues
    {q : WithTop ℕ∞} {B : X → E →L[ℝ] E} {x : X}
    (hB : ContDiffAt ℝ q B x) (h : HasOrderedEigenbasis n (B x))
    (a : X → Fin n → ℝ)
    (ha : ∀ y (b : Module.Basis (Fin n) ℝ E) (s : Fin n → ℝ),
      StrictMono s → (∀ k, B y (b k) = s k • b k) → a y = s)
    (k : Fin n) : ContDiffAt ℝ q (fun y ↦ a y k) x := by
  obtain ⟨s, hs, b, hb⟩ := h
  obtain ⟨ψ, _, U, hU, hx, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame b (B x) s hb hs
  have hψ : ContDiffAt ℝ q (ψ k) (B x) :=
    ((hframe _ hx).2.1 k).1.of_le le_top
  have heq : (fun y ↦ a y k) =ᶠ[𝓝 x] fun y ↦ (ψ k (B y)).2 := by
    filter_upwards [hB.continuousAt (hU.mem_nhds hx)] with y hy
    obtain ⟨hord, heigen, c, hc⟩ := hframe _ hy
    exact congrFun (ha y c (fun j ↦ (ψ j (B y)).2) hord
      (fun j ↦ by rw [hc j]; exact (heigen j).2.1.apply_eq_smul)) k
  exact ((hψ.comp x hB).snd).congr_of_eventuallyEq heq

/-- Ordered eigenvalues retain every finite smoothness order, and smoothness to
all orders, of an operator family. -/
theorem contDiffAt_orderedEigenvalue
    {q : WithTop ℕ∞} {B : X → E →L[ℝ] E} {x : X}
    (hB : ContDiffAt ℝ q B x) (h : HasOrderedEigenbasis n (B x)) (k : Fin n) :
    ContDiffAt ℝ q (fun y ↦ orderedEigenvalue n (B y) k) x :=
  contDiffAt_of_eq_ordered_eigenvalues hB h (fun y ↦ orderedEigenvalue n (B y))
    (fun _ b _ hs hb ↦ orderedEigenvalue_eq_of_eigenbasis b hs hb) k

/-- A nonzero eigenvector of a simple complete spectrum spans its entire
eigenspace, including the zero vector. -/
theorem eigenspace_eq_span_of_eigenbasis
    {A : E →L[ℝ] E} (b : Module.Basis (Fin n) ℝ E) {a : Fin n → ℝ}
    (ha : Function.Injective a) (hb : ∀ k, A (b k) = a k • b k)
    {s : ℝ} {v : E} (hv : Module.End.HasEigenvector A.toLinearMap s v) :
    Module.End.eigenspace A.toLinearMap s = ℝ ∙ v := by
  apply le_antisymm
  · intro w hw
    by_cases hw₀ : w = 0
    · simp [hw₀]
    obtain ⟨c, _, hc⟩ := b.exists_ne_zero_smul_eq_of_eigenvectors A.toLinearMap a ha hb
      hv.2 hw₀ hv.apply_eq_smul (Module.End.mem_eigenspace_iff.mp hw)
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · exact (Submodule.span_singleton_le_iff_mem ..).mpr hv.1

end ContinuousLinearMap
