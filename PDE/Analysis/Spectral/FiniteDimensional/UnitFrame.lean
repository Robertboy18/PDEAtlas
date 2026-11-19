/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.FiniteDimensional.Ordered
public import PDE.Analysis.InnerProductSpace.Line.SmoothSection
public import PDE.Analysis.InnerProductSpace.Eigenbasis
public import PDE.Analysis.InnerProductSpace.Calculus.Normalization

/-!
# Global unit eigenframes

Local analytic eigenpairs identify each ordered eigenspace with a smoothly
generated real line. The unit-line cover supplies a global unit eigenvector
with a prescribed initial sign. Applying the same construction to the adjoint
supplies left eigenvectors, without any self-adjointness assumption.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology ContDiff InnerProductSpace

namespace ContinuousLinearMap

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ} {q : WithTop ℕ∞}

/-- The ordered eigenspace admits local smooth unit generators. -/
theorem exists_local_unit_eigenline
    {B : X → E →L[ℝ] E} (hB : ContDiff ℝ q B)
    {x : X} (h : HasOrderedEigenbasis n (B x)) (k : Fin n) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ v : X → E,
      ContDiffOn ℝ q v U ∧ (∀ y ∈ U, ‖v y‖ = 1) ∧
        ∀ y ∈ U, Module.End.eigenspace (B y).toLinearMap
          (orderedEigenvalue n (B y) k) = ℝ ∙ v y := by
  obtain ⟨s, hs, b, hb⟩ := h
  obtain ⟨ψ, _, W, hW, hxW, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame b (B x) s hb hs
  let v : X → E := fun y ↦ NormedSpace.normalize (ψ k (B y)).1
  refine ⟨B ⁻¹' W, hW.preimage hB.continuous, hxW, v, ?_, ?_, ?_⟩
  · intro y hy
    have hψ : ContDiffAt ℝ q (ψ k) (B y) :=
      ((hframe _ hy).2.1 k).1.of_le le_top
    exact ((NormedSpace.contDiffAt_normalize ((hframe _ hy).2.1 k).2.1.2).comp y
      (hψ.fst.comp y hB.contDiffAt)).contDiffWithinAt
  · intro y hy
    exact NormedSpace.norm_normalize ((hframe _ hy).2.1 k).2.1.2
  · intro y hy
    obtain ⟨hord, heigen, c, hc⟩ := hframe _ hy
    have hcB (j : Fin n) : B y (c j) = (ψ j (B y)).2 • c j := by
      rw [hc j]
      exact (heigen j).2.1.apply_eq_smul
    have heq := orderedEigenvalue_eq_of_eigenbasis c hord hcB
    rw [congrFun heq k, eigenspace_eq_span_of_eigenbasis c hord.injective hcB
      (heigen k).2.1]
    dsimp [v, NormedSpace.normalize]
    exact (Submodule.span_singleton_smul_eq
      (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr (heigen k).2.1.2))) _).symm

/-- An initial unit eigenvector determines one global smooth ordered eigenvector. -/
theorem existsUnique_contDiff_unit_eigenvector
    {B : X → E →L[ℝ] E} (hB : ContDiff ℝ q B)
    (h : ∀ x, HasOrderedEigenbasis n (B x)) (k : Fin n)
    (x₀ : X) (v₀ : E)
    (hv₀ : Module.End.HasEigenvector (B x₀).toLinearMap
      (orderedEigenvalue n (B x₀) k) v₀) (hn₀ : ‖v₀‖ = 1) :
    ∃! v : C(X, E), ContDiff ℝ q v ∧ v x₀ = v₀ ∧
      ∀ x, Module.End.HasEigenvector (B x).toLinearMap
        (orderedEigenvalue n (B x) k) (v x) ∧ ‖v x‖ = 1 := by
  let L : X → Submodule ℝ E :=
    fun x ↦ Module.End.eigenspace (B x).toLinearMap (orderedEigenvalue n (B x) k)
  obtain ⟨v, hv, huniq⟩ :=
    Submodule.UnitTotal.existsUnique_contDiff_unit_section L
      (fun x ↦ exists_local_unit_eigenline hB (h x) k) x₀ v₀ hv₀.1 hn₀
  refine ⟨v, ⟨hv.1, hv.2.1, ?_⟩, ?_⟩
  · intro x
    refine ⟨⟨(hv.2.2 x).1, ?_⟩, (hv.2.2 x).2⟩
    intro hz
    have := (hv.2.2 x).2
    simp [hz] at this
  · rintro w ⟨hw, hw₀, hwv⟩
    exact huniq w ⟨hw, hw₀, fun x ↦ ⟨(hwv x).1.1, (hwv x).2⟩⟩

/-- Prescribed initial signs give a global smooth unit eigenbasis at every point. -/
theorem exists_contDiff_unit_eigenframe
    {B : X → E →L[ℝ] E} (hB : ContDiff ℝ q B)
    (h : ∀ x, HasOrderedEigenbasis n (B x)) (x₀ : X) (r₀ : Fin n → E)
    (hr₀ : ∀ k, Module.End.HasEigenvector (B x₀).toLinearMap
      (orderedEigenvalue n (B x₀) k) (r₀ k) ∧ ‖r₀ k‖ = 1) :
    ∃ r : Fin n → X → E,
      (∀ k, ContDiff ℝ q (r k) ∧ r k x₀ = r₀ k) ∧
      (∀ x k, Module.End.HasEigenvector (B x).toLinearMap
        (orderedEigenvalue n (B x) k) (r k x) ∧ ‖r k x‖ = 1) ∧
      ∀ x, ∃ b : Module.Basis (Fin n) ℝ E, ∀ k, b k = r k x := by
  classical
  choose r hr using fun k ↦
    (existsUnique_contDiff_unit_eigenvector hB h k x₀ (r₀ k) (hr₀ k).1 (hr₀ k).2).exists
  obtain ⟨_, b₀, _⟩ := orderedEigenvalue_spec (h x₀)
  let : FiniteDimensional ℝ E := b₀.finiteDimensional_of_finite
  refine ⟨fun k ↦ r k, fun k ↦ ⟨(hr k).1, (hr k).2.1⟩,
    fun x k ↦ (hr k).2.2 x, ?_⟩
  intro x
  have hli := Module.End.eigenvectors_linearIndependent' (B x).toLinearMap
    (orderedEigenvalue n (B x)) (orderedEigenvalue_spec (h x)).1.injective
    (fun k ↦ r k x) (fun k ↦ ((hr k).2.2 x).1)
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' (fun k ↦ r k x) hli
    (Module.finrank_eq_card_basis b₀).symm, ?_⟩
  intro k
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) k

/-- Normalizing a nonzero eigenvector preserves its eigenvalue. -/
theorem hasEigenvector_normalize {A : E →L[ℝ] E} {s : ℝ} {v : E}
    (hv : Module.End.HasEigenvector A.toLinearMap s v) :
    Module.End.HasEigenvector A.toLinearMap s (NormedSpace.normalize v) :=
  ⟨(Module.End.eigenspace A.toLinearMap s).smul_mem _ hv.1,
    (NormedSpace.normalize_eq_zero_iff v).not.mpr hv.2⟩

section Adjoint

variable [FiniteDimensional ℝ E]

/-- The adjoint has the same ordered simple spectrum. -/
theorem HasOrderedEigenbasis.adjoint {A : E →L[ℝ] E}
    (h : HasOrderedEigenbasis n A) : HasOrderedEigenbasis n (adjoint A) := by
  obtain ⟨a, ha, b, hb⟩ := h
  exact ⟨a, ha, b.innerDual, b.adjoint_apply_innerDual A a hb⟩

theorem orderedEigenvalue_adjoint {A : E →L[ℝ] E} (h : HasOrderedEigenbasis n A) :
    orderedEigenvalue n (adjoint A) = orderedEigenvalue n A := by
  obtain ⟨ha, b, hb⟩ := orderedEigenvalue_spec h
  exact orderedEigenvalue_eq_of_eigenbasis b.innerDual ha
    (b.adjoint_apply_innerDual A _ hb)

/-- A smooth family with simple real spectrum on a real normed parameter space
has global smooth right and left unit eigenframes with the canonical speeds.
The two unit frames need not be biorthonormal. -/
theorem exists_contDiff_unit_spectral_frame
    {B : X → E →L[ℝ] E} (hB : ContDiff ℝ q B)
    (h : ∀ x, HasOrderedEigenbasis n (B x)) :
    ∃ r l : Fin n → X → E,
      (∀ k, ContDiff ℝ q (fun x ↦ orderedEigenvalue n (B x) k) ∧
        ContDiff ℝ q (r k) ∧ ContDiff ℝ q (l k)) ∧
      (∀ x k, B x (r k x) = orderedEigenvalue n (B x) k • r k x ∧
        adjoint (B x) (l k x) = orderedEigenvalue n (B x) k • l k x ∧
        ‖r k x‖ = 1 ∧ ‖l k x‖ = 1) ∧
      (∀ x, ∃ br bl : Module.Basis (Fin n) ℝ E,
        (∀ k, br k = r k x) ∧ ∀ k, bl k = l k x) ∧
      ∀ x i j, ⟪l i x, r j x⟫_ℝ = 0 ↔ i ≠ j := by
  have hBa : ContDiff ℝ q (fun x ↦ adjoint (B x)) :=
    (adjoint (𝕜 := ℝ) (E := E) (F := E)).toContinuousLinearEquiv.contDiff.comp hB
  obtain ⟨_, b₀, hb₀⟩ := orderedEigenvalue_spec (h 0)
  have hr₀ (k : Fin n) :
      Module.End.HasEigenvector (B 0).toLinearMap (orderedEigenvalue n (B 0) k)
        (NormedSpace.normalize (b₀ k)) ∧ ‖NormedSpace.normalize (b₀ k)‖ = 1 :=
    ⟨hasEigenvector_normalize ⟨Module.End.mem_eigenspace_iff.mpr (hb₀ k), b₀.ne_zero k⟩,
      NormedSpace.norm_normalize (b₀.ne_zero k)⟩
  obtain ⟨r, hr, hre, hrb⟩ := exists_contDiff_unit_eigenframe hB h 0
    (fun k ↦ NormedSpace.normalize (b₀ k)) hr₀
  obtain ⟨_, c₀, hc₀⟩ := orderedEigenvalue_spec (h 0).adjoint
  have hl₀ (k : Fin n) :
      Module.End.HasEigenvector (adjoint (B 0)).toLinearMap
        (orderedEigenvalue n (adjoint (B 0)) k) (NormedSpace.normalize (c₀ k)) ∧
        ‖NormedSpace.normalize (c₀ k)‖ = 1 :=
    ⟨hasEigenvector_normalize ⟨Module.End.mem_eigenspace_iff.mpr (hc₀ k), c₀.ne_zero k⟩,
      NormedSpace.norm_normalize (c₀.ne_zero k)⟩
  obtain ⟨l, hl, hle, hlb⟩ := exists_contDiff_unit_eigenframe hBa (fun x ↦ (h x).adjoint)
    0 (fun k ↦ NormedSpace.normalize (c₀ k)) hl₀
  refine ⟨r, l, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨contDiff_iff_contDiffAt.mpr (fun x ↦
      contDiffAt_orderedEigenvalue hB.contDiffAt (h x) k), (hr k).1, (hl k).1⟩
  · intro x k
    refine ⟨(hre x k).1.apply_eq_smul, ?_, (hre x k).2, (hle x k).2⟩
    change (adjoint (B x)).toLinearMap (l k x) = _
    simpa only [orderedEigenvalue_adjoint (h x)] using (hle x k).1.apply_eq_smul
  · intro x
    obtain ⟨br, hbr⟩ := hrb x
    obtain ⟨bl, hbl⟩ := hlb x
    exact ⟨br, bl, hbr, hbl⟩
  · intro x i j
    obtain ⟨br, hbr⟩ := hrb x
    have hA (k : Fin n) :
        B x (br k) = orderedEigenvalue n (B x) k • br k := by
      rw [hbr k]
      exact (hre x k).1.apply_eq_smul
    have hAl : adjoint (B x) (l i x) = orderedEigenvalue n (B x) i • l i x := by
      change (adjoint (B x)).toLinearMap (l i x) = _
      simpa only [orderedEigenvalue_adjoint (h x)] using (hle x i).1.apply_eq_smul
    simpa only [hbr, ne_comm] using br.inner_adjoint_eigenvector_eq_zero_iff
      (B x) _ (orderedEigenvalue_spec (h x)).1.injective hA (hle x i).1.2 i hAl j

end Adjoint

end ContinuousLinearMap
