/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Spectral.FiniteDimensional.Ordered
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Field

/-!
# Canonical ordered characteristic speeds

Strict real hyperbolicity gives an increasing eigenvalue list. Completeness of
the eigenbasis and strict ordering make the list independent of all basis choices.
Consequently its entries agree locally with the analytic operator eigenbranches.
For a `C²` flux they are `C¹` functions of the state.

The family classifications below use these canonical speeds and quantify over
nonzero eigenvectors, without a globally selected smooth frame.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Set
open scoped ContDiff Topology

/-- Strict hyperbolicity supplies an increasing complete eigenbasis. -/
theorem IsStrictlyHyperbolicAt.exists_ordered_eigenbasis {m : ℕ} {flux : ℝ^m → ℝ^m} {q : ℝ^m}
    (h : IsStrictlyHyperbolicAt flux q) :
    ∃ a : Fin m → ℝ, StrictMono a ∧
      ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∀ k, fderiv ℝ flux q (b k) = a k • b k := by
  obtain ⟨_hdiff, b, a, hinj, heigen⟩ := h
  obtain ⟨c, eig, horder, hc⟩ := b.exists_ordered_eigenbasis (fderiv ℝ flux q).toLinearMap a hinj
      (fun k ↦ (heigen k).apply_eq_smul)
  exact ⟨eig, horder, c, hc⟩

/-- The `k`th increasing characteristic speed at a strictly hyperbolic state.
The value is set to zero outside the strictly hyperbolic region. -/
def characteristicSpeed {m : ℕ} (flux : ℝ^m → ℝ^m) (k : Fin m) (q : ℝ^m) : ℝ := by
  classical
  exact if h : IsStrictlyHyperbolicAt flux q then h.exists_ordered_eigenbasis.choose k
  else 0

/-- The canonical characteristic speeds belong to a complete ordered eigenbasis. -/
theorem characteristicSpeed_spec {m : ℕ} {flux : ℝ^m → ℝ^m} {q : ℝ^m}
    (h : IsStrictlyHyperbolicAt flux q) :
    StrictMono (fun k ↦ characteristicSpeed flux k q) ∧ ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∀ k,
      fderiv ℝ flux q (b k) = characteristicSpeed flux k q • b k := by
  simpa only [characteristicSpeed, dite_eq_left h] using h.exists_ordered_eigenbasis.choose_spec

/-- Any complete increasing eigenbasis has the canonical speed list. -/
theorem characteristicSpeed_eq_of_eigenbasis {m : ℕ} {flux : ℝ^m → ℝ^m} {q : ℝ^m}
    (b : Module.Basis (Fin m) ℝ (ℝ^m)) {a : Fin m → ℝ}
    (horder : StrictMono a) (hb : ∀ k, fderiv ℝ flux q (b k) = a k • b k) :
    (fun k ↦ characteristicSpeed flux k q) = a := by
  by_cases hdiff : DifferentiableAt ℝ flux q
  swap
  · have hhyp : ¬IsStrictlyHyperbolicAt flux q := fun h ↦ hdiff h.1
    funext k
    have h := hb k
    rw [fderiv_zero_of_not_differentiableAt hdiff, zero_apply, eq_comm,
      smul_eq_zero] at h
    simp only [characteristicSpeed, hhyp, ↓reduceDIte, h.resolve_right (b.ne_zero k)]
  have hhyper : IsStrictlyHyperbolicAt flux q :=
    ⟨hdiff, b, a, horder.injective, fun k ↦ ⟨Module.End.mem_eigenspace_iff.mpr (hb k), b.ne_zero k⟩⟩
  obtain ⟨hcanonical, c, hc⟩ := characteristicSpeed_spec hhyper
  exact c.eq_eigenvalues_of_strictMono b (fderiv ℝ flux q).toLinearMap hcanonical horder hc hb

/-- Canonical ordered speeds are `C¹` near each strictly hyperbolic state of a
`C²` flux. The regularity follows from local operator eigenbranches and uniqueness
of the increasing eigenvalue list. -/
theorem contDiffAt_characteristicSpeed {m : ℕ} {flux : ℝ^m → ℝ^m} {q₀ : ℝ^m}
    (hflux : ContDiff ℝ 2 flux) (hhyper : IsStrictlyHyperbolicAt flux q₀) (k : Fin m) :
    ContDiffAt ℝ 1 (characteristicSpeed flux k) q₀ := by
  have hD : ContDiff ℝ 1 (fderiv ℝ flux) := hflux.fderiv_right le_rfl
  exact ContinuousLinearMap.contDiffAt_of_eq_ordered_eigenvalues hD.contDiffAt
    hhyper.exists_ordered_eigenbasis (fun q k ↦ characteristicSpeed flux k q)
    (fun q b _ hord hb ↦ characteristicSpeed_eq_of_eigenbasis b hord hb) k

/-- Genuine nonlinearity of the `k`th ordered family, expressed without choosing
an eigenvector field. Every nonzero vector on that eigenline has nonzero
directional derivative of the characteristic speed. -/
def IsGenuinelyNonlinearFamily {m : ℕ} (flux : ℝ^m → ℝ^m) (k : Fin m) : Prop :=
  ∀ q, DifferentiableAt ℝ (characteristicSpeed flux k) q ∧
    ∀ v, Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap (characteristicSpeed flux k q) v →
      fderiv ℝ (characteristicSpeed flux k) q v ≠ 0

/-- Linear degeneracy of the `k`th ordered family, expressed on its eigenline
rather than through a globally selected eigenvector field. -/
def IsLinearlyDegenerateFamily {m : ℕ} (flux : ℝ^m → ℝ^m) (k : Fin m) : Prop :=
  ∀ q, DifferentiableAt ℝ (characteristicSpeed flux k) q ∧
    ∀ v, Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap (characteristicSpeed flux k q) v →
      fderiv ℝ (characteristicSpeed flux k) q v = 0

/-- A local ordered frame agrees with the canonical speeds throughout its
neighborhood. In particular all derivatives of the two speeds agree there. -/
theorem characteristicSpeed_eventuallyEq_of_eigenframe {m : ℕ} {flux : ℝ^m → ℝ^m}
    {q₀ : ℝ^m} {r : Fin m → ℝ^m → ℝ^m} {eig : Fin m → ℝ^m → ℝ}
    (hframe : ∀ᶠ q in 𝓝 q₀, StrictMono (fun k ↦ eig k q) ∧ (∀ k, fderiv ℝ flux q (r k q) =
      eig k q • r k q) ∧ ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∀ k, b k = r k q)
    (k : Fin m) :
    characteristicSpeed flux k =ᶠ[𝓝 q₀] eig k := by
  filter_upwards [hframe] with q hq
  obtain ⟨horder, heigen, b, hb⟩ := hq
  exact congrFun (characteristicSpeed_eq_of_eigenbasis b horder
    (fun j ↦ by rw [hb j]; exact heigen j)) k

/-- Genuine nonlinearity applies to every local ordered eigenfield, regardless
of its normalization. This transfers the family hypothesis to a frame
constructed by an implicit function theorem. -/
theorem IsGenuinelyNonlinearFamily.fderiv_ne_zero_of_eigenframe {m : ℕ} {flux : ℝ^m → ℝ^m}
    {k : Fin m} (hgn : IsGenuinelyNonlinearFamily flux k) {q₀ : ℝ^m}
    {r : Fin m → ℝ^m → ℝ^m} {eig : Fin m → ℝ^m → ℝ}
    (hframe : ∀ᶠ q in 𝓝 q₀, StrictMono (fun k ↦ eig k q) ∧ (∀ k, fderiv ℝ flux q (r k q) =
      eig k q • r k q) ∧ ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∀ k, b k = r k q) :
    fderiv ℝ (eig k) q₀ (r k q₀) ≠ 0 := by
  have heq := characteristicSpeed_eventuallyEq_of_eigenframe hframe k
  obtain ⟨_horder, heigen, b, hb⟩ := hframe.self_of_nhds
  rw [← heq.fderiv_eq]
  apply (hgn q₀).2
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · rw [heq.self_of_nhds]
    exact heigen k
  · rw [← hb k]
    exact b.ne_zero k

/-- Linear degeneracy transfers to a constructed local ordered eigenfield
on a whole state neighborhood, which is needed along its integral curves. -/
theorem IsLinearlyDegenerateFamily.eventually_fderiv_eq_zero_of_eigenframe {m : ℕ}
    {flux : ℝ^m → ℝ^m} {k : Fin m} (hld : IsLinearlyDegenerateFamily flux k)
    {q₀ : ℝ^m} {r : Fin m → ℝ^m → ℝ^m} {eig : Fin m → ℝ^m → ℝ}
    (hframe : ∀ᶠ q in 𝓝 q₀, StrictMono (fun k ↦ eig k q) ∧ (∀ k, fderiv ℝ flux q (r k q) =
      eig k q • r k q) ∧ ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∀ k, b k = r k q) :
    ∀ᶠ q in 𝓝 q₀, fderiv ℝ (eig k) q (r k q) = 0 := by
  have heq := characteristicSpeed_eventuallyEq_of_eigenframe hframe k
  filter_upwards [hframe, heq, heq.fderiv (𝕜 := ℝ)] with q hq heigEq hD
  obtain ⟨_horder, heigen, b, hb⟩ := hq
  rw [← hD]
  apply (hld q).2
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · rw [heigEq]
    exact heigen k
  · rw [← hb k]
    exact b.ne_zero k

/-- A local frame can be completed to pointwise characteristic fields of a
globally strictly hyperbolic flux. The completion agrees on a whole neighborhood with the given
vectors. -/
theorem exists_characteristicFields_of_eigenframe {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q) {q₀ : ℝ^m} {r : Fin m → ℝ^m → ℝ^m}
    {eig : Fin m → ℝ^m → ℝ}
    (hframe : ∀ᶠ q in 𝓝 q₀, StrictMono (fun k ↦ eig k q) ∧ (∀ k, fderiv ℝ flux q (r k q) =
      eig k q • r k q) ∧ ∃ b : Module.Basis (Fin m) ℝ (ℝ^m), ∀ k, b k = r k q) :
    ∃ fields : Fin m → CharacteristicField flux, (∀ k, (fields k).speed =
      characteristicSpeed flux k) ∧ (∀ᶠ q in 𝓝 q₀, ∀ k, (fields k).rightEigenvector q = r k q) := by
  classical
  let chosen (q : ℝ^m) := (characteristicSpeed_spec (hhyper q)).2.choose
  have hchosen (k : Fin m) (q : ℝ^m) : Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap
        (characteristicSpeed flux k q) (chosen q k) := ⟨Module.End.mem_eigenspace_iff.mpr
      ((characteristicSpeed_spec (hhyper q)).2.choose_spec k), (chosen q).ne_zero k⟩
  let fields (k : Fin m) : CharacteristicField flux :=
    { flux_differentiable := fun q ↦ (hhyper q).1
      speed := characteristicSpeed flux k
      rightEigenvector := fun q ↦ if Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap
          (characteristicSpeed flux k q) (r k q) then r k q else chosen q k
      eigenvector := fun q ↦ by
        split_ifs with h
        · exact h
        · exact hchosen k q }
  refine ⟨fields, fun _ ↦ rfl, ?_⟩
  filter_upwards [hframe] with q hq
  obtain ⟨horder, heigen, b, hb⟩ := hq
  have heq := characteristicSpeed_eq_of_eigenbasis b horder
    (fun k ↦ by rw [hb k]; exact heigen k)
  intro k
  have hv : Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap
      (characteristicSpeed flux k q) (r k q) := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · rw [congrFun heq k]
      exact heigen k
    · rw [← hb k]
      exact b.ne_zero k
  exact ite_eq_left hv

/-- The intrinsic genuine-nonlinearity condition is equivalent to the usual
condition for any chosen characteristic field with the canonical speed. -/
theorem isGenuinelyNonlinearFamily_iff {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q) (k : Fin m) (C : CharacteristicField flux)
    (hspeed : C.speed = characteristicSpeed flux k) :
    IsGenuinelyNonlinearFamily flux k ↔ C.IsGenuinelyNonlinear := by
  constructor
  · intro h q
    refine ⟨hspeed ▸ (h q).1, ?_⟩
    rw [hspeed]
    exact (h q).2 _ (hspeed ▸ C.eigenvector q)
  · intro h q
    refine ⟨hspeed ▸ (h q).1, fun v hv ↦ ?_⟩
    obtain ⟨horder, b, hb⟩ := characteristicSpeed_spec (hhyper q)
    have hC := C.eigenvector q
    rw [hspeed] at hC
    obtain ⟨c, hc, heq⟩ := b.exists_ne_zero_smul_eq_of_eigenvectors
      (fderiv ℝ flux q).toLinearMap (fun j ↦ characteristicSpeed flux j q)
      horder.injective hb hC.2 hv.2 hC.apply_eq_smul hv.apply_eq_smul
    rw [heq, map_smul, smul_eq_mul]
    exact mul_ne_zero hc (hspeed ▸ (h q).2)

/-- The intrinsic linear-degeneracy condition is equivalent to the usual
Riemann-invariant condition for any chosen canonical characteristic field. -/
theorem isLinearlyDegenerateFamily_iff {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q) (k : Fin m) (C : CharacteristicField flux)
    (hspeed : C.speed = characteristicSpeed flux k) :
    IsLinearlyDegenerateFamily flux k ↔ C.IsLinearlyDegenerate := by
  constructor
  · intro h
    refine ⟨fun q ↦ hspeed ▸ (h q).1, fun q ↦ ?_⟩
    rw [hspeed]
    exact (h q).2 _ (hspeed ▸ C.eigenvector q)
  · intro h q
    refine ⟨hspeed ▸ h.1 q, fun v hv ↦ ?_⟩
    obtain ⟨horder, b, hb⟩ := characteristicSpeed_spec (hhyper q)
    have hC := C.eigenvector q
    rw [hspeed] at hC
    obtain ⟨c, _hc, heq⟩ := b.exists_ne_zero_smul_eq_of_eigenvectors
      (fderiv ℝ flux q).toLinearMap (fun j ↦ characteristicSpeed flux j q)
      horder.injective hb hC.2 hv.2 hC.apply_eq_smul hv.apply_eq_smul
    rw [heq, map_smul, ← hspeed, h.2 q, smul_zero]

end PDE.Hyperbolic.ConservationLaw.System
