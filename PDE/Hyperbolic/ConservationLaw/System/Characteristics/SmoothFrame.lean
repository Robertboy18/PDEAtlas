/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered
public import PDE.Analysis.Spectral.FiniteDimensional.UnitFrame

/-!
# Smooth global characteristic fields

The global unit-frame construction applies to the Jacobian of a smooth
strictly hyperbolic flux. Its ordered speeds agree with the totalized
`characteristicSpeed`. This is an existence result for smooth choices; the general
`CharacteristicField` structure carries no regularity.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System

/-- On the hyperbolic region, the characteristic speeds are the
canonical ordered eigenvalues of the Jacobian. -/
theorem characteristicSpeed_eq_orderedEigenvalue
    {m : ℕ} {flux : ℝ^m → ℝ^m} {z : ℝ^m} (h : IsStrictlyHyperbolicAt flux z) :
    (fun k ↦ characteristicSpeed flux k z) =
      ContinuousLinearMap.orderedEigenvalue m (fderiv ℝ flux z) := by
  obtain ⟨ha, b, hb⟩ := characteristicSpeed_spec h
  exact (ContinuousLinearMap.orderedEigenvalue_eq_of_eigenbasis b ha hb).symm

/-- A globally smooth strictly hyperbolic flux has smooth unit characteristic
fields for all its ordered families, forming a basis at every state. -/
theorem exists_smooth_unit_characteristicFields {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ ∞ flux) (hhyper : ∀ z, IsStrictlyHyperbolicAt flux z) :
    ∃ C : Fin m → CharacteristicField flux,
      (∀ k, (C k).speed = characteristicSpeed flux k ∧
        ContDiff ℝ ∞ (C k).speed ∧ ContDiff ℝ ∞ (C k).rightEigenvector ∧
        ∀ z, ‖(C k).rightEigenvector z‖ = 1) ∧
      ∀ z, ∃ b : Module.Basis (Fin m) ℝ (ℝ^m),
        ∀ k, b k = (C k).rightEigenvector z := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ flux) := hflux.fderiv_right (by simp)
  obtain ⟨r, _, hreg, heigen, hb, _⟩ := ContinuousLinearMap.exists_contDiff_unit_spectral_frame hD
      (fun z ↦ (hhyper z).exists_ordered_eigenbasis)
  have hs (k : Fin m) : characteristicSpeed flux k =
        fun z ↦ ContinuousLinearMap.orderedEigenvalue m (fderiv ℝ flux z) k := by
    funext z
    exact congrFun (characteristicSpeed_eq_orderedEigenvalue (hhyper z)) k
  let C : Fin m → CharacteristicField flux := fun k ↦
    { flux_differentiable := hflux.differentiable (by simp)
      speed := characteristicSpeed flux k
      rightEigenvector := r k
      eigenvector := fun z ↦ ⟨Module.End.mem_eigenspace_iff.mpr (by
        rw [hs k]; exact (heigen z k).1), by
          intro hz
          have hn := (heigen z k).2.2.1
          simp [hz] at hn⟩ }
  refine ⟨C, ?_, ?_⟩
  · intro k
    refine ⟨rfl, ?_, (hreg k).2.1, fun z ↦ (heigen z k).2.2.1⟩
    change ContDiff ℝ ∞ (characteristicSpeed flux k)
    rw [hs k]
    exact (hreg k).1
  · intro z
    obtain ⟨br, _, hbr, _⟩ := hb z
    exact ⟨br, hbr⟩

end PDE.Hyperbolic.ConservationLaw.System
