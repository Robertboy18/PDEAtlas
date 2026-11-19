/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered

/-!
# Normalization by characteristic speed

Dividing an eigenvector by the directional derivative of its characteristic
speed removes its arbitrary scale. For a simple genuinely nonlinear eigenline,
the resulting vector is continuous even when the selected eigenvectors are not.
This is the regularity needed when an integral curve is parametrized by speed.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Set
open scoped ContDiff Topology

/-- The eigenvector normalized to have characteristic-speed derivative one. -/
def CharacteristicField.speedNormalizedField {m : ℕ} {flux : ℝ^m → ℝ^m}
    (C : CharacteristicField flux) (q : ℝ^m) : ℝ^m :=
  (fderiv ℝ C.speed q (C.rightEigenvector q))⁻¹ • C.rightEigenvector q

/-- Normalization is independent of the nonzero vector chosen on the simple
eigenline. -/
theorem CharacteristicField.speedNormalizedField_eq_of_eigenvector {m : ℕ} {flux : ℝ^m → ℝ^m}
    {k : Fin m} (C : CharacteristicField flux) (hspeed : C.speed = characteristicSpeed flux k)
    {q : ℝ^m} (hhyper : IsStrictlyHyperbolicAt flux q) {v : ℝ^m}
    (hv :
      Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap (characteristicSpeed flux k q) v) :
    C.speedNormalizedField q = (fderiv ℝ C.speed q v)⁻¹ • v := by
  obtain ⟨horder, b, hb⟩ := characteristicSpeed_spec hhyper
  have hC := C.eigenvector q
  rw [hspeed] at hC
  exact b.inv_apply_smul_eq_of_eigenvectors (fderiv ℝ flux q).toLinearMap
    (fun j ↦ characteristicSpeed flux j q) horder.injective hb
    (fderiv ℝ C.speed q).toLinearMap hC.2 hv.2 hC.apply_eq_smul hv.apply_eq_smul

/-- Genuine nonlinearity gives unit speed derivative in the normalized direction. -/
theorem CharacteristicField.fderiv_speedNormalizedField {m : ℕ} {flux : ℝ^m → ℝ^m}
    (C : CharacteristicField flux) {q : ℝ^m} (hgn : C.IsGenuinelyNonlinearAt q) :
    fderiv ℝ C.speed q (C.speedNormalizedField q) = 1 := by
  simp only [speedNormalizedField, map_smul, smul_eq_mul]
  exact inv_mul_cancel₀ hgn.2

/-- Normalization preserves the characteristic eigenvector equation. -/
theorem CharacteristicField.fderiv_flux_speedNormalizedField
    {m : ℕ} {flux : ℝ^m → ℝ^m} (C : CharacteristicField flux) (q : ℝ^m) :
    fderiv ℝ flux q (C.speedNormalizedField q) = C.speed q • C.speedNormalizedField q := by
  have heigen : fderiv ℝ flux q (C.rightEigenvector q) =
      C.speed q • C.rightEigenvector q := (C.eigenvector q).apply_eq_smul
  simp only [speedNormalizedField, map_smul, heigen]
  exact smul_comm (fderiv ℝ C.speed q (C.rightEigenvector q))⁻¹ (C.speed q) (C.rightEigenvector q)

/-- The normalized direction is continuous for a `C²` strictly hyperbolic flux
and a genuinely nonlinear family. The original characteristic field is allowed
to be discontinuous: locally the quotient agrees with a smooth eigenframe. -/
theorem CharacteristicField.continuous_speedNormalizedField {m : ℕ} {flux : ℝ^m → ℝ^m} {k : Fin m}
    (hflux : ContDiff ℝ 2 flux) (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hgn : IsGenuinelyNonlinearFamily flux k) (C : CharacteristicField flux)
    (hspeed : C.speed = characteristicSpeed flux k) :
    Continuous C.speedNormalizedField := by
  refine continuous_iff_continuousAt.mpr fun q₀ ↦ ?_
  obtain ⟨horder, b, hb⟩ := characteristicSpeed_spec (hhyper q₀)
  obtain ⟨ψ, _hbase, W, hW, hAW, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame
      b (fderiv ℝ flux q₀) (fun j ↦ characteristicSpeed flux j q₀) hb horder
  let r : ℝ^m → ℝ^m := fun q ↦ (ψ k (fderiv ℝ flux q)).1
  have hD : ContDiff ℝ 1 (fderiv ℝ flux) := hflux.fderiv_right le_rfl
  have hr : ContinuousAt r q₀ :=
    ((((hframe _ hAW).2.1 k).1.continuousAt.comp hD.continuous.continuousAt).fst)
  have hnear : ∀ᶠ q in 𝓝 q₀, fderiv ℝ flux q ∈ W := hD.continuous.continuousAt (hW.mem_nhds hAW)
  have heigen : ∀ᶠ q in 𝓝 q₀, Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap
        (characteristicSpeed flux k q) (r q) := by
    filter_upwards [hnear] with q hq
    obtain ⟨hord, hvec, c, hc⟩ := hframe _ hq
    have hcanonical := congrFun (characteristicSpeed_eq_of_eigenbasis c hord
      (fun j ↦ by rw [hc j]; exact (hvec j).2.1.apply_eq_smul)) k
    exact hcanonical.symm ▸ (hvec k).2.1
  have hspeedC1 : ContDiffAt ℝ 1 C.speed q₀ := by
    rw [hspeed]
    exact contDiffAt_characteristicSpeed hflux (hhyper q₀) k
  have hdenom : ContinuousAt (fun q ↦ fderiv ℝ C.speed q (r q)) q₀ :=
    (hspeedC1.continuousAt_fderiv one_ne_zero).clm_apply hr
  have hne : fderiv ℝ C.speed q₀ (r q₀) ≠ 0 := by
    rw [hspeed]
    exact (hgn q₀).2 _ heigen.self_of_nhds
  apply ((hdenom.inv₀ hne).smul hr).congr_of_eventuallyEq
  filter_upwards [heigen] with q hq
  exact C.speedNormalizedField_eq_of_eigenvector hspeed (hhyper q) hq

end PDE.Hyperbolic.ConservationLaw.System
