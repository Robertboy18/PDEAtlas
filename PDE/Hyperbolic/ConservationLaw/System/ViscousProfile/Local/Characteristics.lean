/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Local.Family
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered

/-!
# Profile neighborhoods for the canonical characteristic families

The local normalized eigenbranches of the Jacobian match the given
ordered eigenbasis at the left state. This makes the profile amplitude the
same coordinate used by the shock-curve classification. Genuine
nonlinearity supplies the nonzero curvature in this normalization.
-/

@[expose] public noncomputable section

open Filter Metric
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Construct the profile neighborhoods in the coordinates of any canonical
eigenbasis. The genuine-nonlinearity hypothesis supplies the curvature;
no eigenvector field or invariant graph is prescribed. -/
theorem exists_characteristic_profile_radius {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ ∞ flux)
    (q : ℝ^m) (hhyper : IsStrictlyHyperbolicAt flux q) (b : Module.Basis (Fin m) ℝ (ℝ^m))
    (k : Fin m) (hdiag : ∀ i, fderiv ℝ flux q (b i) = characteristicSpeed flux i q • b i)
    (hgn : IsGenuinelyNonlinearFamily flux k) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ δ η : ℝ, 0 < δ ∧ δ < ρ ∧ 0 < η ∧
      ∀ uR ∈ ball q δ, uR ≠ q → ∀ μ ∈ ball 0 η,
        RankineHugoniot flux q uR (characteristicSpeed flux k q + μ) →
        ((∃ v : ℝ → ℝ^m, IsViscousProfile flux q uR (characteristicSpeed flux k q + μ) v ∧ ∀ t,
        v t ∈ ball q ρ) ↔ fderiv ℝ (characteristicSpeed flux k) q (b k) * b.equivFunL (uR - q) k <
        0) := by
  have horder := (characteristicSpeed_spec hhyper).1
  obtain ⟨ψ, hbase, U, hU, hqU, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame b
      (fderiv ℝ flux q) (fun i ↦ characteristicSpeed flux i q) hdiag horder
  let r := fun y ↦ (ψ k (fderiv ℝ flux y)).1
  have hD : ContDiff ℝ ∞ (fderiv ℝ flux) := hflux.fderiv_right (by simp)
  have hr : DifferentiableAt ℝ r q :=
    (((hframe _ hqU).2.1 k).1.differentiableAt (by simp)).fst.comp q
      (hD.differentiable (by simp) q)
  have hrq : r q = b k := congrArg Prod.fst (hbase k)
  have hnear : ∀ᶠ y in 𝓝 q, fderiv ℝ flux y ∈ U := hD.continuous.continuousAt (hU.mem_nhds hqU)
  have hraw : ∀ᶠ y in 𝓝 q, fderiv ℝ flux y (r y) =
      characteristicSpeed flux k y • r y := by
    filter_upwards [hnear] with y hy
    obtain ⟨hord, heigen, c, hc⟩ := hframe _ hy
    have hcanonical := characteristicSpeed_eq_of_eigenbasis c hord
      (fun i ↦ by rw [hc i]; exact (heigen i).2.1.apply_eq_smul)
    rw [congrFun hcanonical k]
    exact (heigen k).2.1.apply_eq_smul
  exact exists_profile_radius_iff_amplitude_sign b hflux q
    (fun i ↦ characteristicSpeed flux i q) horder.injective k hdiag hr (hgn q).1 hrq rfl hraw
    ((hgn q).2 (b k) ⟨Module.End.mem_eigenspace_iff.mpr (hdiag k), b.ne_zero k⟩)

end PDE.Hyperbolic.ConservationLaw.System
