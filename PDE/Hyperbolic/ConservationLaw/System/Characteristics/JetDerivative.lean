/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered
public import PDE.Hyperbolic.ConservationLaw.System.Corrections.Neutral.OpenJets

import PDE.Analysis.Spectral.FiniteDimensional.EigenvalueDerivative

/-!
# Hessian contractions and the canonical characteristic speeds

The jet condition uses the dual coordinates of an eigenbasis. For a `C²` flux,
these contractions are exactly the directional derivatives of its ordered
characteristic speeds. The local spectral frame supplies the differentiable eigenvector needed for
this identity.

The resulting equivalence connects the operator-level perturbation criterion to
the characteristic-family definition of genuine nonlinearity.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- In any ordered eigenbasis, the derivative of the canonical characteristic
speed is the corresponding dual coordinate of the flux Hessian. The direction
`v` is arbitrary; taking `v = b k` gives the genuine-nonlinearity contraction. -/
theorem fderiv_characteristicSpeed_apply_eq {m : ℕ} {flux : ℝ^m → ℝ^m} {q : ℝ^m}
    (hflux : ContDiff ℝ 2 flux) (b : Module.Basis (Fin m) ℝ (ℝ^m)) (eig : Fin m → ℝ)
    (horder : StrictMono eig) (hdiag : ∀ k, fderiv ℝ flux q (b k) = eig k • b k) (k : Fin m)
    (v : ℝ^m) :
    fderiv ℝ (characteristicSpeed flux k) q v = b.repr (fderiv ℝ (fderiv ℝ flux) q v (b k)) k := by
  have hdiff : Differentiable ℝ flux := hflux.differentiable (by norm_num)
  have hhyper : IsStrictlyHyperbolicAt flux q := ⟨hdiff q, b, eig, horder.injective, fun j ↦
      ⟨Module.End.mem_eigenspace_iff.mpr (hdiag j), b.ne_zero j⟩⟩
  have hcanonical := characteristicSpeed_eq_of_eigenbasis b horder hdiag
  obtain ⟨ψ, hbase, U, hU, hqU, hframe⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_local_spectral_frame
      b (fderiv ℝ flux q) eig hdiag horder
  let r : ℝ^m → ℝ^m := fun y ↦ (ψ k (fderiv ℝ flux y)).1
  have hD : ContDiff ℝ 1 (fderiv ℝ flux) := hflux.fderiv_right le_rfl
  have hr : DifferentiableAt ℝ r q :=
    (((hframe _ hqU).2.1 k).1.differentiableAt (by simp)).fst.comp q
      (hD.differentiable one_ne_zero q)
  have hrq : r q = b k := congrArg Prod.fst (hbase k)
  have hnear : ∀ᶠ y in 𝓝 q, fderiv ℝ flux y ∈ U := hD.continuous.continuousAt (hU.mem_nhds hqU)
  have hraw : ∀ᶠ y in 𝓝 q, fderiv ℝ flux y (r y) =
      characteristicSpeed flux k y • r y := by
    filter_upwards [hnear] with y hy
    obtain ⟨hord, heigen, c, hc⟩ := hframe _ hy
    have heq := characteristicSpeed_eq_of_eigenbasis c hord
      (fun j ↦ by rw [hc j]; exact (heigen j).2.1.apply_eq_smul)
    rw [congrFun heq k]
    exact (heigen k).2.1.apply_eq_smul
  exact b.fderiv_eigenvalue_apply eig k hdiag (hD.differentiable one_ne_zero q) hr
    ((contDiffAt_characteristicSpeed hflux hhyper k).differentiableAt one_ne_zero)
    hrq (congrFun hcanonical k) hraw v

/-- For derivatives of a `C²` flux, the open jet condition is equivalent
to strict hyperbolicity and nonzero speed derivatives on every characteristic
eigenline at the given state. The statement permits dimension zero. -/
theorem hasOrderedGenuinelyNonlinearEigenbasis_fderiv_iff
    {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 2 flux) (q : ℝ^m) :
    ContinuousLinearMap.HasOrderedGenuinelyNonlinearEigenbasis (Fin m)
        (fderiv ℝ flux q) (fderiv ℝ (fderiv ℝ flux) q) ↔
      IsStrictlyHyperbolicAt flux q ∧
        ∀ k : Fin m, DifferentiableAt ℝ (characteristicSpeed flux k) q ∧
          ∀ v, Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap
            (characteristicSpeed flux k q) v →
            fderiv ℝ (characteristicSpeed flux k) q v ≠ 0 := by
  constructor
  · rintro ⟨b, eig, horder, hdiag, hgn⟩
    have hhyper : IsStrictlyHyperbolicAt flux q :=
      ⟨hflux.differentiable (by norm_num) q, b, eig, horder.injective, fun k ↦
        ⟨Module.End.mem_eigenspace_iff.mpr (hdiag k), b.ne_zero k⟩⟩
    have hcanonical := characteristicSpeed_eq_of_eigenbasis b horder hdiag
    refine ⟨hhyper, fun k ↦
      ⟨(contDiffAt_characteristicSpeed hflux hhyper k).differentiableAt one_ne_zero, ?_⟩⟩
    intro v hv
    have hbase : fderiv ℝ (characteristicSpeed flux k) q (b k) ≠ 0 := by
      rw [fderiv_characteristicSpeed_apply_eq hflux b eig horder hdiag k (b k)]
      exact hgn k
    have hv' : fderiv ℝ flux q v = eig k • v := by
      have heq := hv.apply_eq_smul
      change fderiv ℝ flux q v = characteristicSpeed flux k q • v at heq
      rwa [congrFun hcanonical k] at heq
    obtain ⟨a, ha, heq⟩ := b.exists_ne_zero_smul_eq_of_eigenvectors
      (fderiv ℝ flux q).toLinearMap eig horder.injective hdiag (b.ne_zero k) hv.2 (hdiag k) hv'
    rw [heq, map_smul, smul_eq_mul]
    exact mul_ne_zero ha hbase
  · rintro ⟨hhyper, hgn⟩
    obtain ⟨horder, b, hdiag⟩ := characteristicSpeed_spec hhyper
    refine ⟨b, fun k ↦ characteristicSpeed flux k q, horder, hdiag, fun k ↦ ?_⟩
    rw [← fderiv_characteristicSpeed_apply_eq hflux b
      (fun j ↦ characteristicSpeed flux j q) horder hdiag k (b k)]
    exact (hgn k).2 (b k) ⟨Module.End.mem_eigenspace_iff.mpr (hdiag k), b.ne_zero k⟩

/-- Pointwise membership of the Jacobian and Hessian in the open jet set
is exactly global strict hyperbolicity together with genuine nonlinearity of
every canonical characteristic family. -/
theorem forall_hasOrderedGenuinelyNonlinearEigenbasis_fderiv_iff
    {m : ℕ} {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ 2 flux) :
    (∀ q, ContinuousLinearMap.HasOrderedGenuinelyNonlinearEigenbasis (Fin m) (fderiv ℝ flux q)
      (fderiv ℝ (fderiv ℝ flux) q)) ↔ (∀ q, IsStrictlyHyperbolicAt flux q) ∧ ∀ k,
      IsGenuinelyNonlinearFamily flux k := by
  constructor
  · intro h
    have hp (q : ℝ^m) := (hasOrderedGenuinelyNonlinearEigenbasis_fderiv_iff hflux q).mp (h q)
    exact ⟨fun q ↦ (hp q).1, fun k q ↦ (hp q).2 k⟩
  · rintro ⟨hhyper, hgn⟩ q
    exact (hasOrderedGenuinelyNonlinearEigenbasis_fderiv_iff hflux q).mpr
      ⟨hhyper q, fun k ↦ hgn k q⟩

end PDE.Hyperbolic.ConservationLaw.System
