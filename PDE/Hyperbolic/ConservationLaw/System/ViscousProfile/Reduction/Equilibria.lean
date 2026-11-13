/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.VectorField

/-!
# Rankine–Hugoniot states on the constructed graph

The augmented coordinates encode the physical displacement and speed
displacement. The equilibrium equation in these coordinates is exactly
Rankine–Hugoniot. Equilibrium containment then puts both shock states on the
same graph and makes them zeros of its scalar reduced field.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis.Evolution

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Encode a physical state displacement and a speed displacement in the
augmented eigenvector coordinates. -/
def augmentedProfileCoordinates (e : E ≃L[ℝ] (ι → ℝ)) :
    (E × ℝ) →L[ℝ] (Option ι → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ match i with
    | none => ContinuousLinearMap.snd ℝ E ℝ
    | some j => (ContinuousLinearMap.proj j).comp
        (e.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ E ℝ))

omit [Fintype ι] in
/-- The extra coordinate is exactly the speed displacement. -/
@[simp] theorem augmentedProfileCoordinates_none
    (e : E ≃L[ℝ] (ι → ℝ)) (z : E × ℝ) :
    augmentedProfileCoordinates e z none = z.2 := rfl

omit [Fintype ι] in
/-- State coordinates are given by the fixed linear equivalence. -/
@[simp] theorem augmentedProfileCoordinates_some
    (e : E ≃L[ℝ] (ι → ℝ)) (z : E × ℝ) (i : ι) :
    augmentedProfileCoordinates e z (some i) = e z.1 i := rfl

omit [Fintype ι] in
/-- Recovering the state from its augmented coordinates gives the original
physical displacement. -/
@[simp] theorem profileStateProjection_augmentedProfileCoordinates
    (e : E ≃L[ℝ] (ι → ℝ)) (z : E × ℝ) :
    profileStateProjection e (augmentedProfileCoordinates e z) = z.1 :=
  e.symm_apply_apply z.1

omit [Fintype ι] in
/-- The coordinate change carries the integrated physical vector field to the
augmented diagonal equation. -/
theorem augmentedProfileCoordinates_integrated_field [Finite ι]
    (b : Module.Basis ι ℝ E) (flux : E → E) (q : E)
    (eig : ι → ℝ) (k : ι)
    (hdiag : ∀ i, fderiv ℝ flux q (b i) = eig i • b i)
    (u : E) (μ : ℝ) :
    let X := augmentedProfileCoordinates b.equivFunL (u - q, μ)
    augmentedProfileCoordinates b.equivFunL
      (flux u - flux q - (eig k + μ) • (u - q), 0) =
        fun i ↦ augmentedProfileRate eig k i * X i +
          augmentedProfileRemainder flux q b.equivFunL X i := by
  let := Fintype.ofFinite ι
  let X := augmentedProfileCoordinates b.equivFunL (u - q, μ)
  change augmentedProfileCoordinates b.equivFunL _ =
    fun i ↦ augmentedProfileRate eig k i * X i +
      augmentedProfileRemainder flux q b.equivFunL X i
  ext i
  cases i with
  | none => simp [augmentedProfileRate, augmentedProfileRemainder]
  | some i =>
    have hdiagonal (y : ι → ℝ) (j : ι) :
        b.equivFunL (fderiv ℝ flux q (b.equivFunL.symm y)) j = eig j * y j := by
      have h := b.equivFun_apply_of_apply_basis_eq_smul
        (fderiv ℝ flux q).toLinearMap eig hdiag (b.equivFunL.symm y) j
      change b.equivFunL (fderiv ℝ flux q (b.equivFunL.symm y)) j =
        eig j * b.equivFunL (b.equivFunL.symm y) j at h
      rwa [b.equivFunL.apply_symm_apply] at h
    have heq := augmentedProfileRemainder_add_linear flux q b.equivFunL eig
      hdiagonal (eig k) X i
    simpa only [X, augmentedProfileRate, augmentedProfileCoordinates_some,
      augmentedProfileCoordinates_none, b.equivFunL.symm_apply_apply,
      add_sub_cancel] using heq.symm

omit [Fintype ι] in
/-- A physical Rankine–Hugoniot state is an equilibrium of the augmented
profile equation, with the shifted speed. -/
theorem augmentedProfile_equilibrium_of_rankine_hugoniot [Finite ι]
    (b : Module.Basis ι ℝ E) (flux : E → E) (q : E)
    (eig : ι → ℝ) (k : ι)
    (hdiag : ∀ i, fderiv ℝ flux q (b i) = eig i • b i)
    (u : E) (μ : ℝ)
    (hRH : flux u - flux q = (eig k + μ) • (u - q)) :
    let X := augmentedProfileCoordinates b.equivFunL (u - q, μ)
    ∀ i, augmentedProfileRate eig k i * X i +
      augmentedProfileRemainder flux q b.equivFunL X i = 0 := by
  let := Fintype.ofFinite ι
  have heq := augmentedProfileCoordinates_integrated_field b flux q eig k hdiag u μ
  rw [hRH, sub_self] at heq
  change _ = _ at heq
  intro X i
  simpa only [← Prod.zero_eq_mk, map_zero, Pi.zero_apply] using! (congrFun heq i).symm

omit [Fintype ι] in
/-- Equilibrium containment identifies the physical endpoint on the graph and
proves that its amplitude is a zero of the reduced field. -/
theorem profileGraph_eq_and_reducedProfileField_eq_zero_of_equilibrium [Finite ι]
    (b : Module.Basis ι ℝ E) (flux : E → E) (q : E)
    (eig : ι → ℝ) (heig : Function.Injective eig) (k : ι)
    {φ : (Option ι → ℝ) → (Option ι → ℝ)}
    (hproject : ∀ ξ, φ (diagonalCenterProjection (augmentedProfileRate eig k) ξ) = φ ξ)
    (u : E) (μ : ℝ)
    (hcontain : let X := augmentedProfileCoordinates b.equivFunL (u - q, μ); X = φ X)
    (hequilibrium :
      let X := augmentedProfileCoordinates b.equivFunL (u - q, μ)
      ∀ i, augmentedProfileRate eig k i * X i +
        augmentedProfileRemainder flux q b.equivFunL X i = 0) :
    profileGraph q b.equivFunL k φ (b.equivFun (u - q) k, μ) = u ∧
      reducedProfileField flux q b.equivFunL k φ (b.equivFun (u - q) k, μ) = 0 := by
  let := Fintype.ofFinite ι
  let X := augmentedProfileCoordinates b.equivFunL (u - q, μ)
  have hφ : φ (profileCenterCoordinates k (b.equivFun (u - q) k, μ)) = X := by
    have hp := hproject X
    rw [diagonalCenterProjection_augmentedProfileRate eig heig k] at hp
    exact hp.trans hcontain.symm
  constructor
  · simp only [profileGraph, hφ, X, profileStateProjection_augmentedProfileCoordinates,
      add_sub_cancel]
  · have hk := hequilibrium (some k)
    simpa only [reducedProfileField, hφ, augmentedProfileRate,
      sub_self, zero_mul, zero_add] using hk

end PDE.Hyperbolic.ConservationLaw.System
