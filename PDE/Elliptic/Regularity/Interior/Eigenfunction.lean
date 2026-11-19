/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.LocalHigherOrder

/-!
# Interior Sobolev bootstrap for weak eigenfunctions

The forcing in `−div(a ∇u) = λu` gains regularity with the solution. On each compact
subset, the preceding local Sobolev representative supplies the next forcing bundle.
The finite-order interior theorem then gives another derivative on a smaller neighborhood.
No boundary condition, domain boundedness, coefficient symmetry, or sign of `λ` is required.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

/-- A local weak eigenfunction has `m + 2` square-integrable derivatives near every
compact subset when the coefficients have `m + 1` bounded weak derivatives. The globally
Lipschitz representatives and global ellipticity are the hypotheses of the
interior `H²` theorem; no regularity of the forcing is assumed independently. -/
theorem exists_eigenfunction_interiorRegularity_open_neighborhood_of_compact
    (m : ℕ) {Omega : Set (ℝ^n)} (hOpen : IsOpen Omega)
    (A0 : Fin n → Fin n → DerivLp n ∞ univ)
    (a : Fin n → Fin n → ℝ^n → ℝ) (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j, (A0 i j : ℝ^n → ℝ) =ᵐ[volume] a i j)
    {alpha : ℝ} (hElliptic : AEUniformlyElliptic (n := n) (Ω := univ) A0 alpha)
    (A : Fin n → Fin n → W^{m + 1,∞}(Omega))
    (hAbase : ∀ i j, (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Omega]
        (restrictDerivLp (n := n) (p := ∞) (subset_univ Omega) (A0 i j) : ℝ^n → ℝ))
    (lambda : ℝ) (u : H¹(Omega))
    (hu : IsInteriorWeakDivergenceSolution
      (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Omega) (A0 i j))
      (lambda • wkpBaseCoordinateCLM u) u)
    (K : Set (ℝ^n)) (hKcompact : IsCompact K) (hKOmega : K ⊆ Omega) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Omega ∧
      ∃ W : W^{m + 2,2}(V),
        (wkpBaseCoordinateCLM W : ℝ^n → ℝ)
          =ᵐ[domainMeasure n V] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) := by
  induction m generalizing Omega u K with
  | zero =>
      let F : W^{0,2}(Omega) :=
        lambda • lowerOrderCLM (n := n) (p := 2) (Ω := Omega)
          (by omega : 0 ≤ 1) u
      have hF : wkpBaseCoordinateCLM F = lambda • wkpBaseCoordinateCLM u := by
        simp [F, wkpBaseCoordinateCLM, wkpCoordinateCLM]
      have hcoeff : (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Omega) (A0 i j)) =
          fun i j ↦ wkpBaseCoordinateCLM (A i j) := funext₂ fun i j ↦ Lp.ext (hAbase i j).symm
      exact exists_local_higherOrder_open_neighborhood_of_compact 0 hOpen A0 a C ha hrep hElliptic
        A F hAbase u (by rwa [hF, ← hcoeff]) K hKcompact hKOmega
  | succ m ih =>
      let Aprev : Fin n → Fin n → W^{m + 1,∞}(Omega) :=
        fun i j ↦ lowerOrderCLM (n := n) (p := ∞) (Ω := Omega)
          (by omega : m + 1 ≤ (m + 1) + 1) (A i j)
      have hAprev (i j : Fin n) : (wkpBaseCoordinateCLM (Aprev i j) : ℝ^n → ℝ)
          =ᵐ[domainMeasure n Omega]
            (restrictDerivLp (n := n) (p := ∞) (subset_univ Omega) (A0 i j) : ℝ^n → ℝ) := by
        simpa [Aprev, wkpBaseCoordinateCLM, wkpCoordinateCLM] using hAbase i j
      obtain ⟨N, hNopen, hKN, hNOmega, U, hU⟩ :=
        ih hOpen Aprev hAprev u hu K hKcompact hKOmega
      let uN : H¹(N) :=
        restrictCLM (n := n) (k := 1) (p := 2) hNopen.measurableSet hNOmega u
      let AN : Fin n → Fin n → W^{(m + 1) + 1,∞}(N) :=
        fun i j ↦ restrictCLM (n := n) (k := (m + 1) + 1) (p := ∞)
          hNopen.measurableSet hNOmega (A i j)
      have hANeq (i j : Fin n) : wkpBaseCoordinateCLM (AN i j) =
          restrictDerivLp (n := n) (p := ∞) (subset_univ N) (A0 i j) := by
        change restrictDerivLp (n := n) (p := ∞) hNOmega (wkpBaseCoordinateCLM (A i j)) = _
        rw [Lp.ext (hAbase i j)]
        exact DFunLike.congr_fun (restrictDerivLp_comp hNOmega (subset_univ Omega)) _
      have hAN (i j : Fin n) : (wkpBaseCoordinateCLM (AN i j) : ℝ^n → ℝ)
          =ᵐ[domainMeasure n N]
            (restrictDerivLp (n := n) (p := ∞) (subset_univ N) (A0 i j) : ℝ^n → ℝ) := by
        rw [hANeq]
      have hrestrictbase : (wkpBaseCoordinateCLM uN : ℝ^n → ℝ)
          =ᵐ[domainMeasure n N] (wkpBaseCoordinateCLM u : ℝ^n → ℝ) :=
        restrictCLM_apply_ae hNopen.measurableSet hNOmega u (baseIndex n 1)
      let F : W^{m + 1,2}(N) :=
        lambda • lowerOrderCLM (n := n) (p := 2) (Ω := N)
          (by omega : m + 1 ≤ m + 2) U
      have hF : wkpBaseCoordinateCLM F = lambda • wkpBaseCoordinateCLM uN := by
        simp only [F, map_smul]
        exact congrArg (lambda • ·) (Lp.ext (hU.trans hrestrictbase.symm))
      have hcoeff : (fun i j ↦ restrictDerivLp (n := n) (p := ∞) hNOmega
          (restrictDerivLp (n := n) (p := ∞) (subset_univ Omega) (A0 i j))) =
          fun i j ↦ wkpBaseCoordinateCLM (AN i j) := funext₂ fun i j ↦ by
        rw [hANeq]
        exact DFunLike.congr_fun (restrictDerivLp_comp hNOmega (subset_univ Omega)) _
      have hforce : restrictDerivLp (n := n) (p := 2) hNOmega
          (lambda • wkpBaseCoordinateCLM u) = wkpBaseCoordinateCLM F := by
        rw [map_smul, hF]
        congr 1
      have huN : IsInteriorWeakDivergenceSolution
          (fun i j ↦ wkpBaseCoordinateCLM (AN i j)) (wkpBaseCoordinateCLM F) uN := by
        have h := hu.restrict hNopen hNOmega
        rwa [hcoeff, hforce] at h
      obtain ⟨V, hVopen, hKV, hVN, W, hW⟩ :=
        exists_local_higherOrder_open_neighborhood_of_compact
          (m + 1) hNopen A0 a C ha hrep hElliptic AN F hAN uN huN K hKcompact hKN
      exact ⟨V, hVopen, hKV, hVN.trans hNOmega, W,
        hW.trans (hrestrictbase.filter_mono (ae_mono (domainMeasure_le hVN)))⟩

end SobolevSpace.GraphSpace.BoundaryRegularity
