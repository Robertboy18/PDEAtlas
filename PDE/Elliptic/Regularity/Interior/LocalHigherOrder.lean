/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.CoefficientLocalization
import PDE.Elliptic.Regularity.Interior.H2Compactness
import PDE.Elliptic.Regularity.Interior.HigherOrderPartitionPiece
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep
public import PDE.Spaces.Sobolev.Calculus.Product.WeakLeibniz

/-!
# Finite-order local elliptic regularity

Every compact subset of the domain has an open neighbourhood on which a weak solution of the
principal divergence-form equation has a `W^{m+2,2}` representative, when the coefficients belong to
`W^{m+1,∞}` and the forcing belongs to `W^{m,2}`
(`exists_local_higherOrder_open_neighborhood_of_compact`). No boundary condition is imposed on the
solution. This is the compact-set form of Evans's §6.3.1, Theorem 2 (Higher interior regularity),
for an operator without lower-order terms and with Sobolev coefficients in place of `C^{m+1}` ones.

The proof starts from the general local `H²` theorem and proceeds by nested cutoffs. At each
successor step it restricts the weak equation to the neighbourhood produced at the preceding order,
applies the compact-local commutator theorem there, and finally restricts to the open set where the
new cutoff is one.

`exists_local_higherOrder_of_aeUniformlyElliptic` assumes only the Sobolev coefficient bundle and
ellipticity on the domain. A cutoff blend and the bounded weak-gradient theorem construct the global
coefficients and their Lipschitz representatives needed by the auxiliary theorem.
`exists_local_higherOrder_of_isLocallyWkpOn` requires the higher coefficient and forcing regularity
only on relatively compact open subdomains.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 2 (Higher interior regularity), pp. 332-333.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open CompactSupportLocalization
open scoped ENNReal

variable {n : ℕ}

/--
Finite-order interior regularity for a general weak divergence-form solution.

The coefficient matrix is represented globally by Lipschitz functions for the
`H²` base case and by one coherent `W^{m+1,∞}(Omega)` bundle for the
higher-order bootstrap. The forcing is represented by one `W^{m,2}(Omega)`
bundle.
-/
theorem exists_local_higherOrder_open_neighborhood_of_compact
    (m : ℕ) {Omega : Set (ℝ^n)}
    (hOpen : IsOpen Omega)
    (A0 : Fin n → Fin n → DerivLp n ∞ Set.univ)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hrep : ∀ i j,
      ((A0 i j : DerivLp n ∞ Set.univ) : ℝ^n → ℝ)
        =ᵐ[volume] a i j)
    {alpha : ℝ}
    (hElliptic :
      AEUniformlyElliptic (n := n) (Ω := Set.univ) A0 alpha)
    (A : Fin n → Fin n → W^{m + 1,∞}(Omega))
    (F : W^{m,2}(Omega))
    (hAbase : ∀ i j,
      (wkpBaseCoordinateCLM
          (n := n) (m := m + 1) (p := ∞) (Ω := Omega) (A i j) :
            ℝ^n → ℝ)
        =ᵐ[domainMeasure n Omega]
          (restrictDerivLp
            (n := n) (p := ∞) (subset_univ Omega) (A0 i j) : ℝ^n → ℝ))
    (u : H¹(Omega))
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦
        wkpBaseCoordinateCLM
          (n := n) (m := m + 1) (p := ∞) (Ω := Omega) (A i j))
      (wkpBaseCoordinateCLM
        (n := n) (m := m) (p := 2) (Ω := Omega) F)
      u)
    (K : Set (ℝ^n)) (hKcompact : IsCompact K) (hKOmega : K ⊆ Omega) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Omega ∧
      ∃ W : W^{m + 2,2}(V),
        ⇑((W : WkpAmbientOn n (m + 2) 2 V)
            (baseIndex n (m + 2)) : DerivLp n 2 V)
          =ᵐ[domainMeasure n V]
            ⇑((u : WkpAmbientOn n 1 2 Omega)
              (baseIndex n 1) : DerivLp n 2 Omega) := by
  induction m generalizing Omega u K with
  | zero =>
      have hcoeff : (fun i j ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := ∞) (Ω := Omega)
          (A i j)) = fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Omega) (A0 i j) :=
        funext₂ fun i j ↦ Lp.ext (hAbase i j)
      simpa only [Nat.zero_add, Nat.add_zero, wkpBaseCoordinateCLM_apply] using
        exists_local_h2_open_neighborhood_of_compact hOpen A0 a C ha hrep hElliptic.1 hElliptic
          (wkpBaseCoordinateCLM (n := n) (m := 0) (p := 2) (Ω := Omega) F) u (hcoeff ▸ hu) K
          hKcompact hKOmega
  | succ r ih =>
      let Aprev : Fin n → Fin n → W^{r + 1,∞}(Omega) := fun i j ↦
        lowerOrderCLM (n := n) (k := r + 1) (m := r + 2) (p := ∞) (Ω := Omega) (by omega) (A i j)
      let Fprev : W^{r,2}(Omega) :=
        lowerOrderCLM (n := n) (k := r) (m := r + 1) (p := 2) (Ω := Omega) (by omega) F
      have hAprev (i j : Fin n) :
          (wkpBaseCoordinateCLM (n := n) (m := r + 1) (p := ∞) (Ω := Omega) (Aprev i j) :
            ℝ^n → ℝ) =ᵐ[domainMeasure n Omega]
              (restrictDerivLp (n := n) (p := ∞) (subset_univ Omega) (A0 i j) : ℝ^n → ℝ) := by
        simpa [Aprev, wkpBaseCoordinateCLM, wkpCoordinateCLM] using hAbase i j
      obtain ⟨N, hNopen, hKN, hNOmega, U, hU⟩ := ih hOpen Aprev Fprev hAprev u
        (by simpa [Aprev, Fprev, wkpBaseCoordinateCLM, wkpCoordinateCLM] using hu) K hKcompact
        hKOmega
      let AN : Fin n → Fin n → W^{r + 2,∞}(N) := fun i j ↦
        restrictCLM (n := n) (k := r + 2) (p := ∞) hNopen.measurableSet hNOmega (A i j)
      let FN : W^{r + 1,2}(N) :=
        restrictCLM (n := n) (k := r + 1) (p := 2) hNopen.measurableSet hNOmega F
      let uN : H¹(N) := restrictCLM (n := n) (k := 1) (p := 2) hNopen.measurableSet hNOmega u
      have huN : IsInteriorWeakDivergenceSolution (n := n) (Ω := N)
          (fun i j ↦ wkpBaseCoordinateCLM (n := n) (m := r + 2) (p := ∞) (Ω := N) (AN i j))
          (wkpBaseCoordinateCLM (n := n) (m := r + 1) (p := 2) (Ω := N) FN) uN := by
        simpa [AN, FN, uN, wkpBaseCoordinateCLM, wkpCoordinateCLM, restrictCLM_apply_coe,
          restrictAmbient_apply] using hu.restrict hNopen hNOmega
      obtain ⟨rho, hrhoN, _, hrhoNhds, _⟩ :=
        TestFunction.exists_eq_one_on_compact hNopen hKcompact hKN
      let AprevN : Fin n → Fin n → W^{r + 1,∞}(N) := fun i j ↦
        lowerOrderCLM (n := n) (k := r + 1) (m := r + 2) (p := ∞) (Ω := N) (by omega) (AN i j)
      have hleN := ae_mono (domainMeasure_le (n := n) hNOmega)
      have hAprevN (i j : Fin n) :
          (wkpBaseCoordinateCLM (n := n) (m := r + 1) (p := ∞) (Ω := N) (AprevN i j) : ℝ^n → ℝ)
            =ᵐ[domainMeasure n N]
              (restrictDerivLp (n := n) (p := ∞) (subset_univ N) (A0 i j) : ℝ^n → ℝ) := by
        rw [show AprevN i j = restrictCLM (n := n) (k := r + 1) (p := ∞) hNopen.measurableSet
            hNOmega (Aprev i j) from (restrictCLM_lowerOrderCLM_apply hNopen.measurableSet
              hNOmega (by omega) (A i j)).symm]
        have hglobal := ((hAprev i j).trans
          (restrictDerivLp_apply_ae (subset_univ Omega) (A0 i j))).filter_mono hleN
        exact (restrictCLM_apply_ae hNopen.measurableSet hNOmega (Aprev i j)
          (baseIndex n (r + 1))).trans
            (hglobal.trans (restrictDerivLp_apply_ae (subset_univ N) (A0 i j)).symm)
      obtain ⟨W, hW⟩ := exists_interior_higherOrder_localized_succ_of_local_previous (r + 1)
        (by omega) hNopen rho hrhoN AN FN uN huN U
        (hU.trans (restrictCLM_apply_ae (p := 2) hNopen.measurableSet hNOmega u
          (baseIndex n 1)).symm)
        fun G0 v hv L hL hLN ↦ ih hNopen AprevN G0 hAprevN _ hv.toInterior L hL hLN
      let V : Set (ℝ^n) := interior {x | rho.toFun x = 1}
      have hrhoOne (x : ℝ^n) (hxV : x ∈ V) : rho.toFun x = 1 :=
        interior_subset (s := {x | rho.toFun x = 1}) hxV
      have hVN : V ⊆ N := fun x hxV ↦
        hrhoN (subset_tsupport _ (show rho.toFun x ≠ 0 by simp [hrhoOne x hxV]))
      have hleV := ae_mono (domainMeasure_le (n := n) hVN)
      refine ⟨V, isOpen_interior, fun x hxK ↦ mem_interior_iff_mem_nhds.mpr (hrhoNhds x hxK),
        hVN.trans hNOmega, restrictCLM (n := n) (k := r + 3) (p := 2)
          isOpen_interior.measurableSet hVN W, ?_⟩
      filter_upwards [restrictCLM_apply_ae (p := 2) isOpen_interior.measurableSet hVN W
          (baseIndex n (r + 3)), hW.filter_mono hleV, (restrictCLM_apply_ae (p := 2)
          hNopen.measurableSet hNOmega u (baseIndex n 1)).filter_mono hleV,
        ae_restrict_mem isOpen_interior.measurableSet] with x hxWV hxW hxU hxV
      refine hxWV.trans (hxW.trans ?_)
      rw [hrhoOne x hxV, one_mul]
      exact hxU

/-- Interior regularity with coefficient assumptions confined to the domain.

The entries and their coherent weak derivatives through order `m + 1` belong to `L∞(Omega)`,
and ellipticity holds almost everywhere on `Omega`. The proof constructs bounded Lipschitz
elliptic extensions near `K` from these data; no representatives or extensions are assumed. -/
theorem exists_local_higherOrder_of_aeUniformlyElliptic
    (m : ℕ) {Omega : Set (ℝ^n)} (hOpen : IsOpen Omega)
    (A : Fin n → Fin n → W^{m + 1,∞}(Omega))
    (F : W^{m,2}(Omega))
    {alpha : ℝ}
    (hElliptic : AEUniformlyElliptic
      (fun i j ↦ wkpBaseCoordinateCLM
        (n := n) (m := m + 1) (p := ∞) (Ω := Omega) (A i j)) alpha)
    (u : H¹(Omega))
    (hu : IsInteriorWeakDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM
        (n := n) (m := m + 1) (p := ∞) (Ω := Omega) (A i j))
      (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) F) u)
    (K : Set (ℝ^n)) (hKcompact : IsCompact K) (hKOmega : K ⊆ Omega) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Omega ∧
      ∃ W : W^{m + 2,2}(V),
        ⇑((W : WkpAmbientOn n (m + 2) 2 V)
            (baseIndex n (m + 2)) : DerivLp n 2 V)
          =ᵐ[domainMeasure n V]
            ⇑((u : WkpAmbientOn n 1 2 Omega)
              (baseIndex n 1) : DerivLp n 2 Omega) := by
  let A1 (i j : Fin n) : W^{1,∞}(Omega) :=
    lowerOrderCLM (n := n) (k := 1) (m := m + 1) (p := ∞) (by omega) (A i j)
  have hA1 : AEUniformlyElliptic
      (fun i j ↦ (A1 i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1)) alpha := by
    simpa [A1, wkpBaseCoordinateCLM, wkpCoordinateCLM] using hElliptic
  obtain ⟨N, hNopen, hKN, hNOmega, B, b, C, hb, hBrep, hB, hBA⟩ :=
    exists_global_elliptic_extension_of_w1Top hOpen A1 hA1 K hKcompact hKOmega
  let AN (i j : Fin n) : W^{m + 1,∞}(N) :=
    restrictCLM hNopen.measurableSet hNOmega (A i j)
  let FN : W^{m,2}(N) := restrictCLM hNopen.measurableSet hNOmega F
  let uN : H¹(N) := restrictCLM hNopen.measurableSet hNOmega u
  have hAN (i j : Fin n) :
      (wkpBaseCoordinateCLM (n := n) (m := m + 1) (p := ∞) (Ω := N) (AN i j) :
        ℝ^n → ℝ) =ᵐ[domainMeasure n N]
          (restrictDerivLp (n := n) (p := ∞) (subset_univ N) (B i j) : ℝ^n → ℝ) := by
    have hBA' : (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n N]
        ⇑((A i j : WkpAmbientOn n (m + 1) ∞ Omega) (baseIndex n (m + 1))) := by
      simpa [A1, baseRepresentative] using hBA i j
    exact (restrictCLM_apply_ae hNopen.measurableSet hNOmega (A i j) (baseIndex n (m + 1))).trans
      (hBA'.symm.trans (restrictDerivLp_apply_ae (subset_univ N) (B i j)).symm)
  have huN : IsInteriorWeakDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM
        (n := n) (m := m + 1) (p := ∞) (Ω := N) (AN i j))
      (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := N) FN) uN := by
    simpa [AN, FN, uN, wkpBaseCoordinateCLM, wkpCoordinateCLM,
      restrictCLM_apply_coe, restrictAmbient_apply] using hu.restrict hNopen hNOmega
  obtain ⟨V, hVopen, hKV, hVN, W, hW⟩ :=
    exists_local_higherOrder_open_neighborhood_of_compact m hNopen B b C hb hBrep hB
      AN FN hAN uN huN K hKcompact hKN
  exact ⟨V, hVopen, hKV, hVN.trans hNOmega, W, hW.trans ((restrictCLM_apply_ae (p := 2)
    hNopen.measurableSet hNOmega u (baseIndex n 1)).filter_mono (ae_mono (domainMeasure_le hVN)))⟩

/-- Higher-order interior regularity from `W^{m+1,∞}_{loc}` coefficients and
`W^{m,2}_{loc}` forcing.

The bounded coefficient and `L²` forcing bundles on `Omega` formulate the weak equation.
Their higher Sobolev norms need be finite only on relatively compact open subdomains.
Neither global Lipschitz representatives nor elliptic extensions are assumed. -/
theorem exists_local_higherOrder_of_isLocallyWkpOn
    (m : ℕ) {Omega : Set (ℝ^n)} (hOpen : IsOpen Omega)
    (A : Fin n → Fin n → DerivLp n ∞ Omega)
    (hAlocal : ∀ i j, IsLocallyWkpOn (m + 1) ∞ Omega (A i j : ℝ^n → ℝ))
    (f : DerivLp n 2 Omega) (hflocal : IsLocallyWkpOn m 2 Omega (f : ℝ^n → ℝ))
    {alpha : ℝ} (hElliptic : AEUniformlyElliptic A alpha)
    (u : H¹(Omega)) (hu : IsInteriorWeakDivergenceSolution A f u)
    (K : Set (ℝ^n)) (hKcompact : IsCompact K) (hKOmega : K ⊆ Omega) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Omega ∧
      ∃ W : W^{m + 2,2}(V),
        ⇑((W : WkpAmbientOn n (m + 2) 2 V)
            (baseIndex n (m + 2)) : DerivLp n 2 V)
          =ᵐ[domainMeasure n V]
            ⇑((u : WkpAmbientOn n 1 2 Omega)
              (baseIndex n 1) : DerivLp n 2 Omega) := by
  obtain ⟨N, hNopen, hKN, hNclosure, hNcompact⟩ :=
    exists_open_between_and_isCompact_closure hKcompact hOpen hKOmega
  have hNOmega : N ⊆ Omega := subset_closure.trans hNclosure
  choose AN hAN using fun i j ↦ hAlocal i j N hNopen hNcompact hNclosure
  obtain ⟨FN, hFN⟩ := hflocal N hNopen hNcompact hNclosure
  have hcoeff : (fun i j ↦ wkpBaseCoordinateCLM (n := n) (m := m + 1) (p := ∞) (Ω := N) (AN i j))
      = fun i j ↦ restrictDerivLp (n := n) (p := ∞) hNOmega (A i j) :=
    funext₂ fun i j ↦ Lp.ext ((hAN i j).trans (restrictDerivLp_apply_ae hNOmega (A i j)).symm)
  have hload : wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := N) FN =
      restrictDerivLp (n := n) (p := 2) hNOmega f :=
    Lp.ext (hFN.trans (restrictDerivLp_apply_ae hNOmega f).symm)
  have hEllipticN : AEUniformlyElliptic
      (fun i j ↦ wkpBaseCoordinateCLM
        (n := n) (m := m + 1) (p := ∞) (Ω := N) (AN i j)) alpha := by
    rw [hcoeff]
    refine ⟨hElliptic.1, ?_⟩
    filter_upwards [ae_mono (domainMeasure_le hNOmega) hElliptic.2, ae_all_iff.mpr fun i ↦
      ae_all_iff.mpr fun j ↦ restrictDerivLp_apply_ae hNOmega (A i j)] with x hx hxA ξ
    simpa only [hxA] using hx ξ
  let uN : H¹(N) := restrictCLM hNopen.measurableSet hNOmega u
  have huN : IsInteriorWeakDivergenceSolution
      (fun i j ↦ wkpBaseCoordinateCLM
        (n := n) (m := m + 1) (p := ∞) (Ω := N) (AN i j))
      (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := N) FN) uN := by
    rw [hcoeff, hload]
    exact hu.restrict hNopen hNOmega
  obtain ⟨V, hVopen, hKV, hVN, W, hW⟩ :=
    exists_local_higherOrder_of_aeUniformlyElliptic m hNopen AN FN hEllipticN uN huN
      K hKcompact hKN
  exact ⟨V, hVopen, hKV, hVN.trans hNOmega, W, hW.trans ((restrictCLM_apply_ae (p := 2)
    hNopen.measurableSet hNOmega u (baseIndex n 1)).filter_mono (ae_mono (domainMeasure_le hVN)))⟩

end SobolevSpace.GraphSpace.BoundaryRegularity
