/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderBounds
public import PDE.Elliptic.Regularity.Localization.CutoffEquation.WeakEquation -- shake: keep

/-!
# Arbitrary-order localization of divergence-form weak equations

Multiplying a weak solution `U` of `-∂ᵢ(aᵢⱼ ∂ⱼ U) = F` by a smooth cutoff `ρ`
gives a zero-trace solution `ρU` of the same operator with the commutator
forcing

`ρF - ∑ᵢⱼ aᵢⱼ ∂ⱼU ∂ᵢρ - ∑ᵢ ∂ᵢ(U ∑ⱼ aᵢⱼ ∂ⱼρ)`.

Each term loses at most one derivative relative to `U` and the coefficients,
and none relative to `F`. Hence if `U ∈ W^{k+1,2}`, `aᵢⱼ ∈ W^{k+1,∞}` and
`F ∈ W^{k,2}`, the forcing is again in `W^{k,2}` and is supported in the
support of `ρ`. Evans proves higher regularity by induction on the order
(§6.3.1, Theorem 2, and §6.3.2, Theorem 5); our version of that induction
localizes with this lemma at every order.

## Main results

* `exists_localized_weakDivergenceSolution_higher`: for a zero-trace solution
  of order `k + 1`, the cutoff product `ρU` is a weak solution with a
  supported `W^{k,2}` forcing.
* `exists_localized_interiorWeakDivergenceSolution_higher`: the same for an
  interior weak solution with no trace condition, provided the cutoff is
  supported inside `Ω`.

## Implementation notes

The `W^{k,2}` forcing is built pointwise from the base coordinates of the
bundles (`higherCutoffForcing`) and then shown to carry all weak derivatives;
the `L²` localized equation from `CutoffEquation` is upgraded rather than
re-derived.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 2 (higher interior regularity), and
  §6.3.2, Theorem 5 (higher boundary regularity), both proved by induction on the order.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open SobolevSpace.CompactSupportLocalization
open scoped BigOperators Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

private def higherCutoffForcing
    (k : ℕ)
    (A : Fin n → Fin n → W^{k + 1,∞}(Ω))
    (F : W^{k,2}(Ω))
    (U : W^{k + 1,2}(Ω))
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ℝ^n → ℝ := by
  let Ak : Fin n → Fin n → W^{k,∞}(Ω) := fun i j ↦
    lowerOrderCLM
      (n := n) (p := ∞) (Ω := Ω) (by omega) (A i j)
  let Uk : W^{k,2}(Ω) :=
    lowerOrderCLM
      (n := n) (p := 2) (Ω := Ω) (by omega) U
  let DUk (ell : Fin n) : W^{k,2}(Ω) :=
    derivativeWordCLM
      (n := n) (m := k + 1) (r := k) (p := 2) (Ω := Ω)
      [ell] (by simp [Nat.add_comm]) U
  let DAk (i j ell : Fin n) : W^{k,∞}(Ω) :=
    derivativeWordCLM
      (n := n) (m := k + 1) (r := k) (p := ∞) (Ω := Ω)
      [ell] (by simp [Nat.add_comm]) (A i j)
  let f : ℝ^n → ℝ :=
    ((F : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
      DerivLp n 2 Ω)
  let aval (i j : Fin n) : ℝ^n → ℝ :=
    ((Ak i j : WkpAmbientOn n k ∞ Ω) (baseIndex n k) :
      DerivLp n ∞ Ω)
  let duval (ell : Fin n) : ℝ^n → ℝ :=
    ((DUk ell : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
      DerivLp n 2 Ω)
  let daval (i j : Fin n) : ℝ^n → ℝ :=
    ((DAk i j i : WkpAmbientOn n k ∞ Ω) (baseIndex n k) :
      DerivLp n ∞ Ω)
  let uval : ℝ^n → ℝ :=
    ((Uk : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
      DerivLp n 2 Ω)
  exact fun x ↦
    ρ.toFun x * f x -
      (∑ i : Fin n, ∑ j : Fin n,
        aval i j x * duval j x *
          iteratedPartialDeriv (n := n) [i] ρ.toFun x) -
      (∑ i : Fin n, ∑ j : Fin n,
        (iteratedPartialDeriv (n := n) [j] ρ.toFun x *
            (aval i j x * duval i x + daval i j x * uval x) +
          iteratedPartialDeriv (n := n) [i, j] ρ.toFun x *
            (aval i j x * uval x)))

/-- Upgrade an already-localized `L²` cutoff equation to its exact
`W^{k,2}` commutator forcing. -/
private theorem exists_localized_weakDivergenceSolution_higher_core
    (k : ℕ) (hk : 0 < k)
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{k + 1,∞}(Ω))
    (F : W^{k,2}(Ω))
    (U : W^{k + 1,2}(Ω))
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (w : H¹₀(Ω))
    (hw :
      ((baseCoordCLM (n := n) (Ω := Ω) w :
          ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ρ.toFun x *
          (((U : WkpAmbientOn n (k + 1) 2 Ω) (baseIndex n (k + 1)) :
            DerivLp n 2 Ω) : ℝ^n → ℝ) x))
    (g : DerivLp n 2 Ω)
    (hg :
      (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        higherCutoffForcing k A F U ρ)
    (hgSupport :
      (tsupport ρ.toFun).indicator (g : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] (g : ℝ^n → ℝ))
    (hgw : IsWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦
        ((lowerOrderCLM
            (n := n) (k := 1) (m := k + 1) (p := ∞) (Ω := Ω)
            (by omega) (A i j) :
              WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
                DerivLp n ∞ Ω))
      g w) :
    ∃ w : H¹₀(Ω),
      ((baseCoordCLM (n := n) (Ω := Ω) w :
          ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ρ.toFun x *
          (((U : WkpAmbientOn n (k + 1) 2 Ω) (baseIndex n (k + 1)) :
            DerivLp n 2 Ω) : ℝ^n → ℝ) x) ∧
      ∃ G : W^{k,2}(Ω),
        (tsupport ρ.toFun).indicator
            ((((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
              DerivLp n 2 Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
          ((((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
            DerivLp n 2 Ω) : ℝ^n → ℝ)) ∧
        IsWeakDivergenceSolution
          (n := n) (Ω := Ω)
          (fun i j ↦
            ((A i j : WkpAmbientOn n (k + 1) ∞ Ω)
              (baseIndex n (k + 1)) : DerivLp n ∞ Ω))
          ((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
            DerivLp n 2 Ω)
          w := by
  classical
  let Ak (i j : Fin n) : W^{k,∞}(Ω) := lowerOrderCLM (n := n) (p := ∞) (Ω := Ω) (by omega) (A i j)
  let Uk : W^{k,2}(Ω) := lowerOrderCLM (n := n) (p := 2) (Ω := Ω) (by omega) U
  let DUk (l : Fin n) : W^{k,2}(Ω) := derivativeWordCLM (n := n) (m := k + 1) (r := k) (p := 2)
    (Ω := Ω) [l] (by simp [Nat.add_comm]) U
  let DAk (i j l : Fin n) : W^{k,∞}(Ω) := derivativeWordCLM (n := n) (m := k + 1) (r := k)
    (p := ∞) (Ω := Ω) [l] (by simp [Nat.add_comm]) (A i j)
  let P := wkTopProduct (n := n) (Ω := Ω) hk hΩopen
  let M := higherOrderCutoffCLM (n := n) (Ω := Ω) hk hΩopen
  have hP := wkTopProduct_base_ae (n := n) (Ω := Ω) hk hΩopen
  have hM := higherOrderCutoffCLM_base_ae (n := n) (k := k) (Ω := Ω) hk hΩopen
  have hD (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (i : Fin n) :
      (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) ψ :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)).toFun = fun x ↦ iteratedPartialDeriv (n := n) [i] ψ.toFun x := by
    funext x
    change (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) ψ :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x = _
    rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp),
      (ψ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl
  let dρ (i : Fin n) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) ρ
  let drift (i j : Fin n) : W^{k,2}(Ω) := M (dρ i) (P (Ak i j) (DUk j))
  let corr (i j : Fin n) : W^{k,2}(Ω) := M (dρ j) (P (Ak i j) (DUk i) + P (DAk i j i) Uk) +
    M (_root_.TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) (dρ j)) (P (Ak i j) Uk)
  let G : W^{k,2}(Ω) := M ρ F - ∑ i, ∑ j, drift i j - ∑ i, ∑ j, corr i j
  have hsum (T : Fin n → Fin n → W^{k,2}(Ω)) : ∀ᵐ x ∂domainMeasure n Ω,
      baseRepresentative (∑ i, ∑ j, T i j) x = ∑ i, ∑ j, baseRepresentative (T i j) x := by
    filter_upwards [baseRepresentative_sum_ae fun i ↦ ∑ j, T i j, ae_all_iff.2 fun i ↦
      baseRepresentative_sum_ae (T i)] with x hx hxi
    rw [hx]
    exact Finset.sum_congr rfl fun i _ ↦ hxi i
  have hdrift : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j, baseRepresentative (drift i j) x =
      baseRepresentative (Ak i j) x * baseRepresentative (DUk j) x *
        iteratedPartialDeriv (n := n) [i] ρ.toFun x := by
    refine ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ ?_
    filter_upwards [hM (dρ i) _, hP (Ak i j) (DUk j)] with x h1 h2
    rw [h1, h2, hD]
    ring
  have hcorr : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j, baseRepresentative (corr i j) x =
      iteratedPartialDeriv (n := n) [j] ρ.toFun x * (baseRepresentative (Ak i j) x *
        baseRepresentative (DUk i) x + baseRepresentative (DAk i j i) x * baseRepresentative Uk x) +
      iteratedPartialDeriv (n := n) [i, j] ρ.toFun x *
        (baseRepresentative (Ak i j) x * baseRepresentative Uk x) := by
    refine ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ ?_
    filter_upwards [baseRepresentative_add_ae _ _, hM (dρ j) _, hM _ _,
      baseRepresentative_add_ae (P (Ak i j) (DUk i)) _, hP (Ak i j) (DUk i), hP (DAk i j i) Uk,
      hP (Ak i j) Uk] with x h1 h2 h3 h4 h5 h6 h7
    rw [h1, h2, h3, h4, h5, h6, h7, hD, hD, hD]
    rfl
  have hGg : baseRepresentative G =ᵐ[domainMeasure n Ω] g := by
    refine Filter.EventuallyEq.trans ?_ hg.symm
    filter_upwards [baseRepresentative_sub_ae (M ρ F - _) _, baseRepresentative_sub_ae (M ρ F) _,
      hM ρ F, hsum drift, hsum corr, hdrift, hcorr]
      with x hsub hsub' hMF hdriftSum hcorrSum hdriftx hcorrx
    rw [hsub, hsub', hMF, hdriftSum, hcorrSum]
    simp only [hdriftx, hcorrx]
    rfl
  refine ⟨w, hw, G, hGg.indicator.trans (hgSupport.trans hGg.symm), ?_⟩
  rw [show ((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) : DerivLp n 2 Ω) = g from Lp.ext hGg]
  simpa using hgw

/--
For positive `k`, cutoff localization sends coefficients and a zero-trace
solution of order `k + 1`, together with forcing of order `k`, to a supported
`W^{k,2}` commutator forcing satisfying the localized weak equation.
-/
theorem exists_localized_weakDivergenceSolution_higher
    (k : ℕ) (hk : 0 < k)
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{k + 1,∞}(Ω))
    (F : W^{k,2}(Ω))
    (U : W^{k + 1,2}(Ω))
    (htrace0 :
      lowerOrderCLM
          (n := n) (p := 2) (Ω := Ω) (by omega) U ∈
        (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (k + 1) ∞ Ω) (baseIndex n (k + 1)) :
          DerivLp n ∞ Ω))
      ((F : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
        DerivLp n 2 Ω)
      ⟨lowerOrderCLM
          (n := n) (p := 2) (Ω := Ω) (by omega) U,
        htrace0⟩)
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ w : H¹₀(Ω),
      ((baseCoordCLM (n := n) (Ω := Ω) w :
          ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ρ.toFun x *
          (((U : WkpAmbientOn n (k + 1) 2 Ω) (baseIndex n (k + 1)) :
            DerivLp n 2 Ω) : ℝ^n → ℝ) x) ∧
      ∃ G : W^{k,2}(Ω),
        (tsupport ρ.toFun).indicator
            ((((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
              DerivLp n 2 Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
          ((((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
            DerivLp n 2 Ω) : ℝ^n → ℝ)) ∧
        IsWeakDivergenceSolution
          (n := n) (Ω := Ω)
          (fun i j ↦
            ((A i j : WkpAmbientOn n (k + 1) ∞ Ω)
              (baseIndex n (k + 1)) : DerivLp n ∞ Ω))
          ((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
            DerivLp n 2 Ω)
          w := by
  let A1 (i j : Fin n) : W^{1,∞}(Ω) := lowerOrderCLM (n := n) (p := ∞) (Ω := Ω) (by omega) (A i j)
  let u : H¹₀(Ω) := ⟨lowerOrderCLM (n := n) (p := 2) (Ω := Ω) (by omega) U, htrace0⟩
  obtain ⟨w, hw, g, hg, hgSupport, hgw⟩ := exists_localized_weakDivergenceSolution hΩopen A1 u
    ((F : WkpAmbientOn n k 2 Ω) (baseIndex n k) : DerivLp n 2 Ω) (by simpa [A1, u] using hu) ρ
  exact exists_localized_weakDivergenceSolution_higher_core k hk hΩopen A F U ρ w
    (by simpa [u] using hw) g
    (by simpa [higherCutoffForcing, A1, u, derivIndexOfList_singleton] using hg) hgSupport
    (by simpa [A1] using hgw)

/--
Higher-order cutoff localization for a general interior weak solution.

The state has no trace condition. The cutoff support is therefore required
to lie inside the domain; its product with the state then belongs to
`H¹₀(Ω)`. The resulting commutator forcing retains the given `W^{k,2}`
regularity.
-/
theorem exists_localized_interiorWeakDivergenceSolution_higher
    (k : ℕ) (hk : 0 < k)
    (A : Fin n → Fin n → W^{k + 1,∞}(Ω))
    (F : W^{k,2}(Ω))
    (U : W^{k + 1,2}(Ω))
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (k + 1) ∞ Ω) (baseIndex n (k + 1)) :
          DerivLp n ∞ Ω))
      ((F : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
        DerivLp n 2 Ω)
      (lowerOrderCLM
        (n := n) (p := 2) (Ω := Ω) (by omega) U))
    (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hρΩ : tsupport ρ.toFun ⊆ Ω) :
    ∃ w : H¹₀(Ω),
      ((baseCoordCLM (n := n) (Ω := Ω) w :
          ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ρ.toFun x *
          (((U : WkpAmbientOn n (k + 1) 2 Ω) (baseIndex n (k + 1)) :
            DerivLp n 2 Ω) : ℝ^n → ℝ) x) ∧
      ∃ G : W^{k,2}(Ω),
        (tsupport ρ.toFun).indicator
            ((((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
              DerivLp n 2 Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
          ((((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
            DerivLp n 2 Ω) : ℝ^n → ℝ)) ∧
        IsWeakDivergenceSolution
          (n := n) (Ω := Ω)
          (fun i j ↦
            ((A i j : WkpAmbientOn n (k + 1) ∞ Ω)
              (baseIndex n (k + 1)) : DerivLp n ∞ Ω))
          ((G : WkpAmbientOn n k 2 Ω) (baseIndex n k) :
            DerivLp n 2 Ω)
          w := by
  have hΩopen : IsOpen Ω := hu.isOpen
  let A1 (i j : Fin n) : W^{1,∞}(Ω) := lowerOrderCLM (n := n) (p := ∞) (Ω := Ω) (by omega) (A i j)
  let U1 : W^{1,2}(Ω) := lowerOrderCLM (n := n) (p := 2) (Ω := Ω) (by omega) U
  obtain ⟨w, hw, g, hg, hgSupport, hgw⟩ := exists_localized_interiorWeakDivergenceSolution
    A1 U1 ((F : WkpAmbientOn n k 2 Ω) (baseIndex n k) : DerivLp n 2 Ω)
    (by simpa [A1, U1] using hu) ρ hρΩ
  exact exists_localized_weakDivergenceSolution_higher_core k hk hΩopen A F U ρ w
    (by simpa [U1, wkpBaseCoordinateCLM, wkpCoordinateCLM] using hw) g
    (by simpa [higherCutoffForcing, A1, U1, wkpBaseCoordinateCLM, wkpCoordinateCLM,
      derivIndexOfList_singleton] using hg) hgSupport (by simpa [A1] using hgw)

end SobolevSpace.GraphSpace
