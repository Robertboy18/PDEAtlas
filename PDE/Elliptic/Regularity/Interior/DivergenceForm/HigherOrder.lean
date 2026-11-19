/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DivergenceForm.H2
public import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import PDE.Elliptic.Regularity.Interior.DivergenceForm.Estimate
import PDE.Elliptic.Regularity.Interior.DivergenceForm.LowerOrderBootstrap
import PDE.Elliptic.Regularity.Interior.LocalHigherOrder

/-!
# Higher interior regularity for the full elliptic equation

If the coefficients of the full divergence-form operator are `C^{m+1}` in the domain and the forcing
belongs to `H^m`, an H¹ weak solution has an `H^{m+2}` representative on each relatively compact
open subdomain, with the estimate `‖u‖_{H^{m+2}(V)} ≤ C (‖f‖_{H^m} + ‖u‖_{L²})`. This is Evans's
§6.3.1, Theorem 2 (Higher interior regularity). Local classical regularity of the coefficients
suffices: their derivatives need not be bounded on the original domain.

## Main results

* `exists_interior_higherOrder_of_contDiffOn`: the `H^{m+2}` representative, Evans's (27).
* `exists_interior_higherOrder_estimate_of_contDiffOn`: the estimate (28).

## How it works

Evans argues by induction on `m`. For `|α| = m + 1` he tests the equation with `(-1)^{|α|} D^α ṽ`,
so that `ũ = D^α u` is a weak solution of `Lũ = f̃` with the forcing (36), and he applies Theorem 1
to `ũ`. Our induction separates the lower-order terms instead. At each step the induction hypothesis
on a larger interior set gives the derivatives of the state there, `exists_lowerOrder_forcing`
places the drift and potential terms in the next Sobolev space, and the principal theorem
`BoundaryRegularity.exists_local_higherOrder_of_aeUniformlyElliptic` applies to the equation without
lower-order terms. The estimate then follows from the closed graph theorem and the interior energy
estimate, as in the H² case.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 2 (Higher interior regularity) and its proof,
  (25)-(37), pp. 332-333.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω V : Set (ℝ^n)}

/-- Higher interior regularity for arbitrary H¹ weak solutions of the full equation.
Only local classical differentiability, rather than global derivative bounds, is required. -/
theorem exists_interior_higherOrder_of_contDiffOn
    (m : ℕ) (hΩ : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (B : Fin n → DerivLp n ∞ Ω) (C : DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ) (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ (m + 1) (a i j) Ω)
    (hb : ∀ i, ContDiffOn ℝ (m + 1) (b i) Ω) (hc : ContDiffOn ℝ (m + 1) c Ω)
    (hArep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    (hBrep : ∀ i, (B i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] b i)
    (hCrep : (C : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] c)
    {alpha : ℝ} (hA : AEUniformlyElliptic A alpha)
    (F : W^{m,2}(Ω)) (u : H¹(Ω))
    (hu : IsInteriorWeakFullDivergenceSolution A B C (wkpBaseCoordinateCLM F) u)
    (hV : IsOpen V) (hcompact : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ W : W^{m + 2,2}(V),
      wkpBaseCoordinateCLM W =
        restrictDerivLp (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u) := by
  induction m generalizing V with
  | zero =>
    exact exists_interior_h2_of_contDiffOn hΩ A a ha hArep hA B C
      (wkpBaseCoordinateCLM F) u hu hV hcompact hVΩ
  | succ m ih =>
    obtain ⟨N, hN, hVN, hNΩ, hNc⟩ :=
      exists_open_between_and_isCompact_closure hcompact hΩ hVΩ
    let hsub : N ⊆ Ω := subset_closure.trans hNΩ
    let AN (i j : Fin n) : DerivLp n ∞ N := restrictDerivLp hsub (A i j)
    let BN (i : Fin n) : DerivLp n ∞ N := restrictDerivLp hsub (B i)
    let CN : DerivLp n ∞ N := restrictDerivLp hsub C
    let uN : H¹(N) := restrictCLM hN.measurableSet hsub u
    let FN : W^{m + 1,2}(N) := restrictCLM hN.measurableSet hsub F
    obtain ⟨U, hU⟩ := ih
      (fun i j ↦ (ha i j).of_le (by simp)) (fun i ↦ (hb i).of_le (by simp))
      (hc.of_le (by simp)) (lowerOrderCLM (Nat.le_succ m) F)
      (by simpa using hu) hN hNc hNΩ
    have hUbase : wkpBaseCoordinateCLM U = wkpBaseCoordinateCLM uN := hU
    have hblocal (i : Fin n) := isLocallyWkpOn_of_contDiffOn (k := m + 1) hΩ
      ((hb i).of_le (by exact_mod_cast Nat.le_succ (m + 1))) ∞ N hN hNc hNΩ
    obtain ⟨CS, hCS⟩ := isLocallyWkpOn_of_contDiffOn (k := m + 1) hΩ
      (hc.of_le (by exact_mod_cast Nat.le_succ (m + 1))) ∞ N hN hNc hNΩ
    choose BS hBS using hblocal
    have hrestrict {X : DerivLp n ∞ Ω} {Y : DerivLp n ∞ N} {f : ℝ^n → ℝ}
        (hY : (Y : ℝ^n → ℝ) =ᵐ[domainMeasure n N] f)
        (hX : (X : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f) : Y = restrictDerivLp hsub X :=
      Lp.ext (hY.trans ((hX.filter_mono (ae_mono (domainMeasure_le hsub))).symm.trans
        (restrictDerivLp_apply_ae hsub X).symm))
    have hBeq : (fun i ↦ wkpBaseCoordinateCLM (BS i)) = BN :=
      funext fun i ↦ hrestrict (hBS i) (hBrep i)
    have hCeq : wkpBaseCoordinateCLM CS = CN := hrestrict hCS hCrep
    obtain ⟨G, hG⟩ := exists_lowerOrder_forcing (Nat.succ_pos m) hN BS CS U uN hUbase
    rw [hBeq, hCeq] at hG
    have hprincipal : IsInteriorWeakDivergenceSolution AN
        (wkpBaseCoordinateCLM (FN - G)) uN := by
      rw [map_sub, hG]
      exact (isInteriorWeakFullDivergenceSolution_iff AN BN CN
        (wkpBaseCoordinateCLM FN) uN).mp (hu.restrict hN hsub)
    choose AS hAS using fun i j ↦
      isLocallyWkpOn_of_contDiffOn hΩ (ha i j) ∞ N hN hNc hNΩ
    have hAeq : (fun i j ↦ wkpBaseCoordinateCLM (AS i j)) = AN :=
      funext₂ fun i j ↦ hrestrict (hAS i j) (hArep i j)
    obtain ⟨P, hP, hVP, _, W, hW⟩ :=
      BoundaryRegularity.exists_local_higherOrder_of_aeUniformlyElliptic (m + 1) hN
        AS (FN - G) (by rw [hAeq]; exact hA.restrict hsub) uN
        (by rw [hAeq]; exact hprincipal) (closure V) hcompact hVN
    let hVP' : V ⊆ P := subset_closure.trans hVP
    refine ⟨restrictCLM hV.measurableSet hVP' W, ?_⟩
    apply Lp.ext
    filter_upwards [restrictCLM_apply_ae hV.measurableSet hVP' W
      (baseIndex n (m + 1 + 2)), ae_mono (domainMeasure_le hVP') hW,
      ae_mono (domainMeasure_le (subset_closure.trans hVN))
        (restrictCLM_apply_ae hN.measurableSet hsub u (baseIndex n 1)),
      restrictDerivLp_apply_ae (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u)]
      with x hx hy hz hw
    exact hx.trans (hy.trans (hz.trans hw.symm))

/-- The full higher-order interior estimate with an L² remainder. The constant
depends on the order, the two domains, and the coefficients, not on the data or state. -/
theorem exists_interior_higherOrder_estimate_of_contDiffOn
    (m : ℕ) (hΩ : IsOpen Ω)
    (A : Fin n → Fin n → DerivLp n ∞ Ω)
    (B : Fin n → DerivLp n ∞ Ω) (C : DerivLp n ∞ Ω)
    (a : Fin n → Fin n → ℝ^n → ℝ) (b : Fin n → ℝ^n → ℝ) (c : ℝ^n → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ (m + 1) (a i j) Ω)
    (hb : ∀ i, ContDiffOn ℝ (m + 1) (b i) Ω) (hc : ContDiffOn ℝ (m + 1) c Ω)
    (hArep : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    (hBrep : ∀ i, (B i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] b i)
    (hCrep : (C : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] c)
    {alpha : ℝ} (hA : AEUniformlyElliptic A alpha)
    (hV : IsOpen V) (hcompact : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : W^{m,2}(Ω)) (u : H¹(Ω)),
      IsInteriorWeakFullDivergenceSolution A B C (wkpBaseCoordinateCLM F) u →
      ∃ W : W^{m + 2,2}(V),
        wkpBaseCoordinateCLM W =
          restrictDerivLp (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM u) ∧
        ‖W‖ ≤ K * (‖F‖ + ‖wkpBaseCoordinateCLM u‖) := by
  apply exists_interior_estimate_with_L2_remainder hΩ hV hcompact hVΩ A B C hA
  intro N hN _ hNΩ hVN F u hu
  let hsub : N ⊆ Ω := subset_closure.trans hNΩ
  exact exists_interior_higherOrder_of_contDiffOn m hN _ _ _ a b c
    (fun i j ↦ (ha i j).mono hsub) (fun i ↦ (hb i).mono hsub) (hc.mono hsub)
    (fun i j ↦ (restrictDerivLp_apply_ae hsub (A i j)).trans
      (ae_mono (domainMeasure_le hsub) (hArep i j)))
    (fun i ↦ (restrictDerivLp_apply_ae hsub (B i)).trans
      (ae_mono (domainMeasure_le hsub) (hBrep i)))
    ((restrictDerivLp_apply_ae hsub C).trans
      (ae_mono (domainMeasure_le hsub) hCrep))
    (hA.restrict hsub) F u hu hV hcompact hVN

end SobolevSpace.GraphSpace
