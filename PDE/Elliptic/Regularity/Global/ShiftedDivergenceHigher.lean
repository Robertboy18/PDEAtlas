/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Elliptic.Variational.ShiftedDivergenceForm
import PDE.Elliptic.Regularity.Global.HigherOrder
import PDE.Elliptic.Regularity.Global.ShiftedDivergence
import PDE.Spaces.Sobolev.Approximation.Density.Global
public import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator

/-!
# Global higher-order regularity for the full divergence-form operator

At arbitrary positive order, the first-order, zero-order, and scalar-shift terms preserve the
forcing Sobolev class once one additional derivative of the solution is known
(`globalHigherRegularity.exists_of_weak_shifted_full_divergence_solution_of_previous`). With the
principal theorem this gives
`globalHigherRegularity.exists_of_weak_shifted_full_divergence_solution`: for forcing in `W^{k,2}`,
principal coefficients in `W^{k+1,∞}` with globally `C^{k+1}` representatives, lower-order
coefficients in `W^{k,∞}`, and charts of orders `k + 2` and `k + 1`, every homogeneous Dirichlet
weak solution has a `W^{k+2,2}` representative. At `λ = 0` this is the qualitative part of Evans's
§6.3.2, Theorem 5 (Higher boundary regularity), whose hypothesis (72) asks for lower-order
coefficients in `C^{k+1}(Ū)`.

## How it works

Evans differentiates the full operator, so the derivatives of the lower-order coefficients enter the
forcing `f̃` defined after (87). We move the lower-order terms into the forcing at every order
instead, as Evans does for Theorem 4 in step 2 of its proof, (44)-(45). If `u ∈ H^{m+1}` and the
lower-order coefficients lie in `W^{m,∞}`, then `F - ∑ᵢ Bᵢ ∂ᵢu - Cu - λu ∈ H^m`, and
`exists_global_higherOrder_of_isWeakDivergenceSolution` gives `u ∈ H^{m+2}`. Strong induction on
`k`, starting from `exists_global_h2_of_weak_shifted_full_divergence_solution`, gives the theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 2 of the proof of Theorem 4, (44)-(45), p. 335;
  Theorem 5 (Higher boundary regularity), (72)-(77), pp. 340-341, and step 3 of its proof,
  (87)-(88), p. 342.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory
open scoped ENNReal BigOperators

variable {n m : ℕ}

namespace globalHigherRegularity

/--
One-step bootstrap for the full shifted divergence-form equation.

Suppose `u` already has an `H^{m+1}` representative, the lower-order
coefficients belong to `W^{m,infinity}`, and the forcing belongs to `H^m`.
Then the lower-order terms form an `H^m` effective forcing for the principal
operator. Any principal `H^m -> H^{m+2}` regularity theorem therefore gives
the same conclusion for the full operator.
-/
theorem exists_of_weak_shifted_full_divergence_solution_of_previous
    {Omega : Set (ℝ^n)}
    (hm : 0 < m)
    (a : Fin n → Fin n → DerivLp n ∞ Omega)
    (B : Fin n → W^{m,∞}(Omega))
    (C : W^{m,∞}(Omega))
    (lambda : ℝ)
    (F : W^{m,2}(Omega))
    (u : H¹₀(Omega))
    (hu : IsWeakShiftedFullDivergenceSolution
      (n := n) (Ω := Omega)
      a
      (fun i ↦ ((B i : WkpAmbientOn n m ∞ Omega)
        (baseIndex n m) : DerivLp n ∞ Omega))
      ((C : WkpAmbientOn n m ∞ Omega)
        (baseIndex n m) : DerivLp n ∞ Omega)
      lambda
      ((F : WkpAmbientOn n m 2 Omega)
        (baseIndex n m) : DerivLp n 2 Omega)
      (0 : Fin n → DerivLp n 2 Omega)
      u)
    (U : W^{m + 1,2}(Omega))
    (hU :
      ⇑((U : WkpAmbientOn n (m + 1) 2 Omega)
          (baseIndex n (m + 1)) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega))
    (hprincipal :
      ∀ G : W^{m,2}(Omega),
        IsWeakDivergenceSolution
          (n := n) (Ω := Omega)
          a
          (wkpBaseCoordinateCLM
            (n := n) (m := m) (p := 2) (Ω := Omega) G)
          u →
        ∃ W : W^{m + 2,2}(Omega),
          ⇑((W : WkpAmbientOn n (m + 2) 2 Omega)
              (baseIndex n (m + 2)) : DerivLp n 2 Omega)
            =ᵐ[domainMeasure n Omega]
              ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
                (baseIndex n 1) : DerivLp n 2 Omega)) :
    ∃ W : W^{m + 2,2}(Omega),
      ⇑((W : WkpAmbientOn n (m + 2) 2 Omega)
          (baseIndex n (m + 2)) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) := by
  classical
  have hOpen : IsOpen Omega := hu.isOpen
  let coeffB : Fin n → DerivLp n ∞ Omega := fun i ↦
    ((B i : WkpAmbientOn n m ∞ Omega) (baseIndex n m) : DerivLp n ∞ Omega)
  let coeffC : DerivLp n ∞ Omega :=
    ((C : WkpAmbientOn n m ∞ Omega) (baseIndex n m) : DerivLp n ∞ Omega)
  let u0 : DerivLp n 2 Omega := baseCoordCLM (n := n) (Ω := Omega) u
  let du (i : Fin n) : DerivLp n 2 Omega := derivCoordCLM (n := n) (Ω := Omega) i u
  let U1 : W^{1,2}(Omega) :=
    lowerOrderCLM (n := n) (k := 1) (m := m + 1) (p := 2) (Ω := Omega) (by omega) U
  have hU1eq : U1 = (u : H¹(Omega)) :=
    WkpSpaceOn.ext_of_base_ae hOpen _ _ (by simpa [U1] using hU)
  let U0 : W^{m,2}(Omega) :=
    lowerOrderCLM (n := n) (k := m) (m := m + 1) (p := 2) (Ω := Omega) (by omega) U
  let Ui (i : Fin n) : W^{m,2}(Omega) := derivativeWordCLM (n := n) (m := m + 1) (r := m)
    (p := 2) (Ω := Omega) [i] (by simp [Nat.add_comm]) U
  have hUiBase (i : Fin n) :
      wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) (Ui i) = du i := by
    simpa [U1, Ui, du, derivativeWordCLM_apply, derivCoordCLM_apply,
      derivIndexOfList_singleton] using congrArg (fun V : W^{1,2}(Omega) ↦
        ((V : WkpAmbientOn n 1 2 Omega) (singleDerivIndex n i) : DerivLp n 2 Omega)) hU1eq
  have hU0Base : wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) U0 = u0 := by
    rw [show wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) U0 =
      wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega) U1 by simp [U0, U1], hU1eq]
    rfl
  have hprod (Cc : W^{m,∞}(Omega)) (V : W^{m,2}(Omega)) :
      wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega)
          (wkTopProduct (n := n) (Ω := Omega) hm hOpen Cc V) =
        ((Cc : WkpAmbientOn n m ∞ Omega) (baseIndex n m) : DerivLp n ∞ Omega) •
          wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) V :=
    Lp.ext ((wkTopProduct_base_ae hm hOpen Cc V).trans (Lp.coeFn_lpSMul (r := 2)
      ((Cc : WkpAmbientOn n m ∞ Omega) (baseIndex n m))
      (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) V)).symm)
  let G : W^{m,2}(Omega) := F - (∑ i : Fin n, wkTopProduct (n := n) (Ω := Omega) hm hOpen (B i)
    (Ui i)) - wkTopProduct (n := n) (Ω := Omega) hm hOpen C U0 - lambda • U0
  have hGBase : wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) G =
      fullDivergencePrincipalForcing coeffB coeffC lambda
        ((F : WkpAmbientOn n m 2 Omega) (baseIndex n m) : DerivLp n 2 Omega) u := by
    simp only [G, map_sub, map_sum, map_smul, hprod, hUiBase, hU0Base]
    rfl
  exact hprincipal G (hGBase ▸ hu.toPrincipal)

variable [Fact (0 < n)]

/--
The qualitative part of Evans's §6.3.2, Theorem 5, for the full shifted
divergence-form operator.

On a domain with the operational boundary atlas and chart regularity of the
indicated orders, forcing in `W^{k,2}`, principal coefficients in
`W^{k+1,infinity}`, and lower-order coefficients in `W^{k,infinity}` promote
every homogeneous-Dirichlet weak solution from `H¹₀` to `W^{k+2,2}`. No
regularity above `H¹₀` is assumed for the weak solution.
-/
theorem exists_of_weak_shifted_full_divergence_solution
    (k : ℕ)
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 1)
        (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{k + 1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n (k + 1) ∞ Omega)
          (baseIndex n (k + 1)) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j,
      ContDiff ℝ (k + 1) (fun x ↦ a x i j))
    (B : Fin n → W^{k,∞}(Omega))
    (C : W^{k,∞}(Omega))
    (lambda : ℝ)
    (F : W^{k,2}(Omega))
    (u : H¹₀(Omega))
    (hu : IsWeakShiftedFullDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (k + 1) ∞ Omega)
          (baseIndex n (k + 1)) : DerivLp n ∞ Omega))
      (fun i ↦
        ((B i : WkpAmbientOn n k ∞ Omega)
          (baseIndex n k) : DerivLp n ∞ Omega))
      ((C : WkpAmbientOn n k ∞ Omega)
        (baseIndex n k) : DerivLp n ∞ Omega)
      lambda
      ((F : WkpAmbientOn n k 2 Omega)
        (baseIndex n k) : DerivLp n 2 Omega)
      (0 : Fin n → DerivLp n 2 Omega)
      u)
    (alpha : ℝ)
    (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{k + 2,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        (fun x ↦
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) x) := by
  classical
  induction k using Nat.strong_induction_on generalizing u with
  | h k ih =>
      rcases k with _ | r
      · simpa using exists_global_h2_of_weak_shifted_full_divergence_solution hOmega A a haRep
          haContDiff _ _ lambda _ u hu alpha halpha hElliptic
      · let Aprev : Fin n → Fin n → W^{r + 1,∞}(Omega) := fun i j ↦
          lowerOrderCLM (n := n) (k := r + 1) (m := r + 2) (p := ∞) (Ω := Omega) (by omega) (A i j)
        let Bprev : Fin n → W^{r,∞}(Omega) := fun i ↦
          lowerOrderCLM (n := n) (k := r) (m := r + 1) (p := ∞) (Ω := Omega) (by omega) (B i)
        let Cprev : W^{r,∞}(Omega) :=
          lowerOrderCLM (n := n) (k := r) (m := r + 1) (p := ∞) (Ω := Omega) (by omega) C
        let Fprev : W^{r,2}(Omega) :=
          lowerOrderCLM (n := n) (k := r) (m := r + 1) (p := 2) (Ω := Omega) (by omega) F
        obtain ⟨U, hU⟩ := ih r (by omega) (fun i ↦ (hChart i).of_le (by gcongr; omega))
          (fun i ↦ (hChartSymm i).of_le (by gcongr; omega)) Aprev
          (fun i j ↦ by simpa [Aprev] using haRep i j)
          (fun i j ↦ (haContDiff i j).of_le (by gcongr; omega)) Bprev Cprev Fprev u
          (by simpa [Aprev, Bprev, Cprev, Fprev] using hu)
        exact exists_of_weak_shifted_full_divergence_solution_of_previous
          (by omega) _ B C lambda F u hu U hU fun G hG ↦
            exists_global_higherOrder_of_isWeakDivergenceSolution (r + 1) hOmega hChart hChartSymm
              A a haRep haContDiff G u hG alpha halpha hElliptic

end globalHigherRegularity

end SobolevSpace.GraphSpace.BoundaryRegularity
