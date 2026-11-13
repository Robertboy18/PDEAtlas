/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Elliptic.Regularity.HigherOrder.DifferentiatedEquation
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder

/-!
# Principal higher-order elliptic induction

This is the successor step of the higher-order regularity argument for the principal divergence-form
operator. If the coefficients lie in `W^{r+2,∞}`, the forcing lies in `H^{r+1}`, and a weak solution
already has an `H^{r+2}` representative, then the equation differentiated once in a coordinate
direction has an `H^r` forcing (`exists_coordinateDerivative_higherOrder_weakEquation_identity`).
The commutator is `D_i ((D_k A_ij) (D_j u))`, and its Sobolev order follows from the arbitrary-order
`W^{r+1,∞} * H^{r+1}` multiplier theorem.

Applying an order-`r` principal regularity theorem to every differentiated equation and assembling
the resulting first derivatives promotes the solution from `H^{r+2}` to `H^{r+3}`
(`exists_principal_higherOrder_succ_of_previous_of_firstDerivatives_zeroTrace`). This needs every
first derivative to have zero trace. On a Dirichlet boundary only the tangential derivatives have
zero trace, and the normal derivatives are recovered from the equation instead, as in step 4 of the
proof of Evans's §6.3.2, Theorem 5. For that use, the identity imposes no boundary condition on the
differentiated function.

## How it works

In the proof of Evans's §6.3.1, Theorem 2, the derivative `ũ = D^α u` with `|α| = m + 1` solves
`Lũ = f̃` with the forcing (36), and Theorem 1, the `H²` theorem, applies to `ũ`. We differentiate
only once, and our commutator is the case `|α| = 1` of (36) without lower-order terms.
`exists_coordinateDerivative_higherOrder_weakEquation_solution` makes each `D_k u` a zero-trace weak
solution with `H^r` forcing, the order-`r` theorem gives `D_k u ∈ H^{r+2}`, and
`exists_succOrder_of_firstDerivatives` assembles the first derivatives into `u ∈ H^{r+3}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 2 (Higher interior regularity) and its proof,
  (33)-(37), pp. 332-333; §6.3.2, step 4 of the proof of Theorem 5 (Higher boundary regularity),
  (91)-(94), pp. 342-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {n r : ℕ} {Omega : Set (ℝ^n)}

/--
The equation for one coordinate derivative has an `H^r` forcing.

This is the differentiated-forcing calculation used by the arbitrary-order
principal induction. No boundary condition is imposed on the selected
derivative: the returned identity is tested only against compactly supported
smooth functions.
-/
theorem exists_coordinateDerivative_higherOrder_weakEquation_identity
    (hOpen : IsOpen Omega)
    (A : Fin n → Fin n → W^{r + 2,∞}(Omega))
    (F : W^{r + 1,2}(Omega))
    (U : W^{r + 2,2}(Omega))
    (k : Fin n)
    (htrace0 :
      lowerOrderCLM
          (n := n) (p := 2) (Ω := Omega) (by omega) U ∈
        (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (r + 2) ∞ Omega)
          (baseIndex n (r + 2)) : DerivLp n ∞ Omega))
      ((F : WkpAmbientOn n (r + 1) 2 Omega)
        (baseIndex n (r + 1)) : DerivLp n 2 Omega)
      ⟨lowerOrderCLM
          (n := n) (p := 2) (Ω := Omega) (by omega) U,
        htrace0⟩) :
    ∃ G : W^{r,2}(Omega), ∀ phi : TestFunctionOn n Omega,
      (∑ i : Fin n, ∑ j : Fin n,
        ∫ x,
          (((A i j : WkpAmbientOn n (r + 2) ∞ Omega)
            (baseIndex n (r + 2)) : DerivLp n ∞ Omega) :
              ℝ^n → ℝ) x *
          ((((derivativeWordCLM
              (n := n) (m := r + 2) (r := 1) (p := 2) (Ω := Omega)
              [k] (by simp) U : W^{1,2}(Omega)) :
                WkpAmbientOn n 1 2 Omega) (singleDerivIndex n j) :
                  DerivLp n 2 Omega) : ℝ^n → ℝ) x *
          (∂[i] phi.1.toFun) x
        ∂domainMeasure n Omega) =
      ∫ x,
        ((((G : WkpAmbientOn n r 2 Omega) (baseIndex n r) :
          DerivLp n 2 Omega) : ℝ^n → ℝ) x) * phi.1.toFun x
        ∂domainMeasure n Omega := by
  classical
  let U0 : W^{1,2}(Omega) := lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega) U
  let Uk : W^{1,2}(Omega) :=
    derivativeWordCLM (n := n) (m := r + 2) (r := 1) (p := 2) (Ω := Omega) [k] (by simp) U
  let Uj1 (j : Fin n) : W^{1,2}(Omega) := derivativeWordCLM (n := n) (m := r + 2) (r := 1) (p := 2)
    (Ω := Omega) [j] (by simp only [List.length_singleton]; omega) U
  let Uj (j : Fin n) : W^{r + 1,2}(Omega) := derivativeWordCLM (n := n) (m := r + 2) (r := r + 1)
    (p := 2) (Ω := Omega) [j] (by simp only [List.length_singleton]; omega) U
  let A0 (i j : Fin n) : W^{1,∞}(Omega) :=
    lowerOrderCLM (n := n) (p := ∞) (Ω := Omega) (by omega) (A i j)
  let Ak1 (i j : Fin n) : W^{1,∞}(Omega) := derivativeWordCLM (n := n) (m := r + 2) (r := 1)
    (p := ∞) (Ω := Omega) [k] (by simp only [List.length_singleton]; omega) (A i j)
  let Ak (i j : Fin n) : W^{r + 1,∞}(Omega) := derivativeWordCLM (n := n) (m := r + 2)
    (r := r + 1) (p := ∞) (Ω := Omega) [k] (by simp only [List.length_singleton]; omega) (A i j)
  let Fk : W^{r,2}(Omega) := derivativeWordCLM (n := n) (m := r + 1) (r := r) (p := 2)
    (Ω := Omega) [k] (by simp only [List.length_singleton]; omega) F
  let u : H¹₀(Omega) := ⟨U0, htrace0⟩
  let w : H¹(Omega) := Uk
  let a : Fin n → Fin n → DerivLp n ∞ Omega := fun i j ↦
    ((A i j : WkpAmbientOn n (r + 2) ∞ Omega) (baseIndex n (r + 2)) : DerivLp n ∞ Omega)
  let da : Fin n → Fin n → DerivLp n ∞ Omega := fun i j ↦
    ((Ak1 i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) : DerivLp n ∞ Omega)
  let f : DerivLp n 2 Omega :=
    ((F : WkpAmbientOn n (r + 1) 2 Omega) (baseIndex n (r + 1)) : DerivLp n 2 Omega)
  let df : DerivLp n 2 Omega :=
    ((Fk : WkpAmbientOn n r 2 Omega) (baseIndex n r) : DerivLp n 2 Omega)
  have hf : HasWeakDerivativeOn (n := n) Omega [k] (f : ℝ^n → ℝ) (df : ℝ^n → ℝ) := by
    simpa [f, df, Fk] using F.property.hasWeakDerivativeOn_first (by omega) k
  have hmixed (j : Fin n) :
      ((Uj1 j : WkpAmbientOn n 1 2 Omega) (singleDerivIndex n k) : DerivLp n 2 Omega) =
        ((w : WkpAmbientOn n 1 2 Omega) (singleDerivIndex n j) : DerivLp n 2 Omega) := by
    change ((U : WkpAmbientOn n (r + 2) 2 Omega) (derivativeWordIndex (n := n) (m := r + 2)
        (r := 1) [j] (by simp) (singleDerivIndex n k)) : DerivLp n 2 Omega) =
      ((U : WkpAmbientOn n (r + 2) 2 Omega) (derivativeWordIndex (n := n) (m := r + 2) (r := 1)
        [k] (by simp) (singleDerivIndex n j)) : DerivLp n 2 Omega)
    rw [show derivativeWordIndex (n := n) (m := r + 2) (r := 1) [j] (by simp)
        (singleDerivIndex n k) = derivativeWordIndex (n := n) (m := r + 2) (r := 1) [k] (by simp)
          (singleDerivIndex n j) by
      simpa using derivativeWordIndex_singleDerivIndex_comm (n := n) (m := r + 2) j k (by omega)]
  have hduk (j : Fin n) : HasWeakDerivativeOn (n := n) Omega [k]
      (derivCoordCLM (n := n) (Ω := Omega) j u : ℝ^n → ℝ)
      (((w : WkpAmbientOn n 1 2 Omega) (singleDerivIndex n j) : DerivLp n 2 Omega) : ℝ^n → ℝ) := by
    rw [← hmixed j]
    simpa [u, U0, Uj1, derivCoordCLM_apply, firstDerivIndex_one, derivIndexOfList_singleton] using
      (Uj1 j).property.hasWeakDerivativeOn_first (by norm_num) k
  have hflux (i j : Fin n) : HasWeakDerivativeOn (n := n) Omega [k]
      (fun x ↦ (a i j : ℝ^n → ℝ) x * (derivCoordCLM (n := n) (Ω := Omega) j u : ℝ^n → ℝ) x)
      (fun x ↦ (a i j : ℝ^n → ℝ) x * (((w : WkpAmbientOn n 1 2 Omega) (singleDerivIndex n j) :
          DerivLp n 2 Omega) : ℝ^n → ℝ) x +
        (da i j : ℝ^n → ℝ) x * (derivCoordCLM (n := n) (Ω := Omega) j u : ℝ^n → ℝ) x) := by
    simpa [a, da, A0, Ak1, derivIndexOfList_singleton] using
      (A0 i j).hasWeakDerivativeOn_mul_W1Top_first hOpen k
        (derivCoordCLM (n := n) (Ω := Omega) j u)
        ((w : WkpAmbientOn n 1 2 Omega) (singleDerivIndex n j)) (hduk j)
  let P (i j : Fin n) : W^{r + 1,2}(Omega) :=
    wkTopProduct (n := n) (Ω := Omega) (by simp) hOpen (Ak i j) (Uj j)
  let Q (i j : Fin n) : W^{r,2}(Omega) := derivativeWordCLM (n := n) (m := r + 1) (r := r) (p := 2)
    (Ω := Omega) [i] (by simp only [List.length_singleton]; omega) (P i j)
  let dq (i j : Fin n) : DerivLp n 2 Omega :=
    ((Q i j : WkpAmbientOn n r 2 Omega) (baseIndex n r) : DerivLp n 2 Omega)
  have hcomm (i j : Fin n) : HasWeakDerivativeOn (n := n) Omega [i]
      (fun x ↦ (da i j : ℝ^n → ℝ) x * (derivCoordCLM (n := n) (Ω := Omega) j u : ℝ^n → ℝ) x)
      (dq i j : ℝ^n → ℝ) := by
    have hPsource : baseRepresentative (P i j) =ᵐ[domainMeasure n Omega] fun x ↦
        (da i j : ℝ^n → ℝ) x * (derivCoordCLM (n := n) (Ω := Omega) j u : ℝ^n → ℝ) x := by
      simpa [baseRepresentative, da, Ak1, Ak, Uj, u, U0, derivCoordCLM_apply,
        derivativeWordCLM_apply, derivIndexOfList_singleton] using
        wkTopProduct_base_ae (n := n) (Ω := Omega) (by simp) hOpen (Ak i j) (Uj j)
    simpa [dq, Q] using
      ((P i j).property.hasWeakDerivativeOn_first (by omega) i).congr_ae hPsource .rfl
  let G : W^{r,2}(Omega) := Fk + ∑ i : Fin n, ∑ j : Fin n, Q i j
  let g : DerivLp n 2 Omega :=
    ((G : WkpAmbientOn n r 2 Omega) (baseIndex n r) : DerivLp n 2 Omega)
  have hg : (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Omega] fun x ↦
      (df : ℝ^n → ℝ) x + ∑ i : Fin n, ∑ j : Fin n, (dq i j : ℝ^n → ℝ) x := by
    rw [show g = df + ∑ i : Fin n, ∑ j : Fin n, dq i j by simp [g, G, df, dq]]
    filter_upwards [Lp.coeFn_add df _, Lp.coeFn_fun_finsetSum _ fun i ↦ ∑ j : Fin n, dq i j,
      ae_all_iff.2 fun i ↦ Lp.coeFn_fun_finsetSum Finset.univ (dq i)] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2]
    simp only [h3]
  refine ⟨G, ?_⟩
  have hidentity := IsWeakDivergenceSolution.coordinateDerivative a da f df g u
    w k (by simpa [a, f, u, U0] using hu) hf hflux dq hcomm hg
  have hUk (j : Fin n) : ((Uk : WkpAmbientOn n 1 2 Omega) (singleDerivIndex n j) :
      DerivLp n 2 Omega) = ((U : WkpAmbientOn n (r + 2) 2 Omega) (derivativeWordIndex (n := n)
        (m := r + 2) (r := 1) [k] (by simp) (singleDerivIndex n j)) : DerivLp n 2 Omega) :=
    derivativeWordCLM_apply (n := n) (m := r + 2) (r := 1) (p := 2) (Ω := Omega) [k] (by simp) U
      (singleDerivIndex n j)
  simp only [w] at hidentity
  simp_rw [hUk] at hidentity
  simpa [a, g] using hidentity

/--
One coordinate derivative, equipped with zero trace, is a weak solution with
`H^r` forcing.

This is the typed counterpart of
`exists_coordinateDerivative_higherOrder_weakEquation_identity`.  The identity
remains available for normal-flux arguments, where the coordinate derivative
need not satisfy a Dirichlet condition.
-/
theorem exists_coordinateDerivative_higherOrder_weakEquation_solution
    (hOpen : IsOpen Omega)
    (A : Fin n → Fin n → W^{r + 2,∞}(Omega))
    (F : W^{r + 1,2}(Omega))
    (U : W^{r + 2,2}(Omega))
    (k : Fin n)
    (htrace0 :
      lowerOrderCLM
          (n := n) (p := 2) (Ω := Omega) (by omega) U ∈
        (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule)
    (htrace :
      derivativeWordCLM
          (n := n) (m := r + 2) (r := 1) (p := 2) (Ω := Omega)
          [k] (by simp) U ∈
        (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (r + 2) ∞ Omega)
          (baseIndex n (r + 2)) : DerivLp n ∞ Omega))
      ((F : WkpAmbientOn n (r + 1) 2 Omega)
        (baseIndex n (r + 1)) : DerivLp n 2 Omega)
      ⟨lowerOrderCLM
          (n := n) (p := 2) (Ω := Omega) (by omega) U,
        htrace0⟩) :
    ∃ G : W^{r,2}(Omega),
      IsWeakDivergenceSolution
        (n := n) (Ω := Omega)
        (fun i j ↦
          ((lowerOrderCLM
              (n := n) (k := r + 1) (m := r + 2) (p := ∞)
              (Ω := Omega) (by simp) (A i j) :
                WkpAmbientOn n (r + 1) ∞ Omega)
            (baseIndex n (r + 1)) : DerivLp n ∞ Omega))
        ((G : WkpAmbientOn n r 2 Omega)
          (baseIndex n r) : DerivLp n 2 Omega)
        ⟨derivativeWordCLM
            (n := n) (m := r + 2) (r := 1) (p := 2) (Ω := Omega)
            [k] (by simp) U,
          htrace⟩ := by
  obtain ⟨G, hG⟩ := exists_coordinateDerivative_higherOrder_weakEquation_identity hOpen A F U k
    htrace0 hu
  exact ⟨G, hOpen, fun phi ↦ by
    simpa [derivCoordCLM_apply, derivativeWordCLM_apply, derivIndexOfList_singleton] using hG phi⟩

/--
Successor step for principal higher regularity.

Assume the principal regularity theorem at forcing order `r`: every
zero-trace weak solution with `H^r` forcing has an `H^{r+2}`
representative. For data one order smoother, a given `H^{r+2}`
representative whose first coordinate derivatives have zero trace is
promoted to `H^{r+3}`.

The hypothesis `hprevious` is exactly the preceding-order theorem.  The
current-order conclusion is obtained by differentiating the equation,
applying `hprevious` to the resulting `H^r` forcings, and using
`exists_succOrder_of_firstDerivatives`; it is not assumed.
-/
theorem exists_principal_higherOrder_succ_of_previous_of_firstDerivatives_zeroTrace
    (hOpen : IsOpen Omega)
    (A : Fin n → Fin n → W^{r + 2,∞}(Omega))
    (F : W^{r + 1,2}(Omega))
    (U : W^{r + 2,2}(Omega))
    (htrace0 :
      lowerOrderCLM
          (n := n) (p := 2) (Ω := Omega) (by omega) U ∈
        (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule)
    (htrace : ∀ k : Fin n,
      derivativeWordCLM
          (n := n) (m := r + 2) (r := 1) (p := 2) (Ω := Omega)
          [k] (by simp) U ∈
        (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule)
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (r + 2) ∞ Omega)
          (baseIndex n (r + 2)) : DerivLp n ∞ Omega))
      ((F : WkpAmbientOn n (r + 1) 2 Omega)
        (baseIndex n (r + 1)) : DerivLp n 2 Omega)
      ⟨lowerOrderCLM
          (n := n) (p := 2) (Ω := Omega) (by omega) U,
        htrace0⟩)
    (hprevious :
      ∀ (G : W^{r,2}(Omega))
        (v : H¹₀(Omega)),
        IsWeakDivergenceSolution
          (n := n) (Ω := Omega)
          (fun i j ↦
            ((lowerOrderCLM
                (n := n) (k := r + 1) (m := r + 2) (p := ∞)
                (Ω := Omega) (by simp) (A i j) :
                  WkpAmbientOn n (r + 1) ∞ Omega)
              (baseIndex n (r + 1)) : DerivLp n ∞ Omega))
          ((G : WkpAmbientOn n r 2 Omega)
            (baseIndex n r) : DerivLp n 2 Omega)
          v →
        ∃ V : W^{r + 2,2}(Omega),
          ⇑((V : WkpAmbientOn n (r + 2) 2 Omega)
              (baseIndex n (r + 2)) : DerivLp n 2 Omega)
            =ᵐ[domainMeasure n Omega]
              ⇑(((v : H¹(Omega)) :
                WkpAmbientOn n 1 2 Omega) (baseIndex n 1) :
                  DerivLp n 2 Omega)) :
    ∃ W : W^{r + 3,2}(Omega),
      ⇑((W : WkpAmbientOn n (r + 3) 2 Omega)
          (baseIndex n (r + 3)) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          ⇑((U : WkpAmbientOn n (r + 2) 2 Omega)
            (baseIndex n (r + 2)) : DerivLp n 2 Omega) := by
  classical
  choose G hG using fun k : Fin n ↦ exists_coordinateDerivative_higherOrder_weakEquation_solution
    hOpen A F U k htrace0 (htrace k) hu
  choose V hV using fun k : Fin n ↦ hprevious (G k) ⟨_, htrace k⟩ (hG k)
  simpa [Nat.add_assoc] using exists_succOrder_of_firstDerivatives (n := n) (m := r + 2) (p := 2)
    (Ω := Omega) (by simp) U V fun k ↦ Lp.ext (by simpa using hV k)

end SobolevSpace.GraphSpace.BoundaryRegularity
