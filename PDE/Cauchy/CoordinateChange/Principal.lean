/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Jet.CoordinateChange
public import PDE.Analysis.Geometry.Hypersurface.Analytic

/-!
# Highest derivatives under an analytic coordinate change

The highest outer derivative occurs linearly in the finite composition
formula. Setting its row to zero leaves a remainder depending only on lower
jets. Expanding the highest row in the coordinate basis gives every
transformed principal coefficient, including the pure transverse coefficient. Compare the
computation of `b_(0,…,0,k)` in Evans, §4.6.1, proof of Theorem 1, step 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.1(b), Theorem 1 (Cauchy data and
  noncharacteristic surfaces) and its proof, (9)-(12), pp. 235-236.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Analysis.MultiIndex

open scoped Gradient

namespace PDE.Cauchy.Quasilinear.Analytic

variable {n k : ℕ}

/-- Matrix of the transformation on derivatives of one fixed order. Its
entries depend only on the first derivative of the coordinate map. -/
def principalMatrix (c : ℝ^n → ℝ^n) (x : ℝ^n)
    (α β : Sym (Fin n) k) : ℝ :=
  multilinearFromCoordinates n k (Pi.single β 1)
    (fun i ↦ fderiv ℝ c x (directions α i))

/-- The highest transformed derivative with its outer highest row set to
zero. This retains every lower derivative of the outer function. -/
def highestRemainder (c : ℝ^n → ℝ^n) (x : ℝ^n)
    (q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ)
    (α : Sym (Fin n) k) : ℝ :=
  transport n (k + 1) (Fin.snoc q 0) (jetLT ℝ (k + 1) c x) (Fin.last k) α

/-- The top row of the coordinate composition formula is affine in the
outer highest derivatives. The remainder depends only on the lower jet of `u`. -/
theorem coordinateDeriv_comp_eq {c : ℝ^n → ℝ^n} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hk : 0 < k) (hc : AnalyticAt ℝ c x) (hu : AnalyticAt ℝ u (c x))
    (α : Sym (Fin n) k) :
    coordinateDeriv α (u ∘ c) x =
      highestRemainder c x (coordinateJetLT k u (c x)) α +
        ∑ β, principalMatrix c x α β * coordinateDeriv β u (c x) := by
  classical
  let q := coordinateJetLT (k + 1) u (c x)
  let r : ∀ j : Fin (k + 1), Sym (Fin n) (j : ℕ) → ℝ :=
    Fin.snoc (coordinateJetLT k u (c x)) 0
  have hqr (i : Fin (k + 1)) (hi : (i : ℕ) < k) :
      fromCoordinates n (k + 1) q i = fromCoordinates n (k + 1) r i := by
    induction i using Fin.lastCases with
    | last => exact False.elim (Nat.lt_irrefl k hi)
    | cast i =>
      simp only [q, r, fromCoordinates, ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Fin.snoc_castSucc]
      rfl
  have h := PDE.Analysis.Jet.compose_sub_of_lower_eq
    (fromCoordinates n (k + 1) q) (fromCoordinates n (k + 1) r)
    (jetLT ℝ (k + 1) c x) (Fin.last k) hk hqr (directions α)
  change transport n (k + 1) q (jetLT ℝ (k + 1) c x) (Fin.last k) α -
      highestRemainder c x (coordinateJetLT k u (c x)) α =
    (multilinearFromCoordinates n k (q (Fin.last k)) -
      multilinearFromCoordinates n k (r (Fin.last k)))
      (fun i ↦ iteratedFDeriv ℝ 1 c x (fun _ ↦ directions α i)) at h
  have hr : r (Fin.last k) = 0 := Fin.snoc_last _ _
  rw [hr, map_zero, sub_zero] at h
  simp only [iteratedFDeriv_one_apply] at h
  have hq : q (Fin.last k) = fun β ↦ coordinateDeriv β u (c x) := rfl
  rw [hq, pi_eq_sum_univ' (fun β ↦ coordinateDeriv β u (c x)), map_sum] at h
  simp only [map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul] at h
  have hactual :
      transport n (k + 1) q (jetLT ℝ (k + 1) c x) (Fin.last k) α =
        coordinateDeriv α (u ∘ c) x :=
    congrFun (congrFun (transport_coordinateJetLT hc hu (k + 1)) (Fin.last k)) α
  rw [hactual] at h
  have hsum :
      (∑ β, coordinateDeriv β u (c x) *
        multilinearFromCoordinates n k (Pi.single β 1)
          (fun i ↦ fderiv ℝ c x (directions α i))) =
        ∑ β, principalMatrix c x α β * coordinateDeriv β u (c x) := by
    apply Finset.sum_congr rfl
    intro β _
    exact mul_comm _ _
  exact (sub_eq_iff_eq_add.mp (h.trans hsum)).trans (add_comm _ _)

/-- When a chart coordinate is the defining function, the corresponding
pure principal entry is the coordinate monomial in its gradient. -/
theorem principalMatrix_replicate {c : ℝ^n → ℝ^n} {φ : ℝ^n → ℝ} {x : ℝ^n}
    (hc : AnalyticAt ℝ c x) (i : Fin n)
    (hlevel : (fun y ↦ c y i) =ᶠ[nhds x] φ) (α : Sym (Fin n) k) :
    principalMatrix c x α (Sym.replicate k i) = monomial α (∇ φ x) := by
  classical
  have hsingle : (Pi.single (Sym.replicate k i) 1 : Sym (Fin n) k → ℝ) =
      (fun β ↦ if β = Sym.replicate k i then 1 else 0) := by
    ext β
    simp [Pi.single_apply]
  rw [principalMatrix, hsingle, multilinearFromCoordinates_single, one_mul,
    monomial_eq_prod_inner]
  have hD := ((EuclideanSpace.proj i).hasFDerivAt.comp x
    hc.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hlevel.symm
  apply Finset.prod_congr rfl
  intro j _
  rw [inner_gradient_left]
  exact congrArg (fun L ↦ L (directions α j)) hD.fderiv.symm

/-- Replacing the gradient by its canonical unit normal multiplies the
principal symbol by the positive gradient norm to the equation order. -/
theorem sum_monomial_gradient {φ : ℝ^n → ℝ} {x : ℝ^n}
    (hreg : fderiv ℝ φ x ≠ 0) (a : Sym (Fin n) k → ℝ) :
    (∑ α, a α * monomial α (∇ φ x)) =
      ‖∇ φ x‖ ^ k *
        ∑ α, a α * monomial α (PDE.Analysis.Hypersurface.levelNormal φ x) := by
  have hm (α : Sym (Fin n) k) :
      monomial α (∇ φ x) =
        ‖∇ φ x‖ ^ k *
          monomial α (PDE.Analysis.Hypersurface.levelNormal φ x) := by
    rw [monomial_eq_prod_inner, monomial_eq_prod_inner]
    simp only [inner_gradient_left,
      PDE.Analysis.Hypersurface.fderiv_eq_norm_mul_inner_levelNormal hreg,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

/-- Every principal-matrix entry is analytic where the coordinate map is
analytic. Only its first derivative enters this matrix. -/
theorem analyticAt_principalMatrix {c : ℝ^n → ℝ^n} {x : ℝ^n}
    (hc : AnalyticAt ℝ c x) (α β : Sym (Fin n) k) :
    AnalyticAt ℝ (fun y ↦ principalMatrix c y α β) x := by
  exact (multilinearFromCoordinates n k (Pi.single β 1)).analyticAt.comp
    (AnalyticAt.pi fun i ↦
      ((ContinuousLinearMap.apply ℝ (ℝ^n) (directions α i)).analyticAt _).comp hc.fderiv)

/-- The highest-derivative remainder is analytic in position and arbitrary
lower coordinate jets. The jet array `q` need not be the jet of a function. -/
theorem analyticAt_highestRemainder {c : ℝ^n → ℝ^n} {x : ℝ^n}
    (hc : AnalyticAt ℝ c x)
    (q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) (α : Sym (Fin n) k) :
    AnalyticAt ℝ (fun z ↦ highestRemainder c z.1 z.2 α) (x, q) := by
  have hcn : AnalyticOnNhd ℝ c {x} := by
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hc
  have hj : AnalyticAt ℝ (jetLT ℝ (k + 1) c) x :=
    AnalyticAt.pi fun j ↦ hcn.iteratedFDeriv j x (Set.mem_singleton _)
  have hs : AnalyticAt ℝ
      (fun q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ ↦
        (Fin.snoc q 0 : ∀ j : Fin (k + 1), Sym (Fin n) (j : ℕ) → ℝ)) q := by
    apply AnalyticAt.pi
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [Fin.snoc_last] using
        (analyticAt_const : AnalyticAt ℝ
          (fun _ : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ ↦
            (0 : Sym (Fin n) k → ℝ)) q)
    · simpa only [Fin.snoc_castSucc, Fin.val_castSucc, id_eq] using
        (analyticAt_pi_iff.mp analyticAt_id i :
          AnalyticAt ℝ (fun q : ∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ ↦ q i) q)
  have hf : AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦ z.1) (x, q) :=
    analyticAt_fst
  have hq : AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦ z.2) (x, q) :=
    analyticAt_snd
  have hin : AnalyticAt ℝ
      (fun z : ℝ^n × (∀ j : Fin k, Sym (Fin n) (j : ℕ) → ℝ) ↦
        ((Fin.snoc z.2 0 : ∀ j : Fin (k + 1), Sym (Fin n) (j : ℕ) → ℝ),
          jetLT ℝ (k + 1) c z.1)) (x, q) :=
    (hs.comp_of_eq hq rfl).prod (hj.comp_of_eq hf rfl)
  have ht := (analyticAt_transport n (k + 1)
    (Fin.snoc q 0, jetLT ℝ (k + 1) c x)).comp_of_eq hin rfl
  exact analyticAt_pi_iff.mp (analyticAt_pi_iff.mp ht (Fin.last k)) α

end PDE.Cauchy.Quasilinear.Analytic
