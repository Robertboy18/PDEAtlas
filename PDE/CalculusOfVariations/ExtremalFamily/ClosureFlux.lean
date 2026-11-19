/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtremalFamily.Flux
public import PDE.Analysis.Calculus.Jet.Composition

/-!
# Continuous closure extensions of the extremal-family flux

The first two closure jets of the family and Lagrangian give continuous
extensions of the velocity-momentum flux and its spatial derivatives. Only the
interior derivatives are identified with ordinary Fréchet derivatives.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.ExtremalFamily

open Analysis Noether

/-- Restrict a differential in space and parameter to its spatial Jacobian. -/
def familySpatialJacobian {n m : ℕ} :
    ((ℝ^n × ℝ) →L[ℝ] ℝ^m) →L[ℝ] Matrix (Fin m) (Fin n) ℝ :=
  ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.pi fun i ↦
    (EuclideanSpace.proj k).comp
      (ContinuousLinearMap.apply ℝ (ℝ^m) (EuclideanSpace.single i 1, 0))

/-- A continuous second closure jet determines the spatial Jacobian in the interior. -/
theorem familySpatialJacobian_first_eq {n m : ℕ} {Ω : Set (ℝ^n)} {J : Set ℝ}
    {U : ℝ → ℝ^n → ℝ^m}
    (hU : ContinuousSecondJetOn (fun p : ℝ^n × ℝ ↦ U p.2 p.1) (Ω ×ˢ J))
    (hopen : IsOpen Ω) (hJ : IsOpen J) {x : ℝ^n} {t : ℝ}
    (hx : x ∈ Ω) (ht : t ∈ J) :
    familySpatialJacobian (hU.first (x, t)) = jacobianMatrix (U t) x := by
  have hd := (hU.hasFDerivAt (hopen.prod hJ) ⟨hx, ht⟩).comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  dsimp only [Function.comp_def] at hd
  ext k i
  change hU.first (x, t) (EuclideanSpace.single i 1, 0) k = _
  erw [jacobianMatrix_apply_eq_fderiv hd.differentiableAt, hd.fderiv]
  rfl

/-- Closure jets provide a flux and continuous extensions of all spatial partials.
The witnesses agree with the family flux throughout the open domain. -/
theorem exists_familyFlux_coordinate_extensions
    {n m : ℕ} {Ω : Set (ℝ^n)} {J : Set ℝ}
    {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ} {U : ℝ → ℝ^n → ℝ^m}
    (hopen : IsOpen Ω) (hJ : IsOpen J)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hU : ContinuousSecondJetOn (fun p : ℝ^n × ℝ ↦ U p.2 p.1) (Ω ×ˢ J)) :
    ∃ (H : Fin n → ℝ^n × ℝ → ℝ) (D : Fin n → Fin n → ℝ^n × ℝ → ℝ),
      (∀ j, ContinuousOn (H j) (closure Ω ×ˢ J)) ∧
      (∀ i j, ContinuousOn (D i j) (closure Ω ×ˢ J)) ∧
      (∀ j x, x ∈ Ω → ∀ t ∈ J, ContDiffAt ℝ 1 (H j) (x, t)) ∧
      (∀ j x, x ∈ Ω → ∀ t ∈ J, H j (x, t) = familyFlux L U t x j) ∧
      (∀ i j x, x ∈ Ω → ∀ t ∈ J,
        D i j (x, t) = fderiv ℝ (H j) (x, t) (EuclideanSpace.single i 1, 0)) := by
  let S := Ω ×ˢ J
  let C := closure Ω ×ˢ J
  let Q := Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n)
  let G (p : ℝ^n × ℝ) : Q :=
    (familySpatialJacobian (hU.first p), (U p.2 p.1, p.1))
  let G' (p : ℝ^n × ℝ) : (ℝ^n × ℝ) →L[ℝ] Q :=
    (familySpatialJacobian.comp (hU.second p)).prod
      ((hU.first p).prod (ContinuousLinearMap.fst ℝ (ℝ^n) ℝ))
  let e (k : Fin m) (j : Fin n) : Q := (Matrix.single k j 1, (0, 0))
  let H (j : Fin n) (p : ℝ^n × ℝ) : ℝ :=
    ∑ k, hU.first p (0, 1) k * hL.first (G p) (e k j)
  let D (i j : Fin n) (p : ℝ^n × ℝ) : ℝ := ∑ k, (
    hU.second p (EuclideanSpace.single i 1, 0) (0, 1) k * hL.first (G p) (e k j) +
      hU.first p (0, 1) k *
        hL.second (G p) (G' p (EuclideanSpace.single i 1, 0)) (e k j))
  have hS : IsOpen S := hopen.prod hJ
  have hSL : IsOpen {a : Q | a.2.2 ∈ Ω} :=
    hopen.preimage (continuous_snd.comp continuous_snd)
  have hC : C ⊆ closure S := by
    intro p hp
    rw [closure_prod_eq]
    exact ⟨hp.1, subset_closure hp.2⟩
  have hAc := hU.continuousOn_first.mono hC
  have hBc := hU.continuousOn_second.mono hC
  have hGc : ContinuousOn G C :=
    (familySpatialJacobian.continuous.comp_continuousOn hAc).prodMk
      ((hU.continuousOn.mono hC).prodMk continuousOn_fst)
  have hGmap : MapsTo G S {a : Q | a.2.2 ∈ Ω} := fun _ hp ↦ hp.1
  have hGcl : MapsTo G C (closure {a : Q | a.2.2 ∈ Ω}) := by
    intro p hp
    have heq : {a : Q | a.2.2 ∈ Ω} = univ ×ˢ (univ ×ˢ Ω) := by
      ext a
      change a.2.2 ∈ Ω ↔ (a.1 ∈ univ ∧ a.2.1 ∈ univ ∧ a.2.2 ∈ Ω)
      simp
    rw [heq, closure_prod_eq, closure_prod_eq, closure_univ, closure_univ]
    exact ⟨mem_univ _, mem_univ _, hp.1⟩
  have hPc := hL.continuousOn_first.comp hGc hGcl
  have hRc := hL.continuousOn_second.comp hGc hGcl
  have hA : ContDiffOn ℝ 1 hU.first S :=
    (hU.contDiffOn.fderiv_of_isOpen hS (by norm_num)).congr hU.first_eq
  have hG : ContDiffOn ℝ 1 G S :=
    (familySpatialJacobian.contDiff.comp_contDiffOn hA).prodMk
      ((hU.contDiffOn.of_le (by norm_num)).prodMk contDiffOn_fst)
  have hP : ContDiffOn ℝ 1 (fun p ↦ hL.first (G p)) S :=
    ((hL.contDiffOn.fderiv_of_isOpen hSL (by norm_num)).congr hL.first_eq).comp hG hGmap
  have hHd (j : Fin n) : ContDiffOn ℝ 1 (H j) S := by
    apply ContDiffOn.sum
    intro k _
    exact ((EuclideanSpace.proj k).contDiff.comp_contDiffOn
      (hA.clm_apply contDiffOn_const)).mul (hP.clm_apply contDiffOn_const)
  refine ⟨H, D, ?_, ?_, (fun j x hx t ht ↦ (hHd j).contDiffAt (hS.mem_nhds ⟨hx, ht⟩)),
    ?_, ?_⟩
  · intro j
    apply continuousOn_finsetSum
    intro k _
    exact ((EuclideanSpace.proj k).continuous.comp_continuousOn
      (hAc.clm_apply continuousOn_const)).mul (hPc.clm_apply continuousOn_const)
  · intro i j
    have hGi : ContinuousOn (fun p ↦ G' p (EuclideanSpace.single i 1, 0)) C :=
      (familySpatialJacobian.continuous.comp_continuousOn
        (hBc.clm_apply continuousOn_const)).prodMk
          ((hAc.clm_apply continuousOn_const).prodMk continuousOn_const)
    apply continuousOn_finsetSum
    intro k _
    exact (((EuclideanSpace.proj k).continuous.comp_continuousOn
      ((hBc.clm_apply continuousOn_const).clm_apply continuousOn_const)).mul
        (hPc.clm_apply continuousOn_const)).add
      (((EuclideanSpace.proj k).continuous.comp_continuousOn
        (hAc.clm_apply continuousOn_const)).mul
          ((hRc.clm_apply hGi).clm_apply continuousOn_const))
  · intro j x hx t ht
    have hGx : G (x, t) = (jacobianMatrix (U t) x, (U t x, x)) := by
      dsimp only [G]
      rw [familySpatialJacobian_first_eq hU hopen hJ hx ht]
    have hv : hU.first (x, t) (0, 1) = deriv (fun s ↦ U s x) t := by
      have hd := (hU.hasFDerivAt hS ⟨hx, ht⟩).comp_hasDerivAt t
        ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
      exact hd.deriv.symm
    have hp (k : Fin m) : hL.first (G (x, t)) (e k j) = momentum L (U t) k j x := by
      rw [hL.first_eq (hGmap ⟨hx, ht⟩), hGx]
      exact (fderiv_lagrangian_matrix_apply
        (hL.hasFDerivAt hSL (show (jacobianMatrix (U t) x, (U t x, x)) ∈
          {a : Q | a.2.2 ∈ Ω} from hx)).differentiableAt (Matrix.single k j 1)).symm
    simp [H, familyFlux, noetherCurrent, hv, hp, mul_comm]
  · intro i j x hx t ht
    have hdA := hU.hasFDerivAt_first hS (show (x, t) ∈ S from ⟨hx, ht⟩)
    have hdU := hU.hasFDerivAt hS (show (x, t) ∈ S from ⟨hx, ht⟩)
    have hdG : HasFDerivAt G (G' (x, t)) (x, t) :=
      (familySpatialJacobian.hasFDerivAt.comp (x, t) hdA).prodMk
        (hdU.prodMk hasFDerivAt_fst)
    have hdP := (hL.hasFDerivAt_first hSL (hGmap ⟨hx, ht⟩)).comp (x, t) hdG
    have hd (k : Fin m) :=
      ((EuclideanSpace.proj k).hasFDerivAt.comp (x, t)
        (hdA.clm_apply (hasFDerivAt_const (0, 1) (x, t)))).mul
          (hdP.clm_apply (hasFDerivAt_const (e k j) (x, t)))
    have hdH := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦ hd k)
    change _ = fderiv ℝ (fun p ↦ ∑ k, hU.first p (0, 1) k * hL.first (G p) (e k j))
      (x, t) (EuclideanSpace.single i 1, 0)
    dsimp only [Function.comp_def, Pi.mul_apply] at hdH
    erw [hdH.fderiv]
    simp only [D, sum_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add, smul_eq_mul]
    congr 1
    funext k
    change _ = hU.first (x, t) (0, 1) k *
      (hL.first (G (x, t)) 0 + hL.second (G (x, t))
        (G' (x, t) (EuclideanSpace.single i 1, 0)) (e k j)) +
      hL.first (G (x, t)) (e k j) *
        hU.second (x, t) (EuclideanSpace.single i 1, 0) (0, 1) k
    rw [map_zero, zero_add]
    ring

end PDE.CalculusOfVariations.ExtremalFamily
