/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Pointwise
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Joint regularity of Sobolev wave representatives

Continuous time and spatial derivatives give the derivative on spacetime by
the partial derivative criterion. Applying this criterion once more to the
first derivatives establishes joint C² regularity, including the mixed terms.
-/

@[expose] public noncomputable section

open Filter Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ}

/-- The spatial derivative of the canonical representative, expressed in the
standard Euclidean coordinates by the representatives of its weak derivatives. -/
theorem hasFDerivAt_classicalRepresentative (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (q : W^{k + 1,2}(ℝ^n)) (x : ℝ^n) :
    HasFDerivAt (classicalRepresentativeCLM hq q : ℝ^n → ℝ) (∑ i : Fin n, classicalRepresentativeCLM
      hk (partialDerivCLM i q) x • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x := by
  have hd := (contDiff_classicalRepresentativeCLM (r := 1) hq
    (by simpa using hq) q).differentiable one_ne_zero x
  convert hd.hasFDerivAt using 1
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext fun i ↦ ?_
  symm
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change ∂[i] (classicalRepresentativeCLM hq q : ℝ^n → ℝ) x = _
  rw [partialDeriv_classicalRepresentative hq hk]
  simp [EuclideanSpace.coe_proj]

/-- On an open time interval, smooth time and spatial derivative fields yield
one further joint derivative. -/
theorem contDiffOn_succ_of_spaceTime_derivatives {r : ℕ} {s : Set ℝ} (hs : IsOpen s)
    {q v : ℝ × ℝ^n → ℝ} {d : Fin n → ℝ × ℝ^n → ℝ}
    (ht : ∀ t ∈ s, ∀ x, HasDerivAt (fun a ↦ q (a, x)) (v (t, x)) t)
    (hx : ∀ t ∈ s, ∀ x,
      HasFDerivAt (fun y ↦ q (t, y)) (∑ i, d i (t, x) • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)) x)
    (hv : ContDiffOn ℝ r v (s ×ˢ univ)) (hd : ∀ i, ContDiffOn ℝ r (d i) (s ×ˢ univ)) :
    ContDiffOn ℝ (r + 1) q (s ×ˢ univ) := by
  let A := fun p : ℝ × ℝ^n ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (v p)
  let B := fun p : ℝ × ℝ^n ↦ ∑ i, d i p • (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)
  have hA : ContDiffOn ℝ r A (s ×ˢ univ) := contDiffOn_const.smulRight hv
  have hB : ContDiffOn ℝ r B (s ×ˢ univ) := ContDiffOn.sum (fun i _ ↦ (hd i).smul contDiffOn_const)
  let J := fun p : ℝ × ℝ^n ↦ (A p).comp (ContinuousLinearMap.fst ℝ ℝ (ℝ^n)) +
      (B p).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ^n))
  have hJ : ContDiffOn ℝ r J (s ×ˢ univ) :=
    (hA.clm_comp contDiffOn_const).add (hB.clm_comp contDiffOn_const)
  rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hs.prod isOpen_univ).uniqueDiffOn]
  refine ⟨by simp, J, hJ, fun p hp ↦ ?_⟩
  have hneigh := (hs.prod isOpen_univ).mem_nhds hp
  have hpartial := hasStrictFDerivAt_uncurry_coprod (f := fun t x ↦ q (t, x))
    (f₁ := fun t x ↦ A (t, x)) (f₂ := fun t x ↦ B (t, x))
    (by
      filter_upwards [hneigh] with z hz using (ht z.1 hz.1 z.2).hasFDerivAt)
    (by
      filter_upwards [hneigh] with z hz using hx z.1 hz.1 z.2) (hA.continuousOn.continuousAt hneigh)
    (hB.continuousOn.continuousAt hneigh)
  exact hpartial.hasFDerivAt.hasFDerivWithinAt

/-- A continuous Hᵏ⁺¹ curve with a jointly continuous pointwise time derivative
has a jointly C¹ canonical representative above the Sobolev threshold. -/
theorem contDiffOn_one_classicalRepresentative (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (q : C(ℝ, W^{k + 1,2}(ℝ^n))) {v : ℝ × ℝ^n → ℝ}
    {s : Set ℝ} (hs : IsOpen s) (hv : ContinuousOn v (s ×ˢ univ))
    (ht : ∀ t ∈ s, ∀ x, HasDerivAt (fun a ↦ classicalRepresentativeCLM hq (q a) x) (v (t, x)) t) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hq (q p.1) p.2) (s ×ˢ univ) := by
  apply contDiffOn_succ_of_spaceTime_derivatives (r := 0)
    (d := fun i p ↦ classicalRepresentativeCLM hk (partialDerivCLM i (q p.1)) p.2) hs ht
    (fun t _ x ↦ hasFDerivAt_classicalRepresentative hk hq (q t) x)
  · exact contDiffOn_zero.mpr hv
  · exact fun i ↦ contDiffOn_zero.mpr (continuous_classicalRepresentativeCLM hk
        ((partialDerivCLM i).continuous.comp q.continuous)).continuousOn

/-- A higher Sobolev wave curve with its two strong time derivatives has a
jointly C² representative. The proof differentiates the spatial derivatives
in time, so the mixed derivatives are included. -/
theorem contDiffOn_two_higherWave (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))) (A : C(ℝ, W^{k,2}(ℝ^n))) {s : Set ℝ}
    (hs : IsOpen s)
    (hU : ∀ t ∈ s, HasDerivAt (fun a ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (U a).1) (U t).2 t)
    (hV : ∀ t ∈ s, HasDerivAt (fun a ↦ lowerOrderCLM (Nat.le_succ k) (U a).2) (A t) t) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hq (U p.1).1 p.2) (s ×ˢ univ) := by
  have htq (t : ℝ) (ht : t ∈ s) (x : ℝ^n) := hasDerivAt_classicalRepresentative_lowerOrder hv hq
      (Nat.le_succ (k + 1)) (hU t ht) x
  have htv (t : ℝ) (ht : t ∈ s) (x : ℝ^n) := hasDerivAt_classicalRepresentative_lowerOrder hk hv
      (Nat.le_succ k) (hV t ht) x
  have hvreg : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hv (U p.1).2 p.2) (s ×ˢ univ) :=
    contDiffOn_one_classicalRepresentative hk hv ⟨_, U.continuous.snd⟩ hs
      (continuous_classicalRepresentativeCLM hk A.continuous).continuousOn htv
  have hdreg (i : Fin n) : ContDiffOn ℝ 1 (fun p : ℝ × ℝ^n ↦
        classicalRepresentativeCLM hv (partialDerivCLM i (U p.1).1) p.2) (s ×ˢ univ) := by
    apply contDiffOn_one_classicalRepresentative hk hv
      ⟨_, (partialDerivCLM i).continuous.comp U.continuous.fst⟩ hs
      (v := fun p ↦ classicalRepresentativeCLM hk (partialDerivCLM i (U p.1).2) p.2)
    · exact (continuous_classicalRepresentativeCLM hk
        ((partialDerivCLM i).continuous.comp U.continuous.snd)).continuousOn
    · intro t ht x
      have hd := (partialDerivCLM (n := n) (k := k) (p := 2) (Ω := univ) i).hasFDerivAt
        |>.comp_hasDerivAt t (hU t ht)
      have heq (a : ℝ) : partialDerivCLM i (lowerOrderCLM (Nat.le_succ (k + 1)) (U a).1) =
            lowerOrderCLM (Nat.le_succ k) (partialDerivCLM i (U a).1) := by
        simp only [partialDerivCLM, derivativeWordCLM_lowerOrderCLM_apply,
          lowerOrderCLM_derivativeWordCLM_apply]
      change HasDerivAt (fun a ↦ partialDerivCLM i (lowerOrderCLM (Nat.le_succ (k + 1)) (U a).1))
        (partialDerivCLM i (U t).2) t at hd
      simp only [heq] at hd
      exact hasDerivAt_classicalRepresentative_lowerOrder hk hv (Nat.le_succ k) hd x
  exact contDiffOn_succ_of_spaceTime_derivatives hs htq
    (fun t _ x ↦ hasFDerivAt_classicalRepresentative hv hq (U t).1 x) hvreg hdreg

end PDE.Hyperbolic.NonlinearWave.Cauchy
