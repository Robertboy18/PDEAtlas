/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Fin.Tuple.Sort
import PDE.Analysis.Calculus.FaaDiBrunoBounds

/-!
# Finite jets under coordinate changes

Finite jet composition is the finite Faà di Bruno polynomial, using Mathlib's
ordered partitions. Coordinate evaluation uses the mixed partials
`coordinateDeriv`. At a zero of a scalar defining function, its powers have a particularly
simple leading jet; this is the transverse coefficient in Cauchy data.
-/

@[expose] public noncomputable section

open scoped Gradient

open scoped ContDiff
open Set

namespace PDE.Analysis.Jet

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Composition of finite tuples of multilinear derivatives. All indices used
by the Faà di Bruno polynomial are strictly below the supplied cutoff. -/
def compose (k : ℕ)
    (q : ∀ i : Fin k, F [×(i : ℕ)]→L[ℝ] G)
    (p : ∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] F) :
    ∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] G :=
  fun i ↦ ∑ c : OrderedFinpartition (i : ℕ),
    c.compAlongOrderedFinpartition
      (q ⟨c.length, lt_of_le_of_lt c.length_le i.isLt⟩)
      (fun a ↦ p ⟨c.partSize a, lt_of_le_of_lt (c.partSize_le a) i.isLt⟩)

/-- The finite composition polynomial computes the actual derivatives of a
composition, including order zero. -/
theorem compose_jetLT {k : ℕ} {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g (f x)) :
    compose k (jetLT ℝ k g (f x)) (jetLT ℝ k f x) =
      jetLT ℝ k (g ∘ f) x := by
  funext i
  symm
  exact iteratedFDeriv_comp hg hf (by exact_mod_cast i.isLt.le)

/-- Finite jet composition is analytic jointly in both supplied jets. -/
theorem analyticAt_compose (k : ℕ)
    (z : (∀ i : Fin k, F [×(i : ℕ)]→L[ℝ] G) ×
      (∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] F)) :
    AnalyticAt ℝ (fun z ↦ compose k z.1 z.2) z := by
  apply AnalyticAt.pi
  intro i
  apply Finset.analyticAt_fun_sum
  intro c _
  let L := c.compAlongOrderedFinpartitionL ℝ E F G
  change AnalyticAt ℝ ((fun z ↦ L z.1 z.2) ∘
    (fun z ↦
      (z.1 ⟨c.length, lt_of_le_of_lt c.length_le i.isLt⟩,
       fun a ↦ z.2 ⟨c.partSize a, lt_of_le_of_lt (c.partSize_le a) i.isLt⟩))) z
  apply (L.analyticOnNhd_uncurry_of_multilinear _ (mem_univ _)).comp
  apply AnalyticAt.prod
  · exact ((ContinuousLinearMap.proj _).analyticAt _).comp
      ((ContinuousLinearMap.fst ℝ _ _).analyticAt z)
  · apply AnalyticAt.pi
    intro a
    exact ((ContinuousLinearMap.proj _).analyticAt _).comp
      ((ContinuousLinearMap.snd ℝ _ _).analyticAt z)

/-- At positive order, changing only the highest outer derivative changes
the composed jet by its evaluation on the first inner derivatives. -/
theorem compose_sub_of_lower_eq {k : ℕ}
    (q r : ∀ i : Fin k, F [×(i : ℕ)]→L[ℝ] G)
    (p : ∀ i : Fin k, E [×(i : ℕ)]→L[ℝ] F)
    (j : Fin k) (hj : 0 < (j : ℕ))
    (hqr : ∀ i : Fin k, (i : ℕ) < j → q i = r i) (v : Fin (j : ℕ) → E) :
    compose k q p j v - compose k r p j v =
      (q j - r j) (fun i ↦ p ⟨1, by omega⟩ (fun _ ↦ v i)) := by
  classical
  simp only [compose, _root_.sum_apply]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (OrderedFinpartition.atomic j)]
  · rfl
  · intro c _ hc
    have hl : c.length < j := by
      have hne : c.length ≠ j := fun h ↦ hc (eq_atomic_of_length_eq c h)
      have := c.length_le
      omega
    rw [hqr ⟨c.length, lt_of_le_of_lt c.length_le j.isLt⟩ hl, sub_self]
  · simp

/-- Powers of a defining function vanish to the expected order on its zero
set. At the leading order the coefficient is the product of the actual first
derivative in the supplied directions. -/
theorem iteratedFDeriv_pow_of_eq_zero {φ : E → ℝ} {x : E}
    (hφ : AnalyticAt ℝ φ x) (hx : φ x = 0)
    {j k : ℕ} (hjk : j ≤ k) (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun y ↦ φ y ^ k) x v =
      if j = k then (k.factorial : ℝ) * ∏ i, fderiv ℝ φ x (v i) else 0 := by
  classical
  change iteratedFDeriv ℝ j ((fun t : ℝ ↦ t ^ k) ∘ φ) x v = _
  have hpow : ContDiffAt ℝ (j : ℕ∞ω) (fun t : ℝ ↦ t ^ k) (φ x) := by fun_prop
  rw [iteratedFDeriv_comp hpow hφ.contDiffAt (i := j) le_rfl]
  simp only [FormalMultilinearSeries.taylorComp, _root_.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    ftaylorSeries, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hx,
    iteratedDeriv_fun_pow_zero]
  by_cases h : j = k
  · subst j
    rw [Finset.sum_eq_single (OrderedFinpartition.atomic k)]
    · simp only [OrderedFinpartition.atomic_length, ↓reduceIte, smul_eq_mul]
      rw [mul_comm]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact iteratedFDeriv_one_apply _
    · intro c _ hc
      have hl : c.length ≠ k := fun hl ↦ hc (eq_atomic_of_length_eq c hl)
      simp [hl]
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro c _
    have hl : c.length ≠ k := by
      have := c.length_le
      omega
    simp [hl]

private theorem norm_iteratedFDeriv_mul_le_at {a b : E → ℝ} {x : E}
    (ha : AnalyticAt ℝ a x) (hb : AnalyticAt ℝ b x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y ↦ a y * b y) x‖ ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i a x‖ * ‖iteratedFDeriv ℝ (j - i) b x‖ := by
  let U := {y | AnalyticAt ℝ a y} ∩ {y | AnalyticAt ℝ b y}
  have hU : IsOpen U := (isOpen_analyticAt ℝ a).inter (isOpen_analyticAt ℝ b)
  have hx : x ∈ U := ⟨ha, hb⟩
  have hau : ContDiffOn ℝ (j : ℕ∞ω) a U := fun y hy ↦ hy.1.contDiffAt.contDiffWithinAt
  have hbu : ContDiffOn ℝ (j : ℕ∞ω) b U := fun y hy ↦ hy.2.contDiffAt.contDiffWithinAt
  have he (f : E → ℝ) (hf : AnalyticAt ℝ f x) (r : ℕ) :
      iteratedFDerivWithin ℝ r f U x = iteratedFDeriv ℝ r f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hf.contDiffAt hx
  have h := norm_iteratedFDerivWithin_mul_le hau hbu hU.uniqueDiffOn hx (n := j) le_rfl
  simpa only [he a ha, he b hb, he (fun y ↦ a y * b y) (ha.mul hb)] using h

/-- A vanishing factor times a function whose lower jets vanish has zero jet
at the next order. This follows from Mathlib's derivative-product bound. -/
theorem iteratedFDeriv_mul_eq_zero_of_lower_eq_zero {a b : E → ℝ} {x : E}
    (ha : AnalyticAt ℝ a x) (hb : AnalyticAt ℝ b x) (ha0 : a x = 0)
    {j : ℕ} (hb0 : ∀ i < j, iteratedFDeriv ℝ i b x = 0) :
    iteratedFDeriv ℝ j (fun y ↦ a y * b y) x = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  refine (norm_iteratedFDeriv_mul_le_at ha hb j).trans_eq ?_
  apply Finset.sum_eq_zero
  intro i hi
  by_cases h : i = 0
  · subst i
    simp [norm_iteratedFDeriv_zero, ha0]
  · rw [hb0 (j - i) (by have := Finset.mem_range.mp hi; omega)]
    simp

/-- If the lower jets of the second factor vanish, only the value of the first
factor contributes to the next product jet. -/
theorem iteratedFDeriv_mul_of_lower_eq_zero {a b : E → ℝ} {x : E}
    (ha : AnalyticAt ℝ a x) (hb : AnalyticAt ℝ b x)
    {j : ℕ} (hb0 : ∀ i < j, iteratedFDeriv ℝ i b x = 0) :
    iteratedFDeriv ℝ j (fun y ↦ a y * b y) x =
      a x • iteratedFDeriv ℝ j b x := by
  have hz := iteratedFDeriv_mul_eq_zero_of_lower_eq_zero
    (ha.sub analyticAt_const) hb (sub_self (a x)) hb0
  change iteratedFDeriv ℝ j (fun y ↦ (a y - a x) * b y) x = 0 at hz
  have he : (fun y ↦ (a y - a x) * b y) =
      (fun y ↦ a y * b y) - a x • b := by
    funext y
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, iteratedFDeriv_sub_apply (f := fun y ↦ a y * b y) (ha.mul hb).contDiffAt
    (hb.const_smul (c := a x)).contDiffAt,
    iteratedFDeriv_const_smul_apply hb.contDiffAt] at hz
  exact sub_eq_zero.mp hz

/-- Multiplication by an analytic amplitude changes the leading jet of a
vanishing power only by the amplitude's value. -/
theorem iteratedFDeriv_mul_pow_of_eq_zero {a φ : E → ℝ} {x : E}
    (ha : AnalyticAt ℝ a x) (hφ : AnalyticAt ℝ φ x) (hx : φ x = 0)
    {j k : ℕ} (hjk : j ≤ k) (v : Fin j → E) :
    iteratedFDeriv ℝ j (fun y ↦ a y * φ y ^ k) x v =
      if j = k then a x * (k.factorial : ℝ) *
        ∏ i, fderiv ℝ φ x (v i) else 0 := by
  have hflat : ∀ i < j, iteratedFDeriv ℝ i (fun y ↦ φ y ^ k) x = 0 := by
    intro i hi
    ext w
    rw [iteratedFDeriv_pow_of_eq_zero hφ hx (by omega)]
    simp [show i ≠ k by omega]
  rw [iteratedFDeriv_mul_of_lower_eq_zero (b := fun y ↦ φ y ^ k) ha (hφ.pow k) hflat]
  simp only [_root_.smul_apply, smul_eq_mul,
    iteratedFDeriv_pow_of_eq_zero hφ hx hjk]
  split_ifs <;> ring

end PDE.Analysis.Jet

namespace PDE.Analysis.MultiIndex

variable {n j : ℕ}

private theorem ofFn_sortedTuple (α : Sym (Fin n) j) :
    List.ofFn α.sortedTuple = (α : Multiset (Fin n)).sort (· ≤ ·) := by
  unfold Sym.sortedTuple
  rw [← List.ofFn_congr
    ((Multiset.length_sort (· ≤ ·)).trans α.card_coe), List.ofFn_get]

private theorem sortedTuple_tupleIndex (a : Fin j → Fin n) :
    (Sym.ofVector (List.Vector.ofFn a)).sortedTuple = a ∘ Tuple.sort a := by
  apply List.ofFn_injective
  rw [ofFn_sortedTuple]
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact Multiset.pairwise_sort _ _
  · exact (Tuple.monotone_sort a).sortedLE_ofFn.pairwise
  · apply Multiset.coe_eq_coe.mp
    rw [Multiset.sort_eq]
    change (List.Vector.ofFn a).toList = (List.ofFn (a ∘ Tuple.sort a) : Multiset (Fin n))
    rw [List.Vector.toList_ofFn]
    exact Multiset.coe_eq_coe.mpr ((Tuple.sort a).ofFn_comp_perm a).symm

/-- Reconstruct a symmetric multilinear derivative from its coordinate
mixed partials. This finite sum uses every ordered coordinate tuple once. -/
def multilinearFromCoordinates (n j : ℕ) :
    (Sym (Fin n) j → ℝ) →L[ℝ] ((ℝ^n) [×j]→L[ℝ] ℝ) :=
  ∑ a : Fin j → Fin n, (ContinuousLinearMap.proj (Sym.ofVector (List.Vector.ofFn a))).smulRight
    ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ).compContinuousLinearMap
      (fun i ↦ EuclideanSpace.proj (a i)))

/-- The reconstruction is the usual coordinate expansion of a tensor. -/
theorem multilinearFromCoordinates_apply (q : Sym (Fin n) j → ℝ) (v : Fin j → ℝ^n) :
    multilinearFromCoordinates n j q v =
      ∑ a : Fin j → Fin n, q (Sym.ofVector (List.Vector.ofFn a)) * ∏ i, v i (a i) := by
  simp [multilinearFromCoordinates, ContinuousMultilinearMap.mkPiAlgebra_apply]

private theorem multilinearFromCoordinates_basis (q : Sym (Fin n) j → ℝ)
    (a : Fin j → Fin n) :
    multilinearFromCoordinates n j q (fun i ↦ EuclideanSpace.basisFun (Fin n) ℝ (a i)) =
      q (Sym.ofVector (List.Vector.ofFn a)) := by
  classical
  rw [multilinearFromCoordinates_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hba
    have hz : (∏ r : Fin j, EuclideanSpace.basisFun (Fin n) ℝ (a r) (b r)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hz, mul_zero]
  · simp

/-- An array supported on a pure coordinate multiindex reconstructs the
corresponding product tensor, including the order-zero case. -/
theorem multilinearFromCoordinates_single (a : Fin n) (r : ℝ) (v : Fin j → ℝ^n) :
    multilinearFromCoordinates n j
      (fun α ↦ if α = Sym.replicate j a then r else 0) v =
        r * ∏ i, v i a := by
  classical
  have hindex (b : Fin j → Fin n) :
      Sym.ofVector (List.Vector.ofFn b) = Sym.replicate j a ↔ b = fun _ ↦ a := by
    rw [Sym.eq_replicate_iff]
    change (∀ c ∈ (List.Vector.ofFn b).toList, c = a) ↔ _
    rw [List.Vector.toList_ofFn, List.forall_mem_ofFn_iff]
    exact ⟨fun h ↦ funext h, fun h i ↦ congrFun h i⟩
  rw [multilinearFromCoordinates_apply, Finset.sum_eq_single (fun _ ↦ a)]
  · simp only [hindex, ↓reduceIte]
  · intro b _ hb
    rw [ite_eq_right (mt (hindex b).mp hb), zero_mul]
  · simp

/-- Reconstructing the actual coordinate derivatives of an analytic
function gives its actual Fréchet derivative, with no factorial rescaling. -/
theorem multilinearFromCoordinates_coordinateDeriv {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : AnalyticAt ℝ u x) (j : ℕ) :
    multilinearFromCoordinates n j (fun α ↦ coordinateDeriv α u x) =
      iteratedFDeriv ℝ j u x := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ ↦ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
  intro a
  change multilinearFromCoordinates n j (fun α ↦ coordinateDeriv α u x)
      (fun i ↦ EuclideanSpace.basisFun (Fin n) ℝ (a i)) =
    iteratedFDeriv ℝ j u x (fun i ↦ EuclideanSpace.basisFun (Fin n) ℝ (a i))
  rw [multilinearFromCoordinates_basis]
  unfold coordinateDeriv directions
  rw [sortedTuple_tupleIndex]
  exact hu.contDiffAt.iteratedFDeriv_comp_perm
    (fun i ↦ EuclideanSpace.basisFun (Fin n) ℝ (a i)) (Tuple.sort a)

/-- Reconstruction of a finite coordinate jet is a continuous linear map. -/
def fromCoordinates (n k : ℕ) :
    (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ) →L[ℝ]
      (∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    (multilinearFromCoordinates n i).comp (ContinuousLinearMap.proj i)

/-- Coordinate arrays recover the finite derivative tuple `jetLT` of an
analytic scalar function. -/
theorem fromCoordinates_coordinateJetLT {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : AnalyticAt ℝ u x) (k : ℕ) :
    fromCoordinates n k (coordinateJetLT k u x) = jetLT ℝ k u x := by
  funext i
  exact multilinearFromCoordinates_coordinateDeriv hu i

/-- Finite coordinate-jet transport under a change of variables. The map is
defined on every coordinate array, not just arrays already realized by a
particular analytic function. -/
def transport (n k : ℕ)
    (q : ∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ)
    (p : ∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] (ℝ^n)) :
    ∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ :=
  coordinateJetMap n k (Jet.compose k (fromCoordinates n k q) p)

/-- Coordinate-jet transport is analytic jointly in both finite arrays. -/
theorem analyticAt_transport (n k : ℕ)
    (z : (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ) ×
      (∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] (ℝ^n))) :
    AnalyticAt ℝ (fun z ↦ transport n k z.1 z.2) z := by
  have hfst := (ContinuousLinearMap.fst ℝ
    (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ)
    (∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] (ℝ^n))).analyticAt z
  have hsnd := (ContinuousLinearMap.snd ℝ
    (∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ)
    (∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] (ℝ^n))).analyticAt z
  have hpair := (((fromCoordinates n k).analyticAt _).comp hfst).prod hsnd
  exact ((coordinateJetMap n k).analyticAt _).comp
    ((Jet.analyticAt_compose k _).comp hpair)

/-- The finite transport map computes the actual mixed partials of a
composition of analytic germs. -/
theorem transport_coordinateJetLT {u : ℝ^n → ℝ} {Φ : ℝ^n → ℝ^n} {x : ℝ^n}
    (hΦ : AnalyticAt ℝ Φ x) (hu : AnalyticAt ℝ u (Φ x)) (k : ℕ) :
    transport n k (coordinateJetLT k u (Φ x)) (jetLT ℝ k Φ x) =
      coordinateJetLT k (u ∘ Φ) x := by
  unfold transport
  rw [fromCoordinates_coordinateJetLT hu, Jet.compose_jetLT hΦ.contDiffAt hu.contDiffAt]
  rfl

/-- The coefficient of the highest pure transverse entry in coordinate
transport is the product of the first coordinate derivatives. The other
entries are arbitrary arrays; no realization by a function is assumed. -/
theorem transport_sub_of_transverse_eq {k : ℕ}
    (q r : ∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ)
    (p : ∀ i : Fin k, (ℝ^n) [×(i : ℕ)]→L[ℝ] (ℝ^n))
    (j : Fin k) (hj : 0 < (j : ℕ)) (a : Fin n) (s : ℝ)
    (hqr : ∀ i : Fin k, (i : ℕ) < j → q i = r i)
    (htop : ∀ α, q j α - r j α = if α = Sym.replicate j a then s else 0)
    (α : Sym (Fin n) j) :
    transport n k q p j α - transport n k r p j α =
      s * ∏ i, p ⟨1, by omega⟩ (fun _ ↦ directions α i) a := by
  change Jet.compose k (fromCoordinates n k q) p j (directions α) -
    Jet.compose k (fromCoordinates n k r) p j (directions α) = _
  have he : ∀ i : Fin k, (i : ℕ) < j →
      fromCoordinates n k q i = fromCoordinates n k r i := by
    intro i hi
    exact congrArg (multilinearFromCoordinates n i) (hqr i hi)
  rw [Jet.compose_sub_of_lower_eq (fromCoordinates n k q) (fromCoordinates n k r)
    p j hj he]
  change (multilinearFromCoordinates n j (q j) -
    multilinearFromCoordinates n j (r j)) _ = _
  rw [← map_sub, show q j - r j =
    (fun β ↦ if β = Sym.replicate j a then s else 0) from funext htop]
  exact multilinearFromCoordinates_single a s _

/-- For an actual coordinate change with transverse coordinate `φ`, the
highest transverse coefficient is exactly the coordinate monomial in `∇φ`.
There is no multinomial factor. Only germ equality of the coordinate is needed. -/
theorem transport_sub_of_transverse_eq_jet {k : ℕ} {Φ : ℝ^n → ℝ^n}
    {φ : ℝ^n → ℝ} {x : ℝ^n} (hΦ : AnalyticAt ℝ Φ x)
    (a : Fin n) (hlevel : (fun y ↦ Φ y a) =ᶠ[nhds x] φ)
    (q r : ∀ i : Fin k, Sym (Fin n) (i : ℕ) → ℝ)
    (j : Fin k) (hj : 0 < (j : ℕ)) (s : ℝ)
    (hqr : ∀ i : Fin k, (i : ℕ) < j → q i = r i)
    (htop : ∀ α, q j α - r j α = if α = Sym.replicate j a then s else 0)
    (α : Sym (Fin n) j) :
    transport n k q (jetLT ℝ k Φ x) j α -
      transport n k r (jetLT ℝ k Φ x) j α =
        s * monomial α (∇ φ x) := by
  rw [transport_sub_of_transverse_eq q r _ j hj a s hqr htop]
  have hD := ((EuclideanSpace.proj a).hasFDerivAt.comp x
    hΦ.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hlevel.symm
  rw [monomial_eq_prod_inner]
  apply congrArg (s * ·)
  apply Finset.prod_congr rfl
  intro i _
  change iteratedFDeriv ℝ 1 Φ x (fun _ ↦ directions α i) a = _
  rw [iteratedFDeriv_one_apply, inner_gradient_left]
  exact congrArg (fun L ↦ L (directions α i)) hD.fderiv.symm

end PDE.Analysis.MultiIndex
