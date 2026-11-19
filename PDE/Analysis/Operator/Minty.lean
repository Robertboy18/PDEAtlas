/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakCompactness
public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Algebra.BigOperators.Field

/-!
# Minty's variational inequality and monotone surjectivity

For a monotone map `A : E → StrongDual ℝ E`, finite feasibility follows from
separating the image of a finite convex hull from the nonnegative orthant.
Weak compactness then gives the Minty inequality
`0 ≤ (A v - f) (v - u)` simultaneously for all test points `v`.
Right hemicontinuity along segments moves `A` from the test point to `u`.

The final result is the coercive Browder–Minty surjectivity theorem in a
reflexive real normed space, an abstract form of the monotonicity method of Evans, §9.1.
Reflexivity means surjectivity of the canonical map into the continuous double dual.
Coercivity is stated without division: every positive multiple of `‖u‖` is eventually
bounded above by `A u u`.

## Main results

* `exists_mem_convexHull_forall_pairing_nonneg`: a finite monotone family of point-functional
  pairs has a point of the convex hull at which every pairing is nonnegative.
* `exists_minty_variational_inequality_of_isCompact`: the Minty inequality on a nonempty weakly
  compact convex set.
* `variational_inequality_of_minty`, `exists_variational_inequality_of_isCompact`: right
  hemicontinuity turns it into a variational inequality.
* `surjective_of_monotone_of_hemicontinuous_of_coercive`: the Browder–Minty theorem.

## How it works

Evans, §9.1, applies the method of Browder and Minty to Galerkin approximations of
`-div a(Du) = f`: he finds them as zeros of a vector field with Brouwer's fixed point theorem
(the Lemma before Theorem 1) and passes to the weak limit in Theorem 3 through the inequality
(18). We work instead with an abstract monotone map and finite families of test points, where
no fixed point theorem is needed: `exists_mem_convexHull_forall_pairing_nonneg` separates the
image of a finite convex hull from the nonnegative orthant with Mathlib's
`ProperCone.hyperplane_separation`. The finite intersection property
`IsCompact.inter_iInter_nonempty` on a weakly compact set then gives the Minty inequality
`0 ≤ (A v - f) (v - u)`, which is Evans's (18). Step 4 of his proof, testing with `u - λ v` and
letting `λ → 0` to get (19), is `variational_inequality_of_minty`. For surjectivity we use the
closed balls, weakly compact by `WeakCompactness.isCompact_closure_of_isBounded_of_reflexive`,
and coercivity puts the solution in the interior.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.1, the Lemma (Zeros of a vector field), p. 529, and
  Theorem 3 and steps 3 and 4 of its proof, (17)-(19), pp. 531-532.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Set Filter Metric
open scoped BigOperators Topology

namespace PDE.Analysis.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Averaging the monotonicity pairing over two indices gives twice the
weighted pairing with the barycenter. -/
private theorem sum_pairing_sub_sum_smul_nonneg
    {ι : Type*} [Fintype ι]
    (v : ι → E) (a : ι → StrongDual ℝ E) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hmono : ∀ i j, 0 ≤ (a i - a j) (v i - v j)) :
    0 ≤ ∑ i, w i * a i (v i - ∑ j, w j • v j) := by
  let u := ∑ j, w j • v j
  let S := ∑ i, w i * a i (v i - u)
  have hrow (i : ι) :
      ∑ j, w j * a i (v i - v j) = a i (v i - u) := by
    calc
      _ = (∑ j, w j) * a i (v i) - ∑ j, w j * a i (v j) := by
        simp only [map_sub, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      _ = a i (v i - u) := by
        rw [hsum, one_mul]
        simp only [u, map_sub, map_sum, map_smul, smul_eq_mul]
  have hsum_pairing :
      (∑ i, ∑ j, w i * w j * a i (v i - v j)) = S := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = w i * ∑ j, w j * a i (v i - v j) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = w i * a i (v i - u) := by rw [hrow]
  have hsum_reversed :
      (∑ i, ∑ j, w i * w j * a j (v i - v j)) = -S := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ∑ j, -(w i * w j * a i (v i - v j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [show v j - v i = -(v i - v j) from (neg_sub _ _).symm, map_neg]
        ring
      _ = -(∑ i, ∑ j, w i * w j * a i (v i - v j)) := by
        simp only [Finset.sum_neg_distrib]
      _ = -S := congrArg Neg.neg hsum_pairing
  have hnonneg :
      0 ≤ ∑ i, ∑ j, w i * w j * (a i - a j) (v i - v j) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (hw i) (hw j)) (hmono i j)
  simp only [sub_apply, mul_sub, Finset.sum_sub_distrib] at hnonneg
  rw [hsum_pairing, hsum_reversed] at hnonneg
  change 0 ≤ S
  linarith

/-- A finite monotone family of point-functional pairs admits a point in the
convex hull at which every Minty pairing is nonnegative. No continuity of the
family with respect to its points is required. -/
theorem exists_mem_convexHull_forall_pairing_nonneg
    {ι : Type*} [Finite ι] [Nonempty ι]
    (v : ι → E) (a : ι → StrongDual ℝ E)
    (hmono : ∀ i j, 0 ≤ (a i - a j) (v i - v j)) :
    ∃ u ∈ convexHull ℝ (range v), ∀ i, 0 ≤ a i (v i - u) := by
  classical
  let _ := Fintype.ofFinite ι
  let Φ : E →ᵃ[ℝ] (ι → ℝ) :=
    { toFun := fun u i ↦ a i (v i - u)
      linear := -(LinearMap.pi fun i ↦ (a i).toLinearMap)
      map_vadd' := by
        intro p z
        ext i
        change a i (v i - (z + p)) = -(a i z) + a i (v i - p)
        simp only [map_sub, map_add]
        ring }
  have hΦ : Continuous Φ :=
    continuous_pi fun i ↦ (a i).continuous.comp (continuous_const.sub continuous_id)
  let C : Set (ι → ℝ) := Φ '' convexHull ℝ (range v)
  have hCconvex : Convex ℝ C := (convex_convexHull ℝ (range v)).affine_image Φ
  have hCcompact : IsCompact C :=
    ((finite_range v).isCompact_convexHull ℝ).image hΦ
  by_contra hnone
  have hdisjoint : Disjoint C (ProperCone.positive ℝ (ι → ℝ)) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨u, hu, rfl⟩ hy
    exact hnone ⟨u, hu, fun i ↦ hy i⟩
  obtain ⟨f, hfpos, hfneg⟩ :=
    (ProperCone.positive ℝ (ι → ℝ)).hyperplane_separation hCconvex hCcompact hdisjoint
  let w : ι → ℝ := fun i ↦ f (fun j ↦ if i = j then 1 else 0)
  have hw (i : ι) : 0 ≤ w i := by
    apply hfpos
    change ∀ j, 0 ≤ (if i = j then (1 : ℝ) else 0)
    intro j
    split_ifs <;> simp
  have hf (y : ι → ℝ) : f y = ∑ i, w i * y i := by
    simpa only [ContinuousLinearMap.coe_coe, w, smul_eq_mul, mul_comm] using
      LinearMap.pi_apply_eq_sum_univ f.toLinearMap y
  let W := ∑ i, w i
  have hW : 0 < W := by
    by_contra! hW
    have hwzero (i : ι) : w i = 0 :=
      le_antisymm
        ((Finset.single_le_sum (fun j _ ↦ hw j) (Finset.mem_univ i)).trans hW)
        (hw i)
    let i₀ : ι := Classical.arbitrary ι
    have hnegative := hfneg (Φ (v i₀))
      ⟨v i₀, subset_convexHull ℝ (range v) (mem_range_self i₀), rfl⟩
    rw [hf] at hnegative
    simp only [hwzero, zero_mul, Finset.sum_const_zero, lt_self_iff_false] at hnegative
  let alpha : ι → ℝ := fun i ↦ w i / W
  have halpha (i : ι) : 0 ≤ alpha i := div_nonneg (hw i) hW.le
  have halpha_sum : ∑ i, alpha i = 1 := by
    dsimp only [alpha]
    rw [← Finset.sum_div]
    exact div_self hW.ne'
  let u := ∑ i, alpha i • v i
  have hu : u ∈ convexHull ℝ (range v) :=
    mem_convexHull_of_exists_fintype alpha v halpha halpha_sum (fun i ↦ mem_range_self i) rfl
  have hpairing := sum_pairing_sub_sum_smul_nonneg v a alpha halpha halpha_sum hmono
  have hvalue : f (Φ u) / W = ∑ i, alpha i * a i (v i - u) := by
    rw [hf, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    change w i * a i (v i - u) / W = w i / W * a i (v i - u)
    ring
  have hnegative := div_neg_of_neg_of_pos (hfneg (Φ u) ⟨u, hu, rfl⟩) hW
  rw [hvalue] at hnegative
  exact hnegative.not_ge hpairing

/-- A monotone map admits a Minty variational inequality on any nonempty
weakly compact convex set. Each constraint uses a fixed continuous linear
functional, so the operator itself need not be continuous. -/
theorem exists_minty_variational_inequality_of_isCompact
    (A : E → StrongDual ℝ E) (f : StrongDual ℝ E) (K : Set E)
    (hne : K.Nonempty) (hconvex : Convex ℝ K)
    (hcompact : IsCompact (toWeakSpace ℝ E '' K))
    (hmono : ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (A u - A v) (u - v)) :
    ∃ u ∈ K, ∀ v ∈ K, 0 ≤ (A v - f) (v - u) := by
  classical
  let H : K → Set (WeakSpace ℝ E) :=
    fun v ↦ {w | 0 ≤ (A v - f) ((v : E) - (toWeakSpace ℝ E).symm w)}
  have hclosed (v : K) : IsClosed (H v) := by
    have heval : Continuous (fun w : WeakSpace ℝ E ↦
        (A v - f) ((toWeakSpace ℝ E).symm w)) :=
      WeakBilin.eval_continuous (topDualPairing ℝ E).flip (A v - f)
    have hdifference : Continuous (fun w : WeakSpace ℝ E ↦
        (A v - f) (v : E) - (A v - f) ((toWeakSpace ℝ E).symm w)) :=
      continuous_const.sub heval
    have hsub : Continuous (fun w : WeakSpace ℝ E ↦
        (A v - f) ((v : E) - (toWeakSpace ℝ E).symm w)) := by
      simpa only [map_sub] using hdifference
    exact isClosed_le continuous_const hsub
  have hfinite (t : Finset K) :
      ((toWeakSpace ℝ E '' K) ∩ ⋂ v ∈ t, H v).Nonempty := by
    rcases t.eq_empty_or_nonempty with rfl | ht
    · obtain ⟨u, hu⟩ := hne
      exact ⟨toWeakSpace ℝ E u, ⟨u, hu, rfl⟩, by simp⟩
    · let : Nonempty t := ⟨⟨ht.choose, ht.choose_spec⟩⟩
      let v : t → E := fun i ↦ i.1.1
      let a : t → StrongDual ℝ E := fun i ↦ A (v i) - f
      have hmonotone (i j : t) : 0 ≤ (a i - a j) (v i - v j) := by
        simpa only [a, sub_sub_sub_cancel_right] using hmono (v i) i.1.2 (v j) j.1.2
      obtain ⟨u, hu, htest⟩ :=
        exists_mem_convexHull_forall_pairing_nonneg v a hmonotone
      have huK : u ∈ K :=
        convexHull_min (by rintro _ ⟨i, rfl⟩; exact i.1.2) hconvex hu
      refine ⟨toWeakSpace ℝ E u, ⟨u, huK, rfl⟩, ?_⟩
      simp only [mem_iInter]
      intro v hv
      exact htest ⟨v, hv⟩
  obtain ⟨w, ⟨u, hu, rfl⟩, hw⟩ := hcompact.inter_iInter_nonempty H hclosed hfinite
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  exact mem_iInter.mp hw ⟨v, hv⟩

/-- Right continuity of the scalar pairing along each segment turns a Minty
inequality into the variational inequality at its solution. Convexity keeps
the positive segment parameters inside the test set. -/
theorem variational_inequality_of_minty
    (A : E → StrongDual ℝ E) (f : StrongDual ℝ E) {K : Set E}
    (hconvex : Convex ℝ K) {u : E} (hu : u ∈ K)
    (hhemi : ∀ v ∈ K, ContinuousWithinAt
      (fun t : ℝ ↦ A (u + t • (v - u)) (v - u)) (Ici 0) 0)
    (hminty : ∀ v ∈ K, 0 ≤ (A v - f) (v - u)) :
    ∀ v ∈ K, 0 ≤ (A u - f) (v - u) := by
  intro v hv
  have hlimit : Tendsto (fun t : ℝ ↦ (A (u + t • (v - u)) - f) (v - u))
      (𝓝[>] (0 : ℝ)) (𝓝 ((A u - f) (v - u))) := by
    simpa only [zero_smul, add_zero, sub_apply] using
      ((hhemi v hv).mono Ioi_subset_Ici_self).tendsto.sub
        (tendsto_const_nhds (x := f (v - u)))
  have hnonneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ (A (u + t • (v - u)) - f) (v - u) := by
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
    filter_upwards [hpos, hsmall] with t ht ht₁
    have htest := hminty (u + t • (v - u))
      (hconvex.add_smul_sub_mem hu hv ⟨ht.le, ht₁.le⟩)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at htest
    exact (mul_nonneg_iff_of_pos_left ht).mp htest
  exact ge_of_tendsto hlimit hnonneg

/-- A monotone, right-hemicontinuous operator has a variational-inequality
solution on a nonempty weakly compact convex set. Only the scalar pairing
with the segment direction needs to be continuous at its initial point. -/
theorem exists_variational_inequality_of_isCompact
    (A : E → StrongDual ℝ E) (f : StrongDual ℝ E) (K : Set E)
    (hne : K.Nonempty) (hconvex : Convex ℝ K)
    (hcompact : IsCompact (toWeakSpace ℝ E '' K))
    (hmono : ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (A u - A v) (u - v))
    (hhemi : ∀ u ∈ K, ∀ v ∈ K, ContinuousWithinAt
      (fun t : ℝ ↦ A (u + t • (v - u)) (v - u)) (Ici 0) 0) :
    ∃ u ∈ K, ∀ v ∈ K, 0 ≤ (A u - f) (v - u) := by
  obtain ⟨u, hu, hminty⟩ :=
    exists_minty_variational_inequality_of_isCompact A f K hne hconvex hcompact hmono
  exact ⟨u, hu, variational_inequality_of_minty A f hconvex hu (hhemi u hu) hminty⟩

/-- A coercive monotone operator on a reflexive real normed space is
surjective if its scalar pairing with each line direction is right-continuous
at the initial point. The coercivity hypothesis says that `A u u / ‖u‖`
tends to infinity as `‖u‖` does, expressed without division.

The proof solves a variational inequality on a weakly compact ball.
Coercivity puts the solution in the interior, where testing both signs of
every direction gives `A u = f`. -/
theorem surjective_of_monotone_of_hemicontinuous_of_coercive
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (A : E → StrongDual ℝ E)
    (hmono : ∀ u v, 0 ≤ (A u - A v) (u - v))
    (hhemi : ∀ u v : E, ContinuousWithinAt
      (fun t : ℝ ↦ A (u + t • v) v) (Ici 0) 0)
    (hcoercive : ∀ M : ℝ, 0 < M → ∃ R : ℝ, 0 < R ∧
      ∀ u : E, R ≤ ‖u‖ → M * ‖u‖ ≤ A u u) :
    Function.Surjective A := by
  intro f
  obtain ⟨R, hR, hbound⟩ := hcoercive (‖f‖ + 1) (by linarith [norm_nonneg f])
  let K : Set E := closedBall 0 R
  have hconvex : Convex ℝ K := convex_closedBall 0 R
  have hclosed : IsClosed (toWeakSpace ℝ E '' K) := by
    have hKclosed : IsClosed K := isClosed_closedBall
    rw [← hKclosed.closure_eq, hconvex.toWeakSpace_closure ℝ]
    exact isClosed_closure
  have hbounded : Bornology.IsBounded
      ((toWeakSpace ℝ E) ⁻¹' (toWeakSpace ℝ E '' K)) := by
    rw [Set.preimage_image_eq K (toWeakSpace ℝ E).injective]
    exact isBounded_closedBall
  have hcompact : IsCompact (toWeakSpace ℝ E '' K) := by
    simpa only [hclosed.closure_eq] using
      WeakCompactness.isCompact_closure_of_isBounded_of_reflexive
        hreflexive (toWeakSpace ℝ E '' K) hbounded
  have hzero : (0 : E) ∈ K := mem_closedBall_self hR.le
  obtain ⟨u, _, htest⟩ := exists_variational_inequality_of_isCompact A f K
    ⟨0, hzero⟩ hconvex hcompact (fun u _ v _ ↦ hmono u v)
    (fun u _ v _ ↦ hhemi u (v - u))
  have hupper : A u u ≤ f u := by
    have h := htest 0 hzero
    simp only [zero_sub, map_neg, sub_apply] at h
    linarith
  have hfu : f u ≤ ‖f‖ * ‖u‖ :=
    (le_abs_self (f u)).trans (f.le_opNorm u)
  have hinterior : ‖u‖ < R := by
    by_contra! hu
    have h := hbound u hu
    nlinarith
  have hpairing (v : E) : 0 ≤ (A u - f) v := by
    let t : ℝ := (R - ‖u‖) / (‖v‖ + 1)
    have hden : 0 < ‖v‖ + 1 := by linarith [norm_nonneg v]
    have ht : 0 < t := div_pos (sub_pos.mpr hinterior) hden
    have ht_mul : t * (‖v‖ + 1) = R - ‖u‖ :=
      div_mul_cancel₀ _ hden.ne'
    have hmem : u + t • v ∈ K := by
      apply mem_closedBall_zero_iff.mpr
      calc
        ‖u + t • v‖ ≤ ‖u‖ + ‖t • v‖ := norm_add_le _ _
        _ = ‖u‖ + t * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        _ ≤ ‖u‖ + t * (‖v‖ + 1) :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) ht.le)
        _ = R := by rw [ht_mul]; ring
    have h := htest (u + t • v) hmem
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h
    exact (mul_nonneg_iff_of_pos_left ht).mp h
  refine ⟨u, ContinuousLinearMap.ext fun v ↦ ?_⟩
  have hpos := hpairing v
  have hneg := hpairing (-v)
  simp only [map_neg] at hneg
  have hzero := le_antisymm (neg_nonneg.mp hneg) hpos
  exact sub_eq_zero.mp hzero

end PDE.Analysis.Operator
