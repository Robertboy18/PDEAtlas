/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Conjugation
public import PDE.Spaces.Sobolev.Fractional.Integer.Energy

/-!
# From integer orders to real orders, for operators on real vector fields

An operator of order `d` on real vector fields in `ℝⁿ` is often known only through bounded lifts
between graph spaces, `VectorH n (k + d) → VectorH n k` for integers `k`. This module turns such
lifts into inequalities for the real-order energies `E_σ` of the complexified components. The
constants are explicit and linear in the norms of the lifts, so a small operator stays small;
the multiplier of the input energy in a lift estimate is the square of such a constant. This
gives the real-order estimates for the Leray projection, linearized transport and convection in
`PDE.Fluid`. The interpolation inequality allows negative energy exponents on these `L²` fields.
Operators between fields with different numbers of components, and operators from or into
spaces of negative order, are not covered.

## Main results

* `besselEnergy_le_of_lift`: a bounded lift `G : VectorH n j → VectorH n l` of an operator `T`
  with `K > 0` and `‖G‖ ≤ K` gives `E_l(Tx) ≤ (c K)² E_j(x)`, with `c = liftConst n j l`.
* `besselEnergy_vectorBaseL2_interpolation`: two energy bounds for an additive `T` interpolate,
  for all real orders and `0 < θ < 1`.
* `besselEnergy_le_of_two_bounds`: the same with one constant at both ends, the ends included.
* `besselEnergy_le_of_four_bounds`: bounds at the four corners `(a, a + d)`,
  `(a + 1, a + 1 + d)`, `(a, a + d + 1)`, `(a + 1, a + d + 2)` give the bound from `a + θ` to
  `a + θ + d + η` with the constant `M^{1-η} N^η`, for `0 ≤ θ, η ≤ 1`.
* `besselEnergy_le_of_lift_pair`: lifts from the order `j` to `l` and from `j + 1` to `l + 1` with
  norms at most `K` give `E_σ(Tx) ≤ (orderConst n j l · K)² E_{σ+j-l}(x)` for every real
  `l ≤ σ ≤ l + 1`.
* `besselEnergy_le_of_ladder`: a ladder `G k : VectorH n (k + 1) → VectorH n k`, compatible in one
  step and with `‖G k‖, ‖G (k + 1)‖ ≤ K`, has
  `E_σ(G r x) ≤ (orderConst n (k + 1) k · K)² E_{σ+1}(x)` for every `r` and every real
  `k ≤ σ ≤ k + 1`. `vectorLowerOrderCLM_ladder` is the compatibility in any number of steps.
* `besselEnergy_le_of_vectorLower`: a ladder of fields `F k ∈ VectorH n k` has
  `E_σ(F r) ≤ (c ‖F k‖)²` for all `r` and every real `σ ≤ k`.
* `exists_besselEnergy_le_of_lifts`: an additive `T` of order `d` with a bounded lift at every
  integer order satisfies, for each real `σ ≥ 0`, `E_σ(Tx) ≤ C E_{σ+d}(x)` for all
  `x ∈ VectorH n d`.

## How it works

Three steps, all on the energies of the complexified components. A lift between graph spaces
gives an energy bound between integer orders, because the graph norm and the energy are
equivalent there (`besselEnergy_vectorBaseL2_le`, `exists_vectorH_of_besselEnergy_lt_top`). Two
energy bounds interpolate by `besselEnergy_interpolation_of_split`. The splitting of the real
method is a Fourier multiplier with a real, even and bounded symbol, so it maps real fields to
real fields, since the transform of a real function is Hermitian
(`isRealL2_iff_isHermitian_fourier`), and it keeps them in `H^d`
(`besselEnergy_fourierMultiplierL2_le`). Finally, a gain `e + η` with `0 ≤ η ≤ 1` comes from the
gains `e` and `e + 1` by the logarithmic convexity of the energy in the order
(`besselEnergy_le_rpow_mul_rpow`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter FourierTransform BesselPotentialSpace SobolevSpace.GraphSpace
open PDE.Analysis.Fourier
open scoped ENNReal NNReal BesselPotentialSpace Sobolev

namespace SobolevSpace.Fractional

variable {n : ℕ}

/-! ## From a lift to an energy bound -/

/-- The constant of `besselEnergy_le_of_lift`. -/
def liftConst (n j l : ℕ) : ℝ :=
  (2 : ℝ) ^ (l - 1) * (1 + (n : ℝ) ^ (l - 1)) * ((n : ℝ) + 1) * (toWkpSpaceNormBound n j + 1)

/-- The constant is positive. -/
theorem liftConst_pos (n j l : ℕ) : 0 < liftConst n j l := by
  have h := toWkpSpaceNormBound_nonneg (n := n) (k := j)
  unfold liftConst
  positivity

/-- **A bounded lift between graph spaces gives an energy bound.** Let `T` map vector fields
in `H^d` to vector fields in `H^e`, and let `G : VectorH n j → VectorH n l`, `d ≤ j`, `e ≤ l`, be
a bounded lift of `T`, in the sense that forgetting the derivatives of `G u` above order `e`
gives `T` applied to `u` with its derivatives above order `d` forgotten. If `‖G‖ ≤ K` with
`K > 0`, then `E_l(Tx) ≤ (c K)² E_j(x)` for every `x`, where `c = liftConst n j l`. A field `x`
of infinite energy is allowed: then the right side is infinite. -/
theorem besselEnergy_le_of_lift {d e j l : ℕ} {hdj : d ≤ j} {hel : e ≤ l}
    {T : VectorH n d → VectorH n e} {G : VectorH n j →L[ℝ] VectorH n l}
    (hG : ∀ u : VectorH n j, vectorLowerOrderCLM hel (G u) =
      T (vectorLowerOrderCLM hdj u))
    {K : ℝ} (hK0 : 0 < K) (hK : ‖G‖ ≤ K) (x : VectorH n d) :
    besselEnergy (l : ℝ) (vectorBaseL2 (T x)) ≤
      ENNReal.ofReal ((liftConst n j l * K) ^ 2) * besselEnergy (j : ℝ) (vectorBaseL2 x) := by
  have hc := liftConst_pos n j l
  by_cases hfin : besselEnergy (j : ℝ) (vectorBaseL2 x) < ⊤
  · -- the field lifts to order `j`
    rw [← vectorBaseL2_vectorLowerOrderCLM (Nat.zero_le d) x] at hfin
    obtain ⟨u, hu, hun⟩ := exists_vectorH_of_besselEnergy_lt_top _ hfin
    rw [vectorBaseL2_vectorLowerOrderCLM (Nat.zero_le d) x] at hun
    have hux : vectorLowerOrderCLM hdj u = x := by
      apply vectorLowerOrderCLM_injective (Nat.zero_le d) isOpen_univ
      rw [vectorLowerOrderCLM_trans_apply]
      exact hu
    have hTx : vectorBaseL2 (T x) = vectorBaseL2 (G u) := by
      rw [← hux, ← hG, vectorBaseL2_vectorLowerOrderCLM]
    have hB := toWkpSpaceNormBound_nonneg (n := n) (k := j)
    set c₁ : ℝ := (2 : ℝ) ^ (l - 1) * (1 + (n : ℝ) ^ (l - 1)) * ((n : ℝ) + 1) with hc₁
    have hc₁0 : 0 ≤ c₁ := by positivity
    have hGu : ‖G u‖ ^ 2 ≤ K ^ 2 * ‖u‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((G.le_opNorm u).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))) 2
    rw [hTx]
    calc besselEnergy (l : ℝ) (vectorBaseL2 (G u))
        ≤ ENNReal.ofReal (c₁ ^ 2 * ‖G u‖ ^ 2) := besselEnergy_vectorBaseL2_le (G u)
      _ ≤ ENNReal.ofReal (c₁ ^ 2 * K ^ 2 * ‖u‖ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hGu (sq_nonneg _)
      _ = ENNReal.ofReal (c₁ ^ 2 * K ^ 2) * ENNReal.ofReal (‖u‖ ^ 2) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (c₁ ^ 2 * K ^ 2) * (ENNReal.ofReal (toWkpSpaceNormBound n j ^ 2) *
            besselEnergy (j : ℝ) (vectorBaseL2 x)) := mul_le_mul' le_rfl hun
      _ = ENNReal.ofReal (c₁ ^ 2 * K ^ 2 * toWkpSpaceNormBound n j ^ 2) *
            besselEnergy (j : ℝ) (vectorBaseL2 x) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((liftConst n j l * K) ^ 2) * besselEnergy (j : ℝ) (vectorBaseL2 x) := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have h1 : c₁ ^ 2 * K ^ 2 * toWkpSpaceNormBound n j ^ 2 =
              (c₁ * toWkpSpaceNormBound n j * K) ^ 2 := by ring
          rw [h1]
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          rw [liftConst, ← hc₁]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hc₁0) hK0.le
  · rw [not_lt, top_le_iff] at hfin
    rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact le_top

/-! ## Interpolation for real fields -/

/-- **Interpolation between Sobolev orders for an additive operator on real vector fields.**
Let `T` be additive from the fields in `H^d` to the fields in `H^e`. If
`E_{b₀}(Tx) ≤ M₀ E_{a₀}(x)` and `E_{b₁}(Tx) ≤ M₁ E_{a₁}(x)` for all `x ∈ VectorH n d`, then
`E_{(1-θ)b₀+θb₁}(Tx) ≤ M₀^{1-θ} M₁^θ E_{(1-θ)a₀+θa₁}(x)` for `0 < θ < 1`. The
energies are those of the complexified components. The pieces of the splitting are real fields
in `H^d` because the symbol of the multiplier is real, even and bounded. -/
theorem besselEnergy_vectorBaseL2_interpolation {d e : ℕ} {T : VectorH n d → VectorH n e}
    (hT : ∀ x y, T (x + y) = T x + T y) {a₀ a₁ b₀ b₁ : ℝ} {M₀ M₁ : ℝ≥0}
    (h0 : ∀ x, besselEnergy b₀ (vectorBaseL2 (T x)) ≤ M₀ * besselEnergy a₀ (vectorBaseL2 x))
    (h1 : ∀ x, besselEnergy b₁ (vectorBaseL2 (T x)) ≤ M₁ * besselEnergy a₁ (vectorBaseL2 x))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (x : VectorH n d) :
    besselEnergy ((1 - θ) * b₀ + θ * b₁) (vectorBaseL2 (T x)) ≤
      (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ *
        besselEnergy ((1 - θ) * a₀ + θ * a₁) (vectorBaseL2 x) := by
  refine besselEnergy_interpolation_of_split (Φ := fun x : VectorH n d ↦ vectorBaseL2 x)
    (Ψ := fun x ↦ vectorBaseL2 (T x)) ?_ h0 h1 hθ0 hθ1 x
  intro x m M hm heven hreal hne
  -- the multiplier maps the real components to real functions
  have hre (i : Fin n) : IsRealL2 (fourierMultiplierL2 m (baseL2 (x i))) := by
    rw [isRealL2_iff_isHermitian_fourier, fourierMultiplierL2_apply, fourier_fourierInv_eq]
    exact (isHermitian_lpSMul_iff m M hm heven hreal hne _).2
      ((isRealL2_iff_isHermitian_fourier _).1 (isRealL2_baseL2 (x i)))
  -- and keeps them in `H^d`
  have hfin (i : Fin n) : besselEnergy (d : ℝ)
      (fun _ : Unit ↦ fourierMultiplierL2 m (baseL2 (x i))) < ⊤ :=
    (besselEnergy_fourierMultiplierL2_le (d : ℝ) m (fun _ : Unit ↦ baseL2 (x i))).trans_lt
      (ENNReal.mul_lt_top (ENNReal.pow_lt_top eNorm_lt_top)
        ((besselEnergy_baseL2_le (x i)).trans_lt ENNReal.ofReal_lt_top))
  choose V hV _ using fun i ↦
    exists_wkpSpace_of_besselEnergy_lt_top (k := d) _ (hre i) (hfin i)
  have hbase (A B : W^{d,2}(ℝ^n)) : baseL2 (A - B) = baseL2 A - baseL2 B := by
    rw [← complexifyL2CLM_base, map_sub, map_sub, complexifyL2CLM_base, complexifyL2CLM_base]
  refine ⟨x - WithLp.toLp 2 V, WithLp.toLp 2 V, fun i ↦ hV i, fun i ↦ ?_, fun i ↦ ?_⟩
  · change baseL2 (x i - V i) = baseL2 (x i) - fourierMultiplierL2 m (baseL2 (x i))
    rw [hbase, hV i]
  · have hsum : T x = T (x - WithLp.toLp 2 V) + T (WithLp.toLp 2 V) := by
      rw [← hT, sub_add_cancel]
    change baseL2 (T x i) = baseL2 (T (x - WithLp.toLp 2 V) i) + baseL2 (T (WithLp.toLp 2 V) i)
    rw [← baseL2_add, hsum]
    rfl

/-! ## The four corners -/

/-- **Interpolation with the same constant at both ends**, the ends included: if
`E_{b₀}(Tx) ≤ K E_{a₀}(x)` and `E_{b₁}(Tx) ≤ K E_{a₁}(x)` with `K ≥ 0`, then
`E_{(1-θ)b₀+θb₁}(Tx) ≤ K E_{(1-θ)a₀+θa₁}(x)` for `0 ≤ θ ≤ 1`. -/
theorem besselEnergy_le_of_two_bounds {d e : ℕ} {T : VectorH n d → VectorH n e}
    (hT : ∀ x y, T (x + y) = T x + T y) {a₀ a₁ b₀ b₁ : ℝ} {K : ℝ≥0}
    (h0 : ∀ x, besselEnergy b₀ (vectorBaseL2 (T x)) ≤ K * besselEnergy a₀ (vectorBaseL2 x))
    (h1 : ∀ x, besselEnergy b₁ (vectorBaseL2 (T x)) ≤ K * besselEnergy a₁ (vectorBaseL2 x))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x : VectorH n d) :
    besselEnergy ((1 - θ) * b₀ + θ * b₁) (vectorBaseL2 (T x)) ≤
      K * besselEnergy ((1 - θ) * a₀ + θ * a₁) (vectorBaseL2 x) := by
  rcases eq_or_lt_of_le hθ0 with rfl | hθ0'
  · simpa using h0 x
  rcases eq_or_lt_of_le hθ1 with rfl | hθ1'
  · simpa using h1 x
  have h := besselEnergy_vectorBaseL2_interpolation hT h0 h1 hθ0' hθ1' x
  rwa [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) hθ0, sub_add_cancel, ENNReal.rpow_one]
    at h

/-- **From four corners to real orders.** Let `T` be additive from real vector fields
in `H^r` to real vector fields in `H^e`.
Suppose that the gain `d` holds with the constant `M` from the orders `a` and `a + 1`, and the
gain `d + 1` with the constant `N` from the same two orders. Then, for `0 ≤ θ ≤ 1` and
`0 ≤ η ≤ 1`, `E_{a+θ+d+η}(Tx) ≤ M^{1-η} N^η E_{a+θ}(x)`.

The source order moves by interpolation (`besselEnergy_vectorBaseL2_interpolation`), the gain by
the logarithmic convexity of the energy (`besselEnergy_le_rpow_mul_rpow`). -/
theorem besselEnergy_le_of_four_bounds {r e : ℕ} {T : VectorH n r → VectorH n e}
    (hT : ∀ x y, T (x + y) = T x + T y) {a d θ η : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {M N : ℝ≥0}
    (h00 : ∀ x, besselEnergy (a + d) (vectorBaseL2 (T x)) ≤ M * besselEnergy a (vectorBaseL2 x))
    (h10 : ∀ x, besselEnergy (a + 1 + d) (vectorBaseL2 (T x)) ≤
      M * besselEnergy (a + 1) (vectorBaseL2 x))
    (h01 : ∀ x, besselEnergy (a + d + 1) (vectorBaseL2 (T x)) ≤
      N * besselEnergy a (vectorBaseL2 x))
    (h11 : ∀ x, besselEnergy (a + 1 + d + 1) (vectorBaseL2 (T x)) ≤
      N * besselEnergy (a + 1) (vectorBaseL2 x)) (x : VectorH n r) :
    besselEnergy (a + θ + d + η) (vectorBaseL2 (T x)) ≤
      (M : ℝ≥0∞) ^ (1 - η) * (N : ℝ≥0∞) ^ η * besselEnergy (a + θ) (vectorBaseL2 x) := by
  have e1 : (1 - θ) * a + θ * (a + 1) = a + θ := by ring
  have e2 : (1 - θ) * (a + d) + θ * (a + 1 + d) = a + θ + d := by ring
  have e3 : (1 - θ) * (a + d + 1) + θ * (a + 1 + d + 1) = a + θ + d + 1 := by ring
  have e4 : (1 - η) * (a + θ + d) + η * (a + θ + d + 1) = a + θ + d + η := by ring
  have s1 := besselEnergy_le_of_two_bounds hT h00 h10 hθ0 hθ1 x
  have s2 := besselEnergy_le_of_two_bounds hT h01 h11 hθ0 hθ1 x
  rw [e1, e2] at s1
  rw [e1, e3] at s2
  have h1η : 0 ≤ 1 - η := by linarith
  have hlog := besselEnergy_le_rpow_mul_rpow (a + θ + d) (a + θ + d + 1) hη0 hη1
    (vectorBaseL2 (T x))
  rw [e4] at hlog
  refine hlog.trans ((mul_le_mul' (ENNReal.rpow_le_rpow s1 h1η)
    (ENNReal.rpow_le_rpow s2 hη0)).trans_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ h1η, ENNReal.mul_rpow_of_nonneg _ _ hη0, mul_mul_mul_comm,
    ← ENNReal.rpow_add_of_nonneg _ _ h1η hη0, sub_add_cancel, ENNReal.rpow_one]

/-! ## Operators of a given order -/

/-- The constant of `besselEnergy_le_of_lift_pair`. -/
def orderConst (n j l : ℕ) : ℝ := liftConst n j l + liftConst n (j + 1) (l + 1)

/-- The constant is positive. -/
theorem orderConst_pos (n j l : ℕ) : 0 < orderConst n j l :=
  add_pos (liftConst_pos _ _ _) (liftConst_pos _ _ _)

/-- **An operator between real orders, with its constant.** Let `T` be additive from real vector
fields in `H^d` to real vector fields in `H^e`, and let `G₀ : VectorH n j → VectorH n l` and
`G₁ : VectorH n (j + 1) → VectorH n (l + 1)` be bounded lifts of `T` with norms at most `K > 0`
(the two orders of `G₁` are parameters `j₁ = j + 1`, `l₁ = l + 1`, so that no cast is needed).
Then, for every real `l ≤ σ ≤ l + 1` and every `x`,

`E_σ(Tx) ≤ (orderConst n j l · K)² E_{σ+j-l}(x)`.

So an operator that loses `j - l` derivatives between two consecutive pairs of integer orders
loses `j - l` derivatives between the real orders in between. The constant is linear in `K`, so
a small operator stays small. -/
theorem besselEnergy_le_of_lift_pair {d e j l j₁ l₁ : ℕ} (hj : j₁ = j + 1) (hl₁ : l₁ = l + 1)
    {hdj : d ≤ j} {hel : e ≤ l} {hdj' : d ≤ j₁} {hel' : e ≤ l₁} {T : VectorH n d → VectorH n e}
    (hT : ∀ x y, T (x + y) = T x + T y)
    {G₀ : VectorH n j →L[ℝ] VectorH n l} {G₁ : VectorH n j₁ →L[ℝ] VectorH n l₁}
    (hG₀ : ∀ u : VectorH n j, vectorLowerOrderCLM hel (G₀ u) = T (vectorLowerOrderCLM hdj u))
    (hG₁ : ∀ u : VectorH n j₁, vectorLowerOrderCLM hel' (G₁ u) =
      T (vectorLowerOrderCLM hdj' u))
    {K : ℝ} (hK0 : 0 < K) (h₀ : ‖G₀‖ ≤ K) (h₁ : ‖G₁‖ ≤ K) {σ : ℝ} (hl : (l : ℝ) ≤ σ)
    (hl1 : σ ≤ l + 1) (x : VectorH n d) :
    besselEnergy σ (vectorBaseL2 (T x)) ≤
      ENNReal.ofReal ((orderConst n j l * K) ^ 2) *
        besselEnergy (σ + j - l) (vectorBaseL2 x) := by
  subst hj hl₁
  have hl₀ := liftConst_pos n j l
  have hl₁ := liftConst_pos n (j + 1) (l + 1)
  have hmono (c : ℝ) (hc : 0 < c) (hle : c ≤ orderConst n j l) :
      ENNReal.ofReal ((c * K) ^ 2) ≤ ((orderConst n j l * K) ^ 2).toNNReal :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hle hK0.le) 2)
  have h0 (y : VectorH n d) : besselEnergy (l : ℝ) (vectorBaseL2 (T y)) ≤
      (((orderConst n j l * K) ^ 2).toNNReal : ℝ≥0∞) *
        besselEnergy (j : ℝ) (vectorBaseL2 y) :=
    (besselEnergy_le_of_lift hG₀ hK0 h₀ y).trans
      (mul_le_mul' (hmono _ hl₀ (by rw [orderConst]; linarith)) le_rfl)
  have h1 (y : VectorH n d) : besselEnergy ((l : ℝ) + 1) (vectorBaseL2 (T y)) ≤
      (((orderConst n j l * K) ^ 2).toNNReal : ℝ≥0∞) *
        besselEnergy ((j : ℝ) + 1) (vectorBaseL2 y) := by
    have h := besselEnergy_le_of_lift hG₁ hK0 h₁ y
    push_cast at h
    exact h.trans (mul_le_mul' (hmono _ hl₁ (by rw [orderConst]; linarith)) le_rfl)
  have hθ0 : 0 ≤ σ - l := by linarith
  have hθ1 : σ - l ≤ 1 := by linarith
  have h := besselEnergy_le_of_two_bounds hT h0 h1 hθ0 hθ1 x
  have e1 : (1 - (σ - l)) * (l : ℝ) + (σ - l) * ((l : ℝ) + 1) = σ := by ring
  have e2 : (1 - (σ - l)) * (j : ℝ) + (σ - l) * ((j : ℝ) + 1) = σ + j - l := by ring
  rwa [e1, e2] at h

/-- **A ladder of operators of order one that is compatible in one step is compatible in every
number of steps.** Let `G k : VectorH n (k + 1) → VectorH n k` be operators such that forgetting
the top order of `G (k + 1) w` gives `G k` applied to `w` with its top order forgotten. Then, for
`r ≤ k`, forgetting the orders above `r` of `G k w` gives `G r` applied to `w` with its orders
above `r + 1` forgotten. -/
theorem vectorLowerOrderCLM_ladder {G : (k : ℕ) → VectorH n (k + 1) →L[ℝ] VectorH n k}
    (hG : ∀ (k : ℕ) (w : VectorH n (k + 2)),
      vectorLower n k (G (k + 1) w) = G k (vectorLower n (k + 1) w))
    {r k : ℕ} (hrk : r ≤ k) (w : VectorH n (k + 1)) :
    vectorLowerOrderCLM hrk (G k w) = G r (vectorLowerOrderCLM (Nat.succ_le_succ hrk) w) := by
  induction k, hrk using Nat.le_induction with
  | base => rw [vectorLowerOrderCLM_refl_apply, vectorLowerOrderCLM_refl_apply]
  | succ k hrk ih =>
    calc vectorLowerOrderCLM (hrk.trans (Nat.le_succ k)) (G (k + 1) w)
        = vectorLowerOrderCLM hrk (vectorLower n k (G (k + 1) w)) :=
          (vectorLowerOrderCLM_trans_apply hrk (Nat.le_succ k) _).symm
      _ = G r (vectorLowerOrderCLM (Nat.succ_le_succ hrk) (vectorLower n (k + 1) w)) := by
          rw [hG, ih]
      _ = _ := congrArg (G r)
          (vectorLowerOrderCLM_trans_apply (Nat.succ_le_succ hrk) (Nat.le_succ (k + 1)) w)

/-- **A ladder of fields that is compatible in one step is compatible in every number of
steps**: if forgetting the top order of `F (k + 1)` gives `F k` for every `k`, then forgetting
the orders above `r` of `F k` gives `F r`, for `r ≤ k`. -/
theorem vectorLowerOrderCLM_of_vectorLower {F : (k : ℕ) → VectorH n k}
    (hF : ∀ k : ℕ, vectorLower n k (F (k + 1)) = F k) {r k : ℕ} (hrk : r ≤ k) :
    vectorLowerOrderCLM hrk (F k) = F r := by
  induction k, hrk using Nat.le_induction with
  | base => rw [vectorLowerOrderCLM_refl_apply]
  | succ k hrk ih =>
    rw [← ih, ← hF k]
    exact (vectorLowerOrderCLM_trans_apply hrk (Nat.le_succ k) _).symm

/-- **A field that has a lift of every integer order has finite energy of every real order**,
with the bound of the lift: if `F k ∈ VectorH n k` is a ladder of fields compatible in one step,
then for all `r`, `k` and every real `σ ≤ k`, `E_σ(F r) ≤ (c ‖F k‖)²` with the constant of
`besselEnergy_vectorBaseL2_le`. The base field of `F r` does not depend on `r`. -/
theorem besselEnergy_le_of_vectorLower {F : (k : ℕ) → VectorH n k}
    (hF : ∀ k : ℕ, vectorLower n k (F (k + 1)) = F k) (r : ℕ) {k : ℕ} {σ : ℝ}
    (hσ : σ ≤ k) :
    besselEnergy σ (vectorBaseL2 (F r)) ≤ ENNReal.ofReal
      (((2 : ℝ) ^ (k - 1) * (1 + (n : ℝ) ^ (k - 1)) * ((n : ℝ) + 1)) ^ 2 * ‖F k‖ ^ 2) := by
  have hbase : vectorBaseL2 (F r) = vectorBaseL2 (F k) := by
    rcases le_total r k with hrk | hkr
    · rw [← vectorLowerOrderCLM_of_vectorLower hF hrk, vectorBaseL2_vectorLowerOrderCLM]
    · rw [← vectorLowerOrderCLM_of_vectorLower hF hkr, vectorBaseL2_vectorLowerOrderCLM]
  rw [hbase]
  exact (besselEnergy_mono hσ _).trans (besselEnergy_vectorBaseL2_le (F k))

/-- **A ladder of operators of order one, between real orders.** Let
`G k : VectorH n (k + 1) → VectorH n k` be a ladder that is compatible in one step, and let
`‖G k‖ ≤ K` and `‖G (k + 1)‖ ≤ K` with `K > 0`. Then, for all `r`, every real `k ≤ σ ≤ k + 1`
and every `x ∈ H^{r+1}`,

`E_σ(G r x) ≤ (orderConst n (k + 1) k · K)² E_{σ+1}(x)`.

For `r > k` the base field of `G r x` is that of `G k` applied to `x` with its orders above
`k + 1` forgotten. -/
theorem besselEnergy_le_of_ladder {G : (k : ℕ) → VectorH n (k + 1) →L[ℝ] VectorH n k}
    (hG : ∀ (k : ℕ) (w : VectorH n (k + 2)),
      vectorLower n k (G (k + 1) w) = G k (vectorLower n (k + 1) w))
    {r k : ℕ} {K : ℝ} (hK0 : 0 < K) (h₀ : ‖G k‖ ≤ K) (h₁ : ‖G (k + 1)‖ ≤ K)
    {σ : ℝ} (hσ : (k : ℝ) ≤ σ) (hσ1 : σ ≤ k + 1) (x : VectorH n (r + 1)) :
    besselEnergy σ (vectorBaseL2 (G r x)) ≤
      ENNReal.ofReal ((orderConst n (k + 1) k * K) ^ 2) *
        besselEnergy (σ + 1) (vectorBaseL2 x) := by
  have e : σ + ((k + 1 : ℕ) : ℝ) - (k : ℝ) = σ + 1 := by
    push_cast
    ring
  have key : ∀ {q : ℕ} (hqk : q ≤ k) (y : VectorH n (q + 1)),
      besselEnergy σ (vectorBaseL2 (G q y)) ≤
        ENNReal.ofReal ((orderConst n (k + 1) k * K) ^ 2) *
          besselEnergy (σ + 1) (vectorBaseL2 y) := by
    intro q hqk y
    have h := besselEnergy_le_of_lift_pair (d := q + 1) (e := q) (j := k + 1) (l := k) rfl rfl
      (T := fun x ↦ G q x) (fun x y ↦ map_add (G q) x y)
      (vectorLowerOrderCLM_ladder hG hqk)
      (vectorLowerOrderCLM_ladder hG (hqk.trans (Nat.le_succ k))) hK0 h₀ h₁ hσ hσ1 y
    rwa [e] at h
  rcases le_total r k with hrk | hkr
  · exact key hrk x
  · have h := key le_rfl (vectorLowerOrderCLM (Nat.succ_le_succ hkr) x)
    rwa [← vectorLowerOrderCLM_ladder hG hkr x, vectorBaseL2_vectorLowerOrderCLM,
      vectorBaseL2_vectorLowerOrderCLM] at h

/-- **An operator of order `d` that lifts to every integer order is bounded from `H^{σ+d}` to
`H^σ` for every real `σ ≥ 0`.** Let `T` be additive on real vector fields in `H^d`, with values
in `L²`, and suppose that for every integer `k` there is a bounded operator from
`VectorH n (k + d)` to `VectorH n k` over `T`. Then for every real `σ ≥ 0` there is `C` with
`E_σ(Tx) ≤ C E_{σ+d}(x)` for all `x`. -/
theorem exists_besselEnergy_le_of_lifts {d : ℕ} {T : VectorH n d → VectorH n 0}
    (hT : ∀ x y, T (x + y) = T x + T y)
    (hlift : ∀ k : ℕ, ∃ G : VectorH n (k + d) →L[ℝ] VectorH n k, ∀ u : VectorH n (k + d),
      vectorLowerOrderCLM (Nat.zero_le k) (G u) =
        T (vectorLowerOrderCLM (Nat.le_add_left d k) u))
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ C : ℝ≥0, ∀ x : VectorH n d,
      besselEnergy σ (vectorBaseL2 (T x)) ≤ C * besselEnergy (σ + d) (vectorBaseL2 x) := by
  obtain ⟨G₀, hG₀⟩ := hlift ⌊σ⌋₊
  obtain ⟨G₁, hG₁⟩ := hlift (⌊σ⌋₊ + 1)
  have hK0 : 0 < ‖G₀‖ + ‖G₁‖ + 1 := by positivity
  refine ⟨((orderConst n (⌊σ⌋₊ + d) ⌊σ⌋₊ * (‖G₀‖ + ‖G₁‖ + 1)) ^ 2).toNNReal, fun x ↦ ?_⟩
  have h := besselEnergy_le_of_lift_pair (Nat.add_right_comm ⌊σ⌋₊ 1 d) rfl hT hG₀ hG₁ hK0
    (by linarith [norm_nonneg G₁]) (by linarith [norm_nonneg G₀])
    (Nat.floor_le hσ) (Nat.lt_floor_add_one σ).le x
  have e : σ + ((⌊σ⌋₊ + d : ℕ) : ℝ) - (⌊σ⌋₊ : ℝ) = σ + d := by
    push_cast
    ring
  rwa [e] at h

end SobolevSpace.Fractional
