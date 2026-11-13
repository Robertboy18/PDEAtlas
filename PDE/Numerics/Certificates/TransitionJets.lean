/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Numerics.IntervalJets
public import PDE.Numerics.Certificates.GridBallTransition
public import CAS.Continuum.Interval.Rational.Meet
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Taylor jets of powers, rational cutoffs and the smooth transition

Interval Taylor jets (`IntervalJets.lean`) of three families of functions of one variable:

* `IntervalJet.pow n k X`, the jet of `t ↦ t^k`;
* `IntervalJet.rationalCutoff n m ν X`, the jet of `t ↦ (1 + (t/ν)^m)⁻¹`;
* `IntervalJet.transition n order L T`, the jet of the smooth transition `χ_e`: zero left of `0`,
  one right of `1`, the composition `(1 + exp(1/τ - 1/(1 - τ)))⁻¹` of jets inside `(0, 1)`, and
  near the ends the flat bounds `‖H_{k-1}‖ e^{2 - 1/δ} (2/δ)^{2k} / k!` of the Taylor
  coefficients, `δ` the distance to the end.

The soundness theorems state `JetEncloses` for each of them.

## Main results

* `JetEncloses.pow`: `IntervalJet.pow n k X` is a jet of `t ↦ t ^ k` on `X`.
* `JetEncloses.rationalCutoff`: a computed `rationalCutoff n m ν X` is a jet of
  `t ↦ (1 + (t / ν) ^ m)⁻¹` on `X`.
* `expNonposRange_sound`: `expNonposRange z` contains `e^z` for `z ≤ 0`.
* `smoothTransition_mem_flat`: for `0 < δ ≤ 1/2` and `t ≤ δ`, `χ_e(t) ∈ [0, e^{2 - 1/δ}]`.
* `seriesTransition_sound`: on `T ⊂ (0, 1)` the composition `seriesTransition` is a jet of `χ_e`.
* `interiorTransition_sound`: on `T ⊂ (0, 1/2]` the closed form `interiorTransition` is a jet of
  `χ_e`.
* `JetEncloses.transition`: a computed `IntervalJet.transition n order L T` is a jet of `χ_e` on
  `T`.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Continuum CAS.Polynomial PDE.Analysis Set Finset

namespace IntervalJet

/-- The jet of `t ↦ t^k` on `X`. -/
def pow (n k : ℕ) (X : RationalInterval) : Array RationalInterval :=
  (List.range k).foldl (fun J _ ↦ mul n J (IntervalJet.id n X)) (const n 1)

/-- The jet of `t ↦ (1 + (t / ν)^m)⁻¹` on `X`. -/
def rationalCutoff (n m : ℕ) (ν : ℚ) (X : RationalInterval) : Option (Array RationalInterval) :=
  inv n (add n (const n 1) (scaleArg n ν⁻¹ (pow n m (X.mul (RationalInterval.const ν⁻¹)))))

/-- The norms `‖H_k‖`, `k < 16`, of the numerators of the derivatives of `χ_e`. -/
def transitionNorms : Array ℚ :=
  ((List.range 16).map fun k ↦ nestedNorm (transitionNumerator k)).toArray

/-- `‖H_k‖`, from `transitionNorms` for `k < 16`. -/
def transitionNorm (k : ℕ) : ℚ :=
  if h : k < transitionNorms.size then transitionNorms[k] else nestedNorm (transitionNumerator k)

/-- The tabulated norm `transitionNorm k` is `‖H_k‖`. -/
theorem transitionNorm_eq (k : ℕ) : transitionNorm k = nestedNorm (transitionNumerator k) := by
  unfold transitionNorm
  split_ifs with h
  · simp [transitionNorms]
  · rfl

/-- The upper bound `c^m` of `e^{-m}`, `c = 0.36788 > e^{-1}`, with the powers rounded up to
`roundBits` relative bits. -/
def expNegBound : ℕ → ℚ
  | 0 => 1
  | m + 1 => RationalInterval.roundUpRel roundBits (expNegBound m * (36788 / 100000))

/-- The enclosure `[0, c^m]` of `e^z` for `z ≤ 0`, `m = min ⌊-z⌋ 2000`. -/
def expNonposRange (z : ℚ) : RationalInterval :=
  RationalInterval.ofBounds 0 (max 0 (expNegBound (min ⌊-z⌋₊ 2000))) (le_max_left _ _)

/-- The numerators `H_k`, `k < 16`, of the derivatives of `χ_e`. -/
def transitionNumerators : Array (List (List ℚ)) :=
  ((List.range 16).map transitionNumerator).toArray

/-- `H_k`, from `transitionNumerators` for `k < 16`. -/
def transitionNumeratorAt (k : ℕ) : List (List ℚ) :=
  if h : k < transitionNumerators.size then transitionNumerators[k] else transitionNumerator k

/-- The tabulated numerator `transitionNumeratorAt k` is `H_k`. -/
theorem transitionNumeratorAt_eq (k : ℕ) : transitionNumeratorAt k = transitionNumerator k := by
  unfold transitionNumeratorAt
  split_ifs with h
  · simp [transitionNumerators]
  · rfl

/-- The flat-end jet of `χ_e` on an interval inside `[0, δ]` (`atOne = false`) or inside
`[1 - δ, 1]`: the value in `[0, E]` or `[1 - E, 1]` with `E ≥ e^{2 - 1/δ}`, and the coefficient
of order `k ≥ 1` in `[-B, B]` with `B ≥ ‖H_{k-1}‖ e^{2 - 1/δ} (2/δ)^{2k} / k!`. -/
def flatTransition (n : ℕ) (δ : ℚ) (atOne : Bool) : Array RationalInterval :=
  let e := expNonposRange (2 - 1 / δ)
  Array.ofFn fun k : Fin (n + 1) ↦ if k.val = 0 then
      (if atOne then (RationalInterval.const 1).sub e else e)
    else
      let B := (RationalInterval.const (transitionNorm (k.val - 1) * (2 / δ) ^ (2 * k.val) /
        k.val.factorial)).mul e
      round (RationalInterval.ofBounds (-|B.hi|) |B.hi| (by linarith [abs_nonneg B.hi]))

/-- The jet of `(1 + exp(1/τ - 1/(1 - τ)))⁻¹` on `T`, by the composition of jets. -/
def seriesTransition (n order : ℕ) (T : RationalInterval) : Option (Array RationalInterval) :=
  (inv n (IntervalJet.id n T)).bind fun a ↦
    (inv n (sub n (const n 1) (IntervalJet.id n T))).bind fun b ↦
      inv n (add n (const n 1) (exp n order (sub n a b)))

/-- The jet of `χ_e` on an interval `T ⊂ (0, 1/2]` from the closed form
`χ_e^(k+1)(t) = σ(1 - σ) H_k(σ, t) / (t(1 - t))^{2k+2}`, `σ = χ_e(t) ∈ [0, E]`,
`E ≥ e^{2 - 1/T.hi}`. -/
def interiorTransition (n : ℕ) (T : RationalInterval) : Option (Array RationalInterval) :=
  let e := expNonposRange (2 - 1 / T.hi)
  (divNonzero (RationalInterval.const 1) (T.mul ((RationalInterval.const 1).sub T))).map
    fun W ↦ Array.ofFn fun k : Fin (n + 1) ↦ if k.val = 0 then e else
      round (((e.mul (RationalInterval.nestedRange (transitionNumeratorAt (k.val - 1)) e T)).mul
        (W.powNat (2 * k.val))).mul (RationalInterval.const (1 / k.val.factorial)))

/-- The jet of `χ_e` at `t` from its jet `J` at `1 - t`: `χ_e(t) = 1 - χ_e(1 - t)` and
`|χ_e^(k)(t)| = |χ_e^(k)(1 - t)|` for `k ≥ 1`. -/
def reflectTransition (n : ℕ) (J : Array RationalInterval) : Array RationalInterval :=
  Array.ofFn fun k : Fin (n + 1) ↦ if k.val = 0 then (RationalInterval.const 1).sub (get J 0)
    else (get J k).hull (get J k).neg

/-- The coefficientwise intersection of two jets of order `n`. -/
def meet (n : ℕ) (A B : Array RationalInterval) : Array RationalInterval :=
  Array.ofFn fun k : Fin (n + 1) ↦ (get A k).meet (get B k)

/-- The intersection of two optional jets. -/
def meetOption (n : ℕ) : Option (Array RationalInterval) → Option (Array RationalInterval) →
    Option (Array RationalInterval)
  | some A, some B => some (meet n A B)
  | some A, none => some A
  | none, B => B

/-- The composition `seriesTransition` when `1/τ, 1/(1 - τ) ≤ L` on `T`. -/
def seriesPart (n order : ℕ) (L : ℚ) (T : RationalInterval) : Option (Array RationalInterval) :=
  if 1 ≤ L * T.lo ∧ 1 ≤ L * (1 - T.hi) then seriesTransition n order T else none

/-- The closed form `interiorTransition` for `T ⊂ (0, 1/2]`, reflected for `T ⊂ [1/2, 1)`. -/
def interiorPart (n : ℕ) (T : RationalInterval) : Option (Array RationalInterval) :=
  if 2 * T.hi ≤ 1 then interiorTransition n T
  else if 1 ≤ 2 * T.lo then
    (interiorTransition n ((RationalInterval.const 1).sub T)).map (reflectTransition n)
  else none

/-- The jet of `χ_e` on `T`: zero for `T ≤ 0`, one for `T ≥ 1`; for `T ⊂ (0, 1)` the intersection
of the composition `seriesTransition` (when `1/τ, 1/(1 - τ) ≤ L` on `T`) and of the closed form
`interiorTransition` (for `T ⊂ (0, 1/2]`, reflected for `T ⊂ [1/2, 1)`); and on an interval
touching an end the flat-end jet with `δ = max d L⁻¹`, `d` the distance to the nearer end, when
`(2n + 2) δ ≤ 1`. -/
def transition (n order : ℕ) (L : ℚ) (T : RationalInterval) : Option (Array RationalInterval) :=
  if T.hi ≤ 0 then some (const n 0)
  else if 1 ≤ T.lo then some (const n 1)
  else if 0 < T.lo ∧ T.hi < 1 then
    meetOption n (seriesPart n order L T) (interiorPart n T)
  else if 0 ≤ T.lo ∧ (2 * n + 2) * max T.hi L⁻¹ ≤ 1 then
    some (flatTransition n (max T.hi L⁻¹) false)
  else if T.hi ≤ 1 ∧ (2 * n + 2) * max (1 - T.lo) L⁻¹ ≤ 1 then
    some (flatTransition n (max (1 - T.lo) L⁻¹) true)
  else none

end IntervalJet

open IntervalJet

/-- A jet of `g` on `X` is a jet of every `f` that agrees with `g` near each point of `X`. -/
theorem JetEncloses.congr {n : ℕ} {J : Array RationalInterval} {f g : ℝ → ℝ}
    {X : RationalInterval} (hJ : JetEncloses n J g X)
    (h : ∀ x, X.MemReal x → g =ᶠ[nhds x] f) : JetEncloses n J f X := by
  intro x hx
  obtain ⟨hg, hJ'⟩ := hJ x hx
  refine ⟨hg.congr_of_eventuallyEq (h x hx).symm, fun k hk ↦ ?_⟩
  rw [← (h x hx).iteratedDeriv_eq k]
  exact hJ' k hk

/-- A jet of `g` is a jet of every `f = g`. -/
theorem JetEncloses.of_eq {n : ℕ} {J : Array RationalInterval} {f g : ℝ → ℝ}
    {X : RationalInterval} (hJ : JetEncloses n J g X) (h : g = f) : JetEncloses n J f X :=
  h ▸ hJ

/-- `IntervalJet.pow n k X` is a jet of `t ↦ t ^ k` on `X`. -/
theorem JetEncloses.pow (n k : ℕ) (X : RationalInterval) :
    JetEncloses n (IntervalJet.pow n k X) (fun x ↦ x ^ k) X := by
  induction k with
  | zero =>
    refine (JetEncloses.const n 1 X).of_eq ?_
    funext x
    simp
  | succ k ih =>
    unfold IntervalJet.pow at ih ⊢
    rw [List.range_succ, List.foldl_append]
    refine (ih.mul (JetEncloses.id n X)).of_eq ?_
    funext x
    simp [pow_succ]

/-- A computed `rationalCutoff n m ν X` is a jet of `t ↦ (1 + (t / ν) ^ m)⁻¹` on `X`. -/
theorem JetEncloses.rationalCutoff {n m : ℕ} {ν : ℚ} {X : RationalInterval}
    {J : Array RationalInterval} (h : IntervalJet.rationalCutoff n m ν X = some J) :
    JetEncloses n J (fun x ↦ (1 + ((ν : ℝ)⁻¹ * x) ^ m)⁻¹) X := by
  have hp := (JetEncloses.pow n m (X.mul (RationalInterval.const ν⁻¹))).scaleArg ν⁻¹
    (contDiff_id.pow m) (X := X) (fun x hx ↦ by
      have := RationalInterval.mul_sound hx (RationalInterval.memReal_const ν⁻¹)
      rwa [mul_comm] at this)
  refine ((JetEncloses.const n 1 X).add hp).inv h |>.of_eq ?_
  funext x
  push_cast
  rfl

/-- `e^{-m} ≤ expNegBound m`. -/
theorem exp_neg_le_expNegBound (m : ℕ) : Real.exp (-(m : ℝ)) ≤ expNegBound m := by
  induction m with
  | zero => simp [expNegBound]
  | succ m ih =>
    have hc : Real.exp (-1) ≤ ((36788 / 100000 : ℚ) : ℝ) := by
      rw [Real.exp_neg]
      have := Real.exp_one_gt_d9
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      push_cast
      linarith
    have h0 : 0 ≤ Real.exp (-(m : ℝ)) := (Real.exp_pos _).le
    calc Real.exp (-((m + 1 : ℕ) : ℝ)) = Real.exp (-(m : ℝ)) * Real.exp (-1) := by
          rw [← Real.exp_add]; push_cast; ring_nf
      _ ≤ (expNegBound m : ℝ) * ((36788 / 100000 : ℚ) : ℝ) :=
          mul_le_mul ih hc (Real.exp_pos _).le (h0.trans ih)
      _ ≤ (expNegBound (m + 1) : ℝ) := by
          rw [expNegBound]
          exact_mod_cast RationalInterval.le_roundUpRel roundBits _

/-- `expNonposRange z` contains `e^z` for `z ≤ 0`. -/
theorem expNonposRange_sound {z : ℚ} (hz : z ≤ 0) :
    (expNonposRange z).MemReal (Real.exp z) := by
  constructor
  · change ((0 : ℚ) : ℝ) ≤ _
    push_cast
    exact (Real.exp_pos _).le
  · change Real.exp z ≤ ((max 0 (expNegBound (min ⌊-z⌋₊ 2000)) : ℚ) : ℝ)
    have hm : (z : ℝ) ≤ -((min ⌊-z⌋₊ 2000 : ℕ) : ℝ) := by
      have := Nat.floor_le (neg_nonneg.mpr hz)
      have : ((⌊-z⌋₊ : ℕ) : ℝ) ≤ -(z : ℝ) := by exact_mod_cast this
      have : ((min ⌊-z⌋₊ 2000 : ℕ) : ℝ) ≤ ((⌊-z⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast min_le_left _ _
      linarith
    calc Real.exp z ≤ Real.exp (-((min ⌊-z⌋₊ 2000 : ℕ) : ℝ)) := Real.exp_le_exp.mpr hm
      _ ≤ expNegBound (min ⌊-z⌋₊ 2000) := exp_neg_le_expNegBound _
      _ ≤ _ := by exact_mod_cast le_max_right _ _

/-- For `0 < δ ≤ 1/2` and `t ≤ δ`, the enclosure `expNonposRange (2 - 1/δ)` of
`[0, e^{2 - 1/δ}]` contains `χ_e(t)`. -/
theorem smoothTransition_mem_flat {δ : ℚ} {t : ℝ} (hδ : (0 : ℝ) < δ) (hδ2 : 2 * (δ : ℝ) ≤ 1)
    (ht : t ≤ δ) : (expNonposRange (2 - 1 / δ)).MemReal (Real.smoothTransition t) := by
  have hz : (2 - 1 / δ : ℚ) ≤ 0 := by
    have : (2 : ℝ) - 1 / δ ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hδ]
      linarith
    exact_mod_cast this
  have he := expNonposRange_sound hz
  constructor
  · change ((0 : ℚ) : ℝ) ≤ _
    push_cast
    exact Real.smoothTransition.nonneg t
  · refine le_trans ?_ he.2
    rcases le_or_gt t 0 with h0 | h0
    · rw [Real.smoothTransition.zero_of_nonpos h0]
      exact (Real.exp_pos _).le
    · refine (smoothTransition_le_exp h0 (by linarith)).trans (Real.exp_le_exp.mpr ?_)
      push_cast
      have : 1 / (δ : ℝ) ≤ 1 / t := one_div_le_one_div_of_le h0 ht
      linarith

/-- If `B ∋ w` and `|v| ≤ w`, then `v ∈ [-|B.hi|, |B.hi|]`. -/
theorem memReal_ofBounds_abs {B : RationalInterval} {w v : ℝ} {h : -|B.hi| ≤ |B.hi|}
    (hB : B.MemReal w) (hv : |v| ≤ w) :
    (RationalInterval.ofBounds (-|B.hi|) |B.hi| h).MemReal v := by
  have hw : w ≤ ((|B.hi| : ℚ) : ℝ) := hB.2.trans (by exact_mod_cast le_abs_self B.hi)
  have h1 := neg_abs_le v
  have h2 := le_abs_self v
  constructor
  · change (((-|B.hi|) : ℚ) : ℝ) ≤ v
    push_cast at hw ⊢
    linarith
  · change v ≤ ((|B.hi| : ℚ) : ℝ)
    push_cast at hw ⊢
    linarith

/-- The bound `|v| ≤ N e^{2 - 1/δ} (2/δ)^{2k+2}` on a derivative gives
`|v / (k + 1)!| ≤ N (2/δ)^{2(k+1)} e^{2 - 1/δ} / (k + 1)!` for its Taylor coefficient. -/
theorem flat_coeff_bound {δ N v : ℝ} {k : ℕ}
    (hb : |v| ≤ N * (Real.exp (2 - 1 / δ) * (2 / δ) ^ (2 * k + 2))) :
    |v / (k + 1).factorial| ≤ N * (2 / δ) ^ (2 * (k + 1)) / (k + 1).factorial *
      Real.exp (2 - 1 / δ) := by
  have hf : (0 : ℝ) < (k + 1).factorial := by positivity
  rw [abs_div, abs_of_pos hf, show 2 * (k + 1) = 2 * k + 2 by ring]
  calc |v| / (k + 1).factorial ≤
        N * (Real.exp (2 - 1 / δ) * (2 / δ) ^ (2 * k + 2)) / (k + 1).factorial :=
      div_le_div_of_nonneg_right hb hf.le
    _ = _ := by ring

/-- On `T ⊂ (0, 1)` a computed `seriesTransition n order T` is a jet of `χ_e`. -/
theorem seriesTransition_sound {n order : ℕ} {T : RationalInterval} {J : Array RationalInterval}
    (h : seriesTransition n order T = some J) (hlo : 0 < T.lo) (hhi : T.hi < 1) :
    JetEncloses n J Real.smoothTransition T := by
  simp only [seriesTransition, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, hJ⟩ := h
  have hA := (JetEncloses.id n T).inv ha
  have hB := ((JetEncloses.const n 1 T).sub (JetEncloses.id n T)).inv hb
  have hE := ((JetEncloses.const n 1 T).add ((hA.sub hB).exp order)).inv hJ
  refine hE.congr fun x hx ↦ ?_
  have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hlo) hx.1
  have hx1 : x < 1 := lt_of_le_of_lt hx.2 (by exact_mod_cast hhi)
  filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy
  rw [smoothTransition_eq_inv_one_add_exp hy.1 hy.2]
  push_cast
  simp only [one_div]

/-- On `T ⊂ (0, 1/2]` a computed `interiorTransition n T` is a jet of `χ_e`. -/
theorem interiorTransition_sound {n : ℕ} {T : RationalInterval} {J : Array RationalInterval}
    (h : interiorTransition n T = some J) (hlo : 0 < T.lo) (hhi : 2 * T.hi ≤ 1) :
    JetEncloses n J Real.smoothTransition T := by
  simp only [interiorTransition, Option.map_eq_some_iff] at h
  obtain ⟨W, hW, rfl⟩ := h
  intro x hx
  have hlo' : (0 : ℝ) < T.lo := by exact_mod_cast hlo
  have hhi' : 2 * (T.hi : ℝ) ≤ 1 := by exact_mod_cast hhi
  have hx0 : 0 < x := hlo'.trans_le hx.1
  have hx1 : x < 1 := by linarith [hx.2]
  have hδ : (0 : ℝ) < T.hi := hx0.trans_le hx.2
  have hσ := smoothTransition_mem_flat (δ := T.hi) hδ hhi' hx.2
  refine ⟨Real.smoothTransition.contDiff.contDiffAt, fun k hk ↦ ?_⟩
  change (get _ k).MemReal _
  rw [get_ofFn _ hk]
  rcases k with _ | k
  · simpa using hσ
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    refine round_sound ?_
    have hσ1 : (expNonposRange (2 - 1 / T.hi)).MemReal
        (Real.smoothTransition x * (1 - Real.smoothTransition x)) := by
      have h0 := Real.smoothTransition.nonneg x
      have h1 := Real.smoothTransition.le_one x
      refine ⟨?_, ?_⟩
      · change ((0 : ℚ) : ℝ) ≤ _
        push_cast
        exact mul_nonneg h0 (by linarith)
      · refine le_trans ?_ hσ.2
        nlinarith
    have hH := RationalInterval.nestedRange_sound (transitionNumeratorAt k) hσ hx
    have hWx := (divNonzero_sound hW (RationalInterval.memReal_const 1)
      (RationalInterval.mul_sound hx (RationalInterval.sub_sound
        (RationalInterval.memReal_const 1) hx))).2
    have hP := RationalInterval.powNat_sound hWx (2 * (k + 1))
    have h := RationalInterval.mul_sound (RationalInterval.mul_sound
      (RationalInterval.mul_sound hσ1 hH) hP)
      (RationalInterval.memReal_const (1 / ((k + 1).factorial : ℚ)))
    rw [iteratedDeriv_succ_smoothTransition k]
    simp only [transitionNumeratorAt_eq] at h ⊢
    convert h using 1
    push_cast
    rw [show 2 * k + 2 = 2 * (k + 1) by ring]
    have hB : x * (1 - x) ≠ 0 := (mul_pos hx0 (by linarith)).ne'
    field_simp
    rw [one_div, inv_pow, mul_inv_cancel_right₀ (pow_ne_zero _ hB)]

/-- A jet of `χ_e` on `1 - T` reflects to the jet `reflectTransition n J` of `χ_e` on `T`. -/
theorem reflectTransition_sound {n : ℕ} {T : RationalInterval} {J : Array RationalInterval}
    (hJ : JetEncloses n J Real.smoothTransition ((RationalInterval.const 1).sub T)) :
    JetEncloses n (reflectTransition n J) Real.smoothTransition T := by
  intro x hx
  have hx' : ((RationalInterval.const 1).sub T).MemReal (1 - x) := by
    simpa using RationalInterval.sub_sound (RationalInterval.memReal_const 1) hx
  obtain ⟨-, hJ'⟩ := hJ (1 - x) hx'
  refine ⟨Real.smoothTransition.contDiff.contDiffAt, fun k hk ↦ ?_⟩
  change (get (reflectTransition n J) k).MemReal _
  rw [reflectTransition, get_ofFn _ hk]
  rcases k with _ | k
  · simp only [↓reduceIte, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have h0 := hJ' 0 (Nat.zero_le n)
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h0
    have h := RationalInterval.sub_sound (RationalInterval.memReal_const 1) h0
    rw [smoothTransition_one_sub, Rat.cast_one, sub_sub_cancel] at h
    exact h
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    have hm := hJ' (k + 1) hk
    have habs := abs_iteratedDeriv_succ_smoothTransition_one_sub k (1 - x)
    rw [sub_sub_cancel] at habs
    rcases abs_eq_abs.mp habs with he | he
    · rw [he]
      exact RationalInterval.memReal_hull_left hm
    · rw [he, neg_div]
      exact RationalInterval.memReal_hull_right (RationalInterval.neg_sound hm)

/-- The coefficientwise meet of two optional jets of `f` on `X` is a jet of `f` on `X`. -/
theorem JetEncloses.meetOption {n : ℕ} {f : ℝ → ℝ} {X : RationalInterval}
    {A B : Option (Array RationalInterval)} {J : Array RationalInterval}
    (hA : ∀ K, A = some K → JetEncloses n K f X) (hB : ∀ K, B = some K → JetEncloses n K f X)
    (h : IntervalJet.meetOption n A B = some J) : JetEncloses n J f X := by
  rcases A with _ | A <;> rcases B with _ | B <;> simp only [IntervalJet.meetOption,
    Option.some.injEq, reduceCtorEq] at h
  · exact hB _ (by rw [h])
  · subst h; exact hA _ rfl
  · subst h
    intro x hx
    obtain ⟨hc, hA'⟩ := hA A rfl x hx
    obtain ⟨-, hB'⟩ := hB B rfl x hx
    refine ⟨hc, fun k hk ↦ ?_⟩
    change (get (IntervalJet.meet n A B) k).MemReal _
    rw [IntervalJet.meet, get_ofFn _ hk]
    exact RationalInterval.memReal_meet (hA' k hk) (hB' k hk)

/-- **Jets of the smooth transition.** A computed `IntervalJet.transition n order L T` is a jet of
`χ_e` on `T`. -/
theorem JetEncloses.transition {n order : ℕ} {L : ℚ} {T : RationalInterval}
    {J : Array RationalInterval} (h : IntervalJet.transition n order L T = some J) :
    JetEncloses n J Real.smoothTransition T := by
  have hcd : ∀ x, ContDiffAt ℝ n Real.smoothTransition x := fun x ↦
    Real.smoothTransition.contDiff.contDiffAt
  unfold IntervalJet.transition at h
  split_ifs at h with h0 h1 h2 h3 h4
  · simp only [Option.some.injEq] at h
    subst h
    intro x hx
    have hx0 : x ≤ 0 := hx.2.trans (by exact_mod_cast h0)
    refine ⟨hcd x, fun k hk ↦ ?_⟩
    change (get (IntervalJet.const n 0) k).MemReal _
    rw [IntervalJet.const, get_ofFn _ hk]
    rcases k with _ | k
    · simp only [↓reduceIte, iteratedDeriv_zero, Real.smoothTransition.zero_of_nonpos hx0,
        zero_div]
      exact_mod_cast RationalInterval.memReal_const 0
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        iteratedDeriv_succ_smoothTransition_of_nonpos k hx0, zero_div]
      exact_mod_cast RationalInterval.memReal_const 0
  · simp only [Option.some.injEq] at h
    subst h
    intro x hx
    have hx1 : 1 ≤ x := (by exact_mod_cast h1 : (1 : ℝ) ≤ T.lo).trans hx.1
    refine ⟨hcd x, fun k hk ↦ ?_⟩
    change (get (IntervalJet.const n 1) k).MemReal _
    rw [IntervalJet.const, get_ofFn _ hk]
    rcases k with _ | k
    · simp only [↓reduceIte, iteratedDeriv_zero, Real.smoothTransition.one_of_one_le hx1,
        Nat.factorial_zero, Nat.cast_one, div_one]
      exact_mod_cast RationalInterval.memReal_const 1
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        iteratedDeriv_succ_smoothTransition_of_one_le k hx1, zero_div]
      exact_mod_cast RationalInterval.memReal_const 0
  · refine JetEncloses.meetOption (fun K hK ↦ ?_) (fun K hK ↦ ?_) h
    · unfold seriesPart at hK
      split_ifs at hK
      exact seriesTransition_sound hK h2.1 h2.2
    · unfold interiorPart at hK
      split_ifs at hK with h5 h6
      · exact interiorTransition_sound hK h2.1 h5
      · simp only [Option.map_eq_some_iff] at hK
        obtain ⟨J', hJ', rfl⟩ := hK
        refine reflectTransition_sound (interiorTransition_sound hJ' ?_ ?_)
        · rw [RationalInterval.sub_lo, RationalInterval.const_lo]; linarith [h2.2]
        · rw [RationalInterval.sub_hi, RationalInterval.const_hi]; linarith [h6]
  · simp only [Option.some.injEq] at h
    subst h
    set δ := max T.hi L⁻¹ with hδdef
    have hhi : (T.hi : ℝ) ≤ δ := by
      have : T.hi ≤ δ := le_max_left _ _
      exact_mod_cast this
    have hδ : (0 : ℝ) < δ :=
      lt_of_lt_of_le (by exact_mod_cast not_le.mp h0 : (0 : ℝ) < T.hi) hhi
    intro x hx
    have hxδ : x ≤ δ := hx.2.trans hhi
    refine ⟨hcd x, fun k hk ↦ ?_⟩
    change (get (flatTransition n δ false) k).MemReal _
    rw [flatTransition, get_ofFn _ hk]
    rcases k with _ | k
    · simp only [↓reduceIte, Bool.false_eq_true, iteratedDeriv_zero, Nat.factorial_zero,
        Nat.cast_one, div_one]
      exact smoothTransition_mem_flat hδ (by
        have h' : ((2 * n + 2 : ℕ) : ℝ) * δ ≤ 1 := by exact_mod_cast h3.2
        push_cast at h'
        nlinarith [hδ.le]) hxδ
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      have hb := abs_iteratedDeriv_succ_smoothTransition_le_of_le (k := k) hδ hxδ (by
        have h3' : ((2 * n + 2 : ℕ) : ℝ) * δ ≤ 1 := by exact_mod_cast h3.2
        have hkn : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk
        push_cast at h3'
        nlinarith)
      refine round_sound (memReal_ofBounds_abs (RationalInterval.mul_sound
        (RationalInterval.memReal_const _) (expNonposRange_sound (z := 2 - 1 / δ) ?_)) ?_)
      · rw [sub_nonpos, le_div_iff₀ (by exact_mod_cast hδ)]
        have : (2 : ℝ) * δ ≤ 1 := by
          have h' : ((2 * n + 2 : ℕ) : ℝ) * δ ≤ 1 := by exact_mod_cast h3.2
          push_cast at h'
          nlinarith [hδ.le]
        exact_mod_cast this
      rw [transitionNorm_eq]
      push_cast
      exact flat_coeff_bound hb
  · simp only [Option.some.injEq] at h
    subst h
    set δ := max (1 - T.lo) L⁻¹ with hδdef
    have hδ0 : (0 : ℝ) < 1 - T.lo := by
      have := not_le.mp h1
      have : (T.lo : ℝ) < 1 := by exact_mod_cast this
      linarith
    have hδle : (1 - T.lo : ℝ) ≤ δ := by
      have : (1 - T.lo : ℚ) ≤ δ := le_max_left _ _
      exact_mod_cast this
    have hδ : (0 : ℝ) < δ := hδ0.trans_le hδle
    intro x hx
    have hxδ : 1 - (δ : ℝ) ≤ x := by linarith [hx.1]
    refine ⟨hcd x, fun k hk ↦ ?_⟩
    change (get (flatTransition n δ true) k).MemReal _
    rw [flatTransition, get_ofFn _ hk]
    rcases k with _ | k
    · simp only [↓reduceIte, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      have hm := smoothTransition_mem_flat (t := 1 - x) hδ (by
        have h' : ((2 * n + 2 : ℕ) : ℝ) * δ ≤ 1 := by exact_mod_cast h4.2
        push_cast at h'
        nlinarith [hδ.le]) (by linarith)
      have := RationalInterval.sub_sound (RationalInterval.memReal_const 1) hm
      rw [smoothTransition_one_sub] at this
      simpa using this
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      have hb := abs_iteratedDeriv_succ_smoothTransition_le_of_one_sub_le (k := k) hδ
        hxδ (by
        have h4' : ((2 * n + 2 : ℕ) : ℝ) * δ ≤ 1 := by exact_mod_cast h4.2
        have hkn : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk
        push_cast at h4' ⊢
        nlinarith)
      refine round_sound (memReal_ofBounds_abs (RationalInterval.mul_sound
        (RationalInterval.memReal_const _) (expNonposRange_sound (z := 2 - 1 / δ) ?_)) ?_)
      · rw [sub_nonpos, le_div_iff₀ (by exact_mod_cast hδ)]
        have : (2 : ℝ) * δ ≤ 1 := by
          have h' : ((2 * n + 2 : ℕ) : ℝ) * δ ≤ 1 := by exact_mod_cast h4.2
          push_cast at h'
          nlinarith [hδ.le]
        exact_mod_cast this
      rw [transitionNorm_eq]
      push_cast
      exact flat_coeff_bound hb

end CAS.Numerics
