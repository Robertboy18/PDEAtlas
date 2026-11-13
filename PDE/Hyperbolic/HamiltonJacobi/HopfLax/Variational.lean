/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Basic
import CAS.ExactTactic

/-!
# Compact attainment and dynamic programming

We minimize over velocities:
`u(t,x) = inf_q (g(x - t • q) + t L(q))`.
For positive time this is the usual minimization over footpoints. At zero
every competitor is exactly `g(x)`, so the formula already includes the datum.

Superlinearity and an affine norm lower bound on the datum make the values
finite at nonnegative times. For continuous data and a continuous cost on a
proper space, the infimum is attained at positive time. This includes bounded
continuous data and unbounded Lipschitz data.
Convexity enters only when two successive velocities are replaced by their
time-weighted average. Comparing paths with the same velocity preserves
spatial moduli without convexity or attainment.

The footpoint form is the Hopf–Lax formula (21) of Evans, §3.3.2(b); Evans leaves the attainment
of its minimum as an exercise in the proof of Theorem 4. Dynamic programming is the functional
identity (22) of Lemma 1, and the spatial Lipschitz and initial-trace estimates for Lipschitz data
come from the proof of Lemma 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 4 and Lemmas 1-2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

set_option linter.missingDocs true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cost of following the straight path of velocity `q` for time `t`. -/
def cost (L g : E → ℝ) (t : ℝ) (x q : E) : ℝ :=
  g (x - t • q) + t * L q

/-- Hopf–Lax evolution, parametrized by velocities rather than footpoints.
Only nonnegative times have the variational interpretation used here. -/
def value (L g : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  sInf (Set.range (cost L g t x))

/-- At nonzero time, changing variables `y = x - t • q` recovers the usual
footpoint formula. This identity uses no convexity or attainment hypothesis. -/
theorem value_eq_inf_footpoints (L g : E → ℝ) {t : ℝ} (ht : t ≠ 0) (x : E) :
    value L g t x = sInf (Set.range fun y : E ↦ g y + t * L (t⁻¹ • (x - y))) := by
  unfold value
  congr 1
  ext a
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨x - t • q, ?_⟩
    simp [cost, smul_smul, ht]
  · rintro ⟨y, rfl⟩
    refine ⟨t⁻¹ • (x - y), ?_⟩
    simp [cost, smul_smul, ht]

/-- The velocity formula gives the initial datum at zero without assigning
a separate value to a singular quotient. -/
@[simp] theorem value_zero (L g : E → ℝ) (x : E) :
    value L g 0 x = g x := by
  change sInf (Set.range fun q : E ↦ g (x - (0 : ℝ) • q) + 0 * L q) = g x
  simp

/-- An affine lower bound on the datum and a norm lower bound on `L` control
every path cost, including for data unbounded below. -/
theorem cost_lower_of_norm_lower_bound {L g : E → ℝ} {K : NNReal} {A B D t : ℝ}
    (hg : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y) (hB : ∀ q, D * ‖q‖ - B ≤ L q) (ht : 0 ≤ t) (x q : E) :
    -A - (K : ℝ) * ‖x‖ + t * ((D - K) * ‖q‖ - B) ≤ cost L g t x q := by
  have hn : ‖x - t • q‖ ≤ ‖x‖ + t * ‖q‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] using norm_sub_le x (t • q)
  have hKn := mul_le_mul_of_nonneg_left hn K.2
  have hdatum := hg (x - t • q)
  have hcost := mul_le_mul_of_nonneg_left (hB q) ht
  calc
    -A - (K : ℝ) * ‖x‖ + t * ((D - K) * ‖q‖ - B) =
        (-A - (K : ℝ) * (‖x‖ + t * ‖q‖)) + t * (D * ‖q‖ - B) := by ring
    _ ≤ g (x - t • q) + t * L q := add_le_add ((sub_le_sub_left hKn (-A)).trans hdatum) hcost
    _ = cost L g t x q := rfl

/-- Superlinearity prevents the infimum from escaping to minus infinity for
any datum with an affine norm lower bound. -/
theorem bddBelow_cost_of_norm_lower_bound {L g : E → ℝ} (hL : Superlinear L) {K : NNReal} {A : ℝ}
    (hg : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    BddBelow (Set.range (cost L g t x)) := by
  obtain ⟨B, hB⟩ := hL K
  refine ⟨-A - (K : ℝ) * ‖x‖ - t * B, ?_⟩
  rintro _ ⟨q, rfl⟩
  simpa using cost_lower_of_norm_lower_bound hg hB ht x q

/-- The evolved datum retains its affine norm lower bound; only the additive
constant changes with time. -/
theorem norm_lower_bound_value {L g : E → ℝ} {K : NNReal} {A B t : ℝ}
    (hg : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y) (hB : ∀ q, (K : ℝ) * ‖q‖ - B ≤ L q) (ht : 0 ≤ t) (x : E) :
    -(A + t * B) - (K : ℝ) * ‖x‖ ≤ value L g t x := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨q, rfl⟩
  have h := cost_lower_of_norm_lower_bound hg hB ht x q
  simp only [sub_self, zero_mul, zero_sub] at h
  dsimp only [cost] at h ⊢
  linarith

/-- Continuous data with an affine norm lower bound attain their Hopf–Lax
infimum at positive time. Superlinearity confines all better competitors to one compact ball. -/
theorem exists_minimizer_of_norm_lower_bound [ProperSpace E] {L g : E → ℝ} (hcont : Continuous L)
    (hL : Superlinear L) (hg : Continuous g) {K : NNReal} {A : ℝ}
    (hlower : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y) {t : ℝ} (ht : 0 < t) (x : E) :
    ∃ q, value L g t x = cost L g t x q ∧ ∀ r, cost L g t x q ≤ cost L g t x r := by
  obtain ⟨B, hB⟩ := hL ((K : ℝ) + 1)
  let R : ℝ := max 0 ((g x + t * L 0 + A + (K : ℝ) * ‖x‖ + t * B) / t)
  have hR : 0 ≤ R := le_max_left _ _
  have hc : Continuous (cost L g t x) :=
    (hg.comp (continuous_const.sub (continuous_const.smul continuous_id))).add
      (continuous_const.mul hcont)
  obtain ⟨q, _, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    ⟨0, by simpa using hR⟩ hc.continuousOn
  have hmin0 : cost L g t x q ≤ cost L g t x 0 := hmin (by simpa using hR)
  have hglobal : ∀ r, cost L g t x q ≤ cost L g t x r := by
    intro r
    by_cases hr : r ∈ Metric.closedBall (0 : E) R
    · exact hmin hr
    · have hnr : R < ‖r‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hr
      have hlarge : g x + t * L 0 + A + (K : ℝ) * ‖x‖ + t * B < ‖r‖ * t :=
        (div_lt_iff₀ ht).mp ((le_max_right _ _).trans_lt hnr)
      have hl := cost_lower_of_norm_lower_bound hlower hB ht.le x r
      simp only [add_sub_cancel_left, one_mul] at hl
      have hz : cost L g t x 0 = g x + t * L 0 := by simp [cost]
      have hzero : cost L g t x 0 ≤ cost L g t x r := by linarith
      exact hmin0.trans hzero
  refine ⟨q, le_antisymm ?_ ?_, hglobal⟩
  · exact csInf_le (bddBelow_cost_of_norm_lower_bound hL hlower ht.le x) ⟨q, rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨r, rfl⟩; exact hglobal r)

omit [NormedSpace ℝ E] in
/-- The Lipschitz estimate from the origin supplies the affine norm lower bound
used to make the variational infimum finite. -/
private theorem lipschitz_norm_lower_bound {g : E → ℝ} {K : NNReal}
    (hg : LipschitzWith K g) (y : E) :
    -(-g 0) - (K : ℝ) * ‖y‖ ≤ g y := by
  have h := hg.dist_le_mul y 0
  rw [Real.dist_eq, dist_zero_right] at h
  linarith [neg_le_abs (g y - g 0)]

/-- Comparing equal velocities preserves any bound on translated spatial
increments of the datum. Neither convexity nor attainment is needed. -/
theorem abs_value_sub_le_of_translate_bound {L g : E → ℝ} (hL : Superlinear L) {K : NNReal} {A : ℝ}
    (hlower : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y) {t : ℝ} (ht : 0 ≤ t) (x y : E) {c : ℝ}
    (hg : ∀ z, |g (x - z) - g (y - z)| ≤ c) :
    |value L g t x - value L g t y| ≤ c := by
  have hupper : ∀ a b : E, (∀ z, g (a - z) - g (b - z) ≤ c) →
      value L g t a - value L g t b ≤ c := by
    intro a b hab
    suffices h : value L g t a - c ≤ value L g t b by linarith
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨q, rfl⟩
    have hv : value L g t a ≤ cost L g t a q :=
      csInf_le (bddBelow_cost_of_norm_lower_bound hL hlower ht a) ⟨q, rfl⟩
    have hd := hab (t • q)
    dsimp only [cost] at hv ⊢
    linarith
  exact abs_sub_le_iff.mpr ⟨hupper x y fun z ↦ (le_abs_self _).trans (hg z),
    hupper y x fun z ↦ by linarith [(neg_le_abs (g (x - z) - g (y - z))).trans (hg z)]⟩

/-- A global affine spatial modulus passes to every nonnegative time with
exactly the same tolerance and slope. -/
theorem abs_value_sub_le_of_modulus {L g : E → ℝ} (hL : Superlinear L) {K : NNReal} {A ε D : ℝ}
    (hlower : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y) (hg : ∀ x y, |g x - g y| ≤ ε + D * dist x y) {t : ℝ}
    (ht : 0 ≤ t) (x y : E) :
    |value L g t x - value L g t y| ≤ ε + D * dist x y :=
  abs_value_sub_le_of_translate_bound hL hlower ht x y fun z ↦ by
    simpa only [dist_sub_right] using hg (x - z) (y - z)

/-- A spatial modulus up to an additive tolerance gives a uniform initial
trace bound. The affine lower bound on `L` controls all velocities. -/
theorem abs_value_sub_data_le_of_modulus {L g : E → ℝ} {ε K C t : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ x y, |g x - g y| ≤ ε + K * dist x y) (hbound : ∀ q, K * ‖q‖ - C ≤ L q) (hLC : L 0 ≤ C)
    (ht : 0 ≤ t) (x : E) :
    |value L g t x - g x| ≤ ε + C * t := by
  have hcost : ∀ q, g x - ε - t * C ≤ cost L g t x q := by
    intro q
    have hd := hg x (x - t • q)
    have hn : dist x (x - t • q) = t * ‖q‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    rw [hn] at hd
    have hdatum := (le_abs_self (g x - g (x - t • q))).trans hd
    have hL := mul_le_mul_of_nonneg_left (hbound q) ht
    dsimp only [cost]
    linarith
  have hb : BddBelow (Set.range (cost L g t x)) :=
    ⟨g x - ε - t * C, by rintro _ ⟨q, rfl⟩; exact hcost q⟩
  have hlo : g x - ε - t * C ≤ value L g t x :=
    le_csInf (Set.range_nonempty _) (by rintro _ ⟨q, rfl⟩; exact hcost q)
  have hhi : value L g t x ≤ cost L g t x 0 := csInf_le hb ⟨0, rfl⟩
  simp only [cost, smul_zero, sub_zero] at hhi
  have hLCt := mul_le_mul_of_nonneg_left hLC ht
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A norm lower bound on `L` offsets the linear variation of Lipschitz data. -/
theorem cost_lower {L g : E → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    {A B t : ℝ} (hB : ∀ q, A * ‖q‖ - B ≤ L q) (ht : 0 ≤ t) (x q : E) :
    g x + t * ((A - K) * ‖q‖ - B) ≤ cost L g t x q := by
  have hd := hg.dist_le_mul x (x - t • q)
  have hn : dist x (x - t • q) = t * ‖q‖ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [hn, Real.dist_eq] at hd
  have hlow := (le_abs_self (g x - g (x - t • q))).trans hd
  have hmul := mul_le_mul_of_nonneg_left (hB q) ht
  dsimp only [cost]
  linarith

/-- Positive and zero-time costs have a lower bound. -/
theorem bddBelow_cost {L g : E → ℝ} (hL : Superlinear L)
    {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    BddBelow (Set.range (cost L g t x)) := by
  obtain ⟨B, hB⟩ := hL K
  refine ⟨g x - t * B, ?_⟩
  rintro _ ⟨q, rfl⟩
  simpa using cost_lower hg hB ht x q

/-- Any straight path is an admissible competitor. -/
theorem value_le_cost {L g : E → ℝ} (hL : Superlinear L)
    {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} (ht : 0 ≤ t) (x q : E) :
    value L g t x ≤ cost L g t x q :=
  csInf_le (bddBelow_cost hL hg ht x) ⟨q, rfl⟩

/-- Compact attainment for continuous superlinear costs and Lipschitz data.
The proof excludes all velocities outside one closed ball. -/
theorem exists_minimizer [ProperSpace E] {L g : E → ℝ} (hcont : Continuous L) (hL : Superlinear L)
    {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} (ht : 0 < t) (x : E) :
    ∃ q, value L g t x = cost L g t x q ∧ ∀ r, cost L g t x q ≤ cost L g t x r :=
  exists_minimizer_of_norm_lower_bound hcont hL hg.continuous (lipschitz_norm_lower_bound hg) ht x

/-- Spatial Lipschitz constants are preserved. This estimate needs neither
convexity nor compact attainment. -/
theorem lipschitzWith_value {L g : E → ℝ} (hL : Superlinear L)
    {K : NNReal} (hg : LipschitzWith K g) {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith K (value L g t) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq]
  exact abs_value_sub_le_of_translate_bound hL (lipschitz_norm_lower_bound hg) ht x y fun z ↦ by
    simpa only [dist_sub_right, Real.dist_eq] using hg.dist_le_mul (x - z) (y - z)

/-- A quantitative initial-trace estimate, uniform over space.
Any affine lower bound with coefficient `K` gives such a constant. -/
theorem abs_value_sub_data_le {L g : E → ℝ} {K : NNReal} (hg : LipschitzWith K g) {B C t : ℝ}
    (hB : ∀ q, (K : ℝ) * ‖q‖ - B ≤ L q) (hBC : B ≤ C) (hLC : L 0 ≤ C) (ht : 0 ≤ t) (x : E) :
    |value L g t x - g x| ≤ C * t := by
  have hmod : ∀ x y, |g x - g y| ≤ (0 : ℝ) + (K : ℝ) * dist x y := fun x y ↦ by
    simpa only [zero_add, Real.dist_eq] using hg.dist_le_mul x y
  simpa only [zero_add] using abs_value_sub_data_le_of_modulus le_rfl hmod
    (fun q ↦ (sub_le_sub_left hBC _).trans (hB q)) hLC ht x

section NormLowerBound

variable [ProperSpace E] {L g : E → ℝ}
    (hcont : Continuous L) (hL : Superlinear L)
    (hconv : ConvexOn ℝ Set.univ L) (hg : Continuous g)
    {K : NNReal} {A : ℝ} (hlower : ∀ y, -A - (K : ℝ) * ‖y‖ ≤ g y)

include hcont hL hconv hg hlower

/-- The cost of a path with two velocities bounds the one-step value. -/
theorem value_le_step_of_norm_lower_bound {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x q : E) :
    value L g (s + t) x ≤ value L g s (x - t • q) + t * L q := by
  obtain ⟨r, hr, _⟩ := exists_minimizer_of_norm_lower_bound hcont hL hg hlower hs (x - t • q)
  let v : E := (s / (s + t)) • r + (t / (s + t)) • q
  have hst : 0 < s + t := add_pos hs ht
  have hab : s / (s + t) + t / (s + t) = (1 : ℝ) := by
    rw [← add_div, div_self (ne_of_gt hst)]
  have hc := hconv.2 (Set.mem_univ r) (Set.mem_univ q)
    (div_nonneg hs.le hst.le) (div_nonneg ht.le hst.le) hab
  have hcmul := mul_le_mul_of_nonneg_left hc hst.le
  have ha : (s + t) * (s / (s + t)) = s := by cas using hst
  have hb : (s + t) * (t / (s + t)) = t := by cas using hst
  have hvel : (s + t) • v = t • q + s • r := by
    simp only [v, smul_add, smul_smul, ha, hb, add_comm]
  have hcost : (s + t) * L v ≤ s * L r + t * L q := by
    simpa only [smul_eq_mul, mul_add, ← mul_assoc, ha, hb] using hcmul
  have hv : value L g (s + t) x ≤ cost L g (s + t) x v :=
    csInf_le (bddBelow_cost_of_norm_lower_bound hL hlower hst.le x) ⟨v, rfl⟩
  have hx : x - (s + t) • v = (x - t • q) - s • r := by
    rw [hvel]
    abel
  rw [hr]
  dsimp only [cost] at hv ⊢
  rw [hx] at hv
  linarith

/-- The Hopf–Lax operators form a semigroup at positive times.
Both sides have bounded cost infima; the earlier datum retains its norm lower bound. -/
theorem dynamic_programming_of_norm_lower_bound {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : E) :
    value L g (s + t) x = value L (value L g s) t x := by
  apply le_antisymm
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨q, rfl⟩
    exact value_le_step_of_norm_lower_bound hcont hL hconv hg hlower hs ht x q
  · obtain ⟨q, hq, _⟩ := exists_minimizer_of_norm_lower_bound hcont hL hg hlower (add_pos hs ht) x
    obtain ⟨B, hB⟩ := hL K
    have hgs : ∀ y, -(A + s * B) - (K : ℝ) * ‖y‖ ≤ value L g s y :=
      norm_lower_bound_value hlower hB hs.le
    have h₁ : value L (value L g s) t x ≤ cost L (value L g s) t x q :=
      csInf_le (bddBelow_cost_of_norm_lower_bound hL hgs ht.le x) ⟨q, rfl⟩
    have h₂ : value L g s (x - t • q) ≤ cost L g s (x - t • q) q :=
      csInf_le (bddBelow_cost_of_norm_lower_bound hL hlower hs.le (x - t • q)) ⟨q, rfl⟩
    have hx : (x - t • q) - s • q = x - (s + t) • q := by module
    rw [hq]
    dsimp only [cost] at h₁ h₂ ⊢
    rw [hx] at h₂
    linarith

end NormLowerBound

end HamiltonJacobi.HopfLax

end
