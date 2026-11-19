/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import PDE.Analysis.Stability.ModulatedNonlinear

/-!
# Validated finite-mode coercivity and analytic tail closure

A computer-assisted stability proof can split the linearized operator into a finite-dimensional
head checked by computer and an infinite-dimensional tail controlled analytically. We prove two
estimates for this split:

* a dissipativity estimate for a target operator from an exactly controlled reference operator
  and a certified operator-norm error;
* a head-tail closure theorem with a tunable Young parameter and an explicit coupling loss.

Concretely, if `⟪L_h h, h⟫ ≤ -a ‖h‖²` on the head, `⟪L_t t, t⟫ ≤ -b ‖t‖²` on the tail, and the
two off-diagonal pairings together are bounded by `c ‖h‖ ‖t‖`, then Young's inequality
`2 ‖h‖ ‖t‖ ≤ ε ‖h‖² + ε⁻¹ ‖t‖²` gives, on the Hilbert direct sum `Head ×₂ Tail`,

  `⟪L s, s⟫ ≤ -min (a - cε/2) (b - c/(2ε)) · ‖s‖²`.

The parameter `ε` is left free so that a strong tail rate `b` can pay for a weak head rate `a`,
or the other way round. All statements are exact real inequalities in abstract inner product
spaces; the numerical inputs (a rational factorisation of the head matrix, an interval
enclosure of an operator norm, a spectral bound for the tail) enter only through the
hypotheses of the structures.

Chen and Hou, Part I, Section 1.1, write the linearized operator as `L₀ + K` with `K` of finite
rank, estimate `L₀` analytically, and estimate the contribution of `K` through approximate
space-time solutions constructed numerically with rigorous error control. The split here is
instead of the state space, into a finite-dimensional head and a tail.

## Main results

* `ValidatedDissipativityEstimate`: a target operator, an exactly controlled reference, its
  rate, and a certified operator-norm error; `target_pairing_le` shows the target is
  dissipative with rate `effectiveRate = referenceRate - errorBound`.
* `HeadTailDissipativityEstimate`: block data for an operator on `SplitState Head Tail`;
  `coupling_pairing_le_young`, `coordinatePairing_le_combined` and `linear_pairing_le` carry
  out the Young split and give the global rate `combinedRate ε`.
* `ofValidatedHead`: assemble a head-tail estimate whose head block is a validated comparison.
* `toModulatedEnergyEstimate`: feed the closed linear estimate into the modulated energy
  framework of `PDE.Analysis.Stability.ModulatedNonlinear`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 1.1.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Stability

open scoped RealInnerProductSpace

variable {H Head Tail : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Head] [InnerProductSpace ℝ Head]
  [NormedAddCommGroup Tail] [InnerProductSpace ℝ Tail]

/-!
## Validated perturbation of a coercive reference operator
-/

/-- Data proving dissipativity of a target operator by comparison with a reference operator.

The reference estimate may come from an exact rational matrix factorization.  The difference
bound may come from interval arithmetic. -/
structure ValidatedDissipativityEstimate (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Operator whose dissipativity is required. -/
  target : H →L[ℝ] H
  /-- Exactly controlled reference operator. -/
  reference : H →L[ℝ] H
  /-- Decay rate of the reference operator. -/
  referenceRate : ℝ
  /-- Certified operator-norm error between target and reference. -/
  errorBound : NNReal
  /-- Exact dissipativity estimate for the reference operator. -/
  reference_pairing_le :
    ∀ state,
      ⟪reference state, state⟫ ≤
        -referenceRate * ‖state‖ * ‖state‖
  /-- Validated operator-norm enclosure. -/
  difference_norm_le : ‖target - reference‖ ≤ errorBound

namespace ValidatedDissipativityEstimate

variable (estimate : ValidatedDissipativityEstimate H)

/-- Decay rate remaining after paying the validated operator error. -/
def effectiveRate : ℝ :=
  estimate.referenceRate - estimate.errorBound

/-- Pointwise form of the certified operator-norm error. -/
theorem difference_apply_norm_le (state : H) :
    ‖(estimate.target - estimate.reference) state‖ ≤
      estimate.errorBound * ‖state‖ := by
  calc
    ‖(estimate.target - estimate.reference) state‖ ≤
        ‖estimate.target - estimate.reference‖ * ‖state‖ :=
      (estimate.target - estimate.reference).le_opNorm state
    _ ≤ estimate.errorBound * ‖state‖ :=
      mul_le_mul_of_nonneg_right estimate.difference_norm_le
        (norm_nonneg state)

/-- A validated operator perturbation loses at most its operator-norm error from the reference
decay rate. -/
theorem target_pairing_le (state : H) :
    ⟪estimate.target state, state⟫ ≤
      -estimate.effectiveRate * ‖state‖ * ‖state‖ := by
  have hdecomposition :
      estimate.target state =
        estimate.reference state +
          (estimate.target - estimate.reference) state := by
    simp
  have herror :
      ⟪(estimate.target - estimate.reference) state, state⟫ ≤
        estimate.errorBound * ‖state‖ * ‖state‖ := by
    calc
      ⟪(estimate.target - estimate.reference) state, state⟫ ≤
          ‖(estimate.target - estimate.reference) state‖ * ‖state‖ :=
        real_inner_le_norm _ _
      _ ≤ (estimate.errorBound * ‖state‖) * ‖state‖ :=
        mul_le_mul_of_nonneg_right
          (estimate.difference_apply_norm_le state)
          (norm_nonneg state)
  rw [hdecomposition, inner_add_left]
  calc
    ⟪estimate.reference state, state⟫ +
        ⟪(estimate.target - estimate.reference) state, state⟫ ≤
        (-estimate.referenceRate * ‖state‖ * ‖state‖) +
          estimate.errorBound * ‖state‖ * ‖state‖ :=
      add_le_add (estimate.reference_pairing_le state) herror
    _ = -estimate.effectiveRate * ‖state‖ * ‖state‖ := by
      simp only [effectiveRate]
      ring

/-- Strict positivity of the effective rate follows from a strict error margin. -/
theorem effectiveRate_pos
    (hmargin : estimate.errorBound < estimate.referenceRate) :
    0 < estimate.effectiveRate := by
  simpa only [effectiveRate, sub_pos] using hmargin

end ValidatedDissipativityEstimate

/-!
## Head-tail closure
-/

/-- The Hilbert direct sum used for a finite head and an analytic tail. -/
abbrev SplitState (Head Tail : Type*) : Type _ :=
  WithLp 2 (Head × Tail)

/-- Block decomposition of a linearized operator with explicit head, tail, and coupling bounds. -/
structure HeadTailDissipativityEstimate (Head Tail : Type*)
    [NormedAddCommGroup Head] [InnerProductSpace ℝ Head]
    [NormedAddCommGroup Tail] [InnerProductSpace ℝ Tail] where
  /-- Full operator on the Hilbert direct sum. -/
  linear : SplitState Head Tail →L[ℝ] SplitState Head Tail
  /-- Finite-dimensional head block. -/
  headOperator : Head →L[ℝ] Head
  /-- Infinite-dimensional tail block. -/
  tailOperator : Tail →L[ℝ] Tail
  /-- Coupling from tail into head. -/
  tailToHead : Tail →L[ℝ] Head
  /-- Coupling from head into tail. -/
  headToTail : Head →L[ℝ] Tail
  /-- Exact block action of the full operator. -/
  linear_apply :
    ∀ head tail,
      linear (WithLp.toLp 2 (head, tail)) =
        WithLp.toLp 2
          (headOperator head + tailToHead tail,
            headToTail head + tailOperator tail)
  /-- Checked finite-head decay rate. -/
  headRate : ℝ
  /-- Analytic tail decay rate. -/
  tailRate : ℝ
  /-- Bound for the sum of both off-diagonal energy pairings. -/
  couplingBound : NNReal
  /-- Dissipativity of the finite head block. -/
  head_pairing_le :
    ∀ head,
      ⟪headOperator head, head⟫ ≤
        -headRate * ‖head‖ * ‖head‖
  /-- Dissipativity of the analytic tail block. -/
  tail_pairing_le :
    ∀ tail,
      ⟪tailOperator tail, tail⟫ ≤
        -tailRate * ‖tail‖ * ‖tail‖
  /-- Explicit head-tail coupling estimate. -/
  coupling_pairing_le :
    ∀ head tail,
      ⟪tailToHead tail, head⟫ +
          ⟪headToTail head, tail⟫ ≤
        couplingBound * ‖head‖ * ‖tail‖

namespace HeadTailDissipativityEstimate

variable (estimate : HeadTailDissipativityEstimate Head Tail)

/-- Head decay remaining after a Young split with parameter `epsilon`. -/
def adjustedHeadRate (epsilon : ℝ) : ℝ :=
  estimate.headRate - estimate.couplingBound * epsilon / 2

/-- Tail decay remaining after a Young split with parameter `epsilon`. -/
def adjustedTailRate (epsilon : ℝ) : ℝ :=
  estimate.tailRate - estimate.couplingBound * epsilon⁻¹ / 2

/-- Global decay rate furnished by the weaker adjusted block. -/
def combinedRate (epsilon : ℝ) : ℝ :=
  min (estimate.adjustedHeadRate epsilon)
    (estimate.adjustedTailRate epsilon)

/-- Energy pairing of the four block contributions in head-tail coordinates. -/
def coordinatePairing (head : Head) (tail : Tail) : ℝ :=
  ⟪estimate.headOperator head + estimate.tailToHead tail, head⟫ +
    ⟪estimate.headToTail head + estimate.tailOperator tail, tail⟫

/-- Tunable Young estimate for the head-tail coupling term. -/
theorem coupling_pairing_le_young
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (head : Head) (tail : Tail) :
    ⟪estimate.tailToHead tail, head⟫ +
          ⟪estimate.headToTail head, tail⟫ ≤
      estimate.couplingBound * epsilon / 2 * ‖head‖ ^ 2 +
        estimate.couplingBound * epsilon⁻¹ / 2 * ‖tail‖ ^ 2 := by
  have hyoung :
      2 * ‖head‖ * ‖tail‖ ≤
        epsilon * ‖head‖ ^ 2 + epsilon⁻¹ * ‖tail‖ ^ 2 :=
    two_mul_le_add_mul_sq hepsilon
  have hscaled :=
    mul_le_mul_of_nonneg_left hyoung
      (div_nonneg estimate.couplingBound.property (by norm_num : (0 : ℝ) ≤ 2))
  calc
    ⟪estimate.tailToHead tail, head⟫ +
          ⟪estimate.headToTail head, tail⟫ ≤
        estimate.couplingBound * ‖head‖ * ‖tail‖ :=
      estimate.coupling_pairing_le head tail
    _ = (estimate.couplingBound / 2) *
        (2 * ‖head‖ * ‖tail‖) := by ring
    _ ≤ (estimate.couplingBound / 2) *
        (epsilon * ‖head‖ ^ 2 +
          epsilon⁻¹ * ‖tail‖ ^ 2) :=
      hscaled
    _ = estimate.couplingBound * epsilon / 2 * ‖head‖ ^ 2 +
        estimate.couplingBound * epsilon⁻¹ / 2 * ‖tail‖ ^ 2 := by
      ring

/-- Separate adjusted decay estimates for the head and tail energies. -/
theorem coordinatePairing_le_adjusted
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (head : Head) (tail : Tail) :
    estimate.coordinatePairing head tail ≤
      -estimate.adjustedHeadRate epsilon * ‖head‖ ^ 2 -
        estimate.adjustedTailRate epsilon * ‖tail‖ ^ 2 := by
  have hhead := estimate.head_pairing_le head
  have htail := estimate.tail_pairing_le tail
  have hcoupling :=
    estimate.coupling_pairing_le_young hepsilon head tail
  simp only [coordinatePairing, inner_add_left]
  simp only [adjustedHeadRate, adjustedTailRate]
  nlinarith

/-- The smaller adjusted block rate controls the sum of the head and tail energies. -/
theorem coordinatePairing_le_combined
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (head : Head) (tail : Tail) :
    estimate.coordinatePairing head tail ≤
      -estimate.combinedRate epsilon *
        (‖head‖ ^ 2 + ‖tail‖ ^ 2) := by
  have hadjusted :=
    estimate.coordinatePairing_le_adjusted hepsilon head tail
  have hhead :
      -estimate.adjustedHeadRate epsilon * ‖head‖ ^ 2 ≤
        -estimate.combinedRate epsilon * ‖head‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      (neg_le_neg (min_le_left
        (estimate.adjustedHeadRate epsilon)
        (estimate.adjustedTailRate epsilon)))
      (sq_nonneg ‖head‖)
  have htail :
      -estimate.adjustedTailRate epsilon * ‖tail‖ ^ 2 ≤
        -estimate.combinedRate epsilon * ‖tail‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      (neg_le_neg (min_le_right
        (estimate.adjustedHeadRate epsilon)
        (estimate.adjustedTailRate epsilon)))
      (sq_nonneg ‖tail‖)
  calc
    estimate.coordinatePairing head tail ≤
        -estimate.adjustedHeadRate epsilon * ‖head‖ ^ 2 -
          estimate.adjustedTailRate epsilon * ‖tail‖ ^ 2 :=
      hadjusted
    _ ≤ -estimate.combinedRate epsilon * ‖head‖ ^ 2 +
        -estimate.combinedRate epsilon * ‖tail‖ ^ 2 := by
      linarith
    _ = -estimate.combinedRate epsilon *
        (‖head‖ ^ 2 + ‖tail‖ ^ 2) := by ring

/-- Global dissipativity of the full block operator on the Hilbert direct sum. -/
theorem linear_pairing_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (state : SplitState Head Tail) :
    ⟪estimate.linear state, state⟫ ≤
      -estimate.combinedRate epsilon * ‖state‖ * ‖state‖ := by
  let head : Head := state.fst
  let tail : Tail := state.snd
  have hstate : state = WithLp.toLp 2 (head, tail) := by
    rfl
  rw [hstate, estimate.linear_apply]
  rw [WithLp.prod_inner_apply]
  change estimate.coordinatePairing head tail ≤
    -estimate.combinedRate epsilon *
      ‖WithLp.toLp 2 (head, tail)‖ *
        ‖WithLp.toLp 2 (head, tail)‖
  calc
    estimate.coordinatePairing head tail ≤
        -estimate.combinedRate epsilon *
          (‖head‖ ^ 2 + ‖tail‖ ^ 2) :=
      estimate.coordinatePairing_le_combined hepsilon head tail
    _ = -estimate.combinedRate epsilon *
        ‖WithLp.toLp 2 (head, tail)‖ *
          ‖WithLp.toLp 2 (head, tail)‖ := by
      have hnorm :
          ‖WithLp.toLp 2 (head, tail)‖ ^ 2 =
            ‖head‖ ^ 2 + ‖tail‖ ^ 2 := by
        simpa using
          (WithLp.prod_norm_sq_eq_of_L2
            (WithLp.toLp 2 (head, tail)))
      rw [← hnorm]
      ring

/-- Build a head-tail estimate whose finite block comes from a validated operator comparison. -/
def ofValidatedHead
    (headEstimate : ValidatedDissipativityEstimate Head)
    (linear : SplitState Head Tail →L[ℝ] SplitState Head Tail)
    (tailOperator : Tail →L[ℝ] Tail)
    (tailToHead : Tail →L[ℝ] Head)
    (headToTail : Head →L[ℝ] Tail)
    (linear_apply :
      ∀ head tail,
        linear (WithLp.toLp 2 (head, tail)) =
          WithLp.toLp 2
            (headEstimate.target head + tailToHead tail,
              headToTail head + tailOperator tail))
    (tailRate : ℝ)
    (couplingBound : NNReal)
    (tail_pairing_le :
      ∀ tail,
        ⟪tailOperator tail, tail⟫ ≤
          -tailRate * ‖tail‖ * ‖tail‖)
    (coupling_pairing_le :
      ∀ head tail,
        ⟪tailToHead tail, head⟫ +
            ⟪headToTail head, tail⟫ ≤
          couplingBound * ‖head‖ * ‖tail‖) :
    HeadTailDissipativityEstimate Head Tail where
  linear := linear
  headOperator := headEstimate.target
  tailOperator := tailOperator
  tailToHead := tailToHead
  headToTail := headToTail
  linear_apply := linear_apply
  headRate := headEstimate.effectiveRate
  tailRate := tailRate
  couplingBound := couplingBound
  head_pairing_le := headEstimate.target_pairing_le
  tail_pairing_le := tail_pairing_le
  coupling_pairing_le := coupling_pairing_le

/-- Add nonlinear, modulation, and residual estimates after closing the linear head-tail bound. -/
def toModulatedEnergyEstimate
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdecay : 0 < estimate.combinedRate epsilon)
    (nonlinear modulation : SplitState Head Tail → SplitState Head Tail)
    (residual : SplitState Head Tail)
    (nonlinearConstant modulationConstant residualBound : NNReal)
    (nonlinear_norm_le :
      ∀ perturbation,
        ‖nonlinear perturbation‖ ≤
          nonlinearConstant * ‖perturbation‖ * ‖perturbation‖)
    (modulation_norm_le :
      ∀ perturbation,
        ‖modulation perturbation‖ ≤
          modulationConstant * ‖perturbation‖)
    (residual_norm_le : ‖residual‖ ≤ residualBound) :
    ModulatedEnergyEstimate (SplitState Head Tail) where
  linear := estimate.linear
  nonlinear := nonlinear
  modulation := modulation
  residual := residual
  decayRate := ⟨estimate.combinedRate epsilon, hdecay⟩
  nonlinearConstant := nonlinearConstant
  modulationConstant := modulationConstant
  residualBound := residualBound
  linear_pairing_le := estimate.linear_pairing_le hepsilon
  nonlinear_norm_le := nonlinear_norm_le
  modulation_norm_le := modulation_norm_le
  residual_norm_le := residual_norm_le

end HeadTailDissipativityEstimate

end PDE.Analysis.Stability
