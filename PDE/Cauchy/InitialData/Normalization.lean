/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet.Operations
public import PDE.Cauchy.Equation.Basic

/-!
# Shifting Cauchy data and normalizing the principal coefficient

Subtracting an analytic data extension translates every lower jet in the
coefficient arguments. The full contribution of its highest derivatives is
subtracted from the forcing. Division by the nonzero pure-time principal
coefficient then gives the normalized scalar equation. Evans makes the same two moves in
§4.6.3(a): he subtracts analytic functions to make the Cauchy data zero, and he uses
`a_(0,...,0,k) ≠ 0` to solve the equation for the pure normal derivative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3(a).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Analysis.MultiIndex

namespace PDE.Cauchy.Quasilinear.Analytic

variable {d k : ℕ}

local notation "J" => (Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ))
local notation "T" => {α : Sym (Fin (d + 1)) k // α ≠ Sym.replicate k 0}
local notation "A" => J ⊕ Fin (d + 1)

/-- Translate all lower jet variables by the jet of the data extension `G`,
keeping all position coordinates. -/
def shiftedArguments (k : ℕ) (G : ℝ^(d + 1) → ℝ)
    (z : ((Σ j : Fin k, Sym (Fin (d + 1)) (j : ℕ)) ⊕ Fin (d + 1)) → ℝ) :
    ℝ^(d + 1) × (∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ) :=
  let x : ℝ^(d + 1) := WithLp.toLp 2 (fun i ↦ z (.inr i))
  (x, fun j α ↦ coordinateDeriv α G x + z (.inl ⟨j, α⟩))

/-- At the zero unknown jet, the translated arguments are the data jet at the origin. -/
theorem shiftedArguments_zero (G : ℝ^(d + 1) → ℝ) :
    shiftedArguments k G 0 = (0, coordinateJetLT k G 0) := by
  simp only [shiftedArguments, Pi.zero_apply, add_zero]
  rfl

/-- Translation by an analytic data extension is analytic in position and jet. -/
theorem analyticAt_shiftedArguments {G : ℝ^(d + 1) → ℝ} (hG : AnalyticAt ℝ G 0) :
    AnalyticAt ℝ (shiftedArguments k G) 0 := by
  let p (z : A → ℝ) : ℝ^(d + 1) := WithLp.toLp 2 (fun i ↦ z (.inr i))
  have hp : AnalyticAt ℝ p 0 :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) ↦ ℝ)).symm.analyticAt _).comp
      (AnalyticAt.pi fun i ↦
        (ContinuousLinearMap.proj (Sum.inr i) : (A → ℝ) →L[ℝ] ℝ).analyticAt 0)
  have hp0 : p 0 = 0 := WithLp.toLp_zero 2
  exact hp.prod (AnalyticAt.pi fun (j : Fin k) ↦
    AnalyticAt.pi fun (α : Sym (Fin (d + 1)) (j : ℕ)) ↦
    ((analyticAt_coordinateDeriv hG α).comp_of_eq hp hp0).add
      ((ContinuousLinearMap.proj (Sum.inl (⟨j, α⟩ : J)) :
        (A → ℝ) →L[ℝ] ℝ).analyticAt 0))

/-- Substituting the lower jet of `w` into the translated arguments gives the
lower jet of `G + w`. -/
theorem shiftedArguments_arguments {G w : ℝ^(d + 1) → ℝ} {x : ℝ^(d + 1)}
    (hG : AnalyticAt ℝ G x) (hw : AnalyticAt ℝ w x) :
    shiftedArguments k G (arguments k w x) = (x, coordinateJetLT k (G + w) x) := by
  apply Prod.ext
  · exact WithLp.toLp_ofLp 2 x
  · funext j α
    change coordinateDeriv α G (WithLp.toLp 2 (fun i ↦ x i)) +
      coordinateDeriv α w x = coordinateDeriv α (G + w) x
    rw [show WithLp.toLp 2 (fun i ↦ x i) = x from WithLp.toLp_ofLp 2 x]
    exact (coordinateDeriv_add α hG.contDiffAt hw.contDiffAt).symm

/-- Coefficients of the non-pure highest derivatives after shifting the data
and solving for the highest pure time derivative. -/
def normalizedCoefficients
    (a : Sym (Fin (d + 1)) k →
      ℝ^(d + 1) × (∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (G : ℝ^(d + 1) → ℝ)
    (α : T) (z : A → ℝ) : ℝ :=
  -a α.1 (shiftedArguments k G z) /
    a (Sym.replicate k 0) (shiftedArguments k G z)

/-- The normalized forcing includes all highest derivatives of the data extension. -/
def normalizedForcing
    (a : Sym (Fin (d + 1)) k →
      ℝ^(d + 1) × (∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (b : ℝ^(d + 1) × (∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (G : ℝ^(d + 1) → ℝ) (z : A → ℝ) : ℝ :=
  (b (shiftedArguments k G z) -
      ∑ α, a α (shiftedArguments k G z) *
        coordinateDeriv α G (shiftedArguments k G z).1) /
    a (Sym.replicate k 0) (shiftedArguments k G z)

/-- Noncharacteristic analytic coefficients remain analytic after the data shift
and division by the pure-time principal coefficient. -/
theorem analyticAt_normalizedCoefficients
    {a : Sym (Fin (d + 1)) k →
      ℝ^(d + 1) × (∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ}
    {G : ℝ^(d + 1) → ℝ}
    (ha : ∀ α, AnalyticAt ℝ (a α) (0, coordinateJetLT k G 0))
    (hG : AnalyticAt ℝ G 0)
    (hprincipal : a (Sym.replicate k 0) (0, coordinateJetLT k G 0) ≠ 0)
    (α : T) :
    AnalyticAt ℝ (normalizedCoefficients a G α) 0 := by
  have harg := analyticAt_shiftedArguments (k := k) hG
  have hc (β : Sym (Fin (d + 1)) k) :
      AnalyticAt ℝ (fun z ↦ a β (shiftedArguments k G z)) 0 :=
    (ha β).comp_of_eq harg (shiftedArguments_zero G)
  exact (hc α.1).neg.div (hc _) (by rwa [shiftedArguments_zero])

/-- The translated forcing is analytic under the same local noncharacteristic
hypothesis as the normalized coefficients. -/
theorem analyticAt_normalizedForcing
    {a : Sym (Fin (d + 1)) k →
      ℝ^(d + 1) × (∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ}
    {b : ℝ^(d + 1) × (∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ}
    {G : ℝ^(d + 1) → ℝ}
    (ha : ∀ α, AnalyticAt ℝ (a α) (0, coordinateJetLT k G 0))
    (hb : AnalyticAt ℝ b (0, coordinateJetLT k G 0))
    (hG : AnalyticAt ℝ G 0)
    (hprincipal : a (Sym.replicate k 0) (0, coordinateJetLT k G 0) ≠ 0) :
    AnalyticAt ℝ (normalizedForcing a b G) 0 := by
  have harg := analyticAt_shiftedArguments (k := k) hG
  have hc (β : Sym (Fin (d + 1)) k) :
      AnalyticAt ℝ (fun z ↦ a β (shiftedArguments k G z)) 0 :=
    (ha β).comp_of_eq harg (shiftedArguments_zero G)
  have hp : AnalyticAt ℝ (fun z ↦ (shiftedArguments k G z).1) 0 :=
    analyticAt_fst.comp harg
  have hp0 : (shiftedArguments k G 0).1 = 0 :=
    congrArg Prod.fst (shiftedArguments_zero G)
  exact ((hb.comp_of_eq harg (shiftedArguments_zero G)).sub
    (Finset.univ.analyticAt_fun_sum fun α _ ↦
      (hc α).mul ((analyticAt_coordinateDeriv hG α).comp_of_eq hp hp0))).div
        (hc _) (by rwa [shiftedArguments_zero])

private theorem sum_mul_add_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι) (a D E : ι → ℝ) (b : ℝ) (hp : a p ≠ 0) :
    (∑ α, a α * (E α + D α)) = b ↔
      D p = (∑ α : {α // α ≠ p}, -a α.1 / a p * D α.1) +
        (b - ∑ α, a α * E α) / a p := by
  have hsplit : (∑ α, a α * D α) =
      a p * D p + ∑ α : {α // α ≠ p}, a α.1 * D α.1 := by
    rw [Fintype.sum_eq_add_sum_compl p]
    congr 1
    exact Finset.sum_subtype _ (by simp) _
  have hrhs : (∑ α : {α // α ≠ p}, -a α.1 / a p * D α.1) +
        (b - ∑ α, a α * E α) / a p =
      (b - (∑ α, a α * E α) - ∑ α : {α // α ≠ p}, a α.1 * D α.1) / a p := by
    simp only [div_mul_eq_mul_div, neg_mul, ← Finset.sum_div, Finset.sum_neg_distrib]
    ring
  rw [hrhs, eq_div_iff hp]
  simp only [mul_add, Finset.sum_add_distrib, hsplit]
  constructor <;> intro h <;> nlinarith

/-- At points where the principal coefficient is nonzero, the normalized
equation for the correction is equivalent to the original equation for the sum. -/
theorem equation_add_iff
    (a : Sym (Fin (d + 1)) k →
      ℝ^(d + 1) × (∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    (b : ℝ^(d + 1) × (∀ j : Fin k, Sym (Fin (d + 1)) (j : ℕ) → ℝ) → ℝ)
    {G w : ℝ^(d + 1) → ℝ} {x : ℝ^(d + 1)}
    (hG : AnalyticAt ℝ G x) (hw : AnalyticAt ℝ w x)
    (hprincipal : a (Sym.replicate k 0) (x, coordinateJetLT k (G + w) x) ≠ 0) :
    (∑ α, a α (x, coordinateJetLT k (G + w) x) * coordinateDeriv α (G + w) x) =
        b (x, coordinateJetLT k (G + w) x) ↔
      coordinateDeriv (Sym.replicate k 0) w x =
        rightHandSide (normalizedCoefficients a G) (normalizedForcing a b G) w x := by
  simp only [coordinateDeriv_add _ hG.contDiffAt hw.contDiffAt, rightHandSide,
    normalizedCoefficients, normalizedForcing, shiftedArguments_arguments hG hw]
  exact sum_mul_add_eq_iff _ _ _ _ _ hprincipal

end PDE.Cauchy.Quasilinear.Analytic
