/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Derivative.Source

/-!
# Sources of the higher derivative equations

Write `B (A, Q) = A H Q` for the bounded bilinear map `firstDerivativeSourceH2CLM` on H². For
`k ≥ 1` the `k`-th spatial derivative `ω_k` of a De Gregorio solution satisfies, along every
characteristic `X`,

  `ω_k (X a t) t = ω_k a 0 + ∫₀ᵗ (ω H ω_k + (1 - k) (H ω) ω_k + F_k) (X a s) s ds`,

where the forcing `F_k` is a finite linear combination of products `B (ω_a, ω_b)` with `a, b ≥ 1`
and `a + b = k`. Differentiating the identity for `ω_k` gives the one for `ω_{k+1}`, with
`F_{k+1} = B (ω_1, ω_k) + (1 - k) B (ω_k, ω_1) + ∂ F_k`. We record such combinations as lists of
triples `(a, b, λ)`, standing for `λ B (ω_a, ω_b)`, so that `∂ F_k` is again a list and no
binomial coefficients appear.

## Main results

* `hasDerivAt_firstDerivativeSource`: the product rule for the representatives of `B`.
* `sourceSum`, `sourceDeriv`, `forcingList`: the forcing lists and their evaluation.
* `hasDerivAt_sourceSum`: the representative of `sourceSum q l` has derivative given by
  `sourceDeriv l` when each `q j` is differentiated into `q (j + 1)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The product rule for the source `B (A, Q) = A H Q`. -/
theorem hasDerivAt_firstDerivativeSource (A Q : W^{2,2}(ℝ^1)) (x : ℝ) :
    HasDerivAt
      (realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (firstDerivativeSourceH2CLM A Q)))
      (realLineRepresentative (∂[0] A) x *
          realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) Q)) x +
        realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) A) x *
          realLineRepresentative (realHilbertH1 (∂[0] Q)) x) x := by
  rw [realLineRepresentative_firstDerivativeSourceH2CLM]
  exact (hasDerivAt_realLineRepresentative_lowerOrder A x).mul
    (hasDerivAt_realHilbertH1_lowerOrder Q x)

/-- The combination `∑ λ B (q a, q b)` over the triples `(a, b, λ)` of a list. -/
def sourceSum (q : ℕ → W^{2,2}(ℝ^1)) (l : List (ℕ × ℕ × ℝ)) : W^{2,2}(ℝ^1) :=
  (l.map fun e ↦ e.2.2 • firstDerivativeSourceH2CLM (q e.1) (q e.2.1)).sum

/-- Differentiating `λ B (q a, q b)` gives `λ B (q (a + 1), q b) + λ B (q a, q (b + 1))`. -/
def sourceDeriv (l : List (ℕ × ℕ × ℝ)) : List (ℕ × ℕ × ℝ) :=
  l.flatMap fun e ↦ [(e.1 + 1, e.2.1, e.2.2), (e.1, e.2.1 + 1, e.2.2)]

/-- The forcing list of the `k`-th derivative equation: empty for `k ≤ 1`, and for `k ≥ 1`
`(1, k, 1) :: (k, 1, 1 - k) :: sourceDeriv (forcingList k)` at `k + 1`. -/
def forcingList : ℕ → List (ℕ × ℕ × ℝ)
  | 0 => []
  | 1 => []
  | m + 2 => (1, m + 1, 1) :: (m + 1, 1, -(m : ℝ)) :: sourceDeriv (forcingList (m + 1))

/-- The empty combination is zero. -/
@[simp] theorem sourceSum_nil (q : ℕ → W^{2,2}(ℝ^1)) : sourceSum q [] = 0 := by
  simp [sourceSum]

/-- A combination with one more term. -/
@[simp] theorem sourceSum_cons (q : ℕ → W^{2,2}(ℝ^1)) (e : ℕ × ℕ × ℝ)
    (l : List (ℕ × ℕ × ℝ)) :
    sourceSum q (e :: l) = e.2.2 • firstDerivativeSourceH2CLM (q e.1) (q e.2.1) +
      sourceSum q l := by
  simp [sourceSum]

/-- The derivative list of a cons. -/
@[simp] theorem sourceDeriv_cons (e : ℕ × ℕ × ℝ) (l : List (ℕ × ℕ × ℝ)) :
    sourceDeriv (e :: l) = (e.1 + 1, e.2.1, e.2.2) :: (e.1, e.2.1 + 1, e.2.2) ::
      sourceDeriv l := by
  simp [sourceDeriv]

/-- The derivative list of the empty list is empty. -/
@[simp] theorem sourceDeriv_nil : sourceDeriv [] = [] := rfl

/-- `sourceSum` depends only on the entries of `q` named in the list. -/
theorem sourceSum_congr {q q' : ℕ → W^{2,2}(ℝ^1)} {l : List (ℕ × ℕ × ℝ)}
    (h : ∀ e ∈ l, q e.1 = q' e.1 ∧ q e.2.1 = q' e.2.1) : sourceSum q l = sourceSum q' l := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [sourceSum_cons]
    rw [(h e (by simp)).1, (h e (by simp)).2, ih fun e' he' ↦ h e' (by simp [he'])]

/-- The entries of `forcingList k` are triples `(a, b, λ)` with `1 ≤ a`, `1 ≤ b` and
`a + b = k`. -/
theorem mem_forcingList {k : ℕ} {e : ℕ × ℕ × ℝ} (he : e ∈ forcingList k) :
    1 ≤ e.1 ∧ 1 ≤ e.2.1 ∧ e.1 + e.2.1 = k := by
  induction k using Nat.strong_induction_on generalizing e with
  | _ k ih =>
    match k, he with
    | 0, he => simp [forcingList] at he
    | 1, he => simp [forcingList] at he
    | m + 2, he =>
      simp only [forcingList, List.mem_cons] at he
      rcases he with rfl | rfl | he
      · dsimp only
        omega
      · dsimp only
        omega
      · simp only [sourceDeriv, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
          or_false] at he
        obtain ⟨e', he', hcase⟩ := he
        have := ih (m + 1) (by omega) he'
        rcases hcase with rfl | rfl
        · dsimp only
          omega
        · dsimp only
          omega

/-- If each `q j` occurring in the list differentiates into `q (j + 1)`, the representative of
`sourceSum q l` has the representative of `sourceSum q (sourceDeriv l)` as derivative. -/
theorem hasDerivAt_sourceSum {q : ℕ → W^{2,2}(ℝ^1)} {l : List (ℕ × ℕ × ℝ)}
    (h : ∀ e ∈ l, ∂[0] (q e.1) = lowerOrderCLM (by decide : 1 ≤ 2) (q (e.1 + 1)) ∧
      ∂[0] (q e.2.1) = lowerOrderCLM (by decide : 1 ≤ 2) (q (e.2.1 + 1))) (x : ℝ) :
    HasDerivAt (realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (sourceSum q l)))
      (realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2)
        (sourceSum q (sourceDeriv l))) x) x := by
  induction l with
  | nil =>
    simp only [sourceSum_nil, sourceDeriv_nil, map_zero]
    rw [realLineRepresentative_zero]
    exact hasDerivAt_const x 0
  | cons e l ih =>
    have he := h e (by simp)
    have ih' := ih fun e' he' ↦ h e' (by simp [he'])
    simp only [sourceSum_cons, sourceDeriv_cons, map_add, map_smul, realLineRepresentative_add,
      realLineRepresentative_smul]
    have hterm := (hasDerivAt_firstDerivativeSource (q e.1) (q e.2.1) x).const_smul e.2.2
    rw [he.1, he.2] at hterm
    convert hterm.add ih' using 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      realLineRepresentative_firstDerivativeSourceH2CLM]
    ring

end DeGregorio.Iteration
