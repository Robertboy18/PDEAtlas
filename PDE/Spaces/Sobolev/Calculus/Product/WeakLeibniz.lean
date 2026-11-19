/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.DerivativeSplits
public import PDE.Spaces.Sobolev.GraphSpace.Local.Definitions
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Higher-order weak Leibniz rule

The Leibniz formula for weak derivatives: if `ζ` is smooth with bounded derivatives on `Ω` and
`u ∈ W^{k,p}(Ω)`, then `ζu ∈ W^{k,p}(Ω)` and

`D^α(ζu) = Σ_{β ≤ α} (α choose β) D^β ζ D^{α-β} u`

for every `|α| ≤ k`. Evans (PDE, §5.2.3, Theorem 1(iv)) proves this for `ζ ∈ C_c^∞(U)` by
induction on `|α|`; we induct on derivative words in the same way, with
`weakLeibnizExpansion_step` as the inductive step. We prove the derivative identity
for an abstract family `D : List (Fin n) → ℝ^n → ℝ` of weak derivative representatives, indexed
by derivative words, that are in `L^p` and are linked by first weak derivatives (`D (i :: β)` is
`∂ᵢ` of `D β`), and then specialize to the spaces `WkpSpaceOn n k p Ω` and to the
local predicate `IsLocallyWkpOn`. The global results assume bounded multiplier derivatives.
For the local result, continuity bounds these derivatives on the compact closure of the
subdomain; the conclusion is the weak-derivative identity.

Derivative words are used instead of multi-indices. Since no quotient by permutations is taken,
the expansion `weakLeibnizExpansion` lists every ordered assignment of the letters of `α` to the
two factors, so the multinomial coefficients appear as repeated terms rather than as numerical
weights. The word passed to the expansion is `α.reverse` because the chain of first derivatives
is built by appending on the right.

## Main results

* `weakLeibnizExpansion`: the right-hand side of the Leibniz formula for a word `α`.
* `weakLeibnizExpansion_step`: one more weak derivative of the expansion for `α` is the
  expansion for `i :: α`.
* `hasWeakDerivativeOn_weakLeibniz`, `hasWeakDerivativeOn_weakLeibniz_order`: the Leibniz rule
  for all words, and for words of length at most `k` under hypotheses only through order `k`.
* `wkpWordRepresentative`: the derivative coordinates of a `WkpSpaceOn` element read off along
  words, with `wkpWordRepresentative_step` giving the linking first derivatives.
* `WkpSpaceOn.hasWeakDerivativeOn_mul_smooth`: the Leibniz rule for a `W^{k,p}(Ω)`
  element.
* `IsLocallyWkpOn.hasWeakDerivativeOn_mul_smooth`: the `W^{k,p}_loc` version,
  stated on relatively compact open subsets.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iv), (7), pp. 261-262, and step 3 of its
  proof, the induction on `|α|`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory ENNReal
open scoped Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- The derivative-word Leibniz expansion associated with a smooth multiplier
`ζ` and a family `D` of weak derivative representatives. -/
def weakLeibnizExpansion
    (ζ : ℝ^n → ℝ) (D : List (Fin n) → ℝ^n → ℝ)
    (α : List (Fin n)) : ℝ^n → ℝ := fun x ↦
  ((derivativeSplits α).map fun q ↦
    iteratedPartialDeriv (n := n) q.1 ζ x * D q.2 x).sum

/-- For the empty word the Leibniz expansion has the single term `ζ · D []`, the product
itself. -/
@[simp]
theorem weakLeibnizExpansion_nil
    (ζ : ℝ^n → ℝ) (D : List (Fin n) → ℝ^n → ℝ) :
    weakLeibnizExpansion ζ D [] = fun x ↦ ζ x * D [] x := by
  funext x
  simp [weakLeibnizExpansion, derivativeSplits, iteratedPartialDeriv]

private theorem hasWeakDerivativeOn_list_pair_sum
    (i : Fin n)
    (terms : List ((ℝ^n → ℝ) × (ℝ^n → ℝ)))
    (hweak : ∀ t ∈ terms,
      HasWeakDerivativeOn (n := n) Ω [i] t.1 t.2) :
    HasWeakDerivativeOn (n := n) Ω [i]
      (fun x ↦ (terms.map fun t ↦ t.1 x).sum)
      (fun x ↦ (terms.map fun t ↦ t.2 x).sum) := by
  induction terms with
  | nil =>
      simpa using hasWeakDerivativeOn_zero (n := n) (Ω := Ω) ([i] : List (Fin n))
  | cons t rest ih =>
      have hsum := hasWeakDerivativeOn_add (hweak t (by simp))
        (ih (fun s hs ↦ hweak s (by simp [hs])))
      convert hsum using 1 <;> funext x <;> rfl

/-- One differentiation of a Leibniz expansion produces the expansion with
the new coordinate prepended to the derivative word. -/
theorem weakLeibnizExpansion_step
    {k : ℕ}
    (ζ : ℝ^n → ℝ) (D : List (Fin n) → ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζBound : ∀ β, β.length ≤ k → MemLp
      (iteratedPartialDeriv (n := n) β ζ) (⊤ : ℝ≥0∞)
      (domainMeasure n Ω))
    (hDlp : ∀ β, β.length ≤ k → MemLp (D β) p (domainMeasure n Ω))
    (hDstep : ∀ β i, β.length < k →
      HasWeakDerivativeOn (n := n) Ω [i] (D β) (D (i :: β)))
    (α : List (Fin n)) (hα : α.length < k) (i : Fin n) :
    HasWeakDerivativeOn (n := n) Ω [i]
      (weakLeibnizExpansion ζ D α)
      (weakLeibnizExpansion ζ D (i :: α)) := by
  let S := derivativeSplits α
  let terms : List ((ℝ^n → ℝ) × (ℝ^n → ℝ)) := S.map fun q ↦
    ( (fun x ↦ iteratedPartialDeriv (n := n) q.1 ζ x * D q.2 x),
      (fun x ↦
        iteratedPartialDeriv (n := n) q.1 ζ x * D (i :: q.2) x +
          iteratedPartialDeriv (n := n) (i :: q.1) ζ x * D q.2 x) )
  have htermWeak : ∀ t ∈ terms,
      HasWeakDerivativeOn (n := n) Ω [i] t.1 t.2 := by
    intro t ht
    simp only [terms, List.mem_map] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    have hlen := derivativeSplits_length (by simpa [S] using hq)
    have hq1 : q.1.length ≤ k := by omega
    have hq1next : (i :: q.1).length ≤ k := by
      simp only [List.length_cons]
      omega
    have hq2 : q.2.length ≤ k := by omega
    have hq2next : (i :: q.2).length ≤ k := by
      simp only [List.length_cons]
      omega
    have hq2lt : q.2.length < k := by omega
    let ζq : ℝ^n → ℝ := iteratedPartialDeriv (n := n) q.1 ζ
    have hζq : ContDiff ℝ (⊤ : ℕ∞) ζq :=
      PDE.contDiff_top_iteratedPartialDeriv (n := n) hζ q.1
    have hmul := hasWeakDerivativeOn_mul_contDiff_first
      (n := n) (p := p) (Ω := Ω) (i := i)
      (hDlp q.2 hq2) (hDlp (i :: q.2) hq2next) hζq (hζBound q.1 hq1)
      (by simpa [ζq, iteratedPartialDeriv] using hζBound (i :: q.1) hq1next)
      (hDstep q.2 i hq2lt)
    simpa [ζq, iteratedPartialDeriv] using hmul
  have hsum := hasWeakDerivativeOn_list_pair_sum (n := n)
    (Ω := Ω) i terms htermWeak
  convert hsum using 1 <;> funext x
  · simp only [terms, S, weakLeibnizExpansion, List.map_map,
      Function.comp_def]
  · simp only [terms, S, weakLeibnizExpansion, derivativeSplits,
      List.map_append, List.map_map, List.sum_append, Function.comp_def]
    exact (List.sum_map_add (l := derivativeSplits α)
      (f := fun q ↦ iteratedPartialDeriv (n := n) q.1 ζ x * D (i :: q.2) x)
      (g := fun q ↦ iteratedPartialDeriv (n := n) (i :: q.1) ζ x * D q.2 x)).symm

/-- Higher-order weak Leibniz rule.  The reverse on the expansion word is an
artifact of composing first derivatives on the right; derivative words encode
commutative multi-indices, so this is exactly the usual multinomial formula.
-/
theorem hasWeakDerivativeOn_weakLeibniz
    (ζ : ℝ^n → ℝ) (D : List (Fin n) → ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζBound : ∀ β, MemLp
      (iteratedPartialDeriv (n := n) β ζ) (⊤ : ℝ≥0∞)
      (domainMeasure n Ω))
    (hDlp : ∀ β, MemLp (D β) p (domainMeasure n Ω))
    (hDstep : ∀ β i,
      HasWeakDerivativeOn (n := n) Ω [i] (D β) (D (i :: β))) :
    ∀ α, HasWeakDerivativeOn (n := n) Ω α
      (fun x ↦ ζ x * D [] x)
      (weakLeibnizExpansion ζ D α.reverse) := by
  intro α
  let L : List (Fin n) → ℝ^n → ℝ := fun β ↦
    weakLeibnizExpansion ζ D β.reverse
  have hL0 : LocallyIntegrableOn (L []) Ω volume := by
    rw [show L [] = fun x ↦ ζ x * D [] x by
      simp [L, weakLeibnizExpansion_nil]]
    have hprod : MemLp (fun x ↦ ζ x * D [] x) p (domainMeasure n Ω) := by
      exact (hζBound ([] : List (Fin n))).fun_mul (r := p)
        (hDlp ([] : List (Fin n)))
    exact memLp_locallyIntegrableOn_domain hprod Fact.out
  have hLstep : ∀ β i,
      HasWeakDerivativeOn (n := n) Ω [i] (L β) (L (β ++ [i])) := by
    intro β i
    simpa [L] using weakLeibnizExpansion_step (n := n) (p := p) (Ω := Ω)
      (k := β.length + 1) ζ D hζ (fun γ _ ↦ hζBound γ)
      (fun γ _ ↦ hDlp γ) (fun γ j _ ↦ hDstep γ j)
      β.reverse (by simp) i
  have hall := hasWeakDerivativeOn_of_append_single_chain (n := n) L hL0 hLstep
  simpa [L, weakLeibnizExpansion_nil] using hall α

/-- Finite-order higher weak Leibniz rule.  Unlike the unrestricted convenience
theorem above, this version assumes only the multiplier bounds and compatible
weak derivatives through the declared order `k`. -/
theorem hasWeakDerivativeOn_weakLeibniz_order
    (k : ℕ) (ζ : ℝ^n → ℝ) (D : List (Fin n) → ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζBound : ∀ β, β.length ≤ k → MemLp
      (iteratedPartialDeriv (n := n) β ζ) (⊤ : ℝ≥0∞)
      (domainMeasure n Ω))
    (hDlp : ∀ β, β.length ≤ k → MemLp (D β) p (domainMeasure n Ω))
    (hDstep : ∀ β i, β.length < k →
      HasWeakDerivativeOn (n := n) Ω [i] (D β) (D (i :: β)))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    HasWeakDerivativeOn (n := n) Ω α
      (fun x ↦ ζ x * D [] x)
      (weakLeibnizExpansion ζ D α.reverse) := by
  have hbaseLp : MemLp (fun x ↦ ζ x * D [] x) p (domainMeasure n Ω) := by
    exact (hζBound [] (by simp)).fun_mul (r := p) (hDlp [] (by simp))
  let L : List (Fin n) → ℝ^n → ℝ := fun β ↦
    weakLeibnizExpansion ζ D β.reverse
  have hL0 : LocallyIntegrableOn (L []) Ω volume := by
    simpa [L, weakLeibnizExpansion_nil] using
      memLp_locallyIntegrableOn_domain hbaseLp Fact.out
  have hLstep : ∀ (β : List (Fin n)) (i : Fin n), β.length < k →
      HasWeakDerivativeOn (n := n) Ω [i] (L β) (L (β ++ [i])) := by
    intro β i hβ
    simpa [L] using weakLeibnizExpansion_step (n := n) (p := p) (Ω := Ω)
      (k := k) ζ D hζ hζBound hDlp hDstep β.reverse (by simpa using hβ) i
  simpa [L, weakLeibnizExpansion_nil] using
    hasWeakDerivativeOn_of_append_single_chain_order
      (n := n) (Ω := Ω) k L hL0 hLstep α hα

namespace GraphSpace

/-- The concrete representative of a derivative word in a finite-order
`W^{k,p}` bundle.  Words above order `k` are assigned zero; finite-order
theorems never inspect that branch. -/
noncomputable def wkpWordRepresentative
    {k : ℕ} (U : W^{k,p}(Ω)) (β : List (Fin n)) : ℝ^n → ℝ :=
  if hβ : β.length ≤ k then
    ((U : WkpAmbientOn n k p Ω)
      (derivIndexOfList (n := n) (k := k) β hβ) : DerivLp n p Ω)
  else 0

omit [Fact (1 ≤ p)] in
/-- The empty word is represented by the base coordinate of `U`. -/
@[simp]
theorem wkpWordRepresentative_nil {k : ℕ} (U : W^{k,p}(Ω)) :
    wkpWordRepresentative U [] =
      ((U : WkpAmbientOn n k p Ω) (baseIndex n k) : DerivLp n p Ω) := by
  simp [wkpWordRepresentative, derivIndexOfList, baseIndex]

omit [Fact (1 ≤ p)] in
/-- Every in-range word representative belongs to the bundle's `L^p` class. -/
theorem wkpWordRepresentative_memLp {k : ℕ} (U : W^{k,p}(Ω))
    (β : List (Fin n)) (hβ : β.length ≤ k) :
    MemLp (wkpWordRepresentative U β) p (domainMeasure n Ω) := by
  simp only [wkpWordRepresentative, dite_eq_left hβ]
  exact MeasureTheory.Lp.memLp _

omit [Fact (1 ≤ p)] in
/-- Adjacent finite-order word representatives are related by the expected
first weak derivative.  Symmetry of mixed derivatives is handled by an
explicit list permutation. -/
theorem wkpWordRepresentative_step {k : ℕ} (U : W^{k,p}(Ω))
    (β : List (Fin n)) (i : Fin n) (hβ : β.length < k) :
    HasWeakDerivativeOn (n := n) Ω [i]
      (wkpWordRepresentative U β) (wkpWordRepresentative U (i :: β)) := by
  have hβle : β.length ≤ k := Nat.le_of_lt hβ
  have hnext : (i :: β).length ≤ k := by simpa using hβ
  simp only [wkpWordRepresentative, dite_eq_left hβle, dite_eq_left hnext]
  let aβ := derivIndexOfList (n := n) (k := k) β hβle
  let aiβ := derivIndexOfList (n := n) (k := k) (i :: β) hnext
  have hbase : HasWeakDerivativeOn (n := n) Ω β
      ((U : WkpAmbientOn n k p Ω) (baseIndex n k) : ℝ^n → ℝ)
      ((U : WkpAmbientOn n k p Ω) aβ : ℝ^n → ℝ) :=
    by simpa [aβ] using
      U.property.hasWeakDerivativeOn_list β hβle
  have hrotate : (i :: β).Perm (β ++ [i]) := by
    simpa only [List.append_nil] using
      (List.perm_middle (l₁ := β) (a := i) (l₂ := [])).symm
  have hfull : HasWeakDerivativeOn (n := n) Ω (β ++ [i])
      ((U : WkpAmbientOn n k p Ω) (baseIndex n k) : ℝ^n → ℝ)
      ((U : WkpAmbientOn n k p Ω) aiβ : ℝ^n → ℝ) :=
    (by simpa [aiβ] using
      (U.property.hasWeakDerivativeOn_list (i :: β) hnext).perm hrotate)
  exact hbase.cancel_prefix_append_single i hfull

/-- Exact finite-order weak Leibniz rule in the graph space
`W^{k,p}(Ω)`. -/
theorem WkpSpaceOn.hasWeakDerivativeOn_mul_smooth
    {k : ℕ} (U : W^{k,p}(Ω)) (ζ : ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζBound : ∀ β, β.length ≤ k → MemLp
      (iteratedPartialDeriv (n := n) β ζ) (⊤ : ℝ≥0∞)
      (domainMeasure n Ω))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    HasWeakDerivativeOn (n := n) Ω α
      (fun x ↦ ζ x *
        ((U : WkpAmbientOn n k p Ω) (baseIndex n k) : ℝ^n → ℝ) x)
      (weakLeibnizExpansion ζ (wkpWordRepresentative U) α.reverse) := by
  simpa using hasWeakDerivativeOn_weakLeibniz_order
    (n := n) (p := p) (Ω := Ω) k ζ (wkpWordRepresentative U) hζ hζBound
    (wkpWordRepresentative_memLp U)
    (fun β i hβ ↦ wkpWordRepresentative_step U β i hβ) α hα

/-- Local finite-order weak Leibniz rule.  On each relatively compact open
`V ⊂⊂ Ω`, the formula is represented by the derivative coordinates of
the local `W^{k,p}` element. Smooth multiplier derivatives are bounded on the
compact closure of `V`; no global derivative bounds are required. -/
theorem IsLocallyWkpOn.hasWeakDerivativeOn_mul_smooth
    {k : ℕ} {u : ℝ^n → ℝ} (hu : IsLocallyWkpOn k p Ω u)
    (ζ : ℝ^n → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (α : List (Fin n)) (hα : α.length ≤ k)
    (V : Set (ℝ^n)) (hVopen : IsOpen V) (hVcompact : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) :
    ∃ U : W^{k,p}(V),
      baseRepresentative U =ᵐ[domainMeasure n V] u ∧
      HasWeakDerivativeOn (n := n) V α (fun x ↦ ζ x * u x)
        (weakLeibnizExpansion ζ (wkpWordRepresentative U) α.reverse) := by
  obtain ⟨U, hUbase⟩ := hu V hVopen hVcompact hVΩ
  refine ⟨U, hUbase, ?_⟩
  have hlocalBound : ∀ β, β.length ≤ k → MemLp
      (iteratedPartialDeriv (n := n) β ζ) (⊤ : ℝ≥0∞)
      (domainMeasure n V) := by
    intro β _
    have hcont := (PDE.contDiff_top_iteratedPartialDeriv hζ β).continuous
    obtain ⟨C, hC⟩ := hVcompact.exists_bound_of_continuousOn hcont.continuousOn
    apply memLp_top_of_bound hcont.aestronglyMeasurable C
    exact ae_restrict_of_forall_mem hVopen.measurableSet fun x hx ↦
      hC x (subset_closure hx)
  have hmain := U.hasWeakDerivativeOn_mul_smooth ζ hζ hlocalBound α hα
  have hsource :
      (fun x ↦ ζ x * baseRepresentative U x)
        =ᵐ[domainMeasure n V] (fun x ↦ ζ x * u x) := by
    filter_upwards [hUbase] with x hx
    rw [hx]
  exact (hasWeakDerivativeOn_congr_ae (n := n) (Ω := V) (α := α)
    hsource Filter.EventuallyEq.rfl).mp hmain

end GraphSpace

end SobolevSpace
