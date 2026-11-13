/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.CutoffConvergence
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.DerivativeSplits
public import PDE.Spaces.Sobolev.Foundations.Representatives.Definitions
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Calculus.Product.ClassicalLeibniz

/-!
# Truncation of mollified Sobolev derivatives

Mollification is uniformly bounded on every weak derivative recorded by a global Sobolev
representative. The Leibniz expansion then separates a convergent principal term from a
finite sum of vanishing cutoff-derivative terms. The mollifier scales and cutoff radii can
be chosen independently.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.Approximation

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Mollification gives a bound uniform in its scale for each recorded Sobolev derivative. -/
theorem exists_uniform_eLpNorm_iteratedPartialDeriv_mollify_le
    (μ : Mollifier n) (hp : p ≠ ∞) (u : GlobalSobolevSpace n k p)
    (α : List (Fin n)) (hαk : α.length ≤ k) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ ε : ℝ, 0 < ε →
      eLpNorm (iteratedPartialDeriv α (mollify μ ε u.toFun)) p volume ≤ B := by
  have hu : MemLp u.toFun p volume := by simpa [domainMeasure] using u.memLp
  by_cases hα : α = []
  · refine ⟨eLpNorm u.toFun p volume, ne_of_lt hu, fun ε hε ↦ ?_⟩
    simpa [hα, iteratedPartialDeriv] using MollifyLp.eLpNorm_mollify_le μ hε hp hu
  · obtain ⟨g, hg, hw⟩ := u.weak_derivs_inLp α hαk
    have hg' : MemLp g p volume := by simpa [domainMeasure] using hg
    refine ⟨eLpNorm g p volume, ne_of_lt hg', fun ε hε ↦ ?_⟩
    have hcomm : iteratedPartialDeriv α (mollify μ ε u.toFun) = mollify μ ε g :=
      iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ μ hε hα
        (hu.locallyIntegrable Fact.out) hw
    rw [hcomm]
    exact MollifyLp.eLpNorm_mollify_le μ hε hp hg'

/-- Truncating mollifications preserves convergence to a nonempty weak derivative.
The finite Leibniz remainder is controlled by the lower-order Sobolev derivatives. -/
theorem tendsto_eLpNorm_iteratedPartialDeriv_cutoff_mollify_sub
    (μ : Mollifier n) (hp : p ≠ ∞) (u : GlobalSobolevSpace n k p)
    (α : List (Fin n)) (hα : α ≠ []) (hαk : α.length ≤ k)
    {g : ℝ^n → ℝ} (hg : MemLp g p volume) (hw : HasWeakDerivativeOn univ α u.toFun g)
    {ε R : ℕ → ℝ} (hεpos : ∀ m, 0 < ε m) (hε : Tendsto ε atTop (𝓝 0))
    (hRpos : ∀ m, 0 < R m) (hR : Tendsto R atTop atTop) :
    Tendsto (fun m ↦ eLpNorm (fun x ↦ iteratedPartialDeriv α
      (fun y ↦ cutoff (R m) y * mollify μ (ε m) u.toFun y) x - g x) p volume)
      atTop (𝓝 0) := by
  classical
  have hu : MemLp u.toFun p volume := by simpa [domainMeasure] using u.memLp
  have huLoc := hu.locallyIntegrable (Fact.out : 1 ≤ p)
  let v (m : ℕ) := mollify μ (ε m) u.toFun
  have hv (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (v m) :=
    mollify_contDiff_of_pos μ (hεpos m) u.toFun huLoc
  have hcomm (m : ℕ) : iteratedPartialDeriv α (v m) = mollify μ (ε m) g :=
    iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ
      μ (hεpos m) hα huLoc hw
  have hmain : Tendsto (fun m ↦ eLpNorm
      (fun x ↦ cutoff (R m) x * iteratedPartialDeriv α (v m) x - g x) p volume)
      atTop (𝓝 0) := by
    simp_rw [hcomm]
    exact tendsto_eLpNorm_cutoff_mul_sub hp hg
      (fun m ↦ (mollify_contDiff_of_pos μ (hεpos m) g
        (hg.locallyIntegrable Fact.out)).continuous.aestronglyMeasurable)
      (mollify_converges_Lp μ p hp ε hεpos hε hg) hRpos hR
  let tail := (derivativeSplits α).tail
  let term (m : ℕ) (q : List (Fin n) × List (Fin n)) : ℝ^n → ℝ :=
    fun x ↦ iteratedPartialDeriv q.1 (cutoff (R m)) x * iteratedPartialDeriv q.2 (v m) x
  have hterm (q : List (Fin n) × List (Fin n)) (hq : q ∈ tail) :
      Tendsto (fun m ↦ eLpNorm (term m q) p volume) atTop (𝓝 0) := by
    have hlen := derivativeSplits_length (List.mem_of_mem_tail hq)
    have hqk : q.2.length ≤ k := by omega
    obtain ⟨B, hBfin, hB⟩ :=
      exists_uniform_eLpNorm_iteratedPartialDeriv_mollify_le μ hp u q.2 hqk
    exact tendsto_eLpNorm_iteratedPartialDeriv_cutoff_mul q.1
      (derivativeSplits_tail_first_ne_nil α q hq) hRpos hR
      (fun m ↦ (PDE.contDiff_top_iteratedPartialDeriv (hv m) q.2).continuous.aestronglyMeasurable)
      hBfin (fun m ↦ hB (ε m) (hεpos m))
  have herr : Tendsto (fun m ↦ eLpNorm ((tail.map (term m)).sum) p volume)
      atTop (𝓝 0) := by
    have hsum := tendsto_list_sum tail hterm
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hsum) (fun _ ↦ bot_le) fun m ↦ ?_
    simpa only [List.map_map, Function.comp_def] using
      List.le_sum_of_subadditive (fun f : ℝ^n → ℝ ↦ eLpNorm f p volume)
        (by simp) (fun _ _ ↦ eLpNorm_add_le (Fact.out : 1 ≤ p)) (tail.map (term m))
  have hsplit (m : ℕ) : iteratedPartialDeriv α
      (fun x ↦ cutoff (R m) x * v m x) =
        (fun x ↦ cutoff (R m) x * iteratedPartialDeriv α (v m) x) +
          (tail.map (term m)).sum := by
    funext x
    have heval (L : List (ℝ^n → ℝ)) : L.sum x = (L.map fun f ↦ f x).sum :=
      map_list_sum (Pi.evalAddMonoidHom (fun _ : ℝ^n ↦ ℝ) x) L
    have hs := iteratedPartialDeriv_mul_eq_sum_split α (cutoff (R m)) (v m)
      (cutoff_contDiff (R m)) (hv m) x
    have hhead := derivativeSplits_head? α
    cases he : derivativeSplits α with
    | nil => exact False.elim (derivativeSplits_ne_nil α he)
    | cons q qs =>
      have hq : q = ([], α) := Option.some.inj (by simpa [he] using hhead)
      subst q
      simpa [he, tail, term, iteratedPartialDeriv, heval, List.map_map, Function.comp_def] using hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hmain.add herr) (fun _ ↦ bot_le) fun m ↦ ?_
  have heq : (fun x ↦ iteratedPartialDeriv α
      (fun y ↦ cutoff (R m) y * v m y) x - g x) =
        (fun x ↦ cutoff (R m) x * iteratedPartialDeriv α (v m) x - g x) +
          (tail.map (term m)).sum := by
    funext x
    rw [hsplit]
    simp only [Pi.add_apply]
    ring
  change eLpNorm (fun x ↦ iteratedPartialDeriv α
    (fun y ↦ cutoff (R m) y * v m y) x - g x) p volume ≤ _
  rw [heq]
  exact eLpNorm_add_le (Fact.out : 1 ≤ p)

end SobolevSpace.Approximation
