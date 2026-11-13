/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Parabolic.Quadratic

/-!
# Compact sets of contacts supported over earlier times

The support region ends at the contact time and therefore moves with the
contact. Separate support at the same time from support at strictly earlier
times: the latter can be written as a closed implication by allowing equality
of the two times. This proves compactness without continuity of a chosen
minimizer or any injectivity of the vertex map.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Analysis

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A fixed rising paraboloid preserves joint continuity of its gap. -/
theorem continuousOn_parabolicQuadraticTilt
    {u : E → ℝ → ℝ} {K : Set (E × ℝ)}
    (hu : ContinuousOn (Function.uncurry u) K) (κ : ℝ) (v : E × ℝ) :
    ContinuousOn (parabolicQuadraticTilt u κ v) K :=
  (hu.add (continuousOn_const.mul
    ((continuous_fst.continuousOn.sub continuousOn_const).norm.pow 2))).sub
      (continuousOn_const.mul (continuous_snd.continuousOn.sub continuousOn_const))

/-- Joint continuity of the value and spatial gradient gives continuity of
the full space and time vertex map. -/
theorem continuousOn_parabolicQuadraticContactMap
    {u : E → ℝ → ℝ} {K : Set (E × ℝ)}
    (hu : ContinuousOn (Function.uncurry u) K)
    (hg : ContinuousOn (fun p : E × ℝ ↦ ∇ (fun x ↦ u x p.2) p.1) K)
    (κ : ℝ) :
    ContinuousOn (parabolicQuadraticContactMap u κ) K := by
  have hy : ContinuousOn
      (fun p : E × ℝ ↦ quadraticContactMap (fun x ↦ u x p.2) κ p.1) K :=
    continuous_fst.continuousOn.add (continuousOn_const.smul hg)
  exact hy.prodMk (continuous_snd.continuousOn.sub
    (continuousOn_const.mul
      (hu.add (continuousOn_const.mul ((continuous_fst.continuousOn.sub hy).norm.pow 2)))))

/-- Compactness retains the entire earlier-time support condition. The value
is continuous on the support cylinder; the spatial gradient need only be
continuous on the compact region where contacts lie. -/
theorem isCompact_parabolicQuadraticContactSet
    {u : E → ℝ → ℝ} {κ a b : ℝ} {S : Set E} {K Y : Set (E × ℝ)}
    (hK : IsCompact K) (hKS : K ⊆ S ×ˢ Icc a b) (hY : IsClosed Y)
    (hu : ContinuousOn (Function.uncurry u) (S ×ˢ Icc a b))
    (hg : ContinuousOn (fun p : E × ℝ ↦ ∇ (fun x ↦ u x p.2) p.1) K) :
    IsCompact (parabolicQuadraticContactSet u κ a S K Y) := by
  let F := parabolicQuadraticContactMap u κ
  have hF : ContinuousOn F K := continuousOn_parabolicQuadraticContactMap (hu.mono hKS) hg κ
  have hsame (x : E) (hx : x ∈ S) : ContinuousOn
      (fun p : E × ℝ ↦ parabolicQuadraticTilt u κ (F p) (x, p.2)) K := by
    have hv : ContinuousOn (fun p : E × ℝ ↦ u x p.2) K :=
      hu.comp (continuous_const.prodMk continuous_snd).continuousOn
        (fun p hp ↦ ⟨hx, (hKS hp).2⟩)
    exact (hv.add (continuousOn_const.mul ((continuousOn_const.sub hF.fst).norm.pow 2))).sub
      (continuousOn_const.mul (continuous_snd.continuousOn.sub hF.snd))
  have hfixed (q : E × ℝ) : ContinuousOn
      (fun p ↦ parabolicQuadraticTilt u κ (F p) q) K :=
    (continuousOn_const.add
      (continuousOn_const.mul ((continuousOn_const.sub hF.fst).norm.pow 2))).sub
        (continuousOn_const.mul (continuousOn_const.sub hF.snd))
  have heq : parabolicQuadraticContactSet u κ a S K Y =
      ((K ∩ F ⁻¹' Y) ∩
        ⋂ x ∈ S, {p | p ∈ K ∧ 0 ≤ parabolicQuadraticTilt u κ (F p) (x, p.2)}) ∩
      ⋂ q ∈ S ×ˢ Icc a b,
        ({p | p ∈ K ∧ p.2 ≤ q.2} ∪
          {p | p ∈ K ∧ 0 ≤ parabolicQuadraticTilt u κ (F p) q}) := by
    ext p
    simp only [parabolicQuadraticContactSet, mem_ofPred_eq, mem_inter_iff, mem_preimage,
      mem_iInter, mem_union]
    constructor
    · rintro ⟨hp, hvertex, hsupport⟩
      refine ⟨⟨⟨hp, hvertex⟩, fun x hx ↦
        ⟨hp, hsupport (x, p.2) ⟨hx, (hKS hp).2.1, le_rfl⟩⟩⟩, ?_⟩
      intro q hq
      by_cases htime : p.2 ≤ q.2
      · exact Or.inl ⟨hp, htime⟩
      · exact Or.inr ⟨hp, hsupport q ⟨hq.1, hq.2.1, (lt_of_not_ge htime).le⟩⟩
    · rintro ⟨⟨⟨hp, hvertex⟩, hsameTime⟩, hpast⟩
      refine ⟨hp, hvertex, ?_⟩
      intro q hq
      rcases hpast q ⟨hq.1, hq.2.1, hq.2.2.trans (hKS hp).2.2⟩ with ht | hs
      · have he : q.2 = p.2 := hq.2.2.antisymm ht.2
        have hepair : q = (q.1, p.2) := Prod.ext rfl he
        rw [hepair]
        exact (hsameTime q.1 hq.1).2
      · exact hs.2
  have hclosed : IsClosed (parabolicQuadraticContactSet u κ a S K Y) := by
    rw [heq]
    refine ((hF.preimage_isClosed_of_isClosed hK.isClosed hY).inter
      (isClosed_biInter fun x hx ↦
        hK.isClosed.isClosed_le continuousOn_const (hsame x hx))).inter ?_
    exact isClosed_biInter fun q _ ↦
      (hK.isClosed.isClosed_le continuous_snd.continuousOn continuousOn_const).union
        (hK.isClosed.isClosed_le continuousOn_const (hfixed q))
  exact hK.of_isClosed_subset hclosed (fun _ hp ↦ hp.1)

end PDE.Analysis
