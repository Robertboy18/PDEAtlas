/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.Algebra.Module.LinearPMap
import PDE.Analysis.MeasureTheory.Lp.WeightedDifference

/-!
# The Gagliardo–Slobodeckij graph space

The intrinsic fractional space is the graph of the weighted difference
operator from `Lᵖ(Ω; F)` to `Lᵖ(Ω × Ω; F)`. Its norm is inherited from the
`WithLp p` product, so it is the usual p-sum of the two component norms for
finite p and their maximum at infinity.

The graph is closed by almost-everywhere convergence of weighted differences.
Consequently it is complete when the real normed codomain is complete.
No openness or finite-volume assumption on the domain is needed. The
interpretation as a first-difference fractional Sobolev space uses `0 < s < 1`,
but the graph and its representatives are defined for every real order.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The domain of the weighted-difference operator on `Lᵖ(Ω; F)`. -/
def gagliardoDomain (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    Submodule ℝ (Lp F p ((volume : Measure (ℝ^n)).restrict Ω)) where
  carrier := {u | MemLp (fun z ↦ diffQuot n s u z (p := p)) p
    (gagliardoProductMeasure n Ω)}
  zero_mem' := by
    refine (memLp_congr_ae (diffQuot_congr_ae
      (n := n) (s := s) (Ω := Ω) (p := p)
      (Lp.coeFn_zero F p ((volume : Measure (ℝ^n)).restrict Ω)))).2 ?_
    simpa only [diffQuot_zero] using
      (MemLp.zero : MemLp (0 : ℝ^n × ℝ^n → F) p (gagliardoProductMeasure n Ω))
  add_mem' {u v} hu hv := by
    refine (memLp_congr_ae (diffQuot_congr_ae
      (n := n) (s := s) (Ω := Ω) (p := p) (Lp.coeFn_add u v))).2 ?_
    simpa only [diffQuot_add, Pi.add_apply] using hu.add hv
  smul_mem' c u hu := by
    refine (memLp_congr_ae (diffQuot_congr_ae
      (n := n) (s := s) (Ω := Ω) (p := p) (Lp.coeFn_smul c u))).2 ?_
    simpa only [diffQuot_smul, Pi.smul_apply] using hu.const_smul c

/-- The weighted difference as a partially defined real linear operator. -/
def gagliardoOperator (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    Lp F p ((volume : Measure (ℝ^n)).restrict Ω) →ₗ.[ℝ]
      Lp F p (gagliardoProductMeasure n Ω) where
  domain := gagliardoDomain n s Ω (p := p) (F := F)
  toFun :=
    { toFun := fun u ↦ u.prop.toLp (fun z ↦ diffQuot n s
        (u : Lp F p ((volume : Measure (ℝ^n)).restrict Ω)) z (p := p))
      map_add' := by
        intro u v
        rw [← MemLp.toLp_add u.prop v.prop]
        apply MemLp.toLp_congr
        have h := diffQuot_congr_ae
          (n := n) (s := s) (Ω := Ω) (p := p)
          (Lp.coeFn_add
            (u : Lp F p ((volume : Measure (ℝ^n)).restrict Ω))
            (v : Lp F p ((volume : Measure (ℝ^n)).restrict Ω)))
        simpa only [Submodule.coe_add, diffQuot_add, Pi.add_apply] using h
      map_smul' := by
        intro c u
        change _ = c • _
        rw [← MemLp.toLp_const_smul c u.prop]
        apply MemLp.toLp_congr
        have h := diffQuot_congr_ae
          (n := n) (s := s) (Ω := Ω) (p := p)
          (Lp.coeFn_smul c
            (u : Lp F p ((volume : Measure (ℝ^n)).restrict Ω)))
        simpa only [Submodule.coe_smul, diffQuot_smul, Pi.smul_apply] using h }

omit [Fact (1 ≤ p)] in
/-- Membership in the operator graph is the physical almost-everywhere
weighted-difference identity. -/
theorem mem_gagliardoOperator_graph_iff
    (z : Lp F p ((volume : Measure (ℝ^n)).restrict Ω) ×
      Lp F p (gagliardoProductMeasure n Ω)) :
    z ∈ (gagliardoOperator n s Ω).graph ↔
      (z.2 : ℝ^n × ℝ^n → F) =ᵐ[gagliardoProductMeasure n Ω]
        fun x ↦ diffQuot n s z.1 x (p := p) := by
  constructor
  · intro hz
    obtain ⟨u, hu₁, hu₂⟩ :=
      (LinearPMap.mem_graph_iff (gagliardoOperator n s Ω)).1 hz
    rw [← hu₁, ← hu₂]
    exact MemLp.coeFn_toLp u.prop
  · intro hz
    have hmem : MemLp (fun x ↦ diffQuot n s z.1 x (p := p)) p
        (gagliardoProductMeasure n Ω) :=
      (memLp_congr_ae hz).1 (Lp.memLp z.2)
    refine (LinearPMap.mem_graph_iff (gagliardoOperator n s Ω)).2
      ⟨⟨z.1, hmem⟩, rfl, ?_⟩
    exact Lp.ext ((MemLp.coeFn_toLp hmem).trans hz.symm)

/-- The Gagliardo operator has closed graph, including at exponent infinity. -/
theorem gagliardoOperator_isClosed :
    (gagliardoOperator n s Ω (p := p) (F := F)).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hclosed := MeasureTheory.Lp.isClosed_graph_weightedDifference
    (F := F) (p := p) (μ := (volume : Measure (ℝ^n)).restrict Ω)
    (fun z ↦ (‖z.1 - z.2‖ ^ ((n : ℝ) / p.toReal + s))⁻¹)
  convert hclosed using 1
  ext z
  exact mem_gagliardoOperator_graph_iff z

/-- The graph of the Gagliardo operator in the p-sum of its two `Lᵖ` spaces. -/
def gagliardoGraph (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    Submodule ℝ (WithLp p
      (Lp F p ((volume : Measure (ℝ^n)).restrict Ω) ×
        Lp F p (gagliardoProductMeasure n Ω))) :=
  (gagliardoOperator n s Ω).graph.comap
    (WithLp.prodContinuousLinearEquiv p ℝ
      (Lp F p ((volume : Measure (ℝ^n)).restrict Ω))
      (Lp F p (gagliardoProductMeasure n Ω))).toLinearMap

/-- The Gagliardo graph is closed in the p-sum product. -/
theorem isClosed_gagliardoGraph :
    IsClosed (gagliardoGraph n s Ω (p := p) (F := F) : Set (WithLp p
      (Lp F p ((volume : Measure (ℝ^n)).restrict Ω) ×
        Lp F p (gagliardoProductMeasure n Ω)))) := by
  change IsClosed
    ((WithLp.prodContinuousLinearEquiv p ℝ
      (Lp F p ((volume : Measure (ℝ^n)).restrict Ω))
      (Lp F p (gagliardoProductMeasure n Ω))) ⁻¹'
        ((gagliardoOperator n s Ω (p := p) (F := F)).graph : Set _))
  exact (gagliardoOperator_isClosed (n := n) (s := s) (Ω := Ω)).preimage
    (WithLp.prodContinuousLinearEquiv p ℝ
      (Lp F p ((volume : Measure (ℝ^n)).restrict Ω))
      (Lp F p (gagliardoProductMeasure n Ω))).continuous

/-- The intrinsic Gagliardo–Slobodeckij space with its `Lᵖ` graph norm.
The omitted parameters recover the real quadratic space. -/
abbrev GagliardoSpace (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n))
    (p : ℝ≥0∞ := 2) (F : Type* := by exact ℝ)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fact (1 ≤ p)] : Type _ :=
  gagliardoGraph n s Ω (p := p) (F := F)

/-- The graph is complete when its codomain is complete. -/
instance [CompleteSpace F] :
    CompleteSpace (GagliardoSpace n s Ω (p := p) (F := F)) :=
  (isClosed_gagliardoGraph (n := n) (s := s) (Ω := Ω)).completeSpace_coe

namespace GagliardoSpace

/-- The underlying `Lᵖ(Ω; F)` class of a Gagliardo-space element. -/
def toLp (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    GagliardoSpace n s Ω (p := p) (F := F) →L[ℝ]
      Lp F p ((volume : Measure (ℝ^n)).restrict Ω) :=
  (WithLp.fstL p ℝ
    (Lp F p ((volume : Measure (ℝ^n)).restrict Ω))
    (Lp F p (gagliardoProductMeasure n Ω))).comp
      (gagliardoGraph n s Ω).subtypeL

/-- The `Lᵖ(Ω × Ω; F)` weighted difference of a Gagliardo-space element. -/
def differenceQuotient (n : ℕ) (s : ℝ) (Ω : Set (ℝ^n)) :
    GagliardoSpace n s Ω (p := p) (F := F) →L[ℝ]
      Lp F p (gagliardoProductMeasure n Ω) :=
  (WithLp.sndL p ℝ
    (Lp F p ((volume : Measure (ℝ^n)).restrict Ω))
    (Lp F p (gagliardoProductMeasure n Ω))).comp
      (gagliardoGraph n s Ω).subtypeL

/-- The two stored coordinates belong to the weighted-difference graph. -/
theorem toLp_differenceQuotient_mem_graph
    (u : GagliardoSpace n s Ω (p := p) (F := F)) :
    (toLp n s Ω u, differenceQuotient n s Ω u) ∈
      (gagliardoOperator n s Ω).graph :=
  Submodule.mem_comap.mp u.prop

/-- The first coordinate lies in the domain of the partial operator. -/
theorem toLp_mem_domain (u : GagliardoSpace n s Ω (p := p) (F := F)) :
    toLp n s Ω u ∈ gagliardoDomain n s Ω :=
  LinearPMap.mem_domain_of_mem_graph (toLp_differenceQuotient_mem_graph u)

/-- The second coordinate is the partial operator applied to the first. -/
theorem differenceQuotient_eq_operator
    (u : GagliardoSpace n s Ω (p := p) (F := F)) :
    differenceQuotient n s Ω u =
      gagliardoOperator n s Ω ⟨toLp n s Ω u, toLp_mem_domain u⟩ :=
  (gagliardoOperator n s Ω).mem_graph_snd_inj
    (toLp_differenceQuotient_mem_graph u)
    ((gagliardoOperator n s Ω).mem_graph ⟨toLp n s Ω u, toLp_mem_domain u⟩) rfl

/-- The second coordinate represents the physical weighted difference almost
everywhere on the product domain. -/
theorem differenceQuotient_apply_ae
    (u : GagliardoSpace n s Ω (p := p) (F := F)) :
    (differenceQuotient n s Ω u : ℝ^n × ℝ^n → F)
      =ᵐ[gagliardoProductMeasure n Ω]
        fun z ↦ diffQuot n s (toLp n s Ω u) z (p := p) :=
  (mem_gagliardoOperator_graph_iff _).1 (toLp_differenceQuotient_mem_graph u)

/-- A graph element is determined by its underlying `Lᵖ` class. -/
theorem toLp_injective :
    Function.Injective (toLp n s Ω (p := p) (F := F)) := by
  intro u v huv
  change (WithLp.ofLp u.1).1 = (WithLp.ofLp v.1).1 at huv
  apply Subtype.ext
  apply WithLp.ofLp_injective
  apply Prod.ext huv
  exact (gagliardoOperator n s Ω).mem_graph_snd_inj'
    (toLp_differenceQuotient_mem_graph u)
    (toLp_differenceQuotient_mem_graph v) huv

/-- Construct a graph element from an `Lᵖ` class in the operator domain. -/
def ofLp (u : Lp F p ((volume : Measure (ℝ^n)).restrict Ω))
    (hu : u ∈ gagliardoDomain n s Ω) :
    GagliardoSpace n s Ω (p := p) (F := F) :=
  ⟨WithLp.toLp p (u, gagliardoOperator n s Ω ⟨u, hu⟩),
    Submodule.mem_comap.mpr ((gagliardoOperator n s Ω).mem_graph ⟨u, hu⟩)⟩

/-- The underlying `Lᵖ` class of the constructed graph element is its input. -/
@[simp]
theorem toLp_ofLp (u : Lp F p ((volume : Measure (ℝ^n)).restrict Ω))
    (hu : u ∈ gagliardoDomain n s Ω) :
    toLp n s Ω (ofLp (n := n) (s := s) (Ω := Ω) u hu) = u :=
  rfl

/-- The second coordinate of `ofLp` is the value of the partial operator. -/
@[simp]
theorem differenceQuotient_ofLp
    (u : Lp F p ((volume : Measure (ℝ^n)).restrict Ω))
    (hu : u ∈ gagliardoDomain n s Ω) :
    differenceQuotient n s Ω (ofLp (n := n) (s := s) (Ω := Ω) u hu) =
      gagliardoOperator n s Ω ⟨u, hu⟩ :=
  rfl

/-- Reconstructing a graph element from its first coordinate gives it back. -/
@[simp]
theorem ofLp_toLp (u : GagliardoSpace n s Ω (p := p) (F := F)) :
    ofLp (n := n) (s := s) (Ω := Ω) (toLp n s Ω u) (toLp_mem_domain u) = u :=
  toLp_injective (toLp_ofLp _ _)

/-- The range of the underlying `Lᵖ` realization is exactly the operator domain. -/
theorem range_toLp :
    LinearMap.range (toLp n s Ω (p := p) (F := F)).toLinearMap =
      gagliardoDomain n s Ω := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact toLp_mem_domain v
  · intro hu
    exact ⟨ofLp (n := n) (s := s) (Ω := Ω) u hu, toLp_ofLp u hu⟩

/-- Construct a graph element from a function satisfying the Gagliardo condition. -/
def ofFunction (u : ℝ^n → F) (hu : MemGagliardo n s Ω u (p := p)) :
    GagliardoSpace n s Ω (p := p) (F := F) :=
  ofLp (n := n) (s := s) (Ω := Ω) (hu.1.toLp u)
    ((memLp_congr_ae (diffQuot_congr_ae
      (n := n) (s := s) (Ω := Ω) (p := p) (MemLp.coeFn_toLp hu.1))).2 hu.2)

/-- The first coordinate of `ofFunction` is the original function's `Lᵖ` class. -/
@[simp]
theorem toLp_ofFunction (u : ℝ^n → F) (hu : MemGagliardo n s Ω u (p := p)) :
    toLp n s Ω (ofFunction (n := n) (s := s) (Ω := Ω) u hu) = hu.1.toLp u :=
  rfl

/-- The first coordinate of `ofFunction` agrees almost everywhere with its input. -/
theorem toLp_ofFunction_apply_ae (u : ℝ^n → F)
    (hu : MemGagliardo n s Ω u (p := p)) :
    (toLp n s Ω (ofFunction (n := n) (s := s) (Ω := Ω) u hu) : ℝ^n → F)
      =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] u := by
  simpa only [toLp_ofFunction] using MemLp.coeFn_toLp hu.1

/-- The raw Gagliardo condition is exactly representability by a graph element. -/
theorem memGagliardo_iff_exists_gagliardoSpace (u : ℝ^n → F) :
    MemGagliardo n s Ω u (p := p) ↔
      ∃ v : GagliardoSpace n s Ω (p := p) (F := F),
        (toLp n s Ω v : ℝ^n → F) =ᵐ[(volume : Measure (ℝ^n)).restrict Ω] u := by
  constructor
  · intro hu
    exact ⟨ofFunction (n := n) (s := s) (Ω := Ω) u hu,
      toLp_ofFunction_apply_ae u hu⟩
  · rintro ⟨v, hv⟩
    refine ⟨(memLp_congr_ae hv).1 (Lp.memLp (toLp n s Ω v)), ?_⟩
    have hdiff : (differenceQuotient n s Ω v : ℝ^n × ℝ^n → F)
        =ᵐ[gagliardoProductMeasure n Ω] fun z ↦ diffQuot n s u z (p := p) :=
      (differenceQuotient_apply_ae v).trans
        (diffQuot_congr_ae (n := n) (s := s) (Ω := Ω) (p := p) hv)
    exact (memLp_congr_ae hdiff).1 (Lp.memLp (differenceQuotient n s Ω v))

/-- At a finite exponent, the p-th power of the graph norm is the sum of the
p-th powers of its two coordinate norms. -/
theorem norm_rpow_eq (hp : p ≠ ∞)
    (u : GagliardoSpace n s Ω (p := p) (F := F)) :
    ‖u‖ ^ p.toReal =
      ‖toLp n s Ω u‖ ^ p.toReal + ‖differenceQuotient n s Ω u‖ ^ p.toReal := by
  have hp₀ : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  change ‖u.1‖ ^ p.toReal = ‖u.1.fst‖ ^ p.toReal + ‖u.1.snd‖ ^ p.toReal
  rw [WithLp.prod_norm_eq_add hp₀, one_div, Real.rpow_inv_rpow]
  · exact add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (norm_nonneg _) _)
  · exact hp₀.ne'

/-- At exponent infinity the graph norm is the maximum of its coordinate norms. -/
theorem norm_top (u : GagliardoSpace n s Ω (p := ∞) (F := F)) :
    ‖u‖ = max ‖toLp n s Ω u‖ ‖differenceQuotient n s Ω u‖ :=
  WithLp.prod_norm_eq_sup u.1

end GagliardoSpace

end SobolevSpace.Fractional
