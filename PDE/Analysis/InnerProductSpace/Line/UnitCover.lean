/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.Homotopy.Lifting

/-!
# The unit vectors of a real line family

A locally continuous unit generator trivializes the unit vectors of a line
family. The fibre is the two real scalars of norm one. Using the induced topology
on the total space makes the projection a covering map.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped InnerProductSpace

namespace Submodule

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit vectors in a family of real subspaces, with its induced topology. -/
abbrev UnitTotal (L : X → Submodule ℝ E) :=
  {p : X × E // p.2 ∈ L p.1 ∧ ‖p.2‖ = 1}

namespace UnitTotal

variable (L : X → Submodule ℝ E)

/-- Projection of a unit vector to its base point. -/
def proj (p : UnitTotal L) : X := p.1.1

/-- The projection from the unit-vector total space to the base is continuous. -/
theorem continuous_proj : Continuous (proj L) :=
  continuous_fst.comp continuous_subtype_val

end UnitTotal

/-- The coordinate of a vector in the line of a unit vector is its inner product. -/
theorem inner_smul_eq_of_mem_span_singleton {v w : E} (hv : ‖v‖ = 1)
    (hw : w ∈ ℝ ∙ v) : ⟪v, w⟫_ℝ • v = w := by
  obtain ⟨a, rfl⟩ := mem_span_singleton.mp hw
  simp [inner_smul_right, hv]

/-- Unit vectors in a real line have a coordinate of absolute value one. -/
theorem abs_inner_eq_one_of_mem_span_singleton {v w : E}
    (hv : ‖v‖ = 1) (hw : w ∈ ℝ ∙ v) (hwn : ‖w‖ = 1) :
    |⟪v, w⟫_ℝ| = 1 := by
  have h := congrArg norm (inner_smul_eq_of_mem_span_singleton hv hw)
  simpa [norm_smul, hv, hwn, Real.norm_eq_abs] using h

namespace UnitTotal

/-- The two signs, realized as a subspace of the real line. -/
abbrev Sign := {a : ℝ // |a| = 1}

/-- The real scalars of absolute value one form a finite set. -/
instance : Finite Sign := by
  have h : {a : ℝ | |a| = 1} = {1, -1} := by
    ext a
    simp [abs_eq (show (0 : ℝ) ≤ 1 by norm_num)]
  exact h ▸ Set.toFinite {1, (-1 : ℝ)} |>.to_subtype

variable (L : X → Submodule ℝ E) {U : Set X} (v : X → E)
  (hv : ContinuousOn v U) (hvn : ∀ x ∈ U, ‖v x‖ = 1)
  (hL : ∀ x ∈ U, L x = ℝ ∙ v x)

/-- Coordinates on the unit vectors above a neighborhood with a unit generator. -/
def homeomorphPreimage : proj L ⁻¹' U ≃ₜ U × Sign where
  toFun p :=
    (⟨proj L p, p.2⟩,
      ⟨⟪v (proj L p), p.1.1.2⟫_ℝ,
        abs_inner_eq_one_of_mem_span_singleton (hvn _ p.2)
          ((hL _ p.2) ▸ p.1.2.1) p.1.2.2⟩)
  invFun p :=
    ⟨⟨(p.1, p.2.1 • v p.1),
      (hL _ p.1.2).symm ▸ smul_mem _ _ (mem_span_singleton_self _),
      by simpa [norm_smul, hvn _ p.1.2, Real.norm_eq_abs] using p.2.2⟩, p.1.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    exact inner_smul_eq_of_mem_span_singleton (hvn _ p.2)
      ((hL _ p.2) ▸ p.1.2.1)
  right_inv p := by
    refine Prod.ext ?_ ?_
    · rfl
    apply Subtype.ext
    simp [proj, inner_smul_right, hvn _ p.1.2]
  continuous_toFun := by
    have hc : Continuous (fun p : proj L ⁻¹' U ↦ (⟨proj L p, p.2⟩ : U)) :=
      ((continuous_proj L).comp continuous_subtype_val).subtype_mk _
    have hcv : Continuous (fun p : proj L ⁻¹' U ↦ v (proj L p)) :=
      (continuousOn_iff_continuous_domRestrict.mp hv).comp hc
    exact hc.prodMk ((hcv.inner (by fun_prop)).subtype_mk _)
  continuous_invFun := by
    have hcv : Continuous (fun p : U × Sign ↦ v p.1) :=
      (continuousOn_iff_continuous_domRestrict.mp hv).comp continuous_fst
    exact ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).smul hcv)).subtype_mk _ |>.subtype_mk _

include hv hvn hL in
/-- A local continuous unit generator gives an evenly covered neighborhood. -/
theorem isEvenlyCovered {x : X} (hx : x ∈ U) (hU : IsOpen U) :
    IsEvenlyCovered (proj L) x Sign :=
  ⟨inferInstance, U, hx, hU, hU.preimage (continuous_proj L),
    homeomorphPreimage L v hv hvn hL, fun _ ↦ rfl⟩

/-- The unit vectors of a locally continuously generated line family form a cover. -/
theorem isCoveringMap
    (h : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ v : X → E,
      ContinuousOn v U ∧ (∀ y ∈ U, ‖v y‖ = 1) ∧
        ∀ y ∈ U, L y = ℝ ∙ v y) :
    IsCoveringMap (proj L) := by
  intro x
  obtain ⟨U, hU, hx, v, hv, hvn, hL⟩ := h x
  exact (isEvenlyCovered L v hv hvn hL hx hU).to_isEvenlyCovered_preimage

/-- Fixing one unit vector determines a unique continuous unit section over a
simply connected, locally path connected base. Local generators supply the cover. -/
theorem existsUnique_continuous_unit_section
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (h : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ v : X → E,
      ContinuousOn v U ∧ (∀ y ∈ U, ‖v y‖ = 1) ∧
        ∀ y ∈ U, L y = ℝ ∙ v y)
    (x₀ : X) (v₀ : E) (hv₀ : v₀ ∈ L x₀) (hn₀ : ‖v₀‖ = 1) :
    ∃! v : C(X, E), v x₀ = v₀ ∧ ∀ x, v x ∈ L x ∧ ‖v x‖ = 1 := by
  let e₀ : UnitTotal L := ⟨(x₀, v₀), hv₀, hn₀⟩
  obtain ⟨F, ⟨hF₀, hF⟩, huniq⟩ :=
    (isCoveringMap L h).existsUnique_continuousMap_lifts
      (ContinuousMap.id X) x₀ e₀ rfl
  have hproj (x : X) : (F x).1.1 = x := congr_fun hF x
  let v : C(X, E) :=
    ⟨fun x ↦ (F x).1.2, continuous_snd.comp (continuous_subtype_val.comp F.continuous)⟩
  refine ⟨v, ⟨?_, ?_⟩, ?_⟩
  · exact congrArg (fun e : UnitTotal L ↦ e.1.2) hF₀
  · intro x
    refine ⟨?_, (F x).2.2⟩
    change (F x).1.2 ∈ L x
    simpa only [hproj x] using (F x).2.1
  · rintro w ⟨hw₀, hw⟩
    let G : C(X, UnitTotal L) :=
      ⟨fun x ↦ ⟨(x, w x), hw x⟩,
        (continuous_id.prodMk w.continuous).subtype_mk _⟩
    have hGF : G = F := huniq G ⟨by
      apply Subtype.ext
      exact Prod.ext rfl hw₀, rfl⟩
    ext x
    exact congrArg (fun H : C(X, UnitTotal L) ↦ (H x).1.2) hGF

end UnitTotal

end Submodule
