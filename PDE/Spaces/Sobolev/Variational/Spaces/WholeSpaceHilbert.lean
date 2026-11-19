/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.H1
public import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Hilbert structures on whole-space H¹ and L²

Evolution problems on `ℝ^n` work with `H¹(ℝ^n)`, the spatial L² space `DerivLp n 2 univ`,
and finite ℓ² products of either or of `W^{k,2}(ℝ^n)`. All of these structures are already
inferable, but for `H¹` the search goes through the graph submodule of a nested `PiLp` bundle and
is slow enough to matter in long proofs. The scoped instances below name each structure directly.

They are scoped so that they stay off the global instance graph. A file that wants them
writes `open scoped SobolevSpace.WholeSpaceHilbert`. Every instance is definitionally the
inherited one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Sobolev

namespace SobolevSpace.WholeSpaceHilbert

open GraphSpace

/-- The H¹ graph norm inherited from the Sobolev submodule. -/
scoped instance h1NormedAddCommGroup {n : ℕ} : NormedAddCommGroup (H¹(ℝ^n)) :=
  Submodule.normedAddCommGroup (wkpSubmoduleOn n 1 2 univ)

/-- Real scalar multiplication on H¹ with its inherited graph norm. -/
scoped instance h1NormedSpace {n : ℕ} : NormedSpace ℝ (H¹(ℝ^n)) :=
  Submodule.normedSpace (wkpSubmoduleOn n 1 2 univ)

/-- The H¹ inner product, pairing the functions and their first weak derivatives. -/
scoped instance h1InnerProductSpace {n : ℕ} : InnerProductSpace ℝ (H¹(ℝ^n)) :=
  Submodule.innerProductSpace (wkpSubmoduleOn n 1 2 univ)

/-- The ℓ² norm on a finite family of H¹ functions. -/
scoped instance piH1NormedAddCommGroup {n : ℕ} {ι : Type*} [Fintype ι] :
    NormedAddCommGroup (PiLp 2 (fun _ : ι ↦ H¹(ℝ^n))) :=
  PiLp.normedAddCommGroup 2 (fun _ : ι ↦ H¹(ℝ^n))

/-- Componentwise real scalar multiplication on a finite ℓ² product of H¹ spaces. -/
scoped instance piH1NormedSpace {n : ℕ} {ι : Type*} [Fintype ι] :
    NormedSpace ℝ (PiLp 2 (fun _ : ι ↦ H¹(ℝ^n))) :=
  PiLp.normedSpace 2 ℝ (fun _ : ι ↦ H¹(ℝ^n))

/-- The sum of the component H¹ inner products on a finite family. -/
scoped instance piH1InnerProductSpace {n : ℕ} {ι : Type*} [Fintype ι] :
    InnerProductSpace ℝ (PiLp 2 (fun _ : ι ↦ H¹(ℝ^n))) :=
  PiLp.innerProductSpace (fun _ : ι ↦ H¹(ℝ^n))

/-- The usual norm on scalar L² fields over `ℝ^n`. -/
scoped instance l2NormedAddCommGroup {n : ℕ} : NormedAddCommGroup (DerivLp n 2 univ) :=
  Lp.instNormedAddCommGroup

/-- Real scalar multiplication on the spatial L² space. -/
scoped instance l2NormedSpace {n : ℕ} : NormedSpace ℝ (DerivLp n 2 univ) :=
  Lp.instNormedSpace

/-- The spatial L² inner product, the integral of the product of representatives. -/
scoped instance l2InnerProductSpace {n : ℕ} : InnerProductSpace ℝ (DerivLp n 2 univ) :=
  L2.innerProductSpace

/-- The ℓ² norm on a finite family of spatial L² fields. -/
scoped instance piL2NormedAddCommGroup {n : ℕ} {ι : Type*} [Fintype ι] :
    NormedAddCommGroup (PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)) :=
  PiLp.normedAddCommGroup 2 (fun _ : ι ↦ DerivLp n 2 univ)

/-- Componentwise real scalar multiplication on a finite ℓ² product of spatial L² spaces. -/
scoped instance piL2NormedSpace {n : ℕ} {ι : Type*} [Fintype ι] :
    NormedSpace ℝ (PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)) :=
  PiLp.normedSpace 2 ℝ (fun _ : ι ↦ DerivLp n 2 univ)

/-- The sum of the component spatial L² inner products on a finite family. -/
scoped instance piL2InnerProductSpace {n : ℕ} {ι : Type*} [Fintype ι] :
    InnerProductSpace ℝ (PiLp 2 (fun _ : ι ↦ DerivLp n 2 univ)) :=
  PiLp.innerProductSpace (fun _ : ι ↦ DerivLp n 2 univ)

/-- Componentwise real scalar multiplication on a finite ℓ² product of `W^{k,2}(ℝ^n)` spaces. -/
scoped instance piSobolevNormedSpace {n k : ℕ} {ι : Type*} [Fintype ι] :
    NormedSpace ℝ (PiLp 2 (fun _ : ι ↦ W^{k,2}(ℝ^n))) :=
  PiLp.normedSpace 2 ℝ (fun _ : ι ↦ W^{k,2}(ℝ^n))

end SobolevSpace.WholeSpaceHilbert
