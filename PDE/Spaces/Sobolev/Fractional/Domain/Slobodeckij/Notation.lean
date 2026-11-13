/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph

/-!
# Notation for intrinsic fractional Sobolev spaces

With `open scoped FractionalSobolev`, write `W^{s,p}(Ω; F)` for the
Gagliardo–Slobodeckij graph on `Ω`, and `W^{s,p}(Ω)` for its scalar version.
The domain determines the dimension; `W^{s,p}(ℝ^n; F)` denotes the whole space.

The scope distinguishes this difference-quotient model from the integer-order
weak-derivative model in the `Sobolev` scope. For the usual fractional Sobolev
interpretation, the order lies strictly between zero and one. The notation
abbreviates the graph and introduces no new instances.
-/

@[expose] public section

/-- Intrinsic fractional Sobolev space with a visible real normed codomain. -/
scoped[FractionalSobolev] notation "W^{" s "," p "}(" Ω "; " F ")" =>
  SobolevSpace.Fractional.GagliardoSpace _ s Ω p F

/-- Intrinsic fractional Sobolev space on a bundled domain. -/
scoped[FractionalSobolev] notation "W^{" s "," p "}(" Ω "; " F ")" =>
  SobolevSpace.Fractional.GagliardoSpace _ s (SetLike.coe Ω) p F

/-- Scalar intrinsic fractional Sobolev space. -/
scoped[FractionalSobolev] notation "W^{" s "," p "}(" Ω ")" =>
  SobolevSpace.Fractional.GagliardoSpace _ s Ω p

/-- Scalar intrinsic fractional Sobolev space on a bundled domain. -/
scoped[FractionalSobolev] notation "W^{" s "," p "}(" Ω ")" =>
  SobolevSpace.Fractional.GagliardoSpace _ s (SetLike.coe Ω) p

/-- Whole-space intrinsic fractional Sobolev space with a visible codomain. -/
scoped[FractionalSobolev] notation "W^{" s "," p "}(" "ℝ^" n "; " F ")" =>
  SobolevSpace.Fractional.GagliardoSpace n s Set.univ p F

/-- Scalar whole-space intrinsic fractional Sobolev space. -/
scoped[FractionalSobolev] notation "W^{" s "," p "}(" "ℝ^" n ")" =>
  SobolevSpace.Fractional.GagliardoSpace n s Set.univ p
