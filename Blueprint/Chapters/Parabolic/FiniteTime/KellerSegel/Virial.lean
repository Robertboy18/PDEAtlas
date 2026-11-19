/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Parabolic.FiniteTime.KellerSegel.Similarity
import PDE.Solution.Singularity.FiniteTime.KellerSegel.Virial

/-!
# Keller–Segel virial horizon

The conditional affine second-moment identity and the resulting upper bound
on a two-dimensional Keller–Segel lifespan.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Directive attributes are single-line syntax; blank lines delimit rendered paragraphs.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

set_option linter.hashCommand false in
#doc (Manual) "Keller–Segel Virial Horizon" =>

# Two-dimensional Keller–Segel virial horizon

The virial mechanism turns a question about how long a PDE solution lives into a
contradiction between two numbers. In the supercritical two-dimensional regime,
the normalized Keller–Segel second moment decreases at a constant rate. A
nonnegative density cannot have a negative second moment, so a classical solution
satisfying the virial hypotheses cannot survive past the moment when that affine
quantity hits zero.

:::definition "parabolic.keller_segel_virial_horizon" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.Virial.decayRate, PDE.Solution.Singularity.FiniteTime.KellerSegel.Virial.horizon")

For mass $`M>8\pi`, define

$$`
\gamma(M)=\frac{M^2}{2\pi}-4M>0,
\qquad
T_{\mathrm{vir}}=\frac{I(0)}{\gamma(M)}.
`

For the whole-space system with sensitivity one and the normalized Newtonian
potential, the classical second-moment identity is $`I'(t)=-\gamma(M)`
(Blanchet–Dolbeault–Perthame, *Electron. J. Differential Equations*
2006(44), Theorem 1.1 and equation (2.3)).

The pointwise Keller–Segel solution predicate does not fix this
normalization: adding a harmonic function to $`\Phi` preserves
$`-\Delta\Phi=u` but can change the drift. A PDE derivation of the sharp
virial law therefore also needs the Newtonian normalization or equivalent
decay, finite moments, mass conservation, differentiation under the integral,
and justified integration by parts. The theorems take the resulting scalar
derivative identity as a hypothesis.
:::

A constant derivative integrates to an affine function, and that is all the
affine law extracts from the identity; no sign condition on the mass is
needed for it.

:::theorem "parabolic.keller_segel_virial_affine" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.Virial.second_moment_eq_affine") (uses := "parabolic.keller_segel_virial_horizon")

If $`I` is continuous on $`[0,T]`, differentiable on $`(0,T)`, and satisfies
the virial identity there, then

$$`I(t)=I(0)-\gamma(M)t\qquad(0\le t\le T).`
:::

:::proof "parabolic.keller_segel_virial_affine"
Rewrite the assumed derivative as the constant $`-\gamma(M)`. The lower and
upper mean-value inequalities on the convex interval $`[0,T]` then bound
$`I(t)-I(0)` from both sides by $`-\gamma(M)t`. The two bounds coincide,
which gives the affine identity.
:::

Supercritical mass enters at this point, through $`\gamma(M)>0`: the affine
function is then strictly decreasing and crosses zero at
$`T_{\mathrm{vir}}`.

:::theorem "parabolic.keller_segel_virial_right_endpoint" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.Virial.right_endpoint_le_horizon") (uses := "parabolic.keller_segel_virial_affine")

Suppose $`T\geq0`, the second moment is continuous on $`[0,T]`,
differentiable on $`(0,T)`, and satisfies the virial identity there. If
$`M>8\pi` and the second moment is nonnegative at $`T`, then

$$`T\le T_{\mathrm{vir}}.`

The endpoint $`T` is any time up to which the hypotheses hold. Jäger–Luckhaus,
*Trans. Amer. Math. Soc.* 329 (1992), DOI 10.1090/S0002-9947-1992-1046835-6,
is the historical background for radial explosion arguments; the whole-space
identity is the one of Blanchet–Dolbeault–Perthame.
:::

:::proof "parabolic.keller_segel_virial_right_endpoint"
Supercritical mass makes $`\gamma(M)` positive. If the endpoint lay strictly
beyond $`I(0)/\gamma(M)`, the affine formula at $`T` would give
$`I(T)=I(0)-\gamma(M)T<0`. This contradicts the assumed nonnegativity of the
endpoint moment.
:::

The scalar theorem never mentions a density. The density-level version
derives the one hypothesis the scalar statement cannot see, nonnegativity of
$`I_u(T)`, from pointwise nonnegativity of the slice at $`T`.

:::theorem "parabolic.keller_segel_virial_density_right_endpoint" (parent := "parabolic.blowup") (lean := "PDE.Solution.Singularity.FiniteTime.KellerSegel.Virial.right_endpoint_le_horizon_of_density") (uses := "parabolic.keller_segel_virial_right_endpoint")

For a density $`u : \mathbb R^2\to\mathbb R\to\mathbb R`, define its mass and
second moment directly by

$$`
M_u(t)=\int_{\mathbb R^2}u(x,t)\,dx,
\qquad
I_u(t)=\int_{\mathbb R^2}|x|^2u(x,t)\,dx.
`

These are totalized Bochner integrals. The theorem assumes $`T\geq0` and a
finite quadratic moment on every slice in $`[0,T]`; the nonzero conserved
mass certifies integrability of the density slices. If $`u(\cdot,T)` is
pointwise nonnegative, $`M_u(t)=M>8\pi`, and $`I_u` has the required
continuity, differentiability, and virial identity, then

$$`T\le \frac{I_u(0)}{M^2/(2\pi)-4M}.`

Mass conservation and the differentiated virial law are hypotheses.
:::

:::proof "parabolic.keller_segel_virial_density_right_endpoint"
Mass conservation rewrites the differentiated density-level virial identity
as the scalar identity with the fixed mass $`M`. Integrability of the
quadratic moment and pointwise nonnegativity at $`T` imply
$`I_u(T)\geq0` by monotonicity of the integral. The scalar endpoint theorem
then yields the displayed bound.
:::
