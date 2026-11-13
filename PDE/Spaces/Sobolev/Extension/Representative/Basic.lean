/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.Representatives.Definitions

/-!
# Representative-level Sobolev extensions

`SobolevSpace.Extension.Representative.HasExtension n k p Ω` says that there is a map sending each
`u ∈ W^{k,p}(Ω)`, in the representative model `SobolevSpaceOn`, to an element of
`GlobalSobolevSpace n k p` that agrees with `u` almost everywhere on `Ω`. This is conclusion (i) of
the extension theorem, Evans §5.4, Theorem 1 (stated there for `k = 1`), without the linearity of
the extension, the support condition (ii) and the bound (iii).

Linearity and norm control are carried by `SobolevSpace.Extension.GraphSpace.Operator`;
`SobolevSpace.Extension.GraphSpace.exists_representativeExtensionOperator` derives `HasExtension`
from such an operator.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, p. 268.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

set_option linter.missingDocs true

namespace SobolevSpace

open MeasureTheory Set
open scoped ENNReal

namespace Extension
namespace Representative

/-- A representative-level Sobolev extension exists on `Ω`.

The witness is an extension map together with almost-everywhere agreement on
the original domain. This proposition forgets linearity and boundedness; the graph-space
extension operators keep them. -/
def HasExtension (n k : ℕ) (p : ℝ≥0∞) (Ω : Set (ℝ^n)) : Prop :=
  ∃ extension : SobolevSpaceOn n k p Ω → _root_.SobolevSpace.GlobalSobolevSpace n k p,
    ∀ u : SobolevSpaceOn n k p Ω,
      ∀ᵐ x ∂ domainMeasure n Ω, (extension u).toFun x = u.toFun x

end Representative
end Extension

end SobolevSpace
