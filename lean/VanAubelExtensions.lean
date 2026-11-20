/-
Copyright (c) 2026 mindofcharles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mindofcharles
-/

import VanAubelExtensions.Basic
import VanAubelExtensions.CenterIdentity
import VanAubelExtensions.SquareGeometry
import VanAubelExtensions.Dimension
import VanAubelExtensions.Rigidity
import VanAubelExtensions.MidpointSquare
import VanAubelExtensions.ComplexAffineTransfer
import VanAubelExtensions.ComplexStructureSpace
import VanAubelExtensions.OperatorDefect
import VanAubelExtensions.MixedSigns
import VanAubelExtensions.MixedSignMeasure
import VanAubelExtensions.ExceptionalNormalForms
import VanAubelExtensions.ExceptionalMetric
import VanAubelExtensions.ExceptionalUnitaryClassification
import VanAubelExtensions.ShearNorm
import VanAubelExtensions.ExceptionalNorm
import VanAubelExtensions.Examples

/-!
# Van Aubel identities, defects, rigidity, normal forms, and complex-affine transfer

This is the public umbrella module for the Lean checks corresponding to
`paper/van-aubel-complex-structure-identity.md`,
`paper/van-aubel-edge-operator-realizations-and-rigidity.md`, and the
non-categorical content of
`paper/van-aubel-complex-affine-naturality-and-transfer.md`.

The Lean files are organized by mathematical topic under the
`VanAubelExtensions/` directory. Importing `VanAubelExtensions` preserves the
original public entry point and makes every theorem available.
-/
