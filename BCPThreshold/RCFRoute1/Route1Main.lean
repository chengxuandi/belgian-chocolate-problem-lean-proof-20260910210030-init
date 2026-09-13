/-
Copyright (c) 2026 BCP formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BCP formalization contributors
-/
import BCPThreshold.RCFRoute1.TrueHierarchy

/-!
# E08 route 1: executable compact-semialgebraic infeasibility

The exported implementation is
`BelgianChocolate.Route1.TrueHierarchy.negative N q stage`.

Its soundness and completeness theorems are respectively
`negative_sound` and `negative_complete`.  The existing certified threshold
algorithm is not changed by this module.
-/
