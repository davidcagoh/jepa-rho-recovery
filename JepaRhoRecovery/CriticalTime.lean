/-
# JepaRhoRecovery.CriticalTime — DELETED Phase 3′-B, session 99.

Paper-1 critical-time machinery (`hittingTime`, `bernoulli_laurent_bound`,
`actual_critical_time_signed`, `purified_*`) plus the 4 supporting axioms
(`bernoulli_exact_solution_exists`, `bernoulli_gronwall_sandwich`,
`bernoulli_exact_laurent`, `purified_laurent_bound`) were deleted in
session 99 as part of the Saxe reimagine. They only supported the
inverted-form Path-C wrapper `signed_recovery_pos_magnitude_jepa`, which
has been re-derived on the Saxe plateau-path in `SignedRecovery.lean`.

This file is preserved as an empty namespace stub so the project structure
documentation continues to round-trip. The umbrella `JepaRhoRecovery.lean`
and `SignedRecovery.lean`'s import list both drop the import.
-/

namespace JepaRhoRecovery

end JepaRhoRecovery
