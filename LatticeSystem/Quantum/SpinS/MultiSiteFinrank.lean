import LatticeSystem.Quantum.SpinS.MultiSite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Dimension of the multi-site spin-`S` Hilbert space

For a finite vertex set `V` with `|V|` sites, the multi-site
spin-`S` Hilbert space `(V → Fin (N + 1)) → ℂ` has
`Module.finrank ℂ` equal to `(N + 1)^|V|`. This is the standard
quantum-mechanical dimension formula `(2S + 1)^|Λ|` with
`2S + 1 = N + 1` and `|Λ| = |V|`.

Direct application of mathlib's `Module.finrank_fintype_fun_eq_card`
combined with `Fintype.card_fun`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The multi-site spin-`S` Hilbert space has `Module.finrank ℂ
= (N + 1)^|V|`. -/
theorem multiSiteSpinS_finrank :
    Module.finrank ℂ ((V → Fin (N + 1)) → ℂ) = (N + 1) ^ Fintype.card V := by
  rw [Module.finrank_fintype_fun_eq_card]
  rw [Fintype.card_fun, Fintype.card_fin]

end LatticeSystem.Quantum
