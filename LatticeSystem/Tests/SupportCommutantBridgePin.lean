import LatticeSystem.Quantum.SpinS.OperatorSupport

/-!
# Signature pin (Red): the support / commutant bridge (issue #5405, PR-1)

Repository-internal generic lemma, **not** a Tasaki result and carrying no book citation
(`.self-local/docs/support-commutant-bridge-5405-math.md` §0, §7). It is the finite-dimensional
commutation theorem for tensor products, `(1 ⊗ M_m)' = M_n ⊗ 1`, specialised to `ManyBodyOpS`: the
two-clause support predicate `SupportedOnS` (`Quantum/SpinS/OperatorSupport.lean:55-59`) coincides
with the commutant-of-off-support-on-site-algebra reading used elsewhere in the library as
`SupportedOn` (`Quantum/SpinS/AndersonTowerLocalDecay.lean:42-43`). The right-hand side is written
out here rather than referring to `SupportedOn` because that predicate lives in a strictly
downstream module that `OperatorSupport.lean` does not import.

This pin states the target theorem `supportedOnS_iff_commute_onSiteS` verbatim, before it exists,
so that PR-1 is a genuine Red: the file fails to build today because the identifier is unknown, and
a later change to the statement (hypothesis set, conclusion shape, or binder order) will break this
pin again once the identifier is introduced.

Reference: no textbook citation (repository-internal lemma; see module doc above).
-/

namespace LatticeSystem.Tests.SupportCommutantBridgePin

open Matrix LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Signature pin (Red): `supportedOnS_iff_commute_onSiteS` -/

/-- **Signature pin (Red).** `A` is supported on `S` iff it commutes with every on-site operator
located at a site off `S`. The typeclass hypotheses are exactly `[Fintype Λ] [DecidableEq Λ]`
(forced by the right-hand side alone; no `1 ≤ N`, no `S.Nonempty`, no `Nonempty Λ`). -/
example {S : Finset Λ} {A : ManyBodyOpS Λ N} :
    SupportedOnS S A ↔
      ∀ z ∉ S, ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute A (onSiteS z B) :=
  supportedOnS_iff_commute_onSiteS

end LatticeSystem.Tests.SupportCommutantBridgePin
