import LatticeSystem.Quantum.SpinS.OperatorSupport

/-!
# Signature pin: the support / commutant bridge for `ManyBodyOpS`

Repository-internal generic lemma, **not** a Tasaki result and carrying no book citation. It is the
finite-dimensional commutation theorem for tensor products, `(1 ⊗ M_m)' = M_n ⊗ 1`, specialised to
`ManyBodyOpS`: the two-clause support predicate `SupportedOnS`
(`Quantum/SpinS/OperatorSupport.lean`) coincides with the commutant-of-off-support-on-site-algebra
reading used elsewhere in the library as `SupportedOn`
(`Quantum/SpinS/AndersonTowerLocalDecay.lean`).

The pin spells the right-hand side out because the theorem does, and the theorem does so for
layering: `OperatorSupport.lean` sits directly on `MultiSiteCore.lean`, whereas naming `SupportedOn`
would pull the whole §4.2.2 Anderson-tower stack carried by `AndersonTowerLocalDecay.lean` into that
base module. Neither module imports the other, even transitively, so this is a layering choice and
not a cycle constraint.

The pin holds the type of `supportedOnS_iff_commute_onSiteS` — hypothesis set, conclusion shape and
binder order — fixed against silent drift: any change to that type stops this fixture elaborating.

Reference: no textbook citation (repository-internal lemma; see
`Quantum/SpinS/OperatorSupport.lean`).
-/

namespace LatticeSystem.Tests.SupportCommutantBridgePin

open Matrix LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Signature pin: `supportedOnS_iff_commute_onSiteS` -/

/-- **Signature pin.** `A` is supported on `S` iff it commutes with every on-site operator
located at a site off `S`. The typeclass hypotheses are exactly `[Fintype Λ] [DecidableEq Λ]`
(forced by the right-hand side alone; no `1 ≤ N`, no `S.Nonempty`, no `Nonempty Λ`). -/
example {S : Finset Λ} {A : ManyBodyOpS Λ N} :
    SupportedOnS S A ↔
      ∀ z ∉ S, ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute A (onSiteS z B) :=
  supportedOnS_iff_commute_onSiteS

end LatticeSystem.Tests.SupportCommutantBridgePin
