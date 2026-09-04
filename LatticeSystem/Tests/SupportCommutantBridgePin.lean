import LatticeSystem.Quantum.SpinS.AndersonTowerLocalDecay
import LatticeSystem.Quantum.SpinS.OperatorSupport

/-!
# Signature pin: the support / commutant bridge for `ManyBodyOpS`

Repository-internal generic lemma, **not** a Tasaki result and carrying no book citation. It is the
finite-dimensional commutation theorem for tensor products, `(1 ⊗ M_m)' = M_n ⊗ 1`, specialised to
`ManyBodyOpS`: the two-clause support predicate `SupportedOnS`
(`Quantum/SpinS/OperatorSupport.lean`) coincides with the commutant-of-off-support-on-site-algebra
reading used elsewhere in the library as `SupportedOn`
(`Quantum/SpinS/AndersonTowerLocalDecay.lean`).

The first pin spells the right-hand side out because the theorem does, and the theorem does so for
layering: `Quantum/SpinS/OperatorSupport.lean` sits directly on `Quantum/SpinS/MultiSiteCore.lean`,
whereas naming `SupportedOn` would pull the whole §4.2.2 Anderson-tower stack carried by
`Quantum/SpinS/AndersonTowerLocalDecay.lean` into that base module. No import relation runs either
way, even transitively, between `Quantum/SpinS/OperatorSupport.lean` and
`Quantum/SpinS/AndersonTowerLocalDecay.lean`, so this is a layering choice and not a cycle
constraint. This file is downstream of both, so it can name the two predicates in one statement and
pin their agreement directly — the second fixture below — which the base module cannot do without
taking that stack on.

The first pin holds the hypothesis set and the shape of the conclusion of
`supportedOnS_iff_commute_onSiteS` fixed against silent drift: acquiring a further hypothesis, or a
change to either side of the equivalence, stops this fixture elaborating — with one exception, so
that instance-implicit arguments are not held: one that instance synthesis discharges from the
ambient `[Fintype Λ]`, `[DecidableEq Λ]` and `N` alone slips through, whereas an explicit hypothesis
and an instance that synthesis cannot supply both break the fixture. Binder order is not held:
`S` and `A` are implicit and unification solves them against the expected type, so permuting them
leaves the fixture elaborating.

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

/-! ## Unfolding pin: the spelled-out commutant is `SupportedOn` -/

/-- **Unfolding pin.** The right-hand side spelled out above is exactly what `SupportedOn`
(`Quantum/SpinS/AndersonTowerLocalDecay.lean`) unfolds to, so a caller holding either support
predicate holds the other. The fixture carries content beyond that unfolding: the two predicates are
not definitionally equal, so `Iff.rfl` does not close this goal and it is the theorem that does; and
it discriminates the right-hand predicate, a clone of `SupportedOn` quantifying over `z ∈ S` in
place of `z ∉ S` failing to typecheck in its place. -/
example {S : Finset Λ} {A : ManyBodyOpS Λ N} : SupportedOnS S A ↔ SupportedOn S A :=
  supportedOnS_iff_commute_onSiteS

end LatticeSystem.Tests.SupportCommutantBridgePin
