import LatticeSystem.Quantum.SpinS.OperatorSupport

/-!
# Signature pin: the support / commutant bridge for `ManyBodyOpS`

Repository-internal generic lemma, **not** a Tasaki result and carrying no book citation. It is the
finite-dimensional commutation theorem for tensor products, `(1 ⊗ M_m)' = M_n ⊗ 1`, specialised to
`ManyBodyOpS`: the two-clause support predicate `SupportedOnS`
(`Quantum/SpinS/OperatorSupport.lean`) coincides with the commutant-of-off-support-on-site-algebra
reading of "acts only on `S`". That commutant reading is what the §4.2.2 local-decay stack
(`Quantum/SpinS/AndersonTowerLocalDecay.lean`) consumes, holding its support hypotheses in terms of
`SupportedOnS` and passing through this equivalence.

The pin spells the right-hand side out because the theorem does; the reason is recorded in that
theorem's doc comment (`supportedOnS_iff_commute_onSiteS`,
`Quantum/SpinS/OperatorSupport.lean`). Spelling the formula out is what gives the pin its content:
the two sides are not definitionally equal, so `Iff.rfl` does not close the goal and it is the
theorem that does.

The pin holds the hypothesis set and the shape of the conclusion of
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

end LatticeSystem.Tests.SupportCommutantBridgePin
