import LatticeSystem.Quantum.SpinS.RingReflectionPositivity
import LatticeSystem.Quantum.SpinS.OperatorSupport

/-!
# Signature pin: the left-half ring locality bridge

`Quantum/SpinS/RingReflectionPositivity.lean` states the left-half locality predicate
`SupportedOnLeftS n N A` inline, through the site conditions `n ≤ (i : ℕ)` / `(i : ℕ) < n` on
`Fin (2 * n)`, rather than through the generic support predicate `SupportedOnS`
(`Quantum/SpinS/OperatorSupport.lean`). This file pins the bridge
`supportedOnLeftS_iff_supportedOnS`, which identifies `SupportedOnLeftS n N A` with
`SupportedOnS S A` at the left-half site set `S := Finset.univ.filter fun i => (i : ℕ) < n`.

The signature pin discriminates the site set: swapping the filter to the right half
(`n ≤ (i : ℕ)`), an off-by-one bound (`(i : ℕ) < n + 1`), or an unrelated distance/condition
each fail to elaborate against the named bridge, since the bridge is stated at exactly this
filter.

The unfolding pin spells out both clauses of `SupportedOnLeftS` verbatim rather than naming the
`def`, so the fixture also breaks if the *definition* of `SupportedOnLeftS` drifts, not merely if
the bridge's statement does: dropping the second (basis-independence) conjunct, or swapping the
`σ`/`σ'` roles inside it, each stop the pinned proposition from being defeq to
`SupportedOnLeftS n N A`, so the term no longer type-checks.

Binder order is **not** held by either pin: `n`, `N`, `A` are implicit and solved by unification
against the expected type, and any instance-implicit arguments discharged by synthesis are not
held either.

Reference: repository-internal lemma (no direct textbook citation); the ring-reflection-positivity
layer it serves formalizes Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st
ed., Springer, 2020), §4.1, Theorem 4.2.
-/

namespace LatticeSystem.Tests.LeftHalfSupportPin

open LatticeSystem.Quantum

/-! ## Signature pin: `SupportedOnLeftS` is `SupportedOnS` at the left-half filter -/

/-- **Signature pin.** The left-half locality predicate is support on the left-half site set. -/
example {n N : ℕ} {A : ManyBodyOpS (Fin (2 * n)) N} :
    SupportedOnLeftS n N A ↔
      SupportedOnS (Finset.univ.filter fun i : Fin (2 * n) => (i : ℕ) < n) A :=
  supportedOnLeftS_iff_supportedOnS

/-! ## Unfolding pin: `SupportedOnLeftS`'s two clauses, written out -/

/-- **Unfolding pin.** `SupportedOnLeftS`'s two clauses, spelled out rather than named, held
equivalent to support on the left-half site set. -/
example {n N : ℕ} {A : ManyBodyOpS (Fin (2 * n)) N} :
    ((∀ σ τ : Fin (2 * n) → Fin (N + 1), A σ τ ≠ 0 →
        ∀ i : Fin (2 * n), n ≤ (i : ℕ) → σ i = τ i)
      ∧ (∀ σ τ σ' τ' : Fin (2 * n) → Fin (N + 1),
          (∀ i : Fin (2 * n), n ≤ (i : ℕ) → σ i = τ i) →
          (∀ i : Fin (2 * n), n ≤ (i : ℕ) → σ' i = τ' i) →
          (∀ i : Fin (2 * n), (i : ℕ) < n → σ i = σ' i) →
          (∀ i : Fin (2 * n), (i : ℕ) < n → τ i = τ' i) → A σ τ = A σ' τ'))
      ↔ SupportedOnS (Finset.univ.filter fun i : Fin (2 * n) => (i : ℕ) < n) A :=
  supportedOnLeftS_iff_supportedOnS

end LatticeSystem.Tests.LeftHalfSupportPin
