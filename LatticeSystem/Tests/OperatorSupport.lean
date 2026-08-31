import LatticeSystem.Quantum.SpinS.MultiSiteCore

/-!
# Test coverage for the operator-support predicate (`Quantum/SpinS/OperatorSupport.lean`)

Fixtures for the not-yet-written `LatticeSystem/Quantum/SpinS/OperatorSupport.lean`: the support
predicate `SupportedOnS` used by Problem 3.4.a, eq. (3.4.13), to phrase Tasaki's unqualified
"acts only on sites within range `r`" as a genuine site-support condition on the many-body matrix
elements, rather than as a bare commutation hypothesis.

## What each pin guarantees

**Signature pins.** `SupportedOnS` is pinned by its own definition, written out with **both**
conjuncts syntactically (the zero-outside-`S` clause and the off-`S`-agreement/rewrite clause), so a
later drift in either conjunct — e.g. weakening the rewrite clause to only universally-quantified
`σ = σ'` — breaks this pin rather than passing silently. `commute_of_supportedOnS_disjoint`,
`supportedOnS_onSiteS`, and `SupportedOnS.add` are each pinned as the declaration's own statement,
discharged only by the identifier itself.

## Coverage limits

These pins guarantee the *signatures* exist with this exact shape; they say nothing about the
correctness of `commute_of_supportedOnS_disjoint`'s proof beyond type-checking, and nothing about
whether `SupportedOnS` is the right reading of Tasaki's informal "local support" — that reading is
argued in the module doc of `OperatorSupport.lean`, not tested here. The joint satisfiability of
`SupportedOnS` alongside a genuine range-`r` window is exercised separately by fixture F-5 of
`Tests/RangeLocalDoubleCommutatorBound.lean`.
-/

namespace LatticeSystem.Tests.OperatorSupport

open LatticeSystem
open LatticeSystem.Quantum
open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Signature pins -/

/-- **Signature pin (`SupportedOnS`).** `A` is supported on `S` iff (i) every nonzero matrix
element `A σ τ` forces `σ, τ` to agree off `S`, and (ii) the matrix element depends only on the
restrictions of `σ, τ` to `S` (given they already agree off `S`). Both conjuncts are written out
syntactically so a later weakening of either one breaks this pin. -/
example (S : Finset Λ) (A : ManyBodyOpS Λ N) :
    SupportedOnS S A =
      ((∀ σ τ : Λ → Fin (N + 1), A σ τ ≠ 0 → ∀ i ∉ S, σ i = τ i) ∧
        (∀ σ τ σ' τ' : Λ → Fin (N + 1),
          (∀ i ∉ S, σ i = τ i) → (∀ i ∉ S, σ' i = τ' i) →
          (∀ i ∈ S, σ i = σ' i) → (∀ i ∈ S, τ i = τ' i) → A σ τ = A σ' τ')) :=
  rfl

/-- **Signature pin (`commute_of_supportedOnS_disjoint`).** Operators supported on disjoint site
sets commute. -/
example {S T : Finset Λ} {A B : ManyBodyOpS Λ N}
    (hA : SupportedOnS S A) (hB : SupportedOnS T B) (hST : Disjoint S T) :
    Commute A B :=
  commute_of_supportedOnS_disjoint hA hB hST

/-- **Signature pin (`supportedOnS_onSiteS`).** A single-site embedding `onSiteS i A` is supported
on any finset `S` containing `i`. -/
example {S : Finset Λ} {i : Λ} (hi : i ∈ S) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    SupportedOnS S (onSiteS i A : ManyBodyOpS Λ N) :=
  supportedOnS_onSiteS hi A

/-- **Signature pin (`SupportedOnS.add`).** The support predicate is closed under addition on the
*same* site set `S` (dot-notation namespacing under `SupportedOnS`). -/
example {S : Finset Λ} {A B : ManyBodyOpS Λ N}
    (hA : SupportedOnS S A) (hB : SupportedOnS S B) :
    SupportedOnS S (A + B) :=
  SupportedOnS.add hA hB

end LatticeSystem.Tests.OperatorSupport
