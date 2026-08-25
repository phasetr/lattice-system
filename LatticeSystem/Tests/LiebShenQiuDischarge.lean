import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuDischarge

/-!
# Test coverage for the Theorem 10.8 capstone assembly and axiom discharge (PR-5)

Pins the API contract of PR-5 of the Theorem 10.8 discharge, design report
`.self-local/docs/theorem-10-8-pr5-design.md` §2 "New file `LiebShenQiuDischarge.lean`", against
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebShenQiuDischarge.lean`.

The design's 6 helper lemmas (items 1–6, design §2) are `private` to that file by construction
(design §2 header: "6 `private` + 1 public capstone"), so they cannot be referenced by name from
this file and are **not** pinned here individually; their correctness is exercised only through the
one public declaration below.

1. **CAP** `theorem_10_8_lieb_shen_qiu_superconductivity` — the capstone (design §2 item 7),
   **statement-identity pin**: the elaborated type is captured verbatim from the current `axiom`
   in `LiebShenQiu.lean` (before its deletion) via
   `lake env lean` on `#check @theorem_10_8_lieb_shen_qiu_superconductivity`, and restated here in
   full so that a future refactor of the capstone's proof cannot silently reorder/add/drop a
   binder or a conjunct without breaking this pin (design §3 step 6, the PR-2 `INV`-pin
   precedent, `Tests/LiebShenQiuShibaBridge.lean` `INV`).

This file **fails to elaborate** until `LiebShenQiuDischarge.lean` exists, is wired into
`LatticeSystem/Fermion/JordanWigner.lean` (build root), and its capstone theorem carries exactly
the pinned type below (TDD Red for the whole PR-5 arc: design §3, §7 "Statement pin").

**Not covered here** (design §7, not independently testable from this file):
* the "instantiation smoke test" at `N = 1`, `A = {0}`, `Ne = 2` is omitted — fabricating a
  placeholder `hGS : IsUniqueGroundStateOn ... E φ` witness without `sorry` (repo policy) requires
  actually producing a ground state, which duplicates Theorem 10.2/10.4's own tests; the capstone
  is exercised end-to-end instead by the eventual proof body itself.
* the "degenerate-branch witness" (`liebShenQiuPairLowerBound A Ne = 0` when
  `A.card = N + 1 ∧ Ne = 2 * (N + 1)`) is a fact about the *existing* `liebShenQiuPairLowerBound`
  definition alone (already provable against `main`, independent of this PR's new file), so it is
  not a Red regression for PR-5 and is left to the design's own verification notes rather than
  duplicated here.
* helper #4 sanity (`liebShenQiu_spinPlusMinus_expectation_eq` at `N = 0`) is `private`
  (design §2 item 4) and hence unreachable from this file.
-/

namespace LatticeSystem.Tests.LiebShenQiuDischarge

open LatticeSystem.Fermion LatticeSystem.Quantum LatticeSystem.Math Matrix

/-- Pins **CAP**: the statement of `theorem_10_8_lieb_shen_qiu_superconductivity` after PR-5's
axiom deletion and re-proof must be *byte-for-byte* the same elaborated type as the `axiom` it
replaces (design §3). The type below is the verbatim `#check` output captured against the `axiom`
in `LiebShenQiu.lean` on this branch, before deletion. -/
example :
    ∀ (N Ne : ℕ) (A : Finset (Fin (N + 1))),
      Even Ne →
        0 < Ne →
          2 * (bipartitionComplement A).card ≤ Ne →
            Ne ≤ 2 * A.card →
              ∀ (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
                (∀ (x y : Fin (N + 1)), T x y = T y x) →
                  HoppingRespectsBipartition A T →
                    (hoppingSupportGraph T).Preconnected →
                      ∀ (U : Fin (N + 1) → ℝ),
                        (∀ (x : Fin (N + 1)), 0 < U x) →
                          ∀ {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)},
                            IsUniqueGroundStateOn
                                (electronNumberSectorEuclidean N Ne)
                                (symmetricAttractiveHubbardHamiltonian N T U) E φ →
                              liebShenQiuPairLowerBound A Ne ≤
                                  (euclideanExpectation
                                      (totalPairCorrelationOperator N) φ).re ∧
                                (euclideanExpectation
                                      (totalPairCorrelationOperator N) φ).im =
                                  0 :=
  theorem_10_8_lieb_shen_qiu_superconductivity

end LatticeSystem.Tests.LiebShenQiuDischarge
