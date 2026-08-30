import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuDischarge

/-!
# Test coverage for the Theorem 10.8 capstone assembly and axiom discharge

Pins the API contract of
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebShenQiuDischarge.lean`.

The six helper lemmas of that file are `private` by construction, so they cannot be referenced by
name from here and are **not** pinned individually; their correctness is exercised only through
the one public declaration below.

1. **CAP** `theorem_10_8_lieb_shen_qiu_superconductivity` — the capstone,
   **statement-identity pin**: the elaborated type, as reported by `lake env lean` on
   `#check @theorem_10_8_lieb_shen_qiu_superconductivity`, is restated here in
   full so that a future refactor of the capstone's proof cannot silently reorder/add/drop a
   binder or a conjunct without breaking this pin (the same discipline as the `INV` pin of
   `Tests/LiebShenQiuShibaBridge.lean`).

This file **fails to elaborate** unless `LiebShenQiuDischarge.lean` is wired into
`LatticeSystem/Fermion/JordanWigner.lean` (build root) and its capstone theorem carries exactly
the pinned type below.

**Not covered here** (not independently testable from this file):
* an "instantiation smoke test" at `N = 1`, `A = {0}`, `Ne = 2` — fabricating a
  placeholder `hGS : IsUniqueGroundStateOn ... E φ` witness without `sorry` (repo policy) requires
  actually producing a ground state, which duplicates Theorem 10.2/10.4's own tests; the capstone
  is exercised end-to-end instead by its own proof body.
* the "degenerate-branch witness" (`liebShenQiuPairLowerBound A Ne = 0` when
  `A.card = N + 1 ∧ Ne = 2 * (N + 1)`) is a fact about the `liebShenQiuPairLowerBound`
  definition alone and is independent of the discharge file, so it guards nothing here.
* helper sanity for `liebShenQiu_spinPlusMinus_expectation_eq` at `N = 0`, which is `private`
  and hence unreachable from this file.
-/

namespace LatticeSystem.Tests.LiebShenQiuDischarge

open LatticeSystem.Fermion LatticeSystem.Quantum LatticeSystem.Math Matrix

/-- Pins **CAP**: the elaborated statement of `theorem_10_8_lieb_shen_qiu_superconductivity` must
be *byte-for-byte* the type restated below, so that reordering, adding or dropping any binder or
conjunct breaks this pin. -/
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
