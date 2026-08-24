import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiu
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaConjugation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveCorrelation

/-!
# Test coverage for the Theorem 10.8 Shiba Hamiltonian bridge (PR-1)

Pins the API contract of the constant-shift identity and the Shiba conjugation bridge that PR-1
of the Theorem 10.8 discharge (design report `.self-local/docs/theorem-10-8-design.md` §1)
introduces, plus the de-privatization of four `euclideanExpectation` helpers currently `private`
in `LiebRepulsiveCorrelation.lean:111-148`:

1. **B1** `symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul` — the constant-shift
   identity `Ĥ^{attr,sym}(T,U) = Ĥ^{attr}(T + diag(U/2), U) − ((ΣU)/4)•1`.
2. **B2** `shibaSignedUnitary_conj_symmetricRepulsive_eq_symmetricAttractive` — the Hamiltonian
   bridge `Ûᴴ Ĥ^{rep,sym}(T,U) Û = Ĥ^{attr,sym}(T,U)` (composing the existing
   `shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive` with B1, the `¼ΣU` shift cancelling
   exactly).
3. **P1–P4** the four `euclideanExpectation` helpers (`_smul`, `_add`, `_shiba_conj`,
   `_conjTranspose_mul_self`), moved out of `private` scope (design report §1, "Reuse ... they are
   `private` in `LiebRepulsiveCorrelation.lean:111-148`; move them ... and un-private them").

**RED (this PR)**: B1/B2 do not yet exist, and P1–P4 are still `private`, so none of the `example`s
below elaborate. Implementation (including the actual move/un-private of P1–P4, and choosing their
final home module) is out of scope for this PR (TDD Red only).

**Not covered here**: the electron-number/spin-`z` sector transport (`shibaTransport_...`, PR-2)
and the `Ŝ³ φ = 0` extraction (PR-2); the `k₀ → k` tower generalization (PR-3); the pair/ladder
algebra and signed-sum inequality (PR-4); and the capstone assembly (PR-5).
-/

namespace LatticeSystem.Tests.LiebShenQiuShibaBridge

open LatticeSystem.Fermion LatticeSystem.Quantum Matrix
open scoped BigOperators

variable {N : ℕ}

/-- Pins **B1**: the symmetric attractive Hamiltonian is the shifted plain attractive Hamiltonian
minus the constant `(ΣU)/4`. -/
example (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    symmetricAttractiveHubbardHamiltonian N T U
      = attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U
        - ((∑ x : Fin (N + 1), (U x : ℂ)) / 4) • (1 : ManyBodyOp (Fin (2 * N + 2))) :=
  symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul N T U

/-- Pins **B2**, the Hamiltonian bridge: the Shiba conjugation of the symmetric repulsive
Hamiltonian equals the symmetric attractive Hamiltonian exactly (the `¼ΣU` shifts of the two sides
cancel). -/
example {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hsymm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (U : Fin (N + 1) → ℝ) :
    Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * symmetricRepulsiveHubbardHamiltonian N T U
        * shibaSignedUnitary N (shibaSignFn A)
      = symmetricAttractiveHubbardHamiltonian N T U :=
  shibaSignedUnitary_conj_symmetricRepulsive_eq_symmetricAttractive hsymm hbip U

/-- Pins **P1** (de-privatized): the Euclidean expectation is homogeneous in the observable. -/
example (a : ℂ) (O : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (a • O) φ = a * euclideanExpectation O φ :=
  euclideanExpectation_smul a O φ

/-- Pins **P2** (de-privatized): the Euclidean expectation is additive in the observable. -/
example (O₁ O₂ : ManyBodyOp (Fin (2 * N + 2)))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (O₁ + O₂) φ
      = euclideanExpectation O₁ φ + euclideanExpectation O₂ φ :=
  euclideanExpectation_add O₁ O₂ φ

/-- Pins **P3** (de-privatized): Shiba transport of the Euclidean expectation. -/
example (O : ManyBodyOp (Fin (2 * N + 2)))
    (Ush : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ)
    (ψ φattr : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2))
    (hψ : ψ.ofLp = Ush.mulVec φattr.ofLp) :
    euclideanExpectation O ψ
      = euclideanExpectation (Matrix.conjTranspose Ush * O * Ush) φattr :=
  euclideanExpectation_shiba_conj O Ush ψ φattr hψ

/-- Pins **P4** (de-privatized): `⟨v| Aᴴ A |v⟩` is the (nonnegative real) squared norm of `A v`. -/
example (M : ManyBodyOp (Fin (2 * N + 2))) (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (Matrix.conjTranspose M * M) φ
      = ((∑ j, Complex.normSq ((M.mulVec φ.ofLp) j) : ℝ) : ℂ) :=
  euclideanExpectation_conjTranspose_mul_self M φ

end LatticeSystem.Tests.LiebShenQiuShibaBridge
