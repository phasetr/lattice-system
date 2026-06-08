import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Tasaki Appendix A.6: Wigner's theorem (Theorems A.21, A.22)

Tasaki's Theorem A.21 (the automorphism variant, "often called Wigner's theorem") and Theorem A.22
(the original Wigner theorem on rays / rank-one projections).  Over a finite-dimensional Hilbert
space `H`, identified with `Matrix (Fin D) (Fin D) ℂ` acting on `Fin D → ℂ`:

* **Theorem A.21** — a *linear* `∗`-automorphism `Γ` of `M(H)` (one-to-one, multiplicative,
  `∗`-preserving, ℂ-linear: (A1)–(A4)) is implemented by a unitary, `Γ(Â) = Û† Â Û`
  (eq. (A.6.1)); an *antilinear* `∗`-automorphism ((A4′)) is implemented by an antiunitary, which
  in matrix form is conjugation-by-`Û` composed with entrywise complex conjugation,
  `Γ(Â) = Û† Â̄ Û` (eq. (A.6.2)).  The implementing operator is unique up to a phase.
* **Theorem A.22** — a map `Γ` on the rank-one (orthogonal) projections preserving the transition
  probabilities `Tr[P P′]` is implemented by a unitary or antiunitary `V̂`, `Γ(P) = V̂ P V̂⁻¹`
  (eq. (A.6.10)).

These are deep results (Wigner / Bargmann); per the project's axiomatize-first treatment of the
operator-algebraic appendix, they are recorded as documented axioms (the antilinear/antiunitary case
is encoded via entrywise conjugation `Â.map conj`, avoiding a separate antiunitary primitive).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.6, Theorems A.21–A.22, eqs. (A.6.1)–(A.6.10), pp. 482–484.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **Tasaki Theorem A.21 (Wigner, linear `∗`-automorphism case), AXIOM.**  A map `Γ` on the
operators `M(H) = Matrix D D ℂ` that is one-to-one (A1), multiplicative `Γ(ÂB̂)=Γ(Â)Γ(B̂)` (A2),
`∗`-preserving `Γ(Â†)=Γ(Â)†` (A3), and ℂ-linear (A4) — a linear `∗`-automorphism — is implemented by
a unitary `Û`: `Γ(Â) = Û† Â Û` for all `Â` (eq. (A.6.1)).  `Û` is unique up to a phase.  Documented
axiom. -/
axiom wignerAutomorphism_unitary (Γ : Matrix D D ℂ → Matrix D D ℂ)
    (hinj : Function.Injective Γ) (hmul : ∀ A B, Γ (A * B) = Γ A * Γ B)
    (hstar : ∀ A, Γ Aᴴ = (Γ A)ᴴ)
    (hlin : ∀ (a b : ℂ) (A B), Γ (a • A + b • B) = a • Γ A + b • Γ B) :
    ∃ U : Matrix D D ℂ, U ∈ Matrix.unitaryGroup D ℂ ∧ ∀ A, Γ A = Uᴴ * A * U

/-- **Tasaki Theorem A.21 (Wigner, antilinear `∗`-automorphism case), AXIOM.**  A map `Γ` on
`Matrix D D ℂ` that is one-to-one (A1), multiplicative (A2), `∗`-preserving (A3), and *antilinear*
(A4′, `Γ(aÂ+bB̂)=ā·Γ(Â)+b̄·Γ(B̂)`) — an antilinear `∗`-automorphism — is implemented by an
antiunitary, which in matrix form is conjugation by a unitary `Û` after entrywise complex
conjugation: `Γ(Â) = Û† (Â.map conj) Û`, eq. (A.6.2).  Documented axiom. -/
axiom wignerAutomorphism_antiunitary (Γ : Matrix D D ℂ → Matrix D D ℂ)
    (hinj : Function.Injective Γ) (hmul : ∀ A B, Γ (A * B) = Γ A * Γ B)
    (hstar : ∀ A, Γ Aᴴ = (Γ A)ᴴ)
    (halin : ∀ (a b : ℂ) (A B),
      Γ (a • A + b • B) = (starRingEnd ℂ a) • Γ A + (starRingEnd ℂ b) • Γ B) :
    ∃ U : Matrix D D ℂ, U ∈ Matrix.unitaryGroup D ℂ ∧
      ∀ A, Γ A = Uᴴ * A.map (starRingEnd ℂ) * U

/-- A *rank-one orthogonal projection* on `H = D → ℂ`: a Hermitian idempotent of trace one
(`P† = P`, `P² = P`, `Tr P = 1`).  These are the "rays" `P1` of Wigner's theorem. -/
def IsRankOneProjection (P : Matrix D D ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ P.trace = 1

/-- **Tasaki Theorem A.22 (Wigner's theorem), AXIOM.**  A map `Γ` carrying rank-one projections to
rank-one projections and preserving the transition probabilities `Tr[P P′] = Tr[Γ(P) Γ(P′)]` is
implemented by a unitary or an antiunitary `V̂`: there is a unitary `U` with either `Γ(P) = U P U†`
for all rank-one `P` (unitary case) or `Γ(P) = U P̄ U†` for all rank-one `P` (antiunitary case,
`P̄ = P.map conj`), eq. (A.6.10).  `V̂` is unique up to a phase.  Documented axiom. -/
axiom wignerProjection (Γ : Matrix D D ℂ → Matrix D D ℂ)
    (hmaps : ∀ P, IsRankOneProjection P → IsRankOneProjection (Γ P))
    (htr : ∀ P P', IsRankOneProjection P → IsRankOneProjection P' →
      (Γ P * Γ P').trace = (P * P').trace) :
    ∃ U : Matrix D D ℂ, U ∈ Matrix.unitaryGroup D ℂ ∧
      ((∀ P, IsRankOneProjection P → Γ P = U * P * Uᴴ) ∨
        (∀ P, IsRankOneProjection P → Γ P = U * P.map (starRingEnd ℂ) * Uᴴ))

end LatticeSystem.Math
