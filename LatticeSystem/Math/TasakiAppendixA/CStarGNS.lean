import LatticeSystem.Math.TasakiAppendixA.CStarState
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Tasaki Appendix A.7: the GNS construction (Theorem A.28)

Tasaki's Theorem A.28: every state `ρ` on a C*-algebra `A` can be realized as a *vector state* in a
Hilbert space — the Gelfand–Naimark–Segal (GNS) construction.  Explicitly there is a (separable)
Hilbert space `H_ρ`, a `∗`-representation `π_ρ : A → B(H_ρ)` (`π(αÂ+βB̂)=απ(Â)+βπ(B̂)`,
`π(ÂB̂)=π(Â)π(B̂)`, `π(Â†)=π(Â)†`), and a cyclic vector `Ω_ρ` with

  `ρ(Â) = ⟨Ω_ρ, π_ρ(Â) Ω_ρ⟩`  (eq. (A.7.11)),

and `{π_ρ(Â) Ω_ρ | Â ∈ A}` dense in `H_ρ`.  `(H_ρ, π_ρ, Ω_ρ)` is the GNS triple.

The `∗`-representation is rendered by a `StarAlgHom` `π : A →⋆ₐ[ℂ] (H →L[ℂ] H)` into the bounded
operators on `H`.  `mathlib` already contains the GNS machinery
(`Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean`: `f.GNS`, `gnsStarAlgHom`); the precise
Tasaki packaging (cyclic vector recovering the state plus density) is recorded here as a documented
axiom, consistent with the axiomatize-first treatment of this appendix and dischargeable from that
machinery.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.7, Theorem A.28, eqs. (A.7.8)–(A.7.11), pp. 489–490.
-/

namespace LatticeSystem.Math

open scoped ComplexOrder InnerProductSpace

variable {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]

/-- **Tasaki Theorem A.28 (GNS construction), AXIOM.**  Every state `ρ` on a unital complex
C*-algebra `A` admits a *GNS triple* `(H_ρ, π_ρ, Ω_ρ)`: a Hilbert space `H_ρ`, a `∗`-representation
`π_ρ : A → B(H_ρ)` (a `StarAlgHom` into the bounded operators `H →L[ℂ] H`), and a cyclic vector
`Ω_ρ` with `ρ(Â) = ⟨Ω_ρ, π_ρ(Â) Ω_ρ⟩` for all `Â` (eq. (A.7.11)) and `{π_ρ(Â) Ω_ρ}` dense in `H_ρ`.
Thus every state is a vector state in its GNS space.  Recorded as a documented axiom (the
construction is available in `mathlib`'s `GelfandNaimarkSegal`). -/
axiom gns_construction (ρ : WeakDual ℂ A) (hρ : IsState ρ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Ω : H),
      (∀ a : A, ρ a = ⟪Ω, π a Ω⟫_ℂ) ∧ Dense (Set.range fun a : A => π a Ω)

end LatticeSystem.Math
