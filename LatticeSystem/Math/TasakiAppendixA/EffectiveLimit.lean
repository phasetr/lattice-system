import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Algebra.Order.Field

/-!
# Tasaki Appendix A.2.3: the strong-coupling effective Hamiltonian (Theorem A.12)

Tasaki's Theorem A.12, "widely used in the physics literature" (and used in §5.1 and §11.2,
and the basis of the §11.5 metallic-ferromagnetism limit): for a Hamiltonian
`Ĥ_v = Ĥ₀ + v V̂` with `Ĥ₀` self-adjoint, `V̂ ≥ 0`, and a parameter `v ≥ 0`, the eigenstates
whose energy stays finite as `v ↑ ∞` are governed by the *effective Schrödinger equation*
`P̂₀ Ĥ₀ |Φ⟩ = E |Φ⟩` on the subspace `H₀ = { Φ : V̂ Φ = 0 }` (`P̂₀` the orthogonal projection
onto `H₀`).

We state it for finite complex matrices without an explicit projection matrix, in the
non-vacuous "finite-energy ⇒ effective" direction: if a family `Φ_v` of `Ĥ_v`-eigenstates
converges as `v ↑ ∞` to a nonzero `Φ` with energy converging to a finite `E`, then `Φ ∈ H₀`
(`V̂ Φ = 0`) and `Φ` solves the effective equation `P̂₀ Ĥ₀ Φ = E Φ`, rendered by its weak
(variational) form `⟨ψ | Ĥ₀ | Φ⟩ = E ⟨ψ | Φ⟩` for every `ψ ∈ H₀` (equivalently
`P̂₀(Ĥ₀ Φ − E Φ) = 0`).  This rests on a continuity/limit argument (Theorem A.12's proof) and
is recorded as a documented axiom; it underlies the §11.5 effective-theory constructions
(`ttDKernel` / `ttEffectiveHamiltonian`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.3, Theorem A.12, p. 470.
-/

namespace LatticeSystem.Math

open Matrix Filter Topology
open scoped ComplexOrder

/-- **Tasaki Theorem A.12 (strong-coupling effective Hamiltonian), AXIOM.**  For
`Ĥ_v = Ĥ₀ + v V̂` with `Ĥ₀` Hermitian and `V̂` positive-semidefinite, the eigenstates whose
energy stays finite as `v ↑ ∞` are governed by the effective Schrödinger equation
`P̂₀ Ĥ₀ |Φ⟩ = E |Φ⟩` on `H₀ = ker V̂`.  Concretely (the "finite-energy ⇒ effective" direction,
which is non-vacuous): if `Φ_v` is a family of `Ĥ_v`-eigenstates with eigenvalue `E_v`, and as
`v ↑ ∞` the states converge to a nonzero `Φ` and the energies to a finite `E`, then the limit
state lies in `H₀` (`V̂ Φ = 0`) and solves the effective equation in weak form,
`⟨ψ|Ĥ₀|Φ⟩ = E ⟨ψ|Φ⟩` for every `ψ ∈ H₀` (i.e. `P̂₀ Ĥ₀ Φ = E Φ`).  Recorded as a documented
axiom (continuity/limit argument); underlies the §11.5 effective-theory limits. -/
axiom effectiveHamiltonian_strongCoupling_limit {n : Type*} [Fintype n]
    (H0 V : Matrix n n ℂ) (hH0 : H0.IsHermitian) (hV : V.PosSemidef)
    (Φv : ℝ → (n → ℂ)) (Ev : ℝ → ℝ) (Φ : n → ℂ) (E : ℝ)
    (heig : ∀ v : ℝ, 0 ≤ v → (H0 + (v : ℂ) • V).mulVec (Φv v) = (Ev v : ℂ) • (Φv v))
    (hΦlim : Tendsto Φv atTop (𝓝 Φ)) (hElim : Tendsto Ev atTop (𝓝 E)) (hΦ : Φ ≠ 0) :
    V.mulVec Φ = 0 ∧
      ∀ ψ : n → ℂ, V.mulVec ψ = 0 → star ψ ⬝ᵥ H0.mulVec Φ = (E : ℂ) * (star ψ ⬝ᵥ Φ)

end LatticeSystem.Math
