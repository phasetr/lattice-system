import LatticeSystem.Math.TasakiAppendixA.CStarState

/-!
# Tasaki Appendix A.7: ground states of infinite systems (Definitions A.25, A.27, Theorem A.26)

For a quantum spin system on `ℤᵈ` the Hamiltonian `Ĥ` is not an element of the quasi-local algebra
`A`, but the commutator `[Ĥ, ·]` is a well-defined `∗`-derivation on the local elements.  We model
the dynamics abstractly by a map `δ : A → A` standing for `Â ↦ [Ĥ, Â]`.

* **Definition A.25 (ground state)** — a state `ω` is a *ground state* iff `ω(Â† [Ĥ, Â]) ≥ 0` for
  every local `Â`; in our notation `0 ≤ ω(star a * δ a)` for all `a`.  (The finite-volume reading is
  `⟨Φ_GS| Â† Ĥ Â |Φ_GS⟩ ≥ E_GS ⟨Φ_GS| Â† Â |Φ_GS⟩`: a local perturbation cannot lower the energy.)
* **Theorem A.26 (variational characterization)** — `ω` is a ground state iff for every `L` the
  energy `ω(Ĥ_L)` of the partial Hamiltonian `Ĥ_L = Σ_{x ∈ Λ_L} ĥ_x` is the least among all states
  `ω′` agreeing with `ω` outside `Λ_L` (eq. (A.7.7)).
* **Definition A.27 (nonzero gap)** — a *unique* ground state `ω` has a *nonzero energy gap* iff
  there is `γ > 0` with `ω(Â† [Ĥ, Â]) ≥ γ ω(Â† Â)` for every local `Â` with `ω(Â) = 0`.

Definitions A.25 and A.27 are genuine `def`s; Theorem A.26 (a deep operator-algebraic result,
[Bratteli–Robinson]) is parametrized by the partial-Hamiltonian family `Ĥ_L` and the constraint sets
`C_L` and recorded as a documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.7, Definitions A.25/A.27 and Theorem A.26, eqs. (A.7.5)–(A.7.7), pp. 489.
-/

namespace LatticeSystem.Math

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]

/-- **Tasaki Definition A.25 (ground state).**  With the dynamics `δ : A → A` modelling the
Hamiltonian commutator `Â ↦ [Ĥ, Â]`, a state `ω` is a *ground state* iff `0 ≤ ω(Â† [Ĥ, Â])` for
every `Â`, i.e. `0 ≤ ω (star a * δ a)` for all `a : A`.  A local perturbation cannot lower the
energy. -/
def IsGroundState (ω : WeakDual ℂ A) (δ : A → A) : Prop :=
  ∀ a : A, 0 ≤ ω (star a * δ a)

/-- **Tasaki Definition A.27 (ground state with a nonzero gap).**  A (unique) ground state `ω`, with
dynamics `δ`, has a *nonzero energy gap* iff there is `γ > 0` with `ω(Â† [Ĥ, Â]) ≥ γ ω(Â† Â)` — i.e.
`(γ : ℂ) * ω (star a * a) ≤ ω (star a * δ a)` — for every `Â` with `ω(Â) = 0`. -/
def HasNonzeroGap (ω : WeakDual ℂ A) (δ : A → A) (γ : ℝ) : Prop :=
  0 < γ ∧ ∀ a : A, ω a = 0 → (γ : ℂ) * ω (star a * a) ≤ ω (star a * δ a)

/-- **Tasaki Theorem A.26 (variational characterization of ground states), AXIOM.**  With dynamics
`δ`, partial Hamiltonians `Ĥ_L = HL L` and constraint sets `CL L` of states agreeing with `ω`
outside `Λ_L` (so `ω ∈ CL L ⊆` states), `ω` is a ground state iff for every `L` the energy
`(ω(Ĥ_L)).re` is the least value of `(ω′(Ĥ_L)).re` over `ω′ ∈ CL L` (eq. (A.7.7)).  A ground state
minimizes every partial Hamiltonian.  Recorded as a documented axiom. -/
axiom groundState_variational (ω : WeakDual ℂ A) (δ : A → A) (HL : ℕ → A)
    (CL : ℕ → Set (WeakDual ℂ A)) (hω : ∀ L, ω ∈ CL L) (hCL : ∀ L, CL L ⊆ stateSpace A) :
    IsGroundState ω δ ↔
      ∀ L, IsLeast ((fun φ : WeakDual ℂ A => (φ (HL L)).re) '' CL L) ((ω (HL L)).re)

end LatticeSystem.Math
