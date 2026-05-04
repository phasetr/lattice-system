import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.MarshallLiebMattis.ToyHamiltonian

/-!
# Toy Hamiltonian for the spin-`S` MLM (Tasaki §2.5 Theorem 2.3)

Spin-`S` analog of `Quantum/MarshallLiebMattis/ToyHamiltonian.lean`:
the toy Hamiltonian

  `Ĥ_toy_S := (1/|Λ|) Σ_{x ∈ A, y ∈ B} Ŝ_x · Ŝ_y = (1/|Λ|) Ŝ_A · Ŝ_B`,

a special case of the spin-`S` Heisenberg Hamiltonian with bipartite
coupling. Reuses the spin-independent `bipartiteCoupling A` from the
spin-`1/2` module (`A x ≠ A y` ↦ `1`, else `0`), then defines

  `heisenbergToyHamiltonianS A N := heisenbergHamiltonianS (bipartiteCoupling A) N`.

We omit the `1/|Λ|` normalisation factor (it only affects spectrum
scaling, not eigenvectors).

Establishes:

1. The toy Hamiltonian is Hermitian via
   `heisenbergHamiltonianS_isHermitian_of_real` and the realness of
   `bipartiteCoupling`.

The Casimir identity
`Ĥ_toy_S = (1/(2|Λ|)) ((Ŝ_tot)² − (Ŝ_A)² − (Ŝ_B)²)` (Tasaki §2.5
eq. (2.5.11)) is deferred to a subsequent PR.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 pp. 40–41, eqs. (2.5.10)–(2.5.11).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The spin-`S` MLM toy Hamiltonian (Tasaki §2.5 eq. (2.5.10) without
the `1/|Λ|` factor): the spin-`S` Heisenberg Hamiltonian with the
bipartite coupling. -/
noncomputable def heisenbergToyHamiltonianS (A : Λ → Bool) (N : ℕ) :
    ManyBodyOpS Λ N :=
  heisenbergHamiltonianS (bipartiteCoupling A) N

/-- The spin-`S` toy Hamiltonian is Hermitian. Real coupling alone
suffices (no symmetry needed) since `Ŝ_x · Ŝ_y` is Hermitian for
spin-`S` and the doubled sum `Σ_{x,y}` symmetrises `J` automatically. -/
theorem heisenbergToyHamiltonianS_isHermitian (A : Λ → Bool) (N : ℕ) :
    (heisenbergToyHamiltonianS (Λ := Λ) A N).IsHermitian := by
  unfold heisenbergToyHamiltonianS
  refine heisenbergHamiltonianS_isHermitian_of_real ?_ N
  intro x y
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re]
  · rw [Complex.star_def, Complex.conj_im, bipartiteCoupling_im, neg_zero]

end LatticeSystem.Quantum
