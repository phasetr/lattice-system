import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight

/-!
# Tasaki §2.5 Theorem 2.3 — Marshall–Lieb–Mattis, general spin-S, `|A| ≠ |¬A|`

This file states the final form of Tasaki §2.5 Theorem 2.3 (p. 42):

> Let `(Λ, B)` be a connected bipartite lattice with `|A| ≥ 1` and
> `|B| ≥ 1`. Then the ground states have total spin
>   `S_tot = ||A| − |B|| · S`,
> and are `2 S_tot + 1` fold degenerate. The ground states are
> expanded as in (2.5.4) with the restriction `σ = 0` replaced by
> `σ = M`, where `M = −S_tot, …, S_tot − 1, S_tot`.

The statement is encoded as a `Prop`-valued definition
`tasaki_2_5_theorem_2_3`. The actual proof reuses the sector-level
Theorem 2.2 result
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
applied independently to each magnetization sector
`M ∈ {|V|·N/2 − S_tot, …, |V|·N/2 + S_tot}` in `magSumS` units
(centered units: `m = M − |V|·N/2 ∈ {−S_tot, …, S_tot}`).

Sketch of proof per Tasaki: "essentially a straightforward
modification of that of Theorem 2.2" — the Marshall sign + PF +
toy-Hamiltonian argument carries through with `H_M` replacing `H_0`,
yielding `2 S_tot + 1` sector-unique ground states sharing the same
energy `μ`. The degeneracy is determined by Theorem A.16 (p. 473).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.

Tracked in Issue #412 (Tasaki §2.5: Marshall–Lieb–Mattis theorem).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 predicted total-spin magnitude**
`S_tot = ||A| − |¬A|| · (N/2)` (the real-valued half-integer
prediction). Equivalent to `‖bipartiteImbalanceWeight A N‖`. -/
noncomputable def tasaki23PredictedTotalSpin (A : V → Bool) (N : ℕ) : ℝ :=
  |((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) -
    ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ)| *
    ((N : ℝ) / 2)

/-- **Tasaki §2.5 Theorem 2.3 predicted spectral degeneracy**
`2 S_tot + 1 = ||A| − |¬A|| · N + 1` (integer-valued). -/
def tasaki23PredictedDegeneracy (A : V → Bool) (N : ℕ) : ℕ :=
  (Int.natAbs (((Finset.univ.filter (fun x : V => A x = true)).card : ℤ) -
    ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℤ))) * N + 1

/-- **Tasaki §2.5 Theorem 2.3 admissible magnetization sectors**:
the set of `magSumS` values `M` whose centered magnetization
`m = M − |V|·N/2` satisfies `m ∈ {−S_tot, …, S_tot}`. In `magSumS`
(non-negative integer) units this is the closed integer interval
`[min(|A|, |¬A|) · N, max(|A|, |¬A|) · N]`, of cardinality
`2 S_tot + 1 = ||A| − |¬A|| · N + 1`. -/
def tasaki23GroundStateSectors (A : V → Bool) (N : ℕ) : Finset ℕ :=
  let cA := (Finset.univ.filter (fun x : V => A x = true)).card
  let cB := (Finset.univ.filter (fun x : V => (! A x) = true)).card
  Finset.Icc (min cA cB * N) (max cA cB * N)

/-- **Tasaki §2.5 Theorem 2.3 (Marshall–Lieb–Mattis general spin-S), final
statement** as a `Prop`.

For a connected bipartite spin-`S` antiferromagnetic Heisenberg system
(encoded by sublattice indicator `A : V → Bool` and positive coupling
`J` on the bipartite complete graph `bipartiteCompleteGraphOf A`),
there exists a common ground-state energy `μ` such that:

- (existence) for every admissible magnetization sector `M ∈
  tasaki23GroundStateSectors A N` the spin-`S` Heisenberg Hamiltonian
  has an eigenvector of eigenvalue `μ` supported on sector `M` with
  the Marshall-dressed expansion (2.5.4);
- (sector uniqueness) within each admissible sector the `μ`-eigenvector
  is unique up to positive scalar;
- (degeneracy) the multiplicity of `μ` equals
  `tasaki23PredictedDegeneracy A N = 2 · S_tot + 1`;
- (minimality) no eigenvalue of the Heisenberg Hamiltonian is strictly
  less than `μ`.

The statement bundles existence + uniqueness across all admissible
sectors into a single `Prop`. The proof (per Tasaki) iterates the
Theorem 2.2 sector argument over `tasaki23GroundStateSectors A N`. -/
def tasaki_2_5_theorem_2_3
    (A : V → Bool) (N : ℕ) (J : V → V → ℂ) : Prop :=
  -- Hypotheses (analogous to Theorem 2.2's hypothesis bundle).
  (∀ x y, (J x y).im = 0) →
  (∀ x y, J x y = J y x) →
  (∀ x y, 0 ≤ (J x y).re) →
  (∀ x y, A x = A y → J x y = 0) →
  (∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re) →
  (1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card) →
  (1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) →
  -- Conclusion: existence of a common GS energy μ realised on every
  -- admissible sector, with sector-uniqueness, and minimality globally.
  ∃ μ : ℝ,
    -- Existence on every admissible sector.
    (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      ∃ Ψ : (V → Fin (N + 1)) → ℂ,
        Ψ ≠ 0 ∧
        (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ ∧
        (∀ σ, magSumS σ ≠ M → Ψ σ = 0)) ∧
    -- Global minimality of μ.
    (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
      Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
      μ ≤ μ')

end LatticeSystem.Quantum
