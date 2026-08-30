/-
Locality of the order-operator double commutator
(Tasaki §3.4, eqs. (3.4.9)-(3.4.11), general theory of low-lying states and SSB).

For a Hamiltonian `Ĥ = Σ_{b∈B} ĥ_b` whose terms act nontrivially only inside a window `W b`, and an
order operator `Ô = Σ_{x∈Λ} ô_x` built from mutually commuting single-site operators, the
commutator `[Ĥ, Ô]` and the double commutator `[Ô, [Ĥ, Ô]]` collapse onto the windows, and the
resulting finitely many terms are bounded one by one by the commutator operator-norm inequality.
This yields the bound `⟨Φ|[Ô,[Ĥ,Ô]]|Φ⟩ ≤ ‖[Ô,[Ĥ,Ô]]‖ ≤ 16 d h₀ o₀² L^d` on a normalized state,
which is the numerator estimate feeding the Horsch-von der Linden variational argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, eqs. (3.4.9)-(3.4.11), pp. 66-67; operator-norm properties (A.2.5)/(A.2.6), p. 463.
-/
import LatticeSystem.Math.CommutatorSum
import LatticeSystem.Quantum.SpinS.ExpectationNormBound

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Tasaki eq. (3.4.9), p. 66** — the commutator of a windowed Hamiltonian with the order
operator collapses onto the windows:
`[Σ_{b∈B} ĥ_b, Σ_{x∈Λ} ô_x] = Σ_{b∈B} Σ_{z∈W b} [ĥ_b, ô_z]`.
The hypothesis `hW` is the Lean content of "`ĥ_b` acts nontrivially only on the sites of `W b`":
it commutes with every `ô_z` seated outside `W b`. -/
theorem commutator_orderSum_eq_windowSum {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W : ι → Finset Λ)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z)) :
    (∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b)
      = ∑ b ∈ B, ∑ z ∈ W b, (hb b * o z - o z * hb b) := by
  rw [commutator_sum_left B (∑ x : Λ, o x) hb]
  refine Finset.sum_congr rfl fun b hbB => ?_
  rw [commutator_sum_right Finset.univ (hb b) o]
  refine (Finset.sum_subset (Finset.subset_univ (W b)) fun z _ hz => ?_).symm
  exact sub_eq_zero.mpr (hW b hbB z hz).eq

end LatticeSystem.Quantum
