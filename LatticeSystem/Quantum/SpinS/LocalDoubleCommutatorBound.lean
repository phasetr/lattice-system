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

/-- **Tasaki eq. (3.4.10), p. 67** — the double commutator of the order operator with the windowed
Hamiltonian collapses onto the windows on *both* index positions:
`[Ô, [Ĥ, Ô]] = Σ_{b∈B} Σ_{x∈W b} Σ_{z∈W b} [ô_x, [ĥ_b, ô_z]]`.
Beyond the window hypothesis `hW` of eq. (3.4.9) this needs `hoo`, the Lean content of "`ô_x` acts
nontrivially only on the spin at `x`": distinct sites carry commuting order operators, which is what
makes the outer sum collapse onto `W b` as well. -/
theorem doubleCommutator_orderSum_eq_windowSum {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W : ι → Finset Λ)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z)) :
    (∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
        - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b)) * (∑ x : Λ, o x)
      = ∑ b ∈ B, ∑ x ∈ W b, ∑ z ∈ W b,
          (o x * (hb b * o z - o z * hb b) - (hb b * o z - o z * hb b) * o x) := by
  have hinner : ∀ x : Λ,
      o x * (∑ b ∈ B, ∑ z ∈ W b, (hb b * o z - o z * hb b))
          - (∑ b ∈ B, ∑ z ∈ W b, (hb b * o z - o z * hb b)) * o x
        = ∑ b ∈ B, (o x * (∑ z ∈ W b, (hb b * o z - o z * hb b))
            - (∑ z ∈ W b, (hb b * o z - o z * hb b)) * o x) := fun x =>
    commutator_sum_right B (o x) fun b => ∑ z ∈ W b, (hb b * o z - o z * hb b)
  rw [commutator_orderSum_eq_windowSum B hb o W hW,
    commutator_sum_left Finset.univ (∑ b ∈ B, ∑ z ∈ W b, (hb b * o z - o z * hb b)) o]
  simp only [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hbB => ?_
  have hcollapse : ∑ x ∈ W b, (o x * (∑ z ∈ W b, (hb b * o z - o z * hb b))
          - (∑ z ∈ W b, (hb b * o z - o z * hb b)) * o x)
      = ∑ x : Λ, (o x * (∑ z ∈ W b, (hb b * o z - o z * hb b))
          - (∑ z ∈ W b, (hb b * o z - o z * hb b)) * o x) := by
    refine Finset.sum_subset (Finset.subset_univ (W b)) fun x _ hx => ?_
    refine sub_eq_zero.mpr (Commute.sum_right _ _ _ fun z hz => ?_).eq
    have hxz : x ≠ z := by rintro rfl; exact hx hz
    exact ((hW b hbB x hx).symm.mul_right (hoo x z hxz)).sub_right
      ((hoo x z hxz).mul_right (hW b hbB x hx).symm)
  rw [← hcollapse]
  exact Finset.sum_congr rfl fun x _ =>
    commutator_sum_right (W b) (o x) fun z => hb b * o z - o z * hb b

end LatticeSystem.Quantum
