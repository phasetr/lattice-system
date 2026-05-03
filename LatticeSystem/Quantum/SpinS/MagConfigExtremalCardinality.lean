import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.MagConfig

/-!
# Cardinality of extremal magnetization sectors for spin-`S`
(Tasaki §2.5 / §2.4 setup)

The two extremal magnetization sectors `M = 0` and `M = |V|·N` are
**1-dimensional**: each contains exactly one configuration — the all-up
or all-down constant configuration respectively. This is the
combinatorial counterpart of the fact that the highest- and
lowest-weight states of the `J_tot = |V|·S` irreducible SU(2)
representation are unique.

These cardinality results are useful for any argument that relies
on uniqueness of the extremal-magnetization configuration (e.g. the
saturated-ferromagnet ground-state argument in
`AllAlignedState.lean`).

Tracked as part of Tasaki §2.5 / §2.4 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The unique element of the M = 0 magnetization sector is the
all-up configuration `allAlignedConfigS V N 0`. -/
theorem magConfigS_zero_eq_allAlignedConfigS
    (τ : magConfigS V N 0) : τ.1 = allAlignedConfigS V N 0 := by
  -- τ.2 : magSumS τ.1 = 0.
  by_contra hne
  have hpos := magSumS_pos_of_ne_allAlignedConfigS_zero hne
  rw [τ.2] at hpos
  exact (Nat.lt_irrefl 0) hpos

/-- The M = 0 magnetization sector has cardinality 1 (containing only
the all-up configuration). -/
theorem magConfigS_card_zero :
    Fintype.card (magConfigS V N 0) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨allAlignedConfigS V N 0, magSumS_allAlignedConfigS_zero⟩, ?_⟩
  intro τ
  exact Subtype.ext (magConfigS_zero_eq_allAlignedConfigS τ)

/-- The unique element of the M = |V|·N magnetization sector is the
all-down configuration `allAlignedConfigS V N (Fin.last N)`. -/
theorem magConfigS_last_eq_allAlignedConfigS
    (τ : magConfigS V N (Fintype.card V * N)) :
    τ.1 = allAlignedConfigS V N (Fin.last N) := by
  by_contra hne
  have hlt := magSumS_lt_card_mul_of_ne_allAlignedConfigS_last hne
  rw [τ.2] at hlt
  exact (Nat.lt_irrefl _) hlt

/-- The M = |V|·N magnetization sector has cardinality 1 (containing
only the all-down configuration). -/
theorem magConfigS_card_last :
    Fintype.card (magConfigS V N (Fintype.card V * N)) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨allAlignedConfigS V N (Fin.last N),
    magSumS_allAlignedConfigS_last⟩, ?_⟩
  intro τ
  exact Subtype.ext (magConfigS_last_eq_allAlignedConfigS τ)

/-- The M = 0 magnetization sector is non-empty. -/
instance magConfigS_zero_instNonempty : Nonempty (magConfigS V N 0) :=
  ⟨⟨allAlignedConfigS V N 0, magSumS_allAlignedConfigS_zero⟩⟩

/-- The M = |V|·N magnetization sector is non-empty. -/
instance magConfigS_last_instNonempty :
    Nonempty (magConfigS V N (Fintype.card V * N)) :=
  ⟨⟨allAlignedConfigS V N (Fin.last N),
    magSumS_allAlignedConfigS_last⟩⟩

end LatticeSystem.Quantum
