import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.HopConfig

/-!
# Span of the one-hole hard-core sector by the basis states

This file continues the Tasaki §11.2 Nagaoka-ferromagnetism infrastructure.
It formalizes the completeness statement of footnote 8 / eq. (11.2.3)
(1st edition, p. 382): the one-hole hard-core sector `H_hc^N`
(`N = |Λ| − 1` electrons, no double occupancy) is spanned by the one-hole
hard-core basis states `|Φ_{x,σ}⟩`.

A one-hole hard-core configuration is a computational basis configuration with
no doubly-occupied site and exactly one empty site (the hole). The core
combinatorial content is the surjectivity of the parametrization
`(x, σ) ↦ hubbardOneHoleConfig N x σ` onto these configurations: every such
configuration has a unique hole `x`, and recording the spin of the singly
occupied sites recovers `σ`. The spanning statement then follows because the
basis states `|Φ_{x,σ}⟩` are exactly the computational basis vectors of the
one-hole hard-core configurations.

Tracked in Issue #4130. References: Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, 1st edition, §11.2, p. 382 (footnote 8) and
eq. (11.2.3).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## One-hole hard-core configurations -/

/-- A computational basis configuration is *one-hole hard-core* when it has no
doubly-occupied site and exactly one empty site (the hole): at every spinful
site at least one orbital is empty, and there is a unique site whose two
orbitals are both empty. -/
def IsOneHoleHardcoreConfig (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : Prop :=
  (∀ i : Fin (N + 1), c (spinfulIndex N i 0) = 0 ∨ c (spinfulIndex N i 1) = 0) ∧
    ∃! i : Fin (N + 1),
      c (spinfulIndex N i 0) = 0 ∧ c (spinfulIndex N i 1) = 0

/-- A `Fin 2` value that is not `1` is `0`. -/
private theorem fin_two_eq_zero_of_ne_one {v : Fin 2} (h : v ≠ 1) : v = 0 := by
  have h2 := v.isLt
  exact Fin.ext (by have : v.val ≠ 1 := fun hv => h (Fin.ext hv); omega)

/-! ## The parametrized configurations are exactly the one-hole hard-core ones -/

/-- Each parametrized configuration `hubbardOneHoleConfig N x σ` is one-hole
hard-core, with hole `x`. -/
theorem hubbardOneHoleConfig_isOneHoleHardcore
    (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) :
    IsOneHoleHardcoreConfig N (hubbardOneHoleConfig N x σ) := by
  constructor
  · -- no double occupancy
    intro i
    by_cases hix : i.val = x.val
    · left; rw [hubbardOneHoleConfig_apply_up, if_pos hix]
    · by_cases hσ : σ i
      · right; rw [hubbardOneHoleConfig_apply_down, if_neg hix, if_pos hσ]
      · left; rw [hubbardOneHoleConfig_apply_up, if_neg hix, if_neg hσ]
  · -- unique hole at x
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · rw [hubbardOneHoleConfig_apply_up, if_pos rfl]
    · rw [hubbardOneHoleConfig_apply_down, if_pos rfl]
    · intro j ⟨hju, hjd⟩
      by_contra hjx
      have hjx' : j.val ≠ x.val := fun h => hjx (Fin.ext h)
      by_cases hσ : σ j
      · rw [hubbardOneHoleConfig_apply_up, if_neg hjx', if_pos hσ] at hju
        exact absurd hju (by decide)
      · rw [hubbardOneHoleConfig_apply_down, if_neg hjx', if_neg hσ] at hjd
        exact absurd hjd (by decide)

/-- Surjectivity of the parametrization: every one-hole hard-core
configuration equals `hubbardOneHoleConfig N x σ` for some hole `x` and spin
configuration `σ`. -/
theorem exists_eq_hubbardOneHoleConfig_of_isOneHoleHardcore
    (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) (hc : IsOneHoleHardcoreConfig N c) :
    ∃ (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool),
      c = hubbardOneHoleConfig N x σ := by
  obtain ⟨hnd, x, hx_hole, hx_uniq⟩ := hc
  refine ⟨x, fun i => decide (c (spinfulIndex N i 0) = 1), ?_⟩
  funext k
  obtain ⟨i, s, rfl⟩ := exists_spinfulIndex N k
  by_cases hs : s = 0
  · -- up orbital
    subst hs
    rw [hubbardOneHoleConfig_apply_up]
    by_cases hix : i = x
    · subst hix; rw [if_pos rfl]; exact hx_hole.1
    · rw [if_neg (fun h => hix (Fin.ext h))]
      simp only [decide_eq_true_eq]
      by_cases hcu : c (spinfulIndex N i 0) = 1
      · rw [if_pos hcu]; exact hcu
      · rw [if_neg hcu]; exact fin_two_eq_zero_of_ne_one hcu
  · -- down orbital
    obtain rfl : s = 1 := fin_two_ne_zero hs
    rw [hubbardOneHoleConfig_apply_down]
    by_cases hix : i = x
    · subst hix; rw [if_pos rfl]; exact hx_hole.2
    · have hnothole : ¬ (c (spinfulIndex N i 0) = 0 ∧ c (spinfulIndex N i 1) = 0) :=
        fun hboth => hix (hx_uniq i hboth)
      rw [if_neg (fun h => hix (Fin.ext h))]
      simp only [decide_eq_true_eq]
      by_cases hcu : c (spinfulIndex N i 0) = 1
      · rw [if_pos hcu]
        rcases hnd i with h | h
        · rw [h] at hcu; exact absurd hcu (by decide)
        · exact h
      · rw [if_neg hcu]
        have hup0 : c (spinfulIndex N i 0) = 0 := fin_two_eq_zero_of_ne_one hcu
        exact fin_two_ne_zero (fun hd => hnothole ⟨hup0, hd⟩)

/-! ## The one-hole hard-core sector and its spanning set -/

/-- The one-hole hard-core sector `H_hc^N`: the subspace spanned by the
computational basis vectors of the one-hole hard-core configurations (Tasaki
§11.2, footnote 8, p. 382). -/
noncomputable def hubbardOneHoleHardcoreSector (N : ℕ) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Submodule.span ℂ
    {ψ | ∃ c, IsOneHoleHardcoreConfig N c ∧ ψ = basisVec c}

/-- The basis states `|Φ_{x,σ}⟩` are exactly the computational basis vectors of
the one-hole hard-core configurations: the generating set of
`hubbardOneHoleHardcoreSector` equals the range of the basis states. -/
theorem oneHoleHardcoreConfig_basisVec_eq_range_basisState (N : ℕ) :
    {ψ | ∃ c, IsOneHoleHardcoreConfig N c ∧ ψ = basisVec c} =
      Set.range (fun p : Fin (N + 1) × (Fin (N + 1) → Bool) =>
        hubbardHardcoreBasisState N p.1 p.2) := by
  ext ψ
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨x, σ, rfl⟩ := exists_eq_hubbardOneHoleConfig_of_isOneHoleHardcore N c hc
    exact ⟨(x, σ), rfl⟩
  · rintro ⟨⟨x, σ⟩, rfl⟩
    exact ⟨hubbardOneHoleConfig N x σ,
      hubbardOneHoleConfig_isOneHoleHardcore N x σ, rfl⟩

/-- Tasaki §11.2 footnote 8 (p. 382): the one-hole hard-core sector is spanned
by the basis states `|Φ_{x,σ}⟩`. -/
theorem hubbardOneHoleHardcoreSector_eq_span_basisState (N : ℕ) :
    hubbardOneHoleHardcoreSector N =
      Submodule.span ℂ (Set.range (fun p : Fin (N + 1) × (Fin (N + 1) → Bool) =>
        hubbardHardcoreBasisState N p.1 p.2)) := by
  unfold hubbardOneHoleHardcoreSector
  rw [oneHoleHardcoreConfig_basisVec_eq_range_basisState]

/-- Every one-hole hard-core basis state lies in the one-hole hard-core
sector. -/
theorem hubbardHardcoreBasisState_mem_sector
    (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) :
    hubbardHardcoreBasisState N x σ ∈ hubbardOneHoleHardcoreSector N :=
  Submodule.subset_span ⟨hubbardOneHoleConfig N x σ,
    hubbardOneHoleConfig_isOneHoleHardcore N x σ, rfl⟩

end LatticeSystem.Fermion
