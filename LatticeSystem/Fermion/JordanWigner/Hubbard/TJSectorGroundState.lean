import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorIrreducible
import LatticeSystem.Math.TasakiAppendixA.PerronFrobeniusSymmetric

/-!
# Tasaki 11.5: the unique positive sector ground state via Perron–Frobenius (Prop 11.24 PR-D)

Applying Tasaki Theorem A.18 (`perronFrobenius_real_symmetric`) to the real symmetric sector matrix
`M = tJEffReMatrixOnSector` (whose shift `c·1 − M` is irreducible, PR-C3) yields: `M` has a strictly
**positive eigenvector** `v` at its **lowest eigenvalue** `μ` (the sector ground energy), and that
eigenspace is **at most one-dimensional** (non-degeneracy).  This is the Perron–Frobenius ground
state of the spin-charge-separated t-J sector.

* `Nonempty (TJSpinHalfFillingSector N Ne)` — an explicit witness (the `Ŝ³ = ½` filling with the
  `↑`'s left of the `↓`'s), needed for the `[Nonempty]` hypothesis of A.18;
* `tJEffReMatrixOnSector_perronFrobenius` — the A.18 conclusion for `M`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443; Theorem A.18.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- The number of sites with index `< m` is `m` (for `m ≤ N`). -/
private theorem card_filter_val_lt (m : ℕ) (hm : m < N + 1) :
    (Finset.univ.filter (fun k : Fin (N + 1) => k.val < m)).card = m := by
  have heq : (Finset.univ.filter (fun k : Fin (N + 1) => k.val < m))
      = Finset.Iio (⟨m, hm⟩ : Fin (N + 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
  rw [heq]; simp

/-- **Explicit witness for the `Ŝ³ = ½`, `N̂ = Ne` sector**: `↑` on the first `(Ne+1)/2` sites, `↓`
on the next `(Ne-1)/2`, empty after. -/
private def tJSectorWitness (N Ne : ℕ) : Fin (N + 1) → Fin 3 :=
  fun k => if k.val < (Ne + 1) / 2 then 1 else if k.val < Ne then 2 else 0

/-- The witness lies in the sector (`#↑ = #↓ + 1`, `#↑ + #↓ = Ne`). -/
private theorem tJSectorWitness_mem (N Ne : ℕ) (hNeLt : Ne < N + 1) (hodd : Odd Ne) :
    (Finset.univ.filter (fun k => tJSectorWitness N Ne k = 1)).card
        = (Finset.univ.filter (fun k => tJSectorWitness N Ne k = 2)).card + 1 ∧
      (Finset.univ.filter (fun k => tJSectorWitness N Ne k = 1)).card
        + (Finset.univ.filter (fun k => tJSectorWitness N Ne k = 2)).card = Ne := by
  obtain ⟨t, rfl⟩ := hodd
  have hhalf : (2 * t + 1 + 1) / 2 = t + 1 := by omega
  -- `#↑ = t + 1` (prefix of length `(Ne+1)/2 = t+1`).
  have hup : (Finset.univ.filter (fun k : Fin (N + 1) => tJSectorWitness N (2 * t + 1) k = 1)).card
      = t + 1 := by
    rw [Finset.filter_congr (q := fun k => k.val < t + 1) (fun k _ => by
      simp only [tJSectorWitness, hhalf]
      constructor
      · intro h; by_contra hlt; rw [if_neg hlt] at h; split_ifs at h <;> simp_all
      · intro h; rw [if_pos h])]
    exact card_filter_val_lt (t + 1) (by omega)
  -- `#∅ = N + 1 − Ne` (complement of the length-`Ne` prefix).
  have hempty : (Finset.univ.filter
        (fun k : Fin (N + 1) => tJSectorWitness N (2 * t + 1) k = 0)).card
      = N + 1 - (2 * t + 1) := by
    rw [Finset.filter_congr (q := fun k => ¬ k.val < 2 * t + 1) (fun k _ => by
      simp only [tJSectorWitness, hhalf]
      constructor
      · intro h hlt; split_ifs at h <;> simp_all
      · intro h; rw [if_neg (fun hl => h (by omega)), if_neg h])]
    have hadd := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (N + 1)))) (p := fun k => k.val < 2 * t + 1)
    rw [card_filter_val_lt (2 * t + 1) hNeLt, Finset.card_univ, Fintype.card_fin] at hadd
    omega
  -- `#↓ = t` from the total count.
  have htot := tJ_value_count_total (tJSectorWitness N (2 * t + 1))
  omega

/-- The witness makes the sector nonempty. -/
instance tJSpinHalfFillingSector_nonempty (Ne : ℕ) [Fact (Ne < N + 1)] [Fact (Odd Ne)] :
    Nonempty (TJSpinHalfFillingSector N Ne) :=
  ⟨⟨tJSectorWitness N Ne, tJSectorWitness_mem N Ne (Fact.out) (Fact.out)⟩⟩

/-- **Perron–Frobenius for the t-J sector matrix.**  For `τ, J > 0`, odd `Ne < N + 1`, and a shift
`c` strictly above every diagonal entry, the real symmetric sector matrix `M`
(`tJEffReMatrixOnSector`) has a strictly positive eigenvector at its lowest eigenvalue `μ` (the
sector ground energy), and that
eigenspace is at most one-dimensional — the unique, non-degenerate, positive Perron–Frobenius ground
state of the spin-charge-separated t-J sector. -/
theorem tJEffReMatrixOnSector_perronFrobenius (hpos : 0 < N) (Ne : ℕ) (hNeLt : Ne < N + 1)
    (hodd : Odd Ne) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) (c : ℝ)
    (hc : ∀ q : TJSpinHalfFillingSector N Ne,
        tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q < c) :
    ∃ (μ : ℝ) (v : TJSpinHalfFillingSector N Ne → ℝ), (∀ q, 0 < v q) ∧
      (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J) *ᵥ v = μ • v ∧
      (∀ (lam : ℝ) (w : TJSpinHalfFillingSector N Ne → ℝ), w ≠ 0 →
        (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J) *ᵥ w = lam • w → μ ≤ lam) ∧
      finrank ℝ (End.eigenspace
        (Matrix.toLin' (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J)) μ) ≤ 1 := by
  haveI : Fact (Ne < N + 1) := ⟨hNeLt⟩
  haveI : Fact (Odd Ne) := ⟨hodd⟩
  have hirr : (c • (1 : Matrix _ _ ℝ)
      - tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J).IsIrreducible := by
    have heq : c • (1 : Matrix (TJSpinHalfFillingSector N Ne) (TJSpinHalfFillingSector N Ne) ℝ)
        - tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J
        = tJSectorShifted N Ne (cycleGraph (N + 1)) τ J c := by
      ext q p; simp [tJSectorShifted, Matrix.one_apply]
    rw [heq]
    exact tJSectorShifted_isIrreducible hpos Ne hodd τ J hτ hJ c hc
  exact LatticeSystem.Math.perronFrobenius_real_symmetric
    (tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J)
    (tJEffReMatrixOnSector_isSymm N Ne (cycleGraph (N + 1)) τ J) c hirr

end LatticeSystem.Fermion
