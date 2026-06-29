import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockKineticMatrix
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHopAction
import LatticeSystem.Fermion.JordanWigner.HopBasisVec

/-!
# Uniqueness of a single configuration hop (Tasaki §10.2.4)

Layer PR40b toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The
configuration-space connectivity of the up-kinetic matrix
`A = hubbardBlockKineticUpFixedMatrix` rests on the up-hopping operator
`Σ_{p,q} T_{p,q} ĉ†_{p,↑} ĉ_{q,↑}` reaching a target configuration through a **unique**
hop. This file proves that combinatorial uniqueness: from a fixed configuration `u`
(with `u j = 1`, `u i = 0`), the single hop `q → p` reaches `hop u j i` only for
`(p, q) = (i, j)`. This is the term-selection input that collapses the kinetic double
sum to the surviving `(i, j)` entry (`= ±T_{i,j}`) in the next layer.

## Main result

* `hubbardSpinHopConfig_inj_of_hop` — the single hop determines its `(source, target)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- **Uniqueness of the single hop.** If two hops `q → p` and `j → i` from the same
configuration `u` (with `u j = 1`, `u i = 0`) reach the same configuration, then `p = i`
and `q = j`. -/
theorem hubbardSpinHopConfig_inj_of_hop (u : hubbardSpinConfig N) (i j p q : Fin (N + 1))
    (huj : u j = 1) (hui : u i = 0)
    (heq : hubbardSpinHopConfig N u q p = hubbardSpinHopConfig N u j i) :
    p = i ∧ q = j := by
  have hij : i ≠ j := by rintro rfl; rw [hui] at huj; exact absurd huj (by decide)
  -- `p = i`: at `i`, the `j → i` hop reads `1`, but the `q → p` hop reads `0` unless `p = i`.
  have hpi : p = i := by
    by_contra hpne
    have hL : hubbardSpinHopConfig N u q p i = 0 := by
      rw [hubbardSpinHopConfig, Function.update_of_ne (Ne.symm hpne), Function.update_apply]
      split_ifs with hiq
      · rfl
      · exact hui
    have hR : hubbardSpinHopConfig N u j i i = 1 := by
      rw [hubbardSpinHopConfig, Function.update_self]
    rw [heq, hR] at hL; exact absurd hL (by decide)
  -- `q = j`: at `j`, the `j → i` hop reads `0`, but the `q → p` hop reads `1` unless `q = j`.
  refine ⟨hpi, ?_⟩
  by_contra hqne
  have hL : hubbardSpinHopConfig N u q p j = 1 := by
    rw [hubbardSpinHopConfig, Function.update_apply, Function.update_apply]
    split_ifs with hjp hjq
    · rfl
    · exact absurd hjq (Ne.symm hqne)
    · exact huj
  have hR : hubbardSpinHopConfig N u j i j = 0 := by
    rw [hubbardSpinHopConfig, Function.update_of_ne (Ne.symm hij), Function.update_self]
  rw [heq, hR] at hL; exact absurd hL (by decide)

end LatticeSystem.Fermion
