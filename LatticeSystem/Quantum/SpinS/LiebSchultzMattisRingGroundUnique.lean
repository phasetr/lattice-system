import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingUniqueness
import LatticeSystem.Quantum.SpinS.StrictHOutsideFerrimagnetic
import LatticeSystem.Quantum.SpinS.ConnectedSectorFinrankLeOne
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLMCore
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLMCoreSectors
import LatticeSystem.Quantum.SpinS.FerrimagneticLROUniversal

/-!
# Tasaki §6.2 Theorem 6.3: ground-state uniqueness of the AFM Heisenberg ring

Building on the ring setup (`LiebSchultzMattisRingUniqueness`), this module proves the
**sublattice balance** of the even ring (the two parity classes have equal cardinality), the
prerequisite for the singleton-ground-sector structure used by the Marshall–Lieb–Mattis
uniqueness machinery toward Theorem 6.3.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, p. 162.
-/

namespace LatticeSystem.Quantum

open Matrix SimpleGraph

/-- **Sublattice balance on the even ring**: the even-index and odd-index sites of `Fin L` are
equinumerous when `L` is even.  The cyclic successor `x ↦ x + 1` is a bijection from one parity
class to the other (parity flips because `L` is even). -/
theorem ringSublattice_card_eq (L : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) :
    (Finset.univ.filter (fun x : Fin L => ringSublattice L x = true)).card =
      (Finset.univ.filter (fun x : Fin L => (! ringSublattice L x) = true)).card := by
  classical
  obtain ⟨k, hk⟩ := hLeven
  have : NeZero L := ⟨by omega⟩
  have hone : ((1 : Fin L)).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  refine Finset.card_nbij' (fun x => x + 1) (fun x => x - 1) ?_ ?_ ?_ ?_
  · -- maps even-class into odd-class
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    simp only [ringSublattice, decide_eq_true_eq] at hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [ringSublattice, Bool.not_eq_true', decide_eq_false_iff_not]
    have hlt : x.val + 1 < L := by omega
    have hxv : ((x + 1 : Fin L)).val = x.val + 1 := by
      rw [Fin.val_add, hone, Nat.mod_eq_of_lt hlt]
    rw [hxv]; omega
  · -- maps odd-class into even-class
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    simp only [ringSublattice, Bool.not_eq_true', decide_eq_false_iff_not] at hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [ringSublattice, decide_eq_true_eq]
    have hxne : x ≠ 0 := by
      intro h; rw [h] at hx; simp at hx
    have hxv : ((x - 1 : Fin L)).val = x.val - 1 := Fin.val_sub_one_of_ne_zero hxne
    rw [hxv]; omega
  · intro x _; simp
  · intro x _; simp

/-- **The even ring has a single ground sector**: the Tasaki §2.5 ground-state sectors of the AFM
Heisenberg ring collapse to the balanced magnetization sector `M0 = (L/2)·N` (the `Ŝ_tot^{(3)} = 0`
sector), since the two parity sublattices are equinumerous.  This is the singleton structure
consumed by the full-eigenspace uniqueness lift. -/
theorem ring_tasaki23GroundStateSectors_singleton (L N : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) :
    tasaki23GroundStateSectors (V := Fin L) (ringSublattice L) N =
      {((Finset.univ.filter (fun x : Fin L => ringSublattice L x = true)).card * N)} :=
  tasaki23GroundStateSectors_eq_singleton_of_card_eq (ringSublattice L) N
    (ringSublattice_card_eq L hLeven hL2)

end LatticeSystem.Quantum
