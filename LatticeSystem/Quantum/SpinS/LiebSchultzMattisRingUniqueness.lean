import LatticeSystem.Quantum.SpinS.HiddenAntiferromagneticOrder
import LatticeSystem.Quantum.SpinS.HaldaneConjecture
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Tasaki §6.2 Theorem 6.3: ring setup for ground-state uniqueness

Foundations for discharging the §6.2 axiom `lieb_schultz_mattis_affleck_lieb` (Theorem 6.3): the
ground state of the antiferromagnetic Heisenberg ring `afmHeisenbergChainHamiltonianS L N` is
unique, which (with Lemmas 6.1 and 6.2) yields the `O(1/L)` spectral gap.

The Marshall–Lieb–Mattis uniqueness machinery (`ConnectedSectorFinrankLeOne`,
`StrictHOutsideFerrimagnetic`, `Theorem24SU2GlobalUniquenessFromMLM`) is stated for a **symmetric**
coupling on a **connected bipartite graph**.  This module packages the ring data in that form:

* the symmetrized ring coupling `ringCouplingSym` gives
  `heisenbergHamiltonianS (ringCouplingSym L) N = 2 · afmHeisenbergChainHamiltonianS L N`
  (so the eigenspaces coincide, eigenvalues doubled);
* the periodic chain graph `cycleGraph L` is bipartite w.r.t. the parity colouring
  `ringSublattice`, with `ringCouplingSym` strictly positive on its edges (for `L` even).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, p. 162.
-/

namespace LatticeSystem.Quantum

open Matrix SimpleGraph

/-- **General-`N` symmetrization identity**: the Heisenberg Hamiltonian with the symmetrized ring
coupling is twice the directed antiferromagnetic chain Hamiltonian (the transpose summand reproduces
the original via `heisenbergHamiltonianS_coupling_swap`).  Generalises
`heisenbergHamiltonianS_ringCouplingSym` (stated at `N = 2`) to arbitrary spin. -/
theorem heisenbergHamiltonianS_ringCouplingSym_eq (L N : ℕ) :
    heisenbergHamiltonianS (ringCouplingSym L) N =
      (2 : ℂ) • afmHeisenbergChainHamiltonianS L N := by
  unfold afmHeisenbergChainHamiltonianS
  rw [show ringCouplingSym L = (fun x y => ringCoupling L x y + ringCoupling L y x) from rfl,
    heisenbergHamiltonianS_add, heisenbergHamiltonianS_coupling_swap, two_smul]

/-- On `Fin (n+2)`, `(x + 1).val = (x.val + 1) % (n+2)` (the cyclic successor's index). -/
private theorem fin_val_add_one (n : ℕ) (x : Fin (n + 2)) :
    (x + 1).val = (x.val + 1) % (n + 2) := by
  rw [Fin.val_add, Fin.val_one]

/-- The directed ring coupling on a successor pair is `1`. -/
private theorem ringCoupling_succ (n : ℕ) (x : Fin (n + 2)) :
    ringCoupling (n + 2) x (x + 1) = 1 := by
  rw [ringCoupling, if_pos (fin_val_add_one n x)]

/-- The directed ring coupling always has nonnegative real part. -/
private theorem ringCoupling_re_nonneg (L : ℕ) (x y : Fin L) : 0 ≤ (ringCoupling L x y).re := by
  rw [ringCoupling]; split <;> simp

/-- **The ring coupling is strictly positive on cycle-graph edges**: every edge of `cycleGraph L`
is a nearest-neighbour pair, where `ringCouplingSym` takes value `1`. -/
theorem cycleGraph_adj_ringCouplingSym_re_pos (L : ℕ) {x y : Fin L}
    (h : (cycleGraph L).Adj x y) : 0 < (ringCouplingSym L x y).re := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := by
    match L, x with
    | 0, x => exact x.elim0
    | 1, x => exact absurd h (by simp [cycleGraph_one_adj])
    | (n + 2), _ => exact ⟨n, rfl⟩
  rw [cycleGraph_adj] at h
  rw [ringCouplingSym, Complex.add_re]
  rcases h with h | h
  · have hx : x = y + 1 := (sub_eq_iff_eq_add.mp h).trans (add_comm 1 y)
    rw [hx, ringCoupling_succ]
    have := ringCoupling_re_nonneg (n + 2) (y + 1) y
    simp only [Complex.one_re]; linarith
  · have hy : y = x + 1 := (sub_eq_iff_eq_add.mp h).trans (add_comm 1 x)
    rw [hy, ringCoupling_succ]
    have := ringCoupling_re_nonneg (n + 2) (x + 1) x
    simp only [Complex.one_re]; linarith

/-- **The cycle graph is bipartite** w.r.t. the parity colouring `ringSublattice` (for `L` even):
adjacent (nearest-neighbour) sites differ in parity. -/
theorem cycleGraph_adj_ringSublattice_ne (L : ℕ) (hLeven : Even L) {x y : Fin L}
    (h : (cycleGraph L).Adj x y) : ringSublattice L x ≠ ringSublattice L y := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 2 := by
    match L, x with
    | 0, x => exact x.elim0
    | 1, x => exact absurd h (by simp [cycleGraph_one_adj])
    | (n + 2), _ => exact ⟨n, rfl⟩
  rw [cycleGraph_adj] at h
  obtain ⟨k, hk⟩ := hLeven
  simp only [ringSublattice, ne_eq, decide_eq_decide]
  -- one of x = y+1, y = x+1; in either case parities differ on the even ring
  have hpar : x.val % 2 ≠ y.val % 2 := by
    rcases h with h | h
    · have hx : x.val = (y.val + 1) % (n + 2) := by
        have hxe : x = y + 1 := (sub_eq_iff_eq_add.mp h).trans (add_comm 1 y)
        rw [hxe]; exact fin_val_add_one n y
      rcases Nat.lt_or_ge (y.val + 1) (n + 2) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hx; omega
      · have hy1 : y.val + 1 = n + 2 := by have := y.isLt; omega
        rw [hy1, Nat.mod_self] at hx; omega
    · have hy : y.val = (x.val + 1) % (n + 2) := by
        have hye : y = x + 1 := (sub_eq_iff_eq_add.mp h).trans (add_comm 1 x)
        rw [hye]; exact fin_val_add_one n x
      rcases Nat.lt_or_ge (x.val + 1) (n + 2) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at hy; omega
      · have hx1 : x.val + 1 = n + 2 := by have := x.isLt; omega
        rw [hx1, Nat.mod_self] at hy; omega
  omega

end LatticeSystem.Quantum
