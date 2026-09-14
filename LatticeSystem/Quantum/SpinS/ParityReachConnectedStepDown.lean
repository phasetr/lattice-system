import LatticeSystem.Quantum.SpinS.ConnectedRaiseLower
import LatticeSystem.Quantum.SpinS.ParityReachableNoParityBond
import LatticeSystem.Quantum.SpinS.ParityReachableNoSingleIon
import LatticeSystem.Quantum.SpinS.ParityReachWitness
import LatticeSystem.Quantum.SpinS.MagSumStepDown
import LatticeSystem.Quantum.SpinS.ParityReachStepDownFull

/-!
# Connected-graph step-down engine for parity-block reachability

Issue #5473 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Given `G.Connected` and `2 ≤ magSumS σ`, each of the three parity-block relations
(`ParityReachableS`, `IonParityReachableS`, `BondParityReachableS`) reaches from `σ` some
configuration whose `magSumS` is smaller by exactly `2`.  These are the connected-graph
analogues of the step-down lemmas behind the complete-bipartite totality theorems
(`ParityReachStepDownFull.lean`, `ParityReachableNoParityBondTotal.lean`,
`ParityReachableNoSingleIonTotal.lean`), and they carry **no** bipartiteness or balance
hypothesis: lowering the magnetization needs only an edge whose two endpoints both carry a
unit, and connectivity supplies one through the single-quantum walk transport of
`ConnectedRaiseLower.lean`.  None of the concentration / canonical-form machinery of the
complete-bipartite route is used.

The auxiliary hypotheses differ between the three relations, and each difference is forced:

* the bond-only relation needs `Nontrivial V`: on the one-vertex connected graph it has no
  available move at all, while `2 ≤ magSumS σ` is satisfiable there as soon as `2 ≤ N`;
* the ion-only relation needs `2 ≤ N`, since its only magnetization-changing move is the
  single-ion `±2` move, which needs room `1 < N`;
* the full relation needs neither beyond `1 ≤ N`, because it lowers with whichever of the two
  move kinds the configuration makes available.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, pp. 43–44.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [DecidableEq V] in
/-- Two distinct sites carrying exactly one unit each, extracted from a configuration all of
whose values are at most `1` and whose magnetization sum is at least `2`. -/
private theorem exists_two_one_sites_of_le_one
    {σ : V → Fin (N + 1)} (h_le1 : ∀ x : V, (σ x).val ≤ 1) (h_pos : 2 ≤ magSumS σ) :
    ∃ u v : V, u ≠ v ∧ (σ u).val = 1 ∧ (σ v).val = 1 := by
  have hcard : 2 ≤ (Finset.univ.filter (fun x : V => (σ x).val = 1)).card := by
    rw [← magSumS_eq_card_one_sites_of_le_one h_le1]
    exact h_pos
  obtain ⟨u, v, hu_mem, hv_mem, huv⟩ :=
    Finset.one_lt_card_iff.mp
      (show 1 < (Finset.univ.filter (fun x : V => (σ x).val = 1)).card from by omega)
  exact ⟨u, v, huv, (Finset.mem_filter.mp hu_mem).2, (Finset.mem_filter.mp hv_mem).2⟩

/-! ## A positive adjacent pair -/

set_option linter.unusedDecidableInType false in
/-- **A `G`-edge with both endpoints occupied, after transverse transport.**  On a connected
graph with at least two vertices and `1 ≤ N`, every configuration of magnetization sum at least
`2` is transverse-reachable to a configuration `τ` carrying at least one unit on both endpoints
of some edge.

This is the only genuinely new combinatorial input of the connected-graph step-down.  It
replaces the sublattice case analysis of the complete-bipartite route, where an edge between any
two distinct sublattice sites was available for free.  Two cases: if some site holds at least
two units, push one unit towards a neighbour (or, if that neighbour is already full, use it as
it stands); otherwise all values are `0` or `1`, so there are two distinct occupied sites, and a
neighbour of one of them is either occupied already or has room to receive a unit from the
other. -/
theorem exists_adj_pair_pos_raiseLowerReachable_of_connected
    {G : SimpleGraph V} (hV : Nontrivial V) (hG : G.Connected) (hN : 1 ≤ N)
    {σ : V → Fin (N + 1)} (h_pos : 2 ≤ magSumS σ) :
    ∃ (τ : V → Fin (N + 1)) (x y : V),
      G.Adj x y ∧ 1 ≤ (τ x).val ∧ 1 ≤ (τ y).val ∧ RaiseLowerReachableS G σ τ := by
  haveI := hV
  by_cases hbig : ∃ x : V, 2 ≤ (σ x).val
  · obtain ⟨x, hx⟩ := hbig
    obtain ⟨w, hadj⟩ := hG.preconnected.exists_adj_of_nontrivial x
    by_cases hw : (σ w).val < N
    · refine ⟨transportOne σ x w, x, w, hadj, ?_, ?_,
        RaiseLowerReachableS.single (raiseLowerStepS_transport hadj (by omega) hw)⟩
      · rw [transportOne_apply_x hadj.ne]; omega
      · rw [transportOne_apply_y hw]; omega
    · exact ⟨σ, x, w, hadj, by omega, by omega, RaiseLowerReachableS.refl G σ⟩
  · have h_le1 : ∀ x : V, (σ x).val ≤ 1 := by
      intro x
      by_contra hge
      exact hbig ⟨x, by omega⟩
    obtain ⟨u, v, huv, hu, hv⟩ := exists_two_one_sites_of_le_one h_le1 h_pos
    obtain ⟨w, hadj⟩ := hG.preconnected.exists_adj_of_nontrivial v
    by_cases hw : 1 ≤ (σ w).val
    · exact ⟨σ, v, w, hadj, by omega, hw, RaiseLowerReachableS.refl G σ⟩
    · have huw : u ≠ w := by
        intro h
        rw [h] at hu
        omega
      refine ⟨transportOne σ u w, v, w, hadj, ?_, ?_,
        raiseLowerReachableS_transportOne_of_connected hG huw (by omega) (by omega)⟩
      · rw [transportOne_apply_off (Ne.symm huv) hadj.ne]; omega
      · rw [transportOne_apply_y (by omega)]; omega

/-! ## Step-down for the three parity-block relations -/

set_option linter.unusedDecidableInType false in
/-- **Bond-only step-down on a connected graph**: with at least two vertices and `1 ≤ N`, a
configuration of magnetization sum at least `2` reaches, by transverse and bond-parity moves
only, a configuration of magnetization sum smaller by exactly `2`. -/
theorem bondParityReachableS_step_down_of_connected
    {G : SimpleGraph V} (hV : Nontrivial V) (hG : G.Connected) (hN : 1 ≤ N)
    {σ : V → Fin (N + 1)} (h_pos : 2 ≤ magSumS σ) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧ BondParityReachableS G σ σ' := by
  obtain ⟨τ, x, y, hadj, hx, hy, hreach⟩ :=
    exists_adj_pair_pos_raiseLowerReachable_of_connected hV hG hN h_pos
  have hmag : magSumS τ = magSumS σ := magSumS_eq_of_raiseLowerReachableS hreach
  refine ⟨_, ?_, (BondParityReachableS.of_raiseLowerReachable hreach).trans
    (BondParityReachableS.of_bond (parityBondStepS_pair_lower hadj hx hy))⟩
  have h_final := parityBondStepS_pair_lower_magSumS_decrease (σ := τ) hadj.ne hx hy
  omega

set_option linter.unusedDecidableInType false in
/-- **Full parity-block step-down on a connected graph**: with `1 ≤ N`, a configuration of
magnetization sum at least `2` reaches a configuration of magnetization sum smaller by exactly
`2`.  No `Nontrivial V` hypothesis: if some site holds at least two units, a single-ion move
lowers it on the spot, and otherwise the two distinct occupied sites themselves witness
`Nontrivial V` for the bond route. -/
theorem parityReachableS_step_down_of_connected
    {G : SimpleGraph V} (hG : G.Connected) (hN : 1 ≤ N)
    {σ : V → Fin (N + 1)} (h_pos : 2 ≤ magSumS σ) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧ ParityReachableS G σ σ' := by
  by_cases hbig : ∃ x : V, 2 ≤ (σ x).val
  · obtain ⟨x, hx⟩ := hbig
    exact ⟨configUpdateOne σ x ⟨(σ x).val - 2, by have := (σ x).isLt; omega⟩,
      singleIonStepS_lower_magSumS_decrease x hx,
      ParityReachableS.of_singleIon (singleIonStepS_lower x hx)⟩
  · have h_le1 : ∀ x : V, (σ x).val ≤ 1 := by
      intro x
      by_contra hge
      exact hbig ⟨x, by omega⟩
    obtain ⟨u, v, huv, -, -⟩ := exists_two_one_sites_of_le_one h_le1 h_pos
    have hV : Nontrivial V := ⟨u, v, huv⟩
    obtain ⟨σ', hmag, hreach⟩ :=
      bondParityReachableS_step_down_of_connected hV hG hN h_pos
    exact ⟨σ', hmag, hreach.to_parityReachableS⟩

set_option linter.unusedDecidableInType false in
/-- **Ion-only step-down on a connected graph**: with `2 ≤ N`, a configuration of magnetization
sum at least `2` reaches, by transverse and single-ion moves only, a configuration of
magnetization sum smaller by exactly `2`.  No `Nontrivial V` hypothesis: a site holding two
units is lowered on the spot, and otherwise the two distinct occupied sites are joined by a walk
along which one unit is transported to stack them. -/
theorem ionParityReachableS_step_down_of_connected
    {G : SimpleGraph V} (hG : G.Connected) (hN : 2 ≤ N)
    {σ : V → Fin (N + 1)} (h_pos : 2 ≤ magSumS σ) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧ IonParityReachableS G σ σ' := by
  by_cases hbig : ∃ x : V, 2 ≤ (σ x).val
  · obtain ⟨x, hx⟩ := hbig
    exact ⟨configUpdateOne σ x ⟨(σ x).val - 2, by have := (σ x).isLt; omega⟩,
      singleIonStepS_lower_magSumS_decrease x hx,
      IonParityReachableS.of_singleIon (singleIonStepS_lower x hx)⟩
  · have h_le1 : ∀ x : V, (σ x).val ≤ 1 := by
      intro x
      by_contra hge
      exact hbig ⟨x, by omega⟩
    obtain ⟨u, v, huv, hu, hv⟩ := exists_two_one_sites_of_le_one h_le1 h_pos
    have hroom : (σ v).val < N := by omega
    have hreach : RaiseLowerReachableS G σ (transportOne σ u v) :=
      raiseLowerReachableS_transportOne_of_connected hG huv (by omega) hroom
    have hv2 : (transportOne σ u v v).val = 2 := by
      rw [transportOne_apply_y hroom]; omega
    have hmag : magSumS (transportOne σ u v) = magSumS σ :=
      magSumS_eq_of_raiseLowerReachableS hreach
    refine ⟨_, ?_, (IonParityReachableS.of_raiseLowerReachable hreach).trans
      (IonParityReachableS.of_singleIon
        (singleIonStepS_lower (σ := transportOne σ u v) v (by omega)))⟩
    have h_final :=
      singleIonStepS_lower_magSumS_decrease (σ := transportOne σ u v) v (by omega)
    omega

end LatticeSystem.Quantum
