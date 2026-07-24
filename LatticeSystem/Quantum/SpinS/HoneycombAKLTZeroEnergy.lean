import LatticeSystem.Quantum.SpinS.HoneycombAKLTBondAnnihilation
import LatticeSystem.Math.FrustrationFree

/-!
# Zero-energy ground state of the finite honeycomb AKLT Hamiltonian

The per-bond annihilation result `honeycombVBSState_bond_annihilated` (proven on forward,
`A → B` oriented darts) is promoted to every *ordered* adjacent pair, and then assembled into
the frustration-free statement that the finite honeycomb VBS state is a zero-energy ground state
of the summed Hamiltonian `regularGraphAKLTHamiltonianS`.  This realizes the hypothesis
`IsGeneralGraphVBSGroundState` of Theorem 7.7 on the canonical honeycomb torus.

The assembly is the `ε ≡ 0` specialization of Tasaki's frustration-free Lemma A.9
(`frustration_free_isGroundState`): each local bond term is positive semidefinite
(`bondMaxSpinProjectionS_three_posSemidef`) and annihilates the state, so their sum is positive
semidefinite and annihilates the state; halving recovers `regularGraphAKLTHamiltonianS`.

## Reference

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer, 2020,
  §7.3.2, eqs. (7.3.6)–(7.3.8), Theorem 7.7, pp. 210–211; Appendix A.2.3, Lemma A.9, p. 469.
-/

namespace LatticeSystem.Quantum

open Matrix LatticeSystem.Lattice
open scoped ComplexOrder

variable {m : ℕ}

/-- On every *ordered* adjacent honeycomb pair `(x, y)`, the maximal-spin projection annihilates
the finite VBS state.  The forward-dart result `honeycombVBSState_bond_annihilated` covers the
`A → B` orientation directly; the reverse orientation is handled by the reversed dart together
with the bond-projection symmetry `bondMaxSpinProjectionS_comm`. -/
theorem honeycombVBSState_adj_bond_annihilated [NeZero m] (hm : 2 ≤ m)
    {x y : HoneycombVertex m} (hadj : (honeycombTorusGraph m).Adj x y) :
    (bondMaxSpinProjectionS x y 3).mulVec (honeycombVBSState m) = 0 := by
  by_cases hx : x.2 = false
  · exact honeycombVBSState_bond_annihilated hm ⟨⟨(x, y), hadj⟩, hx⟩
  · have hy : y.2 = false := by
      rcases honeycombTorusGraph_adj.mp hadj with ⟨hxf, -, -⟩ | ⟨-, hyf, -⟩
      · exact absurd hxf hx
      · exact hyf
    rw [bondMaxSpinProjectionS_comm x y]
    exact honeycombVBSState_bond_annihilated hm ⟨⟨(y, x), hadj.symm⟩, hy⟩

/-- The local frustration-free term at an ordered pair `(x, y)` of honeycomb sites: the
maximal-spin bond projector `P̂_3[Ŝ_x + Ŝ_y]` on adjacent pairs and `0` otherwise.  Summing it
over all ordered pairs and halving recovers `regularGraphAKLTHamiltonianS` (each undirected bond
is counted twice). -/
private noncomputable def honeycombAKLTLocalTerm (m : ℕ) [NeZero m]
    (p : HoneycombVertex m × HoneycombVertex m) : ManyBodyOpS (HoneycombVertex m) 3 :=
  if (honeycombTorusGraph m).Adj p.1 p.2 then bondMaxSpinProjectionS p.1 p.2 3 else 0

/-- The finite honeycomb VBS state is a zero-energy ground state of the regular-graph AKLT
Hamiltonian: `IsGeneralGraphVBSGroundState (honeycombTorusGraph m) 3 (honeycombVBSState m)` for
`m ≥ 2`.  This realizes the ground-state hypothesis of Tasaki Theorem 7.7 on the canonical
honeycomb torus.  Proof: the `ε ≡ 0` frustration-free Lemma A.9 applied to the ordered-pair local
terms, each positive semidefinite and annihilating the state. -/
theorem honeycombVBSState_isGeneralGraphVBSGroundState [NeZero m] (hm : 2 ≤ m) :
    IsGeneralGraphVBSGroundState (honeycombTorusGraph m) 3 (honeycombVBSState m) := by
  have hlb : ∀ p ∈ (Finset.univ : Finset (HoneycombVertex m × HoneycombVertex m)),
      (honeycombAKLTLocalTerm m p -
          ((0 : ℝ) : ℂ) • (1 : ManyBodyOpS (HoneycombVertex m) 3)).PosSemidef := by
    intro p _
    simp only [Complex.ofReal_zero, zero_smul, sub_zero]
    by_cases hadj : (honeycombTorusGraph m).Adj p.1 p.2
    · simp only [honeycombAKLTLocalTerm, if_pos hadj]
      exact bondMaxSpinProjectionS_three_posSemidef hadj.ne
    · simp only [honeycombAKLTLocalTerm, if_neg hadj]
      exact Matrix.PosSemidef.zero
  have heig : ∀ p ∈ (Finset.univ : Finset (HoneycombVertex m × HoneycombVertex m)),
      (honeycombAKLTLocalTerm m p).mulVec (honeycombVBSState m)
        = ((0 : ℝ) : ℂ) • honeycombVBSState m := by
    intro p _
    rw [Complex.ofReal_zero, zero_smul]
    by_cases hadj : (honeycombTorusGraph m).Adj p.1 p.2
    · simp only [honeycombAKLTLocalTerm, if_pos hadj]
      exact honeycombVBSState_adj_bond_annihilated hm hadj
    · simp only [honeycombAKLTLocalTerm, if_neg hadj]
      exact Matrix.zero_mulVec _
  obtain ⟨hpsd, hmul⟩ :=
    LatticeSystem.Math.frustration_free_isGroundState Finset.univ (honeycombAKLTLocalTerm m)
      (fun _ => 0) (honeycombVBSState m) hlb heig
  simp only [Finset.sum_const_zero, Complex.ofReal_zero, zero_smul, sub_zero] at hpsd hmul
  have hsum : regularGraphAKLTHamiltonianS (honeycombTorusGraph m) 3
      = (1 / 2 : ℂ) • ∑ p, honeycombAKLTLocalTerm m p := by
    rw [regularGraphAKLTHamiltonianS, Fintype.sum_prod_type (honeycombAKLTLocalTerm m)]
    simp only [honeycombAKLTLocalTerm]
  have hhalf : (0 : ℂ) ≤ 1 / 2 := by positivity
  refine ⟨?_, ?_, honeycombVBSState_ne_zero hm⟩
  · rw [hsum]
    exact hpsd.smul hhalf
  · rw [hsum, Matrix.smul_mulVec, hmul, smul_zero]

end LatticeSystem.Quantum
