import LatticeSystem.Quantum.SpinS.SPTPhase

/-!
# Tasaki §8.3.2–§8.3.3: protecting symmetries and "topological" indices for SPT phases

Different SPT phases cannot be told apart by any local order parameter (there is no symmetry
breaking).  The Haldane phase is protected by any one of three symmetries:

* **(S1) Z₂ × Z₂** — the π-rotations about the spin axes (`IsZ2Z2Invariant`);
* **(S2) time-reversal** `Θ̂` (`IsTimeReversalInvariant`);
* **(S3) bond-centered inversion** `Û_inv` (`IsBondInversionInvariant`).

A clean characterization uses **"topological" indices** of the ground-state entanglement, invariant
under continuous symmetric deformation.  The simplest is the **inversion parity**: for the spin-`S`
VBS state on an `L`-site ring, `Û_inv |Φ_VBS^S⟩ = (−1)^{L·S} |Φ_VBS^S⟩`.  When `L·S` is odd the VBS
state has *odd* parity and cannot be continuously connected to the *even*-parity trivial state, so
it
is a nontrivial SPT.  More generally the spin-`S` VBS is a nontrivial SPT phase (protected by (S1),
(S2), or (S3)) **iff `S` is odd**; for even `S` it is trivial — a further qualitative odd/even-`S`
distinction beyond Haldane's.

The general "topological" indices arise from the **Schmidt decomposition** of the infinite-chain
ground state `|Φ_GS⟩ = Σ_j √p_j |Φ_j⟩_L ⊗ |Ψ_j⟩_R` (eq. (8.3.7)), the reduced density matrix
`ρ̂_R = Σ_j p_j |Ψ_j⟩_R ⟨Ψ_j|` (eq. (8.3.8)), and the **entanglement entropy**
`S_LR = −Σ_j p_j log p_j` (`entanglementEntropyS`).  This section is heuristic; the precise
definitions for matrix product states are in §8.3.4 and Ogata's rigorous infinite-chain indices in
§8.3.6.

The protecting symmetries, the SPT classification, and the entanglement entropy are uninterpreted
markers (the antiunitary time reversal, the inversion geometry, and the half-infinite-chain Schmidt
decomposition belong to the operator-algebra framework).  The inversion-parity formula `(−1)^{L·S}`
and the odd/even-`S` classification are documented axioms.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.2–§8.3.3, eqs. (8.3.6)–(8.3.10), pp. 256–263; F. Pollmann, A. M. Turner, E. Berg, M.
Oshikawa, Phys. Rev. B **81**, 064439 (2010); Phys. Rev. B **85**, 075125 (2012).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- **(S2) Time-reversal symmetry marker** `IsTimeReversalInvariant H`: the Hamiltonian `H` is
invariant under the antiunitary time-reversal `Θ̂`.  A faithful definition needs the antiunitary
operator; kept as an uninterpreted predicate. -/
axiom IsTimeReversalInvariant (H : ManyBodyOpS (Fin L) 2) : Prop

/-- **(S3) Bond-centered inversion symmetry marker** `IsBondInversionInvariant H`: the Hamiltonian
`H` is invariant under the bond-centered spatial inversion `Û_inv`.  A faithful definition needs the
inversion's geometric action on the chain; kept as an uninterpreted predicate. -/
axiom IsBondInversionInvariant (H : ManyBodyOpS (Fin L) 2) : Prop

/-- The **inversion parity of the spin-`S` VBS state** on an `L`-site ring, valued in `{±1}`: the
eigenvalue of `Û_inv` on `|Φ_VBS^S⟩` (a `Z₂` topological index). -/
axiom vbsInversionParityS : ℕ → ℕ → ℤ

/-- **Tasaki §8.3.2 (VBS inversion parity), AXIOM.**  The spin-`S` VBS state on an `L`-site periodic
chain is an eigenstate of bond-centered inversion with eigenvalue `(−1)^{L·S}`:
`Û_inv |Φ_VBS^S⟩ = (−1)^{L·S} |Φ_VBS^S⟩`.  For odd `L·S` the state has odd parity and so cannot be
continuously connected to the even-parity trivial product state — a `Z₂` topological obstruction. -/
axiom tasaki_vbs_inversion_parity (L S : ℕ) : vbsInversionParityS L S = (-1 : ℤ) ^ (L * S)

/-- **SPT-nontriviality marker** `IsSpinSVBSNontrivialSPT S`: the spin-`S` VBS phase is a nontrivial
SPT phase (protected by (S1), (S2), or (S3)). -/
axiom IsSpinSVBSNontrivialSPT : ℕ → Prop

/-- **Tasaki §8.3.3 (odd/even-`S` SPT classification), AXIOM.**  The spin-`S` VBS state exhibiting
the Haldane gap is a **nontrivial** SPT phase (protected by Z₂ × Z₂, time-reversal, or bond-centered
inversion) **iff `S` is odd**; for even `S` it belongs to the trivial phase and can be continuously
connected to a product state under any of the symmetries. -/
axiom tasaki_spt_classification (S : ℕ) : IsSpinSVBSNontrivialSPT S ↔ Odd S

/-- The **bipartite entanglement entropy** `S_LR = −Σ_j p_j log p_j` of a chain state, from the
Schmidt weights `p_j` of the left/right bipartition (eqs. (8.3.7)–(8.3.8)).  The half-infinite-chain
Schmidt decomposition / partial trace / von Neumann entropy is recorded as an uninterpreted
real-valued marker. -/
axiom entanglementEntropyS {L N : ℕ} : ((Fin L → Fin (N + 1)) → ℂ) → ℝ

end LatticeSystem.Quantum
