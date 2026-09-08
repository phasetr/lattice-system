import LatticeSystem.Quantum.SpinS.FerromagneticSectorSpan
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace

/-!
# Tasaki §2.4 Theorem 2.1: the ferromagnetic ground-state eigenspace

Closes Tasaki's Theorem 2.1 (p. 34) for the spin-`S` Heisenberg model on a connected graph
carrying a real, symmetric, edge-supported, strictly ferromagnetic coupling: the eigenspace of
`Ĥ` *alone* at the saturated-ferromagnet energy is the span of the ladder family
`Φ_M = (Ŝ⁻_tot)^k Φ↑` of eq. (2.4.9), p. 33 -- which is eq. (2.4.10), p. 34.

The analytic input is the per-sector Perron-Frobenius uniqueness of `FerromagneticSectorSpan`
(solution of Problem 2.4.a, p. 496); the assembly across sectors is the pointwise magnetization
decomposition of `SaturatedLadderJointEigenspace`, whose joint `(Ĥ, (Ŝ_tot)²)` analogue this
module upgrades to a statement about `Ĥ` by itself.

Two remarks on the hypotheses.  `hJ_sym` is not an assumption beyond the book: eq. (2.4.1),
p. 32, sums over *unordered* bonds, so one weight per unordered bond is the printed model, and
the repo's ordered double sum encodes exactly that when the weight function is symmetric.  And
`1 ≤ N` is the standing assumption `S ≥ 1/2` of §2.4; it is what makes
`saturatedFerromagnetEigenvalueS` the ground energy rather than merely an eigenvalue.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; eq. (2.4.1), p. 32; eq. (2.4.9), p. 33; eq. (2.4.10), p. 34;
solution of Problem 2.4.a, p. 496.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **The magnetization projector preserves an `Ĥ`-eigenspace.**

`Ĥ` commutes with the pointwise magnetization projector
(`heisenbergHamiltonianS_mulVec_magProjFn_eq`, which needs no hypothesis on `J`), so projecting
an eigenvector onto a magnetization sector leaves the eigenvector equation intact.  This is the
operator form of the block decomposition `Ĥ = ⊕_M Ĥ_M` that the solution of Problem 2.4.a
(p. 496) works in.  The joint `(Ĥ, (Ŝ_tot)²)` counterpart is
`magProjFn_mem_saturatedFerromagnetJointEigenspace`; here only the `Ĥ` factor is available, and
the eigenvalue is arbitrary. -/
private theorem magProjFn_mem_heisenbergHamiltonianS_eigenspace
    {J : V → V → ℂ} {μ M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ∈ Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin) μ) :
    magProjFn (V := V) (N := N) M v
      ∈ Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin) μ := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv ⊢
  rw [heisenbergHamiltonianS_mulVec_magProjFn_eq, hv, magProjFn_smul]

/-- **Tasaki §2.4 Theorem 2.1, eq. (2.4.10), p. 34**: on a connected graph with a real,
symmetric, edge-supported, strictly ferromagnetic coupling, the `Ĥ`-eigenspace at the
saturated-ferromagnet energy is exactly the span of the ladder family `Φ_M` of eq. (2.4.9),
p. 33.

`⊇` is the statement that every ladder iterate is such an eigenvector.  For `⊆`, decompose a
ground state `v = ∑_k magProjFn (m_max - k) v` (`sum_magProjFn_eq`); each summand stays in the
eigenspace by `magProjFn_mem_heisenbergHamiltonianS_eigenspace` and lands in its magnetization
subspace by `magProjFn_mem_magSubspaceS`, so the per-sector Perron-Frobenius identification
(solution of Problem 2.4.a, p. 496) turns it into a multiple of the single ladder state of that
sector.

Non-emptiness of `V` is not a hypothesis: `G.Connected` carries it.  The book's `Φ_M` is the
normalized ladder state and `ladderIterateUp` the unnormalized iterate; only their span
appears. -/
theorem heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro
    {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) :
    Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := V) J N)
      = Submodule.span ℂ (Set.range (ladderIterateUp V N)) := by
  haveI : Nonempty V := hGconn.nonempty
  refine le_antisymm (fun v hv => ?_) ?_
  · rw [← sum_magProjFn_eq (V := V) (N := N) v]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hmem : magProjFn (V := V) (N := N)
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) v ∈
        Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
            (saturatedFerromagnetEigenvalueS (V := V) J N)
          ⊓ magSubspaceS V N ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) :=
      Submodule.mem_inf.mpr
        ⟨magProjFn_mem_heisenbergHamiltonianS_eigenspace hv, magProjFn_mem_magSubspaceS _ v⟩
    rw [heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_eq_span_ladderIterateUp
      hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN k] at hmem
    exact ladderIterateUp_singleton_span_le_span_range (V := V) N k hmem
  · rw [Submodule.span_le, Set.range_subset_iff]
    exact fun k => ladderIterateUp_mem_heisenbergHamiltonianS_eigenspace J k

end LatticeSystem.Quantum
