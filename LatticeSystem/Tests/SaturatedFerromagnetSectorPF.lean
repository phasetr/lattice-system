import LatticeSystem.Quantum.SpinS.FerromagneticSectorSpan

/-!
# Signature pin: sector Perron–Frobenius uniqueness (Tasaki §2.4 Theorem 2.1, p. 34)

Repository-internal regression guard for the four declarations behind the per-sector
Perron–Frobenius uniqueness half of Tasaki's Theorem 2.1: for each magnetization sector `M` of
the ferromagnetic spin-`S` Heisenberg model on a connected graph, the ground state of the
sector-restricted Hamiltonian is `ladderIterateUp V N k` up to a scalar (solution of Problem
2.4.a, p. 496, via Theorem A.18, p. 475).  Pinned are the strict positivity of the restricted
ladder state, its real-form sector eigenvector equation, the sector `finrank ≤ 1` bound and the
resulting span equality.  The four names live in
`LatticeSystem/Quantum/SpinS/FerromagneticSectorPF.lean` and
`LatticeSystem/Quantum/SpinS/FerromagneticSectorSpan.lean`, the second importing the first, so the
single import above reaches all four; any rename, reordering of arguments or weakening of the
hypotheses there breaks this module.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; solution of Problem 2.4.a, p. 496; Theorem A.18, p. 475.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **P2 pin.** The sector restriction of a ladder iterate is strictly positive (real part) on
every configuration of its own magnetization sector: the Perron eigenvector candidate. -/
example (k : Fin (Fintype.card V * N + 1)) (σ : magConfigS V N k.val) :
    0 < (ladderIterateUp V N k σ.1).re :=
  ladderIterateUp_restriction_re_pos k σ

/-- **P3 pin.** The real part of the sector-restricted ladder iterate is a real eigenvector of
the real-form sector matrix at `(saturatedFerromagnetEigenvalueS J N).re`. -/
example (J : V → V → ℂ) (hJ_real : ∀ x y, (J x y).im = 0)
    (k : Fin (Fintype.card V * N + 1)) :
    (heisenbergHamiltonianSReMatrixOnMagSector J N k.val).mulVec
        (fun σ => (magSectorRestriction (M := k.val) (ladderIterateUp V N k) σ).re) =
      (saturatedFerromagnetEigenvalueS (V := V) J N).re •
        (fun σ => (magSectorRestriction (M := k.val) (ladderIterateUp V N k) σ).re) :=
  heisenbergHamiltonianSReMatrixOnMagSector_mulVec_ladder_restriction J hJ_real k

/-- **P4 pin.** On a connected graph with real, symmetric, edge-supported, strictly ferromagnetic
coupling, the complex sector matrix's ground eigenspace has `finrank ≤ 1`. The diagonal shift
witness is discharged internally via `LatticeSystem.Math.exists_gt_of_finite`, so this statement —
like the sector-irreducibility hypotheses reused from it — carries only book hypotheses.  `hN` is
pinned although the Perron-Frobenius step does not use it: it is the standing assumption `S ≥ 1/2`
of §2.4, which is what makes `saturatedFerromagnetEigenvalueS` the ground energy. -/
example {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) (k : Fin (Fintype.card V * N + 1)) :
    Module.finrank ℂ
        (Module.End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianSMatrixOnMagSector J N k.val))
          (saturatedFerromagnetEigenvalueS (V := V) J N)) ≤ 1 :=
  heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_connected_ferro
    hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN k

/-- **P5 pin.** Every sector ground state (the `H`-eigenspace at
`saturatedFerromagnetEigenvalueS J N`, intersected with the magnetization-sector subspace) is
exactly `span ℂ {ladderIterateUp V N k}` — the per-sector uniqueness statement P5 must establish
as an equality of `Submodule`s, not merely a `finrank` bound.  No `[Nonempty V]` instance may be
required: `G.Connected` carries it.  `hN` is pinned for the same reason as in P4. -/
example {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) (k : Fin (Fintype.card V * N + 1)) :
    Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := V) J N)
      ⊓ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) =
    Submodule.span ℂ {ladderIterateUp V N k} :=
  heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_eq_span_ladderIterateUp
    hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN k

end LatticeSystem.Quantum
