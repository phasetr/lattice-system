import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.MagSectorEmbeddingCore
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshallCore
import LatticeSystem.Quantum.SpinS.SaturatedFullLadderLI
import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.EigenspaceFinrankLeOneTransfer
import LatticeSystem.Math.PerronFrobeniusFinrank
import LatticeSystem.Quantum.SpinS.FerromagneticSectorIrreducible
import LatticeSystem.Math.FiniteStrictUpperBound

/-!
# Red fixture: Tasaki §2.4 Theorem 2.1 (p. 34), sector Perron–Frobenius uniqueness (PR-3)

Pins the four public declarations PR-3 must introduce toward the per-sector
Perron–Frobenius uniqueness half of Tasaki's Theorem 2.1: for each magnetization sector `M`
of the ferromagnetic spin-`S` Heisenberg model on a connected graph, the ground state of the
sector-restricted Hamiltonian is `ladderIterateUp V N k` up to scalar (Problem 2.4.a solution,
p. 496, via Theorem A.18, p. 475).

Every `example` below must fail elaboration with `unknown identifier` for the pinned name — this
file has not yet type-checked any of the four statements; the identifiers do not exist on `main`.

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
like the sector-irreducibility hypotheses reused from it — carries only book hypotheses. -/
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

/-- **P5 pin.** Every sector ground state (the joint `H`-eigenspace at
`saturatedFerromagnetEigenvalueS J N`, intersected with the magnetization-sector subspace) is
exactly `span ℂ {ladderIterateUp V N k}` — the per-sector uniqueness statement P5 must establish
as an equality of `Submodule`s, not merely a `finrank` bound. -/
example [Nonempty V] {G : SimpleGraph V} {J : V → V → ℂ}
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
