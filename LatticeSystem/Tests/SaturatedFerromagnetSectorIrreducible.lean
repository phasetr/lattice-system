import LatticeSystem.Quantum.SpinS.MultiSiteDotOffDiag
import LatticeSystem.Quantum.SpinS.HeisenbergRaiseLower
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshallCore
import LatticeSystem.Quantum.SpinS.ConnectedDressedPF

/-!
# Signature pin: off-diagonal signs and connected-sector irreducibility (Tasaki §2.4)

Repository-internal regression guard for the five declarations behind the ferromagnetic
Heisenberg matrix's off-diagonal sign structure and its connected-graph, per-magnetization-sector
Perron–Frobenius irreducibility, the crux input to Tasaki's Theorem 2.1 (p. 34) uniqueness
argument: the sign-free bare bond-term nonnegativity (S1), its Hamiltonian-level ferromagnetic
non-positivity (S2), the strict raise/lower-step negativity (S3), a strict diagonal upper bound
(S4), and the connected-graph sector irreducibility of the shifted matrix (P1). The five names
live in `LatticeSystem/Quantum/SpinS/FerromagneticHeisenbergSign.lean` and
`LatticeSystem/Quantum/SpinS/FerromagneticSectorIrreducible.lean`; any rename, reordering of
arguments or weakening of the hypotheses there breaks this module.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer 2020),
§2.4, p. 34; Problem 2.4.a solution, p. 496.
-/

namespace LatticeSystem.Tests.SaturatedFerromagnetSectorIrreducible

open Matrix LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Signature pin (S1).** The bare bond term `Ŝ_x·Ŝ_y` has non-negative real part on every
off-diagonal entry, for `x ≠ y`. Sign-free: no coupling `J` or ferromagnetic hypothesis enters. -/
example {x y : V} (hxy : x ≠ y) {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    0 ≤ ((spinSDot x y N : ManyBodyOpS V N) σ' σ).re :=
  spinSDot_apply_re_nonneg_of_ne hxy hne

/-- **Signature pin (S2).** For real, ferromagnetic (`≤ 0`) coupling `J`, every off-diagonal
entry of the Heisenberg matrix has non-positive real part. -/
example {J : V → V → ℂ} (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nonpos : ∀ x y, (J x y).re ≤ 0)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ) :
    ((heisenbergHamiltonianS (Λ := V) J N) σ' σ).re ≤ 0 :=
  heisenbergHamiltonianS_apply_re_nonpos_of_ne hJ_real hJ_nonpos hne

/-- **Signature pin (S3).** On a `RaiseLowerStepS G σ σ'` witness `(x, y)` along a `G`-edge with
real, strictly ferromagnetic (`< 0`) symmetric coupling at that bond, the Heisenberg matrix
element has strictly negative real part. -/
example {J : V → V → ℂ} (N : ℕ)
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hJ_real : (J x y).im = 0) (hJ_neg : (J x y).re < 0)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    ((heisenbergHamiltonianS J N) σ' σ).re < 0 :=
  heisenbergHamiltonianS_apply_re_neg_of_raiseLowerStepS_witness N hadj hJ_real hJ_neg hJ_sym
    hsh hagree

/-- **Signature pin (S4).** The real-form Heisenberg matrix's diagonal entries admit a common
strict upper bound `c`, discharging the repo-idiomatic `hc_strict` premise used by the sector
irreducibility argument (P1). -/
example (J : V → V → ℂ) (N : ℕ) :
    ∃ c : ℝ, ∀ σ : V → Fin (N + 1), heisenbergHamiltonianSReMatrix J N σ σ < c :=
  exists_gt_heisenbergHamiltonianSReMatrix_diag J N

/-- **Signature pin (P1).** On a connected graph `G` with real, symmetric coupling `J` supported
on `G`'s edges (`hJ_supp`) and strictly ferromagnetic there (`hJ_ferro`), the shifted real-form
Heisenberg matrix restricted to the magnetization-`M` sector is Perron–Frobenius irreducible,
given a strict diagonal upper bound `c` (S4) and a nonempty sector. -/
example {G : SimpleGraph V} {J : V → V → ℂ} (c : ℝ) {M : ℕ}
    (hGconn : G.Connected)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hc_strict : ∀ σ, heisenbergHamiltonianSReMatrix J N σ σ < c)
    [Nonempty (magConfigS V N M)] :
    (c • (1 : Matrix (magConfigS V N M) (magConfigS V N M) ℝ)
        - heisenbergHamiltonianSReMatrixOnMagSector J N M).IsIrreducible :=
  isIrreducible_shiftedHeisenbergSReMatrixOnMagSector_connected_ferro
    hGconn hJ_supp hJ_ferro hJ_real hJ_sym hc_strict

end LatticeSystem.Tests.SaturatedFerromagnetSectorIrreducible
