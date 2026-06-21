import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.MultiSiteCasimir
import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.LadderBoundary
import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.AllAlignedStateCore

/-!
# Spin-`S` all-aligned (saturated ferromagnet) state
(Tasaki §2.4 generalised to spin-`S`)

For a multi-site spin-`S` system on a finite vertex set `V`, the
**all-aligned** (constant-spin) state with `σ x = c` for all `x : V`
is a basis vector of the multi-site Hilbert space.

This file proves:

1. The all-aligned state at any `c : Fin (N+1)` is a `Ŝ^z_tot`
   eigenvector with eigenvalue `|V|·N/2 − |V|·c`.
2. The two extreme cases `c = 0` (highest weight, "all up") and
   `c = N` (lowest weight, "all down") are the **unique** elements of
   their respective magnetization sectors (`magSumS = 0` and
   `magSumS = |V|·N`), hence automatically Heisenberg eigenvectors
   for ANY coupling via the magnetization-conservation identity
   `[H, Ŝ^z_tot] = 0`. The eigenvalue is the explicit diagonal
   `Σ_x J(x,x) · N(N+2)/4 + Σ_{x≠y} J(x,y) · N²/4`.

The `(Ŝ_tot)²` eigenvalue `(|V|·N/2)(|V|·N/2+1)` (the `J = |V|·S`
highest-weight irreducible representation) is left to a follow-up
textbook unit, since it requires the alternative Casimir form
`(Ŝ_tot)² = Ŝ^-_tot Ŝ^+_tot + (Ŝ^z_tot)² + Ŝ^z_tot` plus
`Ŝ^+_tot · |σ_⊤⟩ = 0`.

The spin-`S` extension of Tasaki §2.4 (which treats `S = 1/2` in
detail) and the operator-level form of the saturated-ferromagnetic
ground state on the bipartite Heisenberg model.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Heisenberg-eigenvalue preservation along the lowering ladder

The Heisenberg Hamiltonian commutes with each total-spin axis
operator `Ŝ^{(α)}_tot` (Tasaki §2.4 (2.4.7) operator-level), hence
also with the raising/lowering operators `Ŝ^±_tot`. Iterated
applications of `Ŝ^-_tot` to the highest-weight all-up state therefore
produce eigenvectors of the Heisenberg Hamiltonian at the SAME
eigenvalue, generating the full $J_{\rm tot} = |V|\cdot S$
irreducible representation as Heisenberg eigenstates. Symmetrically,
iterated `Ŝ^+_tot` applied to the all-down state.
-/

/-- The Heisenberg Hamiltonian commutes with `Ŝ^{(1)}_tot`. Restated
from `heisenbergHamiltonianS_commutator_totalSpinSOp1`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOp1
    (J : V → V → ℂ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSOp1 V N) := by
  unfold Commute SemiconjBy
  have h := heisenbergHamiltonianS_commutator_totalSpinSOp1 (Λ := V) J N
  exact sub_eq_zero.mp h

/-- The Heisenberg Hamiltonian commutes with `Ŝ^{(2)}_tot`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOp2
    (J : V → V → ℂ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSOp2 V N) := by
  unfold Commute SemiconjBy
  have h := heisenbergHamiltonianS_commutator_totalSpinSOp2 (Λ := V) J N
  exact sub_eq_zero.mp h

/-- The Heisenberg Hamiltonian commutes with `Ŝ^+_tot`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOpPlus
    (J : V → V → ℂ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSOpPlus V N) := by
  rw [totalSpinSOpPlus_eq_add]
  exact (heisenbergHamiltonianS_commute_totalSpinSOp1 J).add_right
    ((heisenbergHamiltonianS_commute_totalSpinSOp2 J).smul_right Complex.I)

/-- The Heisenberg Hamiltonian commutes with `Ŝ^-_tot`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOpMinus
    (J : V → V → ℂ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSOpMinus V N) := by
  rw [totalSpinSOpMinus_eq_sub]
  exact (heisenbergHamiltonianS_commute_totalSpinSOp1 J).sub_right
    ((heisenbergHamiltonianS_commute_totalSpinSOp2 J).smul_right Complex.I)

/-- The Heisenberg Hamiltonian commutes with `(Ŝ^-_tot)^k` for any
`k : ℕ`, by induction. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOpMinus_pow
    (J : V → V → ℂ) (k : ℕ) :
    Commute (heisenbergHamiltonianS J N)
      ((totalSpinSOpMinus V N) ^ k) := by
  induction k with
  | zero => simp [Commute, SemiconjBy]
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul_right (heisenbergHamiltonianS_commute_totalSpinSOpMinus J)

/-- **Heisenberg eigenvalue preservation along the lowering ladder
from all-up**: for any `k : ℕ`, the iterated lowering
`(Ŝ^-_tot)^k · |σ_⊤⟩` is a Heisenberg eigenvector with the SAME
eigenvalue as `|σ_⊤⟩` itself.

Proof: `[H, Ŝ^-_tot] = 0` ⟹ `H · (Ŝ^-_tot)^k = (Ŝ^-_tot)^k · H`,
combined with `H · |σ_⊤⟩ = E · |σ_⊤⟩`. -/
theorem heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
    (J : V → V → ℂ) (k : ℕ) :
    (heisenbergHamiltonianS J N).mulVec
      (((totalSpinSOpMinus V N) ^ k).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((heisenbergHamiltonianS J N)
        (allAlignedConfigS V N 0) (allAlignedConfigS V N 0)) •
        ((totalSpinSOpMinus V N) ^ k).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1))) := by
  -- H · ((Ŝ^-)^k · |⊤⟩) = ((Ŝ^-)^k · H) · |⊤⟩  by commutation
  --                   = (Ŝ^-)^k · (E • |⊤⟩)   by H eigenvector
  --                   = E • ((Ŝ^-)^k · |⊤⟩).
  have hcomm : heisenbergHamiltonianS J N * ((totalSpinSOpMinus V N) ^ k) =
      ((totalSpinSOpMinus V N) ^ k) * heisenbergHamiltonianS J N :=
    (heisenbergHamiltonianS_commute_totalSpinSOpMinus_pow J k)
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    heisenbergHamiltonianS_mulVec_allAlignedStateS_zero,
    Matrix.mulVec_smul]

/-- The Heisenberg Hamiltonian commutes with `(Ŝ^+_tot)^k` for any
`k : ℕ`, by induction. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOpPlus_pow
    (J : V → V → ℂ) (k : ℕ) :
    Commute (heisenbergHamiltonianS J N)
      ((totalSpinSOpPlus V N) ^ k) := by
  induction k with
  | zero => simp [Commute, SemiconjBy]
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul_right (heisenbergHamiltonianS_commute_totalSpinSOpPlus J)

/-- **Heisenberg eigenvalue preservation along the raising ladder
from all-down**: for any `k : ℕ`, `(Ŝ^+_tot)^k · |σ_⊥⟩` is a Heisenberg
eigenvector with the same eigenvalue as `|σ_⊥⟩`. -/
theorem heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
    (J : V → V → ℂ) (k : ℕ) :
    (heisenbergHamiltonianS J N).mulVec
      (((totalSpinSOpPlus V N) ^ k).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      ((heisenbergHamiltonianS J N)
        (allAlignedConfigS V N (Fin.last N))
        (allAlignedConfigS V N (Fin.last N))) •
        ((totalSpinSOpPlus V N) ^ k).mulVec
          (allAlignedStateS V N (Fin.last N)) := by
  have hcomm : heisenbergHamiltonianS J N * ((totalSpinSOpPlus V N) ^ k) =
      ((totalSpinSOpPlus V N) ^ k) * heisenbergHamiltonianS J N :=
    (heisenbergHamiltonianS_commute_totalSpinSOpPlus_pow J k)
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    heisenbergHamiltonianS_mulVec_allAlignedStateS_last,
    Matrix.mulVec_smul]

/-! ## Casimir-eigenvalue preservation along the iterated ladder

The Casimir `(Ŝ_tot)²` commutes with each `Ŝ^{(α)}_tot` (and hence
with `Ŝ^±_tot`), so iterated `(Ŝ^-_tot)^k` applied to the highest-
weight all-up state preserves the Casimir eigenvalue
`(|V|·N/2)·(|V|·N/2 + 1)`. Symmetric for `(Ŝ^+_tot)^k` on all-down.
-/

/-- The total Casimir `(Ŝ_tot)²` commutes with `Ŝ^{(1)}_tot`. -/
theorem totalSpinSSquared_commute_totalSpinSOp1 :
    Commute (totalSpinSSquared V N) (totalSpinSOp1 V N) := by
  unfold Commute SemiconjBy
  exact sub_eq_zero.mp (totalSpinSSquared_commutator_totalSpinSOp1 V N)

/-- The total Casimir `(Ŝ_tot)²` commutes with `Ŝ^{(2)}_tot`. -/
theorem totalSpinSSquared_commute_totalSpinSOp2 :
    Commute (totalSpinSSquared V N) (totalSpinSOp2 V N) := by
  unfold Commute SemiconjBy
  exact sub_eq_zero.mp (totalSpinSSquared_commutator_totalSpinSOp2 V N)

/-- The total Casimir `(Ŝ_tot)²` commutes with `Ŝ^+_tot`. -/
theorem totalSpinSSquared_commute_totalSpinSOpPlus :
    Commute (totalSpinSSquared V N) (totalSpinSOpPlus V N) := by
  rw [totalSpinSOpPlus_eq_add]
  exact (totalSpinSSquared_commute_totalSpinSOp1).add_right
    ((totalSpinSSquared_commute_totalSpinSOp2).smul_right Complex.I)

/-- The total Casimir `(Ŝ_tot)²` commutes with `Ŝ^-_tot`. -/
theorem totalSpinSSquared_commute_totalSpinSOpMinus :
    Commute (totalSpinSSquared V N) (totalSpinSOpMinus V N) := by
  rw [totalSpinSOpMinus_eq_sub]
  exact (totalSpinSSquared_commute_totalSpinSOp1).sub_right
    ((totalSpinSSquared_commute_totalSpinSOp2).smul_right Complex.I)

/-- The total Casimir commutes with `(Ŝ^-_tot)^k` for any `k : ℕ`. -/
theorem totalSpinSSquared_commute_totalSpinSOpMinus_pow (k : ℕ) :
    Commute (totalSpinSSquared V N) ((totalSpinSOpMinus V N) ^ k) := by
  induction k with
  | zero => simp [Commute, SemiconjBy]
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul_right totalSpinSSquared_commute_totalSpinSOpMinus

/-- The total Casimir commutes with `(Ŝ^+_tot)^k` for any `k : ℕ`. -/
theorem totalSpinSSquared_commute_totalSpinSOpPlus_pow (k : ℕ) :
    Commute (totalSpinSSquared V N) ((totalSpinSOpPlus V N) ^ k) := by
  induction k with
  | zero => simp [Commute, SemiconjBy]
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul_right totalSpinSSquared_commute_totalSpinSOpPlus

/-- **Casimir eigenvalue preservation along the lowering ladder**
from the all-up state: for any `k : ℕ`, the iterated lowering
`(Ŝ^-_tot)^k · |σ_⊤⟩` is a `(Ŝ_tot)²`-eigenvector with the same
eigenvalue `(|V|·N/2)·(|V|·N/2 + 1)`. -/
theorem totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
    [Nonempty V] (k : ℕ) :
    (totalSpinSSquared V N).mulVec
      (((totalSpinSOpMinus V N) ^ k).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) •
        ((totalSpinSOpMinus V N) ^ k).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1))) := by
  have hcomm : totalSpinSSquared V N * ((totalSpinSOpMinus V N) ^ k) =
      ((totalSpinSOpMinus V N) ^ k) * totalSpinSSquared V N :=
    totalSpinSSquared_commute_totalSpinSOpMinus_pow k
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    totalSpinSSquared_mulVec_allAlignedStateS_zero_eigenvalue,
    Matrix.mulVec_smul]

/-- **Casimir eigenvalue preservation along the raising ladder**
from the all-down state. -/
theorem totalSpinSSquared_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
    [Nonempty V] (k : ℕ) :
    (totalSpinSSquared V N).mulVec
      (((totalSpinSOpPlus V N) ^ k).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) •
        ((totalSpinSOpPlus V N) ^ k).mulVec
          (allAlignedStateS V N (Fin.last N)) := by
  have hcomm : totalSpinSSquared V N * ((totalSpinSOpPlus V N) ^ k) =
      ((totalSpinSOpPlus V N) ^ k) * totalSpinSSquared V N :=
    totalSpinSSquared_commute_totalSpinSOpPlus_pow k
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    totalSpinSSquared_mulVec_allAlignedStateS_last_eigenvalue,
    Matrix.mulVec_smul]

/-! ## Multi-site Cartan relations `[Ŝ^z_{tot}, Ŝ^±_{tot}] = ±Ŝ^±_{tot}`

These are the multi-site lift of the single-site Cartan relations
`[Ŝ^z, Ŝ^±] = ±Ŝ^±` (`spinSOp3_commutator_spinSOp{Plus,Minus}` in
`SpinS/Algebra.lean`). They are the operator-level statement that
`Ŝ^+_{tot}` (resp. `Ŝ^-_{tot}`) shifts the magnetic quantum number
by `+1` (resp. `−1`).

These relations are the operator-algebraic input to the
magnetic-quantum-number labelling along the iterated ladder
`(Ŝ^±_{tot})^k`, which identifies the iterated states with the
`m_z`-basis of the `J_{tot} = |V|·S` irreducible SU(2)
representation.
-/

/-- Multi-site Cartan relation:
`[Ŝ^z_{tot}, Ŝ^-_{tot}] = -Ŝ^-_{tot}`.

Proof: lift the single-site Cartan
`[Ŝ^z, Ŝ^-] = -Ŝ^-` (spinSOp3_commutator_spinSOpMinus) to multi-site
via `onSiteS_commutator_totalOnSiteS` (off-site terms vanish, on-site
terms collapse to single-site commutators) summed over `x : V`. -/
theorem totalSpinSOp3_commutator_totalSpinSOpMinus :
    (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpMinus V N -
      totalSpinSOpMinus V N * totalSpinSOp3 V N =
      -totalSpinSOpMinus V N := by
  unfold totalSpinSOp3 totalSpinSOpMinus
  -- LHS = (Σ_x onSiteS x Ŝ^z) * (Σ_y onSiteS y Ŝ^-) -
  --       (Σ_y onSiteS y Ŝ^-) * (Σ_x onSiteS x Ŝ^z)
  -- Distribute outer sums; for each fixed x:
  --   onSiteS x Ŝ^z * (Σ_y onSiteS y Ŝ^-) - (Σ_y onSiteS y Ŝ^-) * onSiteS x Ŝ^z
  --   = onSiteS x [Ŝ^z, Ŝ^-]   (by onSiteS_commutator_totalOnSiteS)
  --   = onSiteS x (-Ŝ^-)
  --   = -onSiteS x Ŝ^-.
  -- Summing over x gives -Σ_x onSiteS x Ŝ^- = -Ŝ^-_{tot}.
  rw [Finset.sum_mul]
  rw [show ((∑ x : V, onSiteS x (spinSOp3 N) * (∑ y : V, onSiteS y (spinSOpMinus N)) :
            ManyBodyOpS V N) -
          (∑ y : V, onSiteS y (spinSOpMinus N)) *
            (∑ x : V, onSiteS x (spinSOp3 N))) =
        ∑ x : V, ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
            (∑ y : V, onSiteS y (spinSOpMinus N)) -
          (∑ y : V, onSiteS y (spinSOpMinus N)) *
            onSiteS x (spinSOp3 N)) from by
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]]
  rw [show (∑ x : V, ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
            (∑ y : V, onSiteS y (spinSOpMinus N)) -
          (∑ y : V, onSiteS y (spinSOpMinus N)) *
            onSiteS x (spinSOp3 N))) =
        ∑ x : V, (onSiteS x (-spinSOpMinus N) : ManyBodyOpS V N) from by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [onSiteS_commutator_totalOnSiteS x (spinSOp3 N) (spinSOpMinus N),
      spinSOp3_commutator_spinSOpMinus]]
  rw [show (∑ x : V, (onSiteS x (-spinSOpMinus N) : ManyBodyOpS V N)) =
        -∑ x : V, (onSiteS x (spinSOpMinus N) : ManyBodyOpS V N) from by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [show (-spinSOpMinus N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
        (-1 : ℂ) • spinSOpMinus N from by rw [neg_one_smul]]
    rw [onSiteS_smul, neg_one_smul]]

/-- Multi-site Cartan relation:
`[Ŝ^z_{tot}, Ŝ^+_{tot}] = +Ŝ^+_{tot}`. Symmetric proof via
`spinSOp3_commutator_spinSOpPlus`. -/
theorem totalSpinSOp3_commutator_totalSpinSOpPlus :
    (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpPlus V N -
      totalSpinSOpPlus V N * totalSpinSOp3 V N =
      totalSpinSOpPlus V N := by
  unfold totalSpinSOp3 totalSpinSOpPlus
  rw [Finset.sum_mul]
  rw [show ((∑ x : V, onSiteS x (spinSOp3 N) * (∑ y : V, onSiteS y (spinSOpPlus N)) :
            ManyBodyOpS V N) -
          (∑ y : V, onSiteS y (spinSOpPlus N)) *
            (∑ x : V, onSiteS x (spinSOp3 N))) =
        ∑ x : V, ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
            (∑ y : V, onSiteS y (spinSOpPlus N)) -
          (∑ y : V, onSiteS y (spinSOpPlus N)) *
            onSiteS x (spinSOp3 N)) from by
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [onSiteS_commutator_totalOnSiteS x (spinSOp3 N) (spinSOpPlus N),
    spinSOp3_commutator_spinSOpPlus]


end LatticeSystem.Quantum
