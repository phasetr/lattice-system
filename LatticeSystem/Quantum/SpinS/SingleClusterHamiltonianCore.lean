import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.MultiSiteMatrixElement
import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.AllAlignedStateExpectations
import LatticeSystem.Quantum.SpinS.SpinSDotAllAlignedZero
import LatticeSystem.Quantum.SpinS.SpinSDotAllAlignedLast

/-!
# Single-cluster (star-graph) Heisenberg Hamiltonian (Tasaki Problem 2.5.a)

Defines `singleClusterHamiltonianS z N` for spin-`S` (with `S = N/2`)
on the `z + 1`-vertex star configuration with central vertex
`0 : Fin (z + 1)` and `z` leaves at sites `1, …, z`:

  `H = Σ_{j ∈ {1, …, z}} Ŝ_0 · Ŝ_j`

(Tasaki Problem 2.5.a, p. 38). Tasaki shows that the ground-state
energy of this Hamiltonian is `−S(1 + zS)`; the proof is deferred to
subsequent γ-5 steps (via Casimir decomposition `H = (1/2)((Ŝ_tot)² −
Ŝ_0² − Ŝ_R²)` where `Ŝ_R = Σ_{j=1}^z Ŝ_j`).

Note: this is the unordered (sum-over-leaves) form, not the ordered
double-sum convention of `heisenbergHamiltonianOnGraphS` over the
star graph (which would double-count each edge at unit coupling).

Tracked as part of γ-5 (Problem 2.5.a) toward Tasaki §2.5
(Issue #412).

This module was restored to the live import graph after the 2026-05-30
orphan-module sweep had removed the earlier single-cluster files.  The
module is now imported from the build root so the Problem 2.5.a framework
is checked by the default build instead of living only as stale
documentation.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- The single-cluster (star) Heisenberg Hamiltonian on `Fin (z + 1)`,
with central vertex `0` and `z` leaves at sites `1, …, z`:

  `H = Σ_{j ∈ {1,…,z}} Ŝ_0 · Ŝ_j`

(Tasaki Problem 2.5.a, p. 38). Tasaki claims the ground-state energy
is `−S(1 + zS)`; the proof is deferred to subsequent γ-5 steps. -/
noncomputable def singleClusterHamiltonianS (N : ℕ) :
    ManyBodyOpS (Fin (z + 1)) N :=
  ∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0, spinSDot 0 j N

/-- The single-cluster Hamiltonian is Hermitian: sum of Hermitian
two-site dot products `spinSDot 0 j N` (γ-5 step 244). -/
theorem singleClusterHamiltonianS_isHermitian (N : ℕ) :
    (singleClusterHamiltonianS z N : ManyBodyOpS (Fin (z + 1)) N).IsHermitian := by
  unfold singleClusterHamiltonianS
  classical
  induction (Finset.univ.erase (0 : Fin (z + 1))) using Finset.induction_on with
  | empty => simp [Matrix.IsHermitian]
  | @insert a t hns ih =>
    rw [Finset.sum_insert hns]
    exact Matrix.IsHermitian.add (spinSDot_isHermitian 0 a N) ih

/-- At `z = 0` (single-vertex configuration), the Hamiltonian is zero
since there are no leaves to couple to: `Finset.univ.erase 0 = ∅` in
`Fin 1`. The expected ground-state energy `−S(1 + 0·S) = −S` is
**not** matched by `0`; this discrepancy reflects that Tasaki's
formula is intended for `z ≥ 1` (γ-5 step 245). -/
theorem singleClusterHamiltonianS_zero_z (N : ℕ) :
    (singleClusterHamiltonianS 0 N : ManyBodyOpS (Fin 1) N) = 0 := by
  unfold singleClusterHamiltonianS
  rw [show (Finset.univ.erase (0 : Fin 1) : Finset (Fin 1)) = ∅ by
    ext j
    simp [Fin.fin_one_eq_zero]]
  exact Finset.sum_empty

/-- The all-up state expectation of the single-cluster Hamiltonian:
`<Φ_⊤ | H | Φ_⊤> = z·(N/2)²` for `H = Σ_{j ≠ 0} Ŝ_0 · Ŝ_j` on
`Fin (z + 1)`.

Each two-site dot product `Ŝ_0 · Ŝ_j` at `j ≠ 0` evaluated on the
constant-`0` (all-up) configuration gives `(N/2 − 0)(N/2 − 0) = (N/2)²`
(via `spinSDot_apply_diag_of_ne`). Sum over `z` leaves gives `z·(N/2)²`.

This is far above Tasaki's true GS energy `−S(1 + zS) = −(N/2)(1 + zN/2)`
since the all-up state is in the maximum-`s_tot` sector (the highest
Casimir energy), not the minimum `s_tot = (z−1)S` sector
(γ-5 step 246). -/
theorem singleClusterHamiltonianS_allUp_expectation (N : ℕ) :
    dotProduct (star (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1))))
        ((singleClusterHamiltonianS z N).mulVec
          (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1)))) =
      (z : ℂ) * ((N : ℂ) / 2) ^ 2 := by
  unfold singleClusterHamiltonianS allAlignedStateS
  rw [Matrix.sum_mulVec, dotProduct_sum]
  have hEach : ∀ j ∈ Finset.univ.erase (0 : Fin (z + 1)),
      dotProduct (star (basisVecS (allAlignedConfigS (Fin (z + 1)) N 0)))
          ((spinSDot 0 j N).mulVec
            (basisVecS (allAlignedConfigS (Fin (z + 1)) N 0))) =
        ((N : ℂ) / 2) ^ 2 := by
    intro j hj
    rw [basisVecS_expectation_eq_diagonal]
    have h0j : (0 : Fin (z + 1)) ≠ j := (Finset.ne_of_mem_erase hj).symm
    rw [spinSDot_apply_diag_of_ne h0j]
    unfold allAlignedConfigS
    simp
    ring
  rw [Finset.sum_congr rfl hEach]
  rw [Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (z + 1))),
    Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-- The all-aligned-`c` expectation of the single-cluster Hamiltonian:
`<Φ_aligned(c) | H | Φ_aligned(c)> = z·(N/2 − c.val)²`. Generalises
γ-5 step 246 (the `c = 0` case, all-up). For `c = Fin.last N` (all-down)
gives the same `z·(N/2)²` since the squared `Ŝ^(3)` eigenvalue is
sign-flip invariant (γ-5 step 247). -/
theorem singleClusterHamiltonianS_allAligned_expectation
    (N : ℕ) (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS (Fin (z + 1)) N c))
        ((singleClusterHamiltonianS z N).mulVec
          (allAlignedStateS (Fin (z + 1)) N c)) =
      (z : ℂ) * ((N : ℂ) / 2 - (c.val : ℂ)) ^ 2 := by
  unfold singleClusterHamiltonianS allAlignedStateS
  rw [Matrix.sum_mulVec, dotProduct_sum]
  have hEach : ∀ j ∈ Finset.univ.erase (0 : Fin (z + 1)),
      dotProduct (star (basisVecS (allAlignedConfigS (Fin (z + 1)) N c)))
          ((spinSDot 0 j N).mulVec
            (basisVecS (allAlignedConfigS (Fin (z + 1)) N c))) =
        ((N : ℂ) / 2 - (c.val : ℂ)) ^ 2 := by
    intro j hj
    rw [basisVecS_expectation_eq_diagonal]
    have h0j : (0 : Fin (z + 1)) ≠ j := (Finset.ne_of_mem_erase hj).symm
    rw [spinSDot_apply_diag_of_ne h0j]
    unfold allAlignedConfigS
    ring
  rw [Finset.sum_congr rfl hEach]
  rw [Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (z + 1))),
    Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-- The all-down state expectation of the single-cluster Hamiltonian:
`<Φ_⊥ | H | Φ_⊥> = z·(N/2)²`. Direct specialisation of γ-5 step 247
at `c = Fin.last N`; the squared `(N/2 − N)² = (N/2)²` matches the
all-up case (γ-5 step 246) (γ-5 step 248). -/
theorem singleClusterHamiltonianS_allDown_expectation (N : ℕ) :
    dotProduct (star (allAlignedStateS (Fin (z + 1)) N (Fin.last N)))
        ((singleClusterHamiltonianS z N).mulVec
          (allAlignedStateS (Fin (z + 1)) N (Fin.last N))) =
      (z : ℂ) * ((N : ℂ) / 2) ^ 2 := by
  rw [singleClusterHamiltonianS_allAligned_expectation]
  rw [show ((Fin.last N).val : ℂ) = (N : ℂ) from by simp [Fin.last]]
  ring

/-! ## Leaf-spin operators (γ-5 step 249)

Define `Ŝ_R^{(α)}`: sum of single-site `Ŝ^{(α)}` over the leaves
`j ∈ univ.erase 0`. These are needed to express the Hamiltonian as
`Ŝ_0 · Ŝ_R = Σ_α onSiteS 0 (Ŝ^(α)) · Ŝ_R^{(α)}` for the Casimir
decomposition `H = (Ŝ_tot² − Ŝ_0² − Ŝ_R²)/2` (subsequent γ-5 steps).
-/

/-- Leaf-spin operator in the 1-axis: `Ŝ_R^(1) = Σ_{j ≠ 0} onSiteS j Ŝ^(1)`
on `Fin (z + 1)`. -/
noncomputable def leafSpinSOp1 (N : ℕ) : ManyBodyOpS (Fin (z + 1)) N :=
  ∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0, onSiteS j (spinSOp1 N)

/-- Leaf-spin operator in the 2-axis: `Ŝ_R^(2) = Σ_{j ≠ 0} onSiteS j Ŝ^(2)`
on `Fin (z + 1)`. -/
noncomputable def leafSpinSOp2 (N : ℕ) : ManyBodyOpS (Fin (z + 1)) N :=
  ∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0, onSiteS j (spinSOp2 N)

/-- Leaf-spin operator in the 3-axis: `Ŝ_R^(3) = Σ_{j ≠ 0} onSiteS j Ŝ^(3)`
on `Fin (z + 1)`. -/
noncomputable def leafSpinSOp3 (N : ℕ) : ManyBodyOpS (Fin (z + 1)) N :=
  ∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0, onSiteS j (spinSOp3 N)

/-- **`Ŝ_0 · Ŝ_R` decomposition** of the single-cluster Hamiltonian:
`H = onSiteS 0 (Ŝ^(1)) * Ŝ_R^(1) + onSiteS 0 (Ŝ^(2)) * Ŝ_R^(2) +
     onSiteS 0 (Ŝ^(3)) * Ŝ_R^(3)`

where `Ŝ_R^(α)` are the leaf-spin operators (γ-5 step 249). Direct
distribution of left multiplication over the sum
`Σ_j (A * B_j) = A * (Σ_j B_j)` (γ-5 step 250). -/
theorem singleClusterHamiltonianS_eq_dot_leaves (N : ℕ) :
    (singleClusterHamiltonianS z N : ManyBodyOpS (Fin (z + 1)) N) =
      onSiteS 0 (spinSOp1 N) * leafSpinSOp1 z N +
        onSiteS 0 (spinSOp2 N) * leafSpinSOp2 z N +
        onSiteS 0 (spinSOp3 N) * leafSpinSOp3 z N := by
  unfold singleClusterHamiltonianS leafSpinSOp1 leafSpinSOp2 leafSpinSOp3
  simp_rw [spinSDot_def]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **Total = central + leaves** (axis 1):
`totalSpinSOp1 (Fin (z + 1)) N = onSiteS 0 (Ŝ^(1)) + leafSpinSOp1 z N`.
Direct from `Finset.sum_eq_sum_diff_singleton_add` on `Finset.univ` with
the singleton `{0}` (γ-5 step 251). -/
theorem totalSpinSOp1_eq_onSite_zero_add_leafSpinSOp1 (N : ℕ) :
    (totalSpinSOp1 (Fin (z + 1)) N : ManyBodyOpS (Fin (z + 1)) N) =
      onSiteS 0 (spinSOp1 N) + leafSpinSOp1 z N := by
  unfold totalSpinSOp1 leafSpinSOp1
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (z + 1))) _
    (Finset.mem_univ 0)]
  exact add_comm _ _

/-- **Total = central + leaves** (axis 2). Spin-`S` mirror of step 251 axis 1. -/
theorem totalSpinSOp2_eq_onSite_zero_add_leafSpinSOp2 (N : ℕ) :
    (totalSpinSOp2 (Fin (z + 1)) N : ManyBodyOpS (Fin (z + 1)) N) =
      onSiteS 0 (spinSOp2 N) + leafSpinSOp2 z N := by
  unfold totalSpinSOp2 leafSpinSOp2
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (z + 1))) _
    (Finset.mem_univ 0)]
  exact add_comm _ _

/-- **Total = central + leaves** (axis 3). -/
theorem totalSpinSOp3_eq_onSite_zero_add_leafSpinSOp3 (N : ℕ) :
    (totalSpinSOp3 (Fin (z + 1)) N : ManyBodyOpS (Fin (z + 1)) N) =
      onSiteS 0 (spinSOp3 N) + leafSpinSOp3 z N := by
  unfold totalSpinSOp3 leafSpinSOp3
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin (z + 1))) _
    (Finset.mem_univ 0)]
  exact add_comm _ _

/-- Leaf-spin Casimir: `Ŝ_R² := (Ŝ_R^(1))² + (Ŝ_R^(2))² + (Ŝ_R^(3))²`,
the total-spin-squared operator restricted to the leaves
`j ∈ univ.erase 0` of `Fin (z + 1)` (γ-5 step 252). -/
noncomputable def leafSpinSSquared (N : ℕ) : ManyBodyOpS (Fin (z + 1)) N :=
  leafSpinSOp1 z N * leafSpinSOp1 z N +
    leafSpinSOp2 z N * leafSpinSOp2 z N +
    leafSpinSOp3 z N * leafSpinSOp3 z N

/-! ## Center-leaf commutativity (γ-5 step 253)

`onSiteS 0 (Ŝ^(α))` commutes with `leafSpinSOp_α z N` since each leaf
operator `onSiteS j (Ŝ^(α))` for `j ≠ 0` acts on a disjoint site.
Crucial for expanding the squared sum `(onSite 0 + leaf)²` in the
Casimir decomposition. -/

/-- `onSiteS 0 (Ŝ^(1))` commutes with `leafSpinSOp1 z N` (γ-5 step 253). -/
theorem onSiteS_zero_commute_leafSpinSOp1 (N : ℕ) :
    Commute (onSiteS 0 (spinSOp1 N) : ManyBodyOpS (Fin (z + 1)) N)
      (leafSpinSOp1 z N) := by
  unfold leafSpinSOp1
  exact Commute.sum_right _ _ _ (fun j hj =>
    onSiteS_commute_of_ne (Finset.ne_of_mem_erase hj).symm _ _)

/-- `onSiteS 0 (Ŝ^(2))` commutes with `leafSpinSOp2 z N` (γ-5 step 253). -/
theorem onSiteS_zero_commute_leafSpinSOp2 (N : ℕ) :
    Commute (onSiteS 0 (spinSOp2 N) : ManyBodyOpS (Fin (z + 1)) N)
      (leafSpinSOp2 z N) := by
  unfold leafSpinSOp2
  exact Commute.sum_right _ _ _ (fun j hj =>
    onSiteS_commute_of_ne (Finset.ne_of_mem_erase hj).symm _ _)

/-- `onSiteS 0 (Ŝ^(3))` commutes with `leafSpinSOp3 z N` (γ-5 step 253). -/
theorem onSiteS_zero_commute_leafSpinSOp3 (N : ℕ) :
    Commute (onSiteS 0 (spinSOp3 N) : ManyBodyOpS (Fin (z + 1)) N)
      (leafSpinSOp3 z N) := by
  unfold leafSpinSOp3
  exact Commute.sum_right _ _ _ (fun j hj =>
    onSiteS_commute_of_ne (Finset.ne_of_mem_erase hj).symm _ _)

/-- Helper: `(a + b)² = a² + 2(a·b) + b²` when `Commute a b`, in the
matrix algebra `ManyBodyOpS`. Pure non-commutative algebra. -/
private theorem add_mul_self_of_commute
    {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
    {a b : ManyBodyOpS V N} (hab : Commute a b) :
    (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [add_mul, mul_add, mul_add]
  rw [show b * a = a * b from hab.symm.eq]
  noncomm_ring

/-- **Casimir decomposition** of the single-cluster Hamiltonian
(γ-5 step 254):
`2 · H = (Ŝ_tot)² − Ŝ_0² − Ŝ_R²`

where `Ŝ_0² := spinSDot 0 0 N` is the single-site Casimir at the
central vertex and `Ŝ_R² := leafSpinSSquared z N` is the leaf Casimir.

Proof: expand `Σ_α totalSpinSOp_α² = Σ_α (onSite 0 + leaf_α)²` using
γ-5 step 251 and γ-5 step 253 (commutativity); the cross term sums to
`2 · H` via γ-5 step 250 (`Ŝ_0 · Ŝ_R` decomposition); the squared
center term sums to `spinSDot 0 0` by definition. -/
theorem singleClusterHamiltonianS_two_mul_eq_casimir_diff
    (N : ℕ) :
    2 * singleClusterHamiltonianS z N =
      totalSpinSSquared (Fin (z + 1)) N -
        spinSDot 0 0 N - leafSpinSSquared z N := by
  rw [singleClusterHamiltonianS_eq_dot_leaves]
  unfold totalSpinSSquared leafSpinSSquared
  rw [totalSpinSOp1_eq_onSite_zero_add_leafSpinSOp1,
    totalSpinSOp2_eq_onSite_zero_add_leafSpinSOp2,
    totalSpinSOp3_eq_onSite_zero_add_leafSpinSOp3]
  rw [add_mul_self_of_commute (onSiteS_zero_commute_leafSpinSOp1 (z := z) N),
    add_mul_self_of_commute (onSiteS_zero_commute_leafSpinSOp2 (z := z) N),
    add_mul_self_of_commute (onSiteS_zero_commute_leafSpinSOp3 (z := z) N)]
  -- Now LHS = 2 · (onSite 0 Ŝ^1 · leaf_1 + onSite 0 Ŝ^2 · leaf_2 + onSite 0 Ŝ^3 · leaf_3)
  -- RHS = (Σ_α (onSite 0 Ŝ^α)² + 2(onSite 0 Ŝ^α · leaf_α) + leaf_α²)
  --      − (onSite 0 Ŝ^1·onSite 0 Ŝ^1 + onSite 0 Ŝ^2·onSite 0 Ŝ^2 + onSite 0 Ŝ^3·onSite 0 Ŝ^3)
  --      − (leaf_1² + leaf_2² + leaf_3²)
  unfold spinSDot
  noncomm_ring

/-- **Casimir decomposition** ℂ-smul form:
`(2 : ℂ) • H = (Ŝ_tot)² − Ŝ_0² − Ŝ_R²`.
Direct corollary of γ-5 step 254 (γ-5 step 255). -/
theorem singleClusterHamiltonianS_two_smul_eq_casimir_diff (N : ℕ) :
    (2 : ℂ) • (singleClusterHamiltonianS z N : ManyBodyOpS (Fin (z + 1)) N) =
      totalSpinSSquared (Fin (z + 1)) N -
        spinSDot 0 0 N - leafSpinSSquared z N := by
  have h := singleClusterHamiltonianS_two_mul_eq_casimir_diff (z := z) N
  rw [show (2 : ℂ) • (singleClusterHamiltonianS z N : ManyBodyOpS (Fin (z + 1)) N) =
      (2 : ManyBodyOpS (Fin (z + 1)) N) * singleClusterHamiltonianS z N from by
    rw [two_mul, two_smul]]
  exact h

/-- **Casimir decomposition expectation form** (γ-5 step 256):
`2 · <v | H | v> = <v | Ŝ_tot² | v> − <v | Ŝ_0² | v> − <v | Ŝ_R² | v>`

for any vector `v`. Direct corollary of γ-5 step 255 (ℂ-smul form) +
linearity of `dotProduct` and `mulVec` over `smul` and subtraction.
Bridges the operator-level Casimir decomposition to
expectation-value calculations. -/
theorem singleClusterHamiltonianS_two_mul_expectation
    (N : ℕ) (v : (Fin (z + 1) → Fin (N + 1)) → ℂ) :
    2 * dotProduct (star v)
        ((singleClusterHamiltonianS z N).mulVec v) =
      dotProduct (star v)
        ((totalSpinSSquared (Fin (z + 1)) N).mulVec v) -
      dotProduct (star v) ((spinSDot 0 0 N).mulVec v) -
      dotProduct (star v) ((leafSpinSSquared z N).mulVec v) := by
  have h := singleClusterHamiltonianS_two_smul_eq_casimir_diff (z := z) N
  have hv := congrArg (fun M => dotProduct (star v) (M.mulVec v)) h
  simp only at hv
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hv
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, dotProduct_sub, dotProduct_sub] at hv
  exact hv

/-- **Single-site Casimir expectation** (γ-5 step 257):
`<v | spinSDot x x N | v> = (N(N+2)/4) · <v | v>` for any vector `v`
and any site `x`. Direct from `spinSDot_self : spinSDot x x N =
(N(N+2)/4) • 1` + linearity. -/
theorem spinSDot_self_expectation_general
    {V : Type*} [Fintype V] [DecidableEq V] (N : ℕ)
    (x : V) (v : (V → Fin (N + 1)) → ℂ) :
    dotProduct (star v) ((spinSDot x x N).mulVec v) =
      ((N : ℂ) * ((N : ℂ) + 2) / 4) *
        dotProduct (star v) v := by
  rw [spinSDot_self, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- **Simplified Casimir expectation form** (γ-5 step 258):
`2 · <v | H | v> = <v | Ŝ_tot² | v> − (N(N+2)/4)·<v|v> − <v | Ŝ_R² | v>`.

Combines γ-5 step 256 (Casimir decomposition expectation) with γ-5 step 257
(`<v|S0²|v> = (N(N+2)/4)·<v|v>`). The `Ŝ_0²` term is now a fixed scalar
multiple of the norm-squared. -/
theorem singleClusterHamiltonianS_two_mul_expectation_simplified
    (N : ℕ) (v : (Fin (z + 1) → Fin (N + 1)) → ℂ) :
    2 * dotProduct (star v)
        ((singleClusterHamiltonianS z N).mulVec v) =
      dotProduct (star v)
        ((totalSpinSSquared (Fin (z + 1)) N).mulVec v) -
      ((N : ℂ) * ((N : ℂ) + 2) / 4) * dotProduct (star v) v -
      dotProduct (star v) ((leafSpinSSquared z N).mulVec v) := by
  rw [singleClusterHamiltonianS_two_mul_expectation,
    spinSDot_self_expectation_general]

end LatticeSystem.Quantum
