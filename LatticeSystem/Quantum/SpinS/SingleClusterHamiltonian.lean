import LatticeSystem.Quantum.SpinS.MultiSiteDot
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

/-- **H eigenvalue from Casimir eigenvalues** (γ-5 step 259):
if `v` is a joint eigenvector of `Ŝ_tot²` (eigenvalue `α`) and `Ŝ_R²`
(eigenvalue `β`), then `v` is an `H`-eigenvector with eigenvalue
`(α − N(N+2)/4 − β)/2`.

Direct from γ-5 step 255 (ℂ-smul Casimir form) + linearity of `mulVec`. -/
theorem singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (N : ℕ) {α β : ℂ} {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v = α • v)
    (hR : (leafSpinSSquared z N).mulVec v = β • v) :
    (singleClusterHamiltonianS z N).mulVec v =
      ((α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) / 2) • v := by
  have h := singleClusterHamiltonianS_two_smul_eq_casimir_diff (z := z) N
  have hv := congrArg (fun M => M.mulVec v) h
  simp only at hv
  rw [Matrix.smul_mulVec] at hv
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec] at hv
  rw [htot, hR] at hv
  -- v · spinSDot 0 0 = (N(N+2)/4) • v
  rw [show (spinSDot (0 : Fin (z + 1)) 0 N).mulVec v =
      ((N : ℂ) * ((N : ℂ) + 2) / 4) • v from by
    rw [spinSDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]] at hv
  -- hv: 2 • H.mulVec v = α • v - (N(N+2)/4) • v - β • v
  rw [show ((α : ℂ) • v - ((N : ℂ) * ((N : ℂ) + 2) / 4) • v - β • v) =
      (α - (N : ℂ) * ((N : ℂ) + 2) / 4 - β) • v from by
    rw [sub_smul, sub_smul]] at hv
  -- hv: (2 : ℂ) • H.mulVec v = (α - (N(N+2)/4) - β) • v
  -- Goal: H.mulVec v = ((α - (N(N+2)/4) - β) / 2) • v.
  -- Multiply both sides of hv by (1/2 : ℂ).
  have hv' := congrArg (((1 / 2 : ℂ)) • ·) hv
  simp only at hv'
  rw [smul_smul, smul_smul] at hv'
  rw [show ((1 / 2 : ℂ) * 2) = 1 from by norm_num] at hv'
  rw [one_smul] at hv'
  rw [hv']
  congr 1
  ring

/-- **Single-site Casimir as scalar action** (γ-5 step 260):
`spinSDot x x N · v = (N(N+2)/4) • v` for any vector `v` and any
site `x`. Direct from `spinSDot_self : spinSDot x x N = (N(N+2)/4) • 1`
+ `Matrix.smul_mulVec` + `Matrix.one_mulVec`. -/
theorem spinSDot_self_mulVec_eq_smul
    {V : Type*} [Fintype V] [DecidableEq V] (N : ℕ)
    (x : V) (v : (V → Fin (N + 1)) → ℂ) :
    (spinSDot x x N).mulVec v =
      ((N : ℂ) * ((N : ℂ) + 2) / 4) • v := by
  rw [spinSDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Edge case: `leafSpinSOp1 0 N = 0` (no leaves on `Fin 1`) (γ-5 step 261). -/
theorem leafSpinSOp1_zero_z (N : ℕ) :
    (leafSpinSOp1 0 N : ManyBodyOpS (Fin 1) N) = 0 := by
  unfold leafSpinSOp1
  rw [show (Finset.univ.erase (0 : Fin 1) : Finset (Fin 1)) = ∅ by
    ext j; simp [Fin.fin_one_eq_zero]]
  exact Finset.sum_empty

/-- Edge case: `leafSpinSOp2 0 N = 0` (γ-5 step 261). -/
theorem leafSpinSOp2_zero_z (N : ℕ) :
    (leafSpinSOp2 0 N : ManyBodyOpS (Fin 1) N) = 0 := by
  unfold leafSpinSOp2
  rw [show (Finset.univ.erase (0 : Fin 1) : Finset (Fin 1)) = ∅ by
    ext j; simp [Fin.fin_one_eq_zero]]
  exact Finset.sum_empty

/-- Edge case: `leafSpinSOp3 0 N = 0` (γ-5 step 261). -/
theorem leafSpinSOp3_zero_z (N : ℕ) :
    (leafSpinSOp3 0 N : ManyBodyOpS (Fin 1) N) = 0 := by
  unfold leafSpinSOp3
  rw [show (Finset.univ.erase (0 : Fin 1) : Finset (Fin 1)) = ∅ by
    ext j; simp [Fin.fin_one_eq_zero]]
  exact Finset.sum_empty

/-- Edge case: `leafSpinSSquared 0 N = 0` for the single-vertex
configuration (no leaves). Direct from γ-5 step 261 axis-wise vanishing. -/
theorem leafSpinSSquared_zero_z (N : ℕ) :
    (leafSpinSSquared 0 N : ManyBodyOpS (Fin 1) N) = 0 := by
  unfold leafSpinSSquared
  rw [leafSpinSOp1_zero_z, leafSpinSOp2_zero_z, leafSpinSOp3_zero_z]
  simp

/-- **`leafSpinSSquared` as double sum**:
`leafSpinSSquared z N = Σ_{j,k ∈ univ.erase 0} spinSDot j k N` on
`Fin (z + 1)`. Direct expansion of `Σ_α (Σ_j onSite j Ŝ^α)²` using
`spinSDot_def` (γ-5 step 262). -/
theorem leafSpinSSquared_eq_sum_spinSDot (N : ℕ) :
    (leafSpinSSquared z N : ManyBodyOpS (Fin (z + 1)) N) =
      ∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
        ∑ k ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
          spinSDot j k N := by
  unfold leafSpinSSquared leafSpinSOp1 leafSpinSOp2 leafSpinSOp3
  simp_rw [spinSDot_def]
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [show (∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
        ∑ k ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
          (onSiteS j (spinSOp1 N) * onSiteS k (spinSOp1 N) +
            onSiteS j (spinSOp2 N) * onSiteS k (spinSOp2 N) +
            onSiteS j (spinSOp3 N) * onSiteS k (spinSOp3 N))) =
      (∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
        ∑ k ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
          onSiteS j (spinSOp1 N) * onSiteS k (spinSOp1 N)) +
      (∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
        ∑ k ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
          onSiteS j (spinSOp2 N) * onSiteS k (spinSOp2 N)) +
      (∑ j ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
        ∑ k ∈ (Finset.univ : Finset (Fin (z + 1))).erase 0,
          onSiteS j (spinSOp3 N) * onSiteS k (spinSOp3 N)) from by
    simp_rw [Finset.sum_add_distrib]]

/-- **All-up expectation of `leafSpinSSquared`**:
`<Φ_⊤ | leafSpinSSquared z N | Φ_⊤> = (zN/2)·(zN/2 + 1) = s_R(s_R+1)`
where `s_R = z·(N/2)` is the maximum total leaf spin (γ-5 step 263).

Computed via rearranging γ-5 step 254 (Casimir decomposition):
`SR² = Stot² − S0² − 2·H`, and applying:
- existing `totalSpinSSquared_mulVec_allAlignedStateS_zero_eigenvalue`:
  `<Φ_⊤|Stot²|Φ_⊤> = m_max(m_max+1)` with `m_max = (z+1)·N/2`.
- γ-5 step 257: `<Φ_⊤|S0²|Φ_⊤> = N(N+2)/4 · <Φ_⊤|Φ_⊤> = N(N+2)/4`.
- γ-5 step 246: `<Φ_⊤|H|Φ_⊤> = z·(N/2)²`.

Verifying: `m_max(m_max+1) − N(N+2)/4 − 2·z·(N/2)²
  = ((z+1)N/2)((z+1)N/2+1) − N(N+2)/4 − zN²/2 = (zN/2)(zN/2+1)`. -/
theorem leafSpinSSquared_allUp_expectation (N : ℕ) [Nonempty (Fin (z + 1))] :
    dotProduct (star (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1))))
        ((leafSpinSSquared z N).mulVec
          (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1)))) =
      ((z : ℂ) * (N : ℂ) / 2) * ((z : ℂ) * (N : ℂ) / 2 + 1) := by
  -- From step 256 expectation form: 2 <H> = <Stot²> - <S0²> - <SR²>.
  -- Compute each closed form, then combine.
  have hStot : dotProduct (star (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1))))
        ((totalSpinSSquared (Fin (z + 1)) N).mulVec
          (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1)))) =
      (((z : ℂ) + 1) * (N : ℂ) / 2) *
        (((z : ℂ) + 1) * (N : ℂ) / 2 + 1) := by
    have := allAlignedStateS_zero_expectation_totalSpinSSquared
      (V := Fin (z + 1)) (N := N)
    rw [Fintype.card_fin] at this
    push_cast at this
    exact this
  have hS0 : dotProduct (star (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1))))
        ((spinSDot 0 0 N).mulVec
          (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1)))) =
      (N : ℂ) * ((N : ℂ) + 2) / 4 := by
    rw [spinSDot_self_expectation_general, allAlignedStateS_inner_self, mul_one]
  have hH := singleClusterHamiltonianS_allUp_expectation (z := z) N
  have h := singleClusterHamiltonianS_two_mul_expectation (z := z) N
    (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1)))
  linear_combination h + hStot - hS0 - 2 * hH

/-- **Eigenvector form on allUp**: `singleClusterHamiltonianS z N · |Φ_⊤⟩ =
z·(N/2)² · |Φ_⊤⟩`. The all-up state is an `H`-eigenvector with
eigenvalue `z·(N/2)²` (γ-5 step 264).

Proof: each `spinSDot 0 j` for `j ≠ 0` acts as `(N/2)²·1` on `|Φ_⊤⟩`
(via `spinSDot_mulVec_allAlignedStateS_zero_of_ne`); sum over `z` leaves. -/
theorem singleClusterHamiltonianS_mulVec_allAlignedStateS_zero (N : ℕ) :
    (singleClusterHamiltonianS z N).mulVec
        (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1))) =
      ((z : ℂ) * (N : ℂ) ^ 2 / 4) •
        allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1)) := by
  unfold singleClusterHamiltonianS
  rw [Matrix.sum_mulVec]
  have hEach : ∀ j ∈ Finset.univ.erase (0 : Fin (z + 1)),
      (spinSDot 0 j N).mulVec
          (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1))) =
        ((N : ℂ) * (N : ℂ) / 4) •
          allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1)) := by
    intros j hj
    have h0j : (0 : Fin (z + 1)) ≠ j := (Finset.ne_of_mem_erase hj).symm
    exact spinSDot_mulVec_allAlignedStateS_zero_of_ne h0j
  rw [Finset.sum_congr rfl hEach]
  rw [← Finset.sum_smul]
  rw [Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (z + 1))),
    Finset.card_univ, Fintype.card_fin]
  rw [show z + 1 - 1 = z from by omega]
  rw [show (z : ℕ) • ((N : ℂ) * (N : ℂ) / 4) =
      ((z : ℂ) * (N : ℂ) ^ 2 / 4 : ℂ) from by
    rw [nsmul_eq_mul]; ring]

/-- **Eigenvector form on allUp** (γ-5 step 265):
`leafSpinSSquared z N · |Φ_⊤⟩ = (zN/2)·(zN/2 + 1) · |Φ_⊤⟩`.

Witnesses that `|Φ_⊤⟩` is in the maximum-leaf-spin Casimir sector
`s_R = zN/2`. Combined with γ-5 step 264 and existing `Stot²`
eigenvector identity, confirms `|Φ_⊤⟩` is a joint eigenstate of
`H, Stot², S_0², S_R²`.

Proof: rearrange γ-5 step 255 (ℂ-smul Casimir form) to express
`SR² = Stot² − S0² − (2:ℂ) • H`, apply to `|Φ_⊤⟩` using existing
eigenvector identities, then collect scalar coefficients via
`smul_smul + sub_smul`. -/
theorem leafSpinSSquared_mulVec_allAlignedStateS_zero
    (N : ℕ) [Nonempty (Fin (z + 1))] :
    (leafSpinSSquared z N).mulVec
        (allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1))) =
      ((z : ℂ) * (N : ℂ) / 2 * ((z : ℂ) * (N : ℂ) / 2 + 1)) •
        allAlignedStateS (Fin (z + 1)) N (0 : Fin (N + 1)) := by
  have h := singleClusterHamiltonianS_two_smul_eq_casimir_diff (z := z) N
  -- Rearrange: (2:ℂ)•H = Stot² − S0² − SR² → SR² = Stot² − S0² − (2:ℂ)•H.
  have hSR : leafSpinSSquared z N =
      totalSpinSSquared (Fin (z + 1)) N - spinSDot 0 0 N -
        (2 : ℂ) • singleClusterHamiltonianS z N := by
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq']
    exact h
  rw [hSR, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
  rw [totalSpinSSquared_mulVec_allAlignedStateS_zero_eigenvalue,
    spinSDot_self_mulVec_eq_smul,
    singleClusterHamiltonianS_mulVec_allAlignedStateS_zero]
  rw [Fintype.card_fin]
  rw [smul_smul, ← sub_smul, ← sub_smul]
  congr 1
  push_cast
  ring

/-- **Eigenvector form on allDown** (γ-5 step 266):
`singleClusterHamiltonianS z N · |Φ_⊥⟩ = z·(N/2)² · |Φ_⊥⟩`.

The all-down state is also an `H`-eigenvector with the same eigenvalue
`z·(N/2)²` as `|Φ_⊤⟩` (γ-5 step 264). This reflects the spin-flip
symmetry of the Heisenberg Hamiltonian. -/
theorem singleClusterHamiltonianS_mulVec_allAlignedStateS_last (N : ℕ) :
    (singleClusterHamiltonianS z N).mulVec
        (allAlignedStateS (Fin (z + 1)) N (Fin.last N)) =
      ((z : ℂ) * (N : ℂ) ^ 2 / 4) •
        allAlignedStateS (Fin (z + 1)) N (Fin.last N) := by
  unfold singleClusterHamiltonianS
  rw [Matrix.sum_mulVec]
  have hEach : ∀ j ∈ Finset.univ.erase (0 : Fin (z + 1)),
      (spinSDot 0 j N).mulVec
          (allAlignedStateS (Fin (z + 1)) N (Fin.last N)) =
        ((N : ℂ) * (N : ℂ) / 4) •
          allAlignedStateS (Fin (z + 1)) N (Fin.last N) := by
    intros j hj
    have h0j : (0 : Fin (z + 1)) ≠ j := (Finset.ne_of_mem_erase hj).symm
    exact spinSDot_mulVec_allAlignedStateS_last_of_ne h0j
  rw [Finset.sum_congr rfl hEach]
  rw [← Finset.sum_smul]
  rw [Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin (z + 1))),
    Finset.card_univ, Fintype.card_fin]
  rw [show z + 1 - 1 = z from by omega]
  rw [show (z : ℕ) • ((N : ℂ) * (N : ℂ) / 4) =
      ((z : ℂ) * (N : ℂ) ^ 2 / 4 : ℂ) from by
    rw [nsmul_eq_mul]; ring]

/-- **Eigenvector form on allDown** (γ-5 step 267, allDown mirror of γ-5 step 265):
`leafSpinSSquared z N · |Φ_⊥⟩ = (zN/2)·(zN/2 + 1) · |Φ_⊥⟩`.

Same Casimir eigenvalue as `|Φ_⊤⟩` (both states are in the
maximum-leaf-spin Casimir sector `s_R = zN/2`, just differing by total
`Ŝ_tot^(3)` magnetization). -/
theorem leafSpinSSquared_mulVec_allAlignedStateS_last
    (N : ℕ) [Nonempty (Fin (z + 1))] :
    (leafSpinSSquared z N).mulVec
        (allAlignedStateS (Fin (z + 1)) N (Fin.last N)) =
      ((z : ℂ) * (N : ℂ) / 2 * ((z : ℂ) * (N : ℂ) / 2 + 1)) •
        allAlignedStateS (Fin (z + 1)) N (Fin.last N) := by
  have h := singleClusterHamiltonianS_two_smul_eq_casimir_diff (z := z) N
  have hSR : leafSpinSSquared z N =
      totalSpinSSquared (Fin (z + 1)) N - spinSDot 0 0 N -
        (2 : ℂ) • singleClusterHamiltonianS z N := by
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq']
    exact h
  rw [hSR, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
  rw [totalSpinSSquared_mulVec_allAlignedStateS_last_eigenvalue,
    spinSDot_self_mulVec_eq_smul,
    singleClusterHamiltonianS_mulVec_allAlignedStateS_last]
  rw [Fintype.card_fin]
  rw [smul_smul, ← sub_smul, ← sub_smul]
  congr 1
  push_cast
  ring

/-- **GS-sector eigenvalue specialisation** (γ-5 step 268):
if `v` is a joint eigenvector of `Ŝ_tot²` (eigenvalue
`((z−1)·N/2)·((z−1)·N/2 + 1)`) and `Ŝ_R²` (eigenvalue
`(z·N/2)·(z·N/2 + 1)`), then `v` is an `H`-eigenvector with eigenvalue
`−(N/2)·(z·N/2 + 1) = −S(1 + zS)` where `S = N/2`.

Specialisation of γ-5 step 259 to the ground-state Casimir sector
predicted by Tasaki Problem 2.5.a. The eigenvector is *not* one of the
extremal aligned states `|Φ_⊤⟩, |Φ_⊥⟩` (which sit at `s_tot = (z+1)N/2`,
the maximum sector). Constructing an actual joint eigenstate at this
sector requires SU(2) representation theory (Clebsch–Gordan
decomposition), deferred to a later γ-5 phase. -/
theorem singleClusterHamiltonianS_eigenvalue_at_gs_casimir_sector
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 * ((z : ℂ) * (N : ℂ) / 2 + 1)) • v) :
    (singleClusterHamiltonianS z N).mulVec v =
      (-((N : ℂ) / 2) * ((z : ℂ) * (N : ℂ) / 2 + 1)) • v := by
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := z) N htot hR
  rw [h]
  congr 1
  ring

/-- **Max-Casimir-sector eigenvalue specialisation** (γ-5 step 269):
if `v` is a joint eigenvector of `Ŝ_tot²` (eigenvalue
`((z+1)·N/2)·((z+1)·N/2 + 1)`) and `Ŝ_R²` (eigenvalue
`(z·N/2)·(z·N/2 + 1)`), then `v` is an `H`-eigenvector with eigenvalue
`z·(N/2)² = zS²` where `S = N/2`.

Specialisation of γ-5 step 259 to the maximum Casimir sector — the
sector containing both extremal aligned states `|Φ_⊤⟩, |Φ_⊥⟩` (cf. γ-5
steps 264–267). This is the *highest* `H`-eigenvalue compatible with
the maximum `Ŝ_R²` Casimir; the *lowest* (Tasaki Problem 2.5.a target)
is at the `(z−1)·N/2` total-spin sector and given by γ-5 step 268. -/
theorem singleClusterHamiltonianS_eigenvalue_at_max_casimir_sector
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) + 1) * (N : ℂ) / 2 *
            (((z : ℂ) + 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 * ((z : ℂ) * (N : ℂ) / 2 + 1)) • v) :
    (singleClusterHamiltonianS z N).mulVec v =
      ((z : ℂ) * (N : ℂ) ^ 2 / 4) • v := by
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := z) N htot hR
  rw [h]
  congr 1
  ring

/-- **Predicted ground-state energy** (γ-5 step 270, Tasaki Problem 2.5.a):
`singleClusterGSEnergyS z N = −(N/2)·(z·N/2 + 1) = −S(1 + zS)` for
spin `S = N/2`.

This is the target eigenvalue of the single-cluster Heisenberg
Hamiltonian `H = Σ_{j=1}^z Ŝ_0 · Ŝ_j` at the GS Casimir sector
`(s_0, s_R, s_tot) = (N/2, zN/2, (z−1)N/2)` (cf. γ-5 step 268).
-/
@[simp] noncomputable def singleClusterGSEnergyS (z N : ℕ) : ℂ :=
  -((N : ℂ) / 2) * ((z : ℂ) * (N : ℂ) / 2 + 1)

/-- **Named GS-sector eigenvalue identity** (γ-5 step 270):
restate γ-5 step 268 using the predicted GS energy
`singleClusterGSEnergyS`. For a joint eigenvector `v` at
`Stot² = ((z−1)N/2)((z−1)N/2+1)`, `SR² = (zN/2)(zN/2+1)`:
`H · v = singleClusterGSEnergyS z N • v`. -/
theorem singleClusterHamiltonianS_mulVec_eq_gs_energy_smul
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) - 1) * (N : ℂ) / 2 *
            (((z : ℂ) - 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 * ((z : ℂ) * (N : ℂ) / 2 + 1)) • v) :
    (singleClusterHamiltonianS z N).mulVec v =
      singleClusterGSEnergyS z N • v := by
  unfold singleClusterGSEnergyS
  exact singleClusterHamiltonianS_eigenvalue_at_gs_casimir_sector
    (z := z) N htot hR

/-- **Predicted maximum-Casimir-sector energy** (γ-5 step 271):
`singleClusterMaxEnergyS z N := z·(N/2)² = zS²` for spin `S = N/2`.

The `H`-eigenvalue at the maximum Casimir sector
`(s_R, s_tot) = (zN/2, (z+1)N/2)` containing both extremal aligned
states `|Φ_⊤⟩, |Φ_⊥⟩` (γ-5 steps 264, 266). -/
@[simp] noncomputable def singleClusterMaxEnergyS (z N : ℕ) : ℂ :=
  (z : ℂ) * (N : ℂ) ^ 2 / 4

/-- **Named max-Casimir-sector eigenvalue identity** (γ-5 step 271):
restate γ-5 step 269 using `singleClusterMaxEnergyS`. For a joint
eigenvector `v` at `Stot² = ((z+1)N/2)((z+1)N/2+1)`,
`SR² = (zN/2)(zN/2+1)`:
`H · v = singleClusterMaxEnergyS z N • v`. -/
theorem singleClusterHamiltonianS_mulVec_eq_max_energy_smul
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        (((z : ℂ) + 1) * (N : ℂ) / 2 *
            (((z : ℂ) + 1) * (N : ℂ) / 2 + 1)) • v)
    (hR : (leafSpinSSquared z N).mulVec v =
        ((z : ℂ) * (N : ℂ) / 2 * ((z : ℂ) * (N : ℂ) / 2 + 1)) • v) :
    (singleClusterHamiltonianS z N).mulVec v =
      singleClusterMaxEnergyS z N • v := by
  unfold singleClusterMaxEnergyS
  exact singleClusterHamiltonianS_eigenvalue_at_max_casimir_sector
    (z := z) N htot hR

/-- **GS energy real-part sign** (γ-5 step 272):
`Re(singleClusterGSEnergyS z N) ≤ 0` for all `z, N : ℕ`.

This is the physical AFM ground-state energy bound: an antiferromagnetic
Heisenberg cluster has a non-positive ground-state energy. -/
theorem singleClusterGSEnergyS_re_le_zero (z N : ℕ) :
    (singleClusterGSEnergyS z N).re ≤ 0 := by
  have hcast : singleClusterGSEnergyS z N =
      ((-((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
    unfold singleClusterGSEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]
  have h1 : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have h2 : (0 : ℝ) ≤ (z : ℝ) * (N : ℝ) / 2 + 1 := by positivity
  nlinarith [mul_nonneg h1 h2]

/-- **Max-Casimir-sector energy real-part sign** (γ-5 step 272):
`0 ≤ Re(singleClusterMaxEnergyS z N)` for all `z, N : ℕ`.

The maximum Casimir sector contains the extremal aligned states `|Φ_⊤⟩`,
`|Φ_⊥⟩`, whose `H`-eigenvalue `z·(N/2)²` is non-negative. -/
theorem singleClusterMaxEnergyS_re_nonneg (z N : ℕ) :
    0 ≤ (singleClusterMaxEnergyS z N).re := by
  have hcast : singleClusterMaxEnergyS z N =
      (((z : ℝ) * (N : ℝ) ^ 2 / 4 : ℝ) : ℂ) := by
    unfold singleClusterMaxEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]
  positivity

/-- **GS energy ≤ Max energy** (γ-5 step 273):
`Re(singleClusterGSEnergyS z N) ≤ Re(singleClusterMaxEnergyS z N)`.

Consistency check that the two named eigenvalues from γ-5 steps 268, 269
sit in the correct order: the GS-sector eigenvalue lies (weakly) below
the maximum-Casimir-sector eigenvalue. The gap closes only at `N = 0`
(spin-`0` trivial case). -/
theorem singleClusterGSEnergyS_re_le_singleClusterMaxEnergyS_re (z N : ℕ) :
    (singleClusterGSEnergyS z N).re ≤ (singleClusterMaxEnergyS z N).re := by
  have hg : (singleClusterGSEnergyS z N).re =
      -((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) := by
    have hcast : singleClusterGSEnergyS z N =
        ((-((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
      unfold singleClusterGSEnergyS; push_cast; ring
    rw [hcast, Complex.ofReal_re]
  have hm : (singleClusterMaxEnergyS z N).re =
      (z : ℝ) * (N : ℝ) ^ 2 / 4 := by
    have hcast : singleClusterMaxEnergyS z N =
        (((z : ℝ) * (N : ℝ) ^ 2 / 4 : ℝ) : ℂ) := by
      unfold singleClusterMaxEnergyS; push_cast; ring
    rw [hcast, Complex.ofReal_re]
  rw [hg, hm]
  have h1 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (z : ℝ) * (N : ℝ) + 1 := by positivity
  nlinarith [mul_nonneg h1 h2]

/-- **GS energy is real** (γ-5 step 274):
`Im(singleClusterGSEnergyS z N) = 0`. The Hermitian Hamiltonian has
real eigenvalues, in particular the Tasaki Problem 2.5.a target. -/
theorem singleClusterGSEnergyS_im_zero (z N : ℕ) :
    (singleClusterGSEnergyS z N).im = 0 := by
  have hcast : singleClusterGSEnergyS z N =
      ((-((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
    unfold singleClusterGSEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_im]

/-- **Max-Casimir-sector energy is real** (γ-5 step 274):
`Im(singleClusterMaxEnergyS z N) = 0`. -/
theorem singleClusterMaxEnergyS_im_zero (z N : ℕ) :
    (singleClusterMaxEnergyS z N).im = 0 := by
  have hcast : singleClusterMaxEnergyS z N =
      (((z : ℝ) * (N : ℝ) ^ 2 / 4 : ℝ) : ℂ) := by
    unfold singleClusterMaxEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_im]

/-- **Dimer (z=1) ground-state energy** (γ-5 step 275):
`singleClusterGSEnergyS 1 N = −(N/2)·(N/2 + 1) = −S(S+1)` for `S = N/2`.

The canonical singlet eigenvalue of `Ŝ_0 · Ŝ_1` for two spin-`S` sites,
specialisation of γ-5 step 270 at `z = 1`. -/
theorem singleClusterGSEnergyS_one_eq (N : ℕ) :
    singleClusterGSEnergyS 1 N = -((N : ℂ) / 2) * ((N : ℂ) / 2 + 1) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Dimer (z=1) maximum-Casimir-sector energy** (γ-5 step 275):
`singleClusterMaxEnergyS 1 N = (N/2)² = S²` for `S = N/2`.

The canonical triplet eigenvalue of `Ŝ_0 · Ŝ_1` for two spin-`S` sites,
specialisation of γ-5 step 271 at `z = 1`. -/
theorem singleClusterMaxEnergyS_one_eq (N : ℕ) :
    singleClusterMaxEnergyS 1 N = ((N : ℂ) / 2) ^ 2 := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Trivial GS energy at N=0** (γ-5 step 276):
`singleClusterGSEnergyS z 0 = 0`. The spin-0 trivial case. -/
@[simp] theorem singleClusterGSEnergyS_zero_right (z : ℕ) :
    singleClusterGSEnergyS z 0 = 0 := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Trivial max-Casimir-sector energy at N=0** (γ-5 step 276):
`singleClusterMaxEnergyS z 0 = 0`. The spin-0 trivial case. -/
@[simp] theorem singleClusterMaxEnergyS_zero_right (z : ℕ) :
    singleClusterMaxEnergyS z 0 = 0 := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Trivial max-Casimir-sector energy at z=0** (γ-5 step 276):
`singleClusterMaxEnergyS 0 N = 0`. The single-site cluster (no leaves)
case. -/
@[simp] theorem singleClusterMaxEnergyS_zero_left (N : ℕ) :
    singleClusterMaxEnergyS 0 N = 0 := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **GS energy real-part closed form** (γ-5 step 278):
`Re(singleClusterGSEnergyS z N) = -(N/2)·(zN/2 + 1)` as an `ℝ` value.

Useful as a simp lemma for downstream real comparisons. -/
theorem singleClusterGSEnergyS_re_eq (z N : ℕ) :
    (singleClusterGSEnergyS z N).re =
      -((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) := by
  have hcast : singleClusterGSEnergyS z N =
      ((-((N : ℝ) / 2) * ((z : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
    unfold singleClusterGSEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

/-- **Max-Casimir-sector energy real-part closed form** (γ-5 step 278):
`Re(singleClusterMaxEnergyS z N) = z·N²/4` as an `ℝ` value. -/
theorem singleClusterMaxEnergyS_re_eq (z N : ℕ) :
    (singleClusterMaxEnergyS z N).re = (z : ℝ) * (N : ℝ) ^ 2 / 4 := by
  have hcast : singleClusterMaxEnergyS z N =
      (((z : ℝ) * (N : ℝ) ^ 2 / 4 : ℝ) : ℂ) := by
    unfold singleClusterMaxEnergyS
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

/-- **GS-Max energy gap** (γ-5 step 280):
`singleClusterMaxEnergyS z N - singleClusterGSEnergyS z N = (N/2)(zN+1) = S(2zS+1)`
for spin `S = N/2`.

Closed form for the energy difference between the two named eigenvalues
of γ-5 steps 270, 271. The gap is non-negative and grows linearly in
both `z` and `N²`. -/
theorem singleClusterMaxEnergyS_sub_singleClusterGSEnergyS (z N : ℕ) :
    singleClusterMaxEnergyS z N - singleClusterGSEnergyS z N =
      ((N : ℂ) / 2) * ((z : ℂ) * (N : ℂ) + 1) := by
  unfold singleClusterMaxEnergyS singleClusterGSEnergyS
  ring

/-- **Strict GS < Max gap** (γ-5 step 281):
`Re(singleClusterGSEnergyS z N) < Re(singleClusterMaxEnergyS z N)` for
`N ≥ 1`. The Casimir spectrum is non-degenerate at the GS / Max
sectors whenever the spin is non-trivial (`S ≥ 1/2`). -/
theorem singleClusterGSEnergyS_re_lt_singleClusterMaxEnergyS_re_of_pos
    (z : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (singleClusterGSEnergyS z N).re < (singleClusterMaxEnergyS z N).re := by
  rw [singleClusterGSEnergyS_re_eq, singleClusterMaxEnergyS_re_eq]
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : (0 : ℝ) ≤ (z : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (z : ℝ) * (N : ℝ) := mul_nonneg h2 (by linarith)
  nlinarith [mul_nonneg h2 (sq_nonneg ((N : ℝ) - 1))]

/-- **Strict GS energy negativity** (γ-5 step 283):
`Re(singleClusterGSEnergyS z N) < 0` for `N ≥ 1`. Strengthens γ-5 step
272 to strict for non-trivial spin. -/
theorem singleClusterGSEnergyS_re_neg_of_pos
    (z : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (singleClusterGSEnergyS z N).re < 0 := by
  rw [singleClusterGSEnergyS_re_eq]
  have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : (0 : ℝ) ≤ (z : ℝ) := by positivity
  nlinarith [mul_nonneg h2 (by linarith : (0 : ℝ) ≤ (N : ℝ))]

/-- **Strict max-Casimir-sector energy positivity** (γ-5 step 283):
`0 < Re(singleClusterMaxEnergyS z N)` for `z ≥ 1, N ≥ 1`. Strengthens
γ-5 step 272 to strict when both `z` and `N` are non-trivial. -/
theorem singleClusterMaxEnergyS_re_pos_of_pos
    {z N : ℕ} (hz : 1 ≤ z) (hN : 1 ≤ N) :
    0 < (singleClusterMaxEnergyS z N).re := by
  rw [singleClusterMaxEnergyS_re_eq]
  have h1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith [sq_nonneg ((N : ℝ) - 1)]

/-- **Single-leaf leaf-Casimir reduces to single-site spinSDot** (γ-5 step 285):
`leafSpinSSquared 1 N = spinSDot 1 1 N` on `Fin 2`.

For the dimer (z=1), the leaf set is `{1}`, so each leaf-spin operator
`Ŝ_R^(α) = Σ_{j ∈ erase 0} onSiteS j Ŝ^(α)` reduces to a single
`onSiteS 1 Ŝ^(α)` term, and the leaf-Casimir
`Ŝ_R² = Σ_α (Ŝ_R^(α))²` collapses to the single-site Casimir
`spinSDot 1 1 = Σ_α (onSiteS 1 Ŝ^(α))²`. -/
theorem leafSpinSSquared_one (N : ℕ) :
    (leafSpinSSquared 1 N : ManyBodyOpS (Fin 2) N) = spinSDot 1 1 N := by
  unfold leafSpinSSquared leafSpinSOp1 leafSpinSOp2 leafSpinSOp3 spinSDot
  have h : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  rw [h]
  simp [Finset.sum_singleton]

/-- **Single-leaf leaf-Casimir scalar action** (γ-5 step 286, helper):
`leafSpinSSquared 1 N · v = (N(N+2)/4) • v` for any `v` on `Fin 2`.

Direct corollary of γ-5 step 285 + `spinSDot_self_mulVec_eq_smul`. The
single-leaf leaf-Casimir is the constant scalar `N(N+2)/4 = S(S+1)`. -/
theorem leafSpinSSquared_one_mulVec
    (N : ℕ) (v : (Fin 2 → Fin (N + 1)) → ℂ) :
    (leafSpinSSquared 1 N).mulVec v =
      ((N : ℂ) * ((N : ℂ) + 2) / 4) • v := by
  rw [leafSpinSSquared_one]
  exact spinSDot_self_mulVec_eq_smul N 1 v

/-- **Dimer eigenvalue from total Casimir alone** (γ-5 step 286):
for `z = 1`, the leaf-Casimir is the constant `N(N+2)/4` (γ-5 step 285),
so any total-Casimir eigenvector is automatically a joint eigenvector.
The H-eigenvalue depends only on the total-Casimir eigenvalue:
if `Ŝ_tot² · v = α · v`, then
`H · v = ((α − N(N+2)/2) / 2) • v`
on the dimer.

Specialisation of γ-5 step 259 to z=1, removing the SR² hypothesis. -/
theorem singleClusterHamiltonianS_eigenvalue_dimer
    (N : ℕ) {α : ℂ} {v : (Fin 2 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 2) N).mulVec v = α • v) :
    (singleClusterHamiltonianS 1 N).mulVec v =
      ((α - (N : ℂ) * ((N : ℂ) + 2) / 2) / 2) • v := by
  have hR : (leafSpinSSquared 1 N).mulVec v =
      ((1 : ℂ) * (N : ℂ) / 2 * ((1 : ℂ) * (N : ℂ) / 2 + 1)) • v := by
    rw [leafSpinSSquared_one_mulVec]
    congr 1
    ring
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := 1) N htot hR
  rw [h]
  congr 1
  ring

/-- **Dimer singlet attains GS energy** (γ-5 step 287):
for `z = 1`, any `Stot² = 0` eigenvector is an `H`-eigenvector at the
predicted GS energy: `H · v = singleClusterGSEnergyS 1 N • v`.

Combines γ-5 step 286 (dimer eigenvalue from `Stot²` alone) with γ-5
step 275 (`singleClusterGSEnergyS 1 N = −(N/2)(N/2+1)` closed form).

This is the strongest concrete realisation of Tasaki Problem 2.5.a in
the dimer case: any singlet is an explicit GS eigenvector at the
predicted energy. The existence of a singlet (Clebsch–Gordan
construction) remains separate. -/
theorem singleClusterHamiltonianS_eigenvalue_dimer_singlet
    (N : ℕ) {v : (Fin 2 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 2) N).mulVec v = (0 : ℂ) • v) :
    (singleClusterHamiltonianS 1 N).mulVec v =
      singleClusterGSEnergyS 1 N • v := by
  rw [singleClusterGSEnergyS_one_eq]
  have h := singleClusterHamiltonianS_eigenvalue_dimer N htot
  rw [h]
  congr 1
  ring

/-- **Dimer top-spin attains Max energy** (γ-5 step 288):
for `z = 1`, any `Stot² = N(N+1)` eigenvector (i.e. total spin
`s_tot = N = 2S`) is an `H`-eigenvector at the predicted maximum
Casimir-sector energy: `H · v = singleClusterMaxEnergyS 1 N • v`.

Companion to γ-5 step 287 (singlet at the GS energy). Combines γ-5
step 286 with γ-5 step 275 (`singleClusterMaxEnergyS 1 N = (N/2)²`).
-/
theorem singleClusterHamiltonianS_eigenvalue_dimer_top
    (N : ℕ) {v : (Fin 2 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 2) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 1)) • v) :
    (singleClusterHamiltonianS 1 N).mulVec v =
      singleClusterMaxEnergyS 1 N • v := by
  rw [singleClusterMaxEnergyS_one_eq]
  have h := singleClusterHamiltonianS_eigenvalue_dimer N htot
  rw [h]
  congr 1
  ring

/-- **Trimer (z=2) leaf-Casimir decomposition** (γ-5 step 292):
`leafSpinSSquared 2 N = (N(N+2)/2) • 1 + 2 • spinSDot 1 2 N` on `Fin 3`.

For two leaves (`erase 0 = {1, 2}`), the leaf-Casimir double sum
`Σ_{j,k ∈ {1,2}} spinSDot j k` decomposes into two diagonal terms
(`spinSDot 1 1`, `spinSDot 2 2`, each scalar `N(N+2)/4 • 1`) and two
off-diagonal terms (`spinSDot 1 2`, `spinSDot 2 1`, equal by
`spinSDot_comm`). Bridges the leaf-Casimir machinery to direct
two-leaf coupling. -/
theorem leafSpinSSquared_two (N : ℕ) :
    (leafSpinSSquared 2 N : ManyBodyOpS (Fin 3) N) =
      ((N : ℂ) * ((N : ℂ) + 2) / 2) • 1 +
        (2 : ℂ) • spinSDot 1 2 N := by
  rw [leafSpinSSquared_eq_sum_spinSDot]
  have h12 : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  rw [h12]
  rw [show ({1, 2} : Finset (Fin 3)) = insert 1 {2} from rfl]
  rw [Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
  rw [Finset.sum_singleton]
  rw [Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
  rw [Finset.sum_singleton]
  rw [Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
  rw [Finset.sum_singleton]
  rw [spinSDot_self 1 N, spinSDot_self 2 N]
  rw [spinSDot_comm 2 1]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 2 : ℂ) =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) + ((N : ℂ) * ((N : ℂ) + 2) / 4) from by ring]
  rw [add_smul, two_smul]
  abel

/-- **Trimer eigenvalue from `Stot²` + leaf-leaf coupling** (γ-5 step 293):
for `z = 2`, if `v` is a joint eigenvector of `Ŝ_tot²` (eigenvalue `α`)
and the leaf-leaf coupling `spinSDot 1 2 N` (eigenvalue `β`), then `v`
is an `H`-eigenvector with eigenvalue
`(α − 3·N(N+2)/4 − 2β) / 2`.

Specialisation of γ-5 step 259 to z=2 using the trimer leaf-Casimir
decomposition (γ-5 step 292): `SR² = (N(N+2)/2)·I + 2·(Ŝ_1·Ŝ_2)`.
Substituting `Ŝ_1 · Ŝ_2 · v = β·v` gives `SR² · v = (N(N+2)/2 + 2β)·v`,
which combined with `S0² · v = (N(N+2)/4)·v` and the Casimir
decomposition `2H = Stot² − S0² − SR²` yields the formula. -/
theorem singleClusterHamiltonianS_eigenvalue_trimer
    (N : ℕ) {α β : ℂ} {v : (Fin 3 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 3) N).mulVec v = α • v)
    (hLeafLeaf : (spinSDot 1 2 N).mulVec v = β • v) :
    (singleClusterHamiltonianS 2 N).mulVec v =
      ((α - 3 * (N : ℂ) * ((N : ℂ) + 2) / 4 - 2 * β) / 2) • v := by
  have hR : (leafSpinSSquared 2 N).mulVec v =
      ((N : ℂ) * ((N : ℂ) + 2) / 2 + 2 * β) • v := by
    rw [leafSpinSSquared_two, Matrix.add_mulVec]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hLeafLeaf]
    rw [smul_smul, ← add_smul]
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := 2) N htot hR
  rw [h]
  congr 1
  ring

/-- **Trimer GS-sector eigenvalue** (γ-5 step 294):
for `z = 2`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`) and the leaf-leaf
coupling `spinSDot 1 2 · v = (N²/4)·v` (i.e. leaf-pair at max coupling
in the triplet sector `s_R = N`), then `v` is an `H`-eigenvector at
the predicted GS energy `singleClusterGSEnergyS 2 N = -N(N+1)/2`.

This is the trimer analogue of γ-5 step 287 (dimer singlet attains GS).
The hypotheses correspond to the Tasaki Problem 2.5.a GS Casimir
sector for `z = 2`: leaves form a triplet (`s_R = N`, max), and the
total spin couples to the central spin to give `s_tot = (z−1)N/2 = N/2`. -/
theorem singleClusterHamiltonianS_eigenvalue_trimer_gs
    (N : ℕ) {v : (Fin 3 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 3) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hLeafLeaf : (spinSDot 1 2 N).mulVec v = ((N : ℂ) ^ 2 / 4) • v) :
    (singleClusterHamiltonianS 2 N).mulVec v =
      singleClusterGSEnergyS 2 N • v := by
  unfold singleClusterGSEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_trimer N htot hLeafLeaf
  rw [h]
  congr 1
  ring

/-- **Trimer top-spin sector eigenvalue at Max energy** (γ-5 step 295):
for `z = 2`, if `v` is a joint eigenvector of `Stot²` at the maximum
total-spin sector (`Stot²·v = (3N/2)(3N/2+1)·v`, i.e. `s_tot = 3N/2`)
and the leaf-leaf coupling `spinSDot 1 2·v = (N²/4)·v` (leaf triplet,
`s_R = N`), then `v` is an `H`-eigenvector at the predicted maximum
Casimir-sector energy `singleClusterMaxEnergyS 2 N = N²/2`.

Trimer companion to γ-5 step 288 (dimer top-spin attains Max). -/
theorem singleClusterHamiltonianS_eigenvalue_trimer_top
    (N : ℕ) {v : (Fin 3 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 3) N).mulVec v =
        ((3 : ℂ) * (N : ℂ) / 2 * ((3 : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hLeafLeaf : (spinSDot 1 2 N).mulVec v = ((N : ℂ) ^ 2 / 4) • v) :
    (singleClusterHamiltonianS 2 N).mulVec v =
      singleClusterMaxEnergyS 2 N • v := by
  unfold singleClusterMaxEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_trimer N htot hLeafLeaf
  rw [h]
  congr 1
  ring

/-- **Trimer leaf-singlet sector eigenvalue = 0** (γ-5 step 296):
for `z = 2`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`, the central spin alone)
and the leaf-leaf coupling at `spinSDot 1 2·v = -(N(N+2)/4)·v` (leaf
singlet, `s_R = 0`), then `H · v = 0`.

The leaf-singlet sector decouples: with leaves combined into a
total-spin-zero singlet, the central spin couples trivially to give
H = 0. The spin-1/2 trimer spectrum `{-1, 0, 1/2}` includes `0` from
exactly this sector. -/
theorem singleClusterHamiltonianS_eigenvalue_trimer_leaf_singlet
    (N : ℕ) {v : (Fin 3 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 3) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hLeafLeaf : (spinSDot 1 2 N).mulVec v =
        (-((N : ℂ) * ((N : ℂ) + 2) / 4)) • v) :
    (singleClusterHamiltonianS 2 N).mulVec v = 0 := by
  have h := singleClusterHamiltonianS_eigenvalue_trimer N htot hLeafLeaf
  rw [h]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 4 -
        3 * (N : ℂ) * ((N : ℂ) + 2) / 4 -
        2 * -((N : ℂ) * ((N : ℂ) + 2) / 4)) / 2 = 0 from by ring]
  rw [zero_smul]

/-- **Quartet (z=3) leaf-Casimir decomposition** (γ-5 step 303):
`leafSpinSSquared 3 N = (3·N(N+2)/4) • 1 + 2 • (spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3)`
on `Fin 4`.

For three leaves (`erase 0 = {1, 2, 3}`), the leaf-Casimir double sum
`Σ_{j,k ∈ {1,2,3}} spinSDot j k` decomposes into three diagonal
`spinSDot j j` terms (each scalar `N(N+2)/4 • 1`) and six off-diagonal
terms grouped into three `spinSDot j k` pairs (`(j,k) = (1,2), (1,3),
(2,3)`) related by `spinSDot_comm`. Generalises γ-5 step 292 (z=2) to
the quartet. -/
theorem leafSpinSSquared_three (N : ℕ) :
    (leafSpinSSquared 3 N : ManyBodyOpS (Fin 4) N) =
      (3 * (N : ℂ) * ((N : ℂ) + 2) / 4) • 1 +
        (2 : ℂ) • (spinSDot 1 2 N + spinSDot 1 3 N + spinSDot 2 3 N) := by
  rw [leafSpinSSquared_eq_sum_spinSDot]
  have h123 : (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} := by decide
  rw [h123]
  have hne12 : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4)) := by decide
  have hne23 : (2 : Fin 4) ∉ ({3} : Finset (Fin 4)) := by decide
  rw [show ({1, 2, 3} : Finset (Fin 4)) = insert 1 (insert 2 {3}) from rfl]
  simp_rw [Finset.sum_insert hne12, Finset.sum_insert hne23, Finset.sum_singleton]
  rw [spinSDot_self 1 N, spinSDot_self 2 N, spinSDot_self 3 N]
  rw [spinSDot_comm 2 1, spinSDot_comm 3 1, spinSDot_comm 3 2]
  rw [show (3 * (N : ℂ) * ((N : ℂ) + 2) / 4 : ℂ) =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) + ((N : ℂ) * ((N : ℂ) + 2) / 4) +
          ((N : ℂ) * ((N : ℂ) + 2) / 4) from by ring]
  rw [add_smul, add_smul, two_smul]
  abel

/-- **Quartet eigenvalue from `Stot²` + leaf-leaf sum** (γ-5 step 304):
for `z = 3`, if `v` is a joint eigenvector of `Ŝ_tot²` (eigenvalue `α`)
and the leaf-leaf sum
`spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3` (eigenvalue `γ`), then
`v` is an `H`-eigenvector with eigenvalue
`(α − N(N+2) − 2γ)/2`.

Specialisation of γ-5 step 259 to z=3 using the quartet leaf-Casimir
decomposition (γ-5 step 303): `SR² = (3N(N+2)/4)·I +
2·(Ŝ_1·Ŝ_2 + Ŝ_1·Ŝ_3 + Ŝ_2·Ŝ_3)`. Substituting the hypothesis on
the leaf-leaf sum gives the leaf-Casimir eigenvalue
`3N(N+2)/4 + 2γ`, which combined with the central-Casimir scalar
action and the Casimir decomposition yields the formula. -/
theorem singleClusterHamiltonianS_eigenvalue_quartet
    (N : ℕ) {α γ : ℂ} {v : (Fin 4 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 4) N).mulVec v = α • v)
    (hLeafSum :
        (spinSDot (1 : Fin 4) 2 N + spinSDot (1 : Fin 4) 3 N +
            spinSDot (2 : Fin 4) 3 N).mulVec v = γ • v) :
    (singleClusterHamiltonianS 3 N).mulVec v =
      ((α - (N : ℂ) * ((N : ℂ) + 2) - 2 * γ) / 2) • v := by
  have hR : (leafSpinSSquared 3 N).mulVec v =
      (3 * (N : ℂ) * ((N : ℂ) + 2) / 4 + 2 * γ) • v := by
    rw [leafSpinSSquared_three]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hLeafSum]
    rw [smul_smul, ← add_smul]
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := 3) N htot hR
  rw [h]
  congr 1
  ring

/-- **Quartet GS-sector eigenvalue at GS energy** (γ-5 step 305):
for `z = 3`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = N(N+1)·v` (i.e. `s_tot = N`) and the leaf-leaf sum at
`(spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3)·v = (3N²/4)·v`
(corresponding to leaves at the maximum total leaf-spin
`s_R = 3N/2`), then `v` is an `H`-eigenvector at the predicted GS
energy `singleClusterGSEnergyS 3 N = -N(3N+2)/4`.

Quartet analogue of γ-5 step 294 (trimer GS sector). The hypotheses
correspond to the Tasaki Problem 2.5.a GS Casimir sector for `z = 3`:
leaves form the maximum leaf-spin sector `(s_R = 3N/2)` and couple
with the central spin to give `s_tot = (z−1)N/2 = N`. -/
theorem singleClusterHamiltonianS_eigenvalue_quartet_gs
    (N : ℕ) {v : (Fin 4 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 4) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 1)) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 4) 2 N + spinSDot (1 : Fin 4) 3 N +
            spinSDot (2 : Fin 4) 3 N).mulVec v =
          (3 * (N : ℂ) ^ 2 / 4) • v) :
    (singleClusterHamiltonianS 3 N).mulVec v =
      singleClusterGSEnergyS 3 N • v := by
  unfold singleClusterGSEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_quartet N htot hLeafSum
  rw [h]
  congr 1
  ring

/-- **Quartet top-spin sector eigenvalue at Max energy** (γ-5 step 306):
for `z = 3`, if `v` is a joint eigenvector of `Stot²` at the maximum
total-spin sector (`Stot²·v = 2N(2N+1)·v`, i.e. `s_tot = 2N = (z+1)N/2`)
and the leaf-leaf sum at `(spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3)·v
= (3N²/4)·v` (max leaf-spin `s_R = 3N/2`), then `v` is an `H`-eigenvector
at the predicted maximum Casimir-sector energy
`singleClusterMaxEnergyS 3 N = 3N²/4`.

Quartet companion to γ-5 step 295 (trimer top sector). -/
theorem singleClusterHamiltonianS_eigenvalue_quartet_top
    (N : ℕ) {v : (Fin 4 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 4) N).mulVec v =
        ((2 : ℂ) * (N : ℂ) * ((2 : ℂ) * (N : ℂ) + 1)) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 4) 2 N + spinSDot (1 : Fin 4) 3 N +
            spinSDot (2 : Fin 4) 3 N).mulVec v =
          (3 * (N : ℂ) ^ 2 / 4) • v) :
    (singleClusterHamiltonianS 3 N).mulVec v =
      singleClusterMaxEnergyS 3 N • v := by
  unfold singleClusterMaxEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_quartet N htot hLeafSum
  rw [h]
  congr 1
  ring

/-- **Pentamer (z=4) leaf-Casimir decomposition** (γ-5 step 312):
`leafSpinSSquared 4 N = (N(N+2)) • 1 + 2 • (Σ_{1 ≤ j < k ≤ 4} spinSDot j k N)`
on `Fin 5`.

For four leaves (`erase 0 = {1, 2, 3, 4}`), the leaf-Casimir double sum
`Σ_{j,k ∈ {1,...,4}} spinSDot j k` decomposes into four diagonal
`spinSDot j j` terms (each scalar `N(N+2)/4 • 1`) and twelve
off-diagonal terms grouped into six `spinSDot j k` pairs related by
`spinSDot_comm`. Generalises γ-5 step 303 (z=3 quartet) to the
pentamer. -/
theorem leafSpinSSquared_four (N : ℕ) :
    (leafSpinSSquared 4 N : ManyBodyOpS (Fin 5) N) =
      ((N : ℂ) * ((N : ℂ) + 2)) • 1 +
        (2 : ℂ) • (spinSDot 1 2 N + spinSDot 1 3 N + spinSDot 1 4 N +
          spinSDot 2 3 N + spinSDot 2 4 N + spinSDot 3 4 N) := by
  rw [leafSpinSSquared_eq_sum_spinSDot]
  have h1234 : (Finset.univ.erase (0 : Fin 5)) = {1, 2, 3, 4} := by decide
  rw [h1234]
  have hne1 : (1 : Fin 5) ∉ ({2, 3, 4} : Finset (Fin 5)) := by decide
  have hne2 : (2 : Fin 5) ∉ ({3, 4} : Finset (Fin 5)) := by decide
  have hne3 : (3 : Fin 5) ∉ ({4} : Finset (Fin 5)) := by decide
  rw [show ({1, 2, 3, 4} : Finset (Fin 5)) = insert 1 (insert 2 (insert 3 {4}))
        from rfl]
  simp_rw [Finset.sum_insert hne1, Finset.sum_insert hne2,
    Finset.sum_insert hne3, Finset.sum_singleton]
  rw [spinSDot_self 1 N, spinSDot_self 2 N, spinSDot_self 3 N, spinSDot_self 4 N]
  rw [spinSDot_comm 2 1, spinSDot_comm 3 1, spinSDot_comm 4 1]
  rw [spinSDot_comm 3 2, spinSDot_comm 4 2]
  rw [spinSDot_comm 4 3]
  conv_rhs =>
    rw [show ((N : ℂ) * ((N : ℂ) + 2) : ℂ) =
          ((N : ℂ) * ((N : ℂ) + 2) / 4) + ((N : ℂ) * ((N : ℂ) + 2) / 4) +
            ((N : ℂ) * ((N : ℂ) + 2) / 4) + ((N : ℂ) * ((N : ℂ) + 2) / 4)
            from by ring]
    rw [add_smul, add_smul, add_smul, two_smul]
  abel

/-- **Pentamer eigenvalue from `Stot²` + leaf-leaf sum** (γ-5 step 313):
for `z = 4`, if `v` is a joint eigenvector of `Ŝ_tot²` (eigenvalue `α`)
and the leaf-leaf sum
`spinSDot 1 2 + spinSDot 1 3 + spinSDot 1 4 + spinSDot 2 3 +
spinSDot 2 4 + spinSDot 3 4` (eigenvalue `γ`), then `v` is an
`H`-eigenvector with eigenvalue `(α − 5N(N+2)/4 − 2γ)/2`.

Specialisation of γ-5 step 259 to z=4 using the pentamer leaf-Casimir
decomposition (γ-5 step 312): `SR² = N(N+2)·I + 2·(sum-of-6-pair-couplings)`.
-/
theorem singleClusterHamiltonianS_eigenvalue_pentamer
    (N : ℕ) {α γ : ℂ} {v : (Fin 5 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 5) N).mulVec v = α • v)
    (hLeafSum :
        (spinSDot (1 : Fin 5) 2 N + spinSDot (1 : Fin 5) 3 N +
            spinSDot (1 : Fin 5) 4 N + spinSDot (2 : Fin 5) 3 N +
            spinSDot (2 : Fin 5) 4 N + spinSDot (3 : Fin 5) 4 N).mulVec v =
          γ • v) :
    (singleClusterHamiltonianS 4 N).mulVec v =
      ((α - 5 * (N : ℂ) * ((N : ℂ) + 2) / 4 - 2 * γ) / 2) • v := by
  have hR : (leafSpinSSquared 4 N).mulVec v =
      ((N : ℂ) * ((N : ℂ) + 2) + 2 * γ) • v := by
    rw [leafSpinSSquared_four]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hLeafSum]
    rw [smul_smul, ← add_smul]
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := 4) N htot hR
  rw [h]
  congr 1
  ring

/-- **Pentamer GS-sector eigenvalue at GS energy** (γ-5 step 314):
for `z = 4`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (3N/2)(3N/2+1)·v` (i.e. `s_tot = 3N/2 = (z-1)N/2`) and the
6-pair leaf-leaf sum at `(3N²/2)·v` (corresponding to leaves at the
maximum total leaf-spin `s_R = 2N`), then `v` is an `H`-eigenvector
at the predicted GS energy
`singleClusterGSEnergyS 4 N = -N(2N+1)/2`.

Pentamer analogue of γ-5 steps 294 (trimer GS) and 305 (quartet GS).
The hypotheses correspond to the Tasaki Problem 2.5.a GS Casimir
sector for `z = 4`: leaves form max leaf-spin sector and couple with
the central spin to give `s_tot = (z-1)N/2 = 3N/2`. -/
theorem singleClusterHamiltonianS_eigenvalue_pentamer_gs
    (N : ℕ) {v : (Fin 5 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 5) N).mulVec v =
        ((3 : ℂ) * (N : ℂ) / 2 * ((3 : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 5) 2 N + spinSDot (1 : Fin 5) 3 N +
            spinSDot (1 : Fin 5) 4 N + spinSDot (2 : Fin 5) 3 N +
            spinSDot (2 : Fin 5) 4 N + spinSDot (3 : Fin 5) 4 N).mulVec v =
          (3 * (N : ℂ) ^ 2 / 2) • v) :
    (singleClusterHamiltonianS 4 N).mulVec v =
      singleClusterGSEnergyS 4 N • v := by
  unfold singleClusterGSEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_pentamer N htot hLeafSum
  rw [h]
  congr 1
  ring

/-- **Pentamer top-spin sector eigenvalue at Max energy** (γ-5 step 315):
for `z = 4`, if `v` is a joint eigenvector of `Stot²` at the maximum
total-spin sector (`Stot²·v = (5N/2)(5N/2+1)·v`, i.e. `s_tot = 5N/2 =
(z+1)N/2`) and the 6-pair leaf-leaf sum at `(3N²/2)·v` (max leaf-spin
`s_R = 2N`), then `v` is an `H`-eigenvector at the predicted maximum
Casimir-sector energy `singleClusterMaxEnergyS 4 N = N²`.

Pentamer companion to γ-5 steps 295 (trimer top) and 306 (quartet top). -/
theorem singleClusterHamiltonianS_eigenvalue_pentamer_top
    (N : ℕ) {v : (Fin 5 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 5) N).mulVec v =
        ((5 : ℂ) * (N : ℂ) / 2 * ((5 : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 5) 2 N + spinSDot (1 : Fin 5) 3 N +
            spinSDot (1 : Fin 5) 4 N + spinSDot (2 : Fin 5) 3 N +
            spinSDot (2 : Fin 5) 4 N + spinSDot (3 : Fin 5) 4 N).mulVec v =
          (3 * (N : ℂ) ^ 2 / 2) • v) :
    (singleClusterHamiltonianS 4 N).mulVec v =
      singleClusterMaxEnergyS 4 N • v := by
  unfold singleClusterMaxEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_pentamer N htot hLeafSum
  rw [h]
  congr 1
  ring

/-- **Quartet leaf-singlet sector eigenvalue = 0** (γ-5 step 321):
for `z = 3`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`, central spin alone)
and the leaf-leaf sum at
`(spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3)·v = (-3N(N+2)/8)·v`
(corresponding to leaves in a singlet, `s_R = 0`), then `H · v = 0`.

The leaf-singlet sector decouples: with the three leaves combined
into a total-spin-zero singlet, the central spin couples trivially.
A 3-leaf singlet exists only for **integer** spin `S` (i.e. `N` even):
three half-integer spins sum to a half-integer total, never zero.
For `S = 1, 2, 3, ...` (i.e. `N = 2, 4, 6, ...`), three spins admit
`s_R = 0` with multiplicity `≥ 1`.

Quartet analogue of γ-5 step 296 (trimer leaf-singlet decoupling). -/
theorem singleClusterHamiltonianS_eigenvalue_quartet_leaf_singlet
    (N : ℕ) {v : (Fin 4 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 4) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 4) 2 N + spinSDot (1 : Fin 4) 3 N +
            spinSDot (2 : Fin 4) 3 N).mulVec v =
          (-3 * (N : ℂ) * ((N : ℂ) + 2) / 8) • v) :
    (singleClusterHamiltonianS 3 N).mulVec v = 0 := by
  have h := singleClusterHamiltonianS_eigenvalue_quartet N htot hLeafSum
  rw [h]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 4 - (N : ℂ) * ((N : ℂ) + 2) -
        2 * (-3 * (N : ℂ) * ((N : ℂ) + 2) / 8)) / 2 = 0 from by ring]
  rw [zero_smul]

/-- **Pentamer leaf-singlet sector eigenvalue = 0** (γ-5 step 322):
for `z = 4`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`, central spin alone)
and the 6-pair leaf-leaf sum at
`(spinSDot 1 2 + ... + spinSDot 3 4)·v = (-N(N+2)/2)·v`
(corresponding to leaves in a singlet, `s_R = 0`), then `H · v = 0`.

The leaf-singlet sector decouples. A 4-leaf singlet exists for any
spin `S`: four spins of any magnitude can combine to total spin 0
(since four half-integers also sum to integer 0).

Pentamer analogue of γ-5 step 296 (trimer) and step 321 (quartet). -/
theorem singleClusterHamiltonianS_eigenvalue_pentamer_leaf_singlet
    (N : ℕ) {v : (Fin 5 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 5) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 5) 2 N + spinSDot (1 : Fin 5) 3 N +
            spinSDot (1 : Fin 5) 4 N + spinSDot (2 : Fin 5) 3 N +
            spinSDot (2 : Fin 5) 4 N + spinSDot (3 : Fin 5) 4 N).mulVec v =
          (-((N : ℂ) * ((N : ℂ) + 2) / 2)) • v) :
    (singleClusterHamiltonianS 4 N).mulVec v = 0 := by
  have h := singleClusterHamiltonianS_eigenvalue_pentamer N htot hLeafSum
  rw [h]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 4 -
        5 * (N : ℂ) * ((N : ℂ) + 2) / 4 -
        2 * (-((N : ℂ) * ((N : ℂ) + 2) / 2))) / 2 = 0 from by ring]
  rw [zero_smul]

/-- **Generic leaf-singlet sector eigenvalue = 0** (γ-5 step 323):
for any `z : ℕ`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`, central spin alone)
and the leaf-Casimir at `leafSpinSSquared z N · v = 0` (leaves in a
total-spin-zero singlet), then `H · v = 0`.

The leaf-singlet sector decouples: with the leaves combined into a
total-spin-zero singlet, the central spin couples trivially via the
Casimir formula. Generalises γ-5 step 296 (z=2 trimer), γ-5 step 321
(z=3 quartet), γ-5 step 322 (z=4 pentamer) to arbitrary cluster size.

A `z`-leaf singlet exists when total spin 0 is achievable from `z`
spins of magnitude `S = N/2`: always for **even** `z`, and for **odd**
`z` only when `S` is integer (since odd-many half-integer spins sum
to a half-integer, never zero). -/
theorem singleClusterHamiltonianS_eigenvalue_leaf_singlet
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hR : (leafSpinSSquared z N).mulVec v = 0) :
    (singleClusterHamiltonianS z N).mulVec v = 0 := by
  have hR' : (leafSpinSSquared z N).mulVec v = (0 : ℂ) • v := by
    rw [hR, zero_smul]
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := z) N htot hR'
  rw [h]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 4 - (N : ℂ) * ((N : ℂ) + 2) / 4 - 0) / 2 =
        0 from by ring]
  rw [zero_smul]

end LatticeSystem.Quantum
