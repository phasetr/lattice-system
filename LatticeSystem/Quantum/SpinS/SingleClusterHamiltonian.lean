import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonianCore

/-!
# Single-cluster Hamiltonian: Casimir-sector eigenvalues — capstone

Continued from `SingleClusterHamiltonianCore.lean` (the single-cluster
Heisenberg-type Hamiltonian definition, its Hermiticity, the all-up /
all-aligned / all-down expectations, the leaf-spin operators, center-leaf
commutativity, and the `2H = Ŝ_tot² − Ŝ_R² − N(N+2)/4` Casimir-difference
family).  This file carries the eigenvalue layer: the joint-Casimir
eigenvector eigenvalue formula, the leaf-Casimir `Ŝ_R²` action on aligned
states, and the ground-state / maximal-Casimir-sector eigenvalues and
energy-eigenvector identities.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

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


end LatticeSystem.Quantum
