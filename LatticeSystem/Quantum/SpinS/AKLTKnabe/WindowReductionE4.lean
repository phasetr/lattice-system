import LatticeSystem.Quantum.SpinS.AKLTKnabe.Sl2LadderSectorsE3
import LatticeSystem.Quantum.SpinS.AKLTKnabe.TotalSpinCommuteE1b

/-!
# Gate E4: reduction of the spectrum of the AKLT window to the highest-weight blocks

This module (Issue #5094; Tasaki §7.1.4, Knabe's argument, pp. 188–190) carries out step **(E)** of
the design note `aklt-theorem-7-1-e1a-general-window-bound-design.md` §2.1: the *spectral reduction*

  every eigenvalue of the open three-bond window `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃` on `(ℂ³)^{⊗4}` is already
  an eigenvalue of `ĥ` restricted to one of the five highest-weight spaces `hw_k`
  (`k = 0, …, 4`), whose dimensions are `1, 3, 6, 6, 3` (Gate E3).

The whole argument is `sl₂` bookkeeping on top of Gates E1b/E2/E3; **no `81 × 81` entry
computation occurs anywhere**.  The chain is:

1. *sector invariance* — an operator commuting with `Ŝ³_tot` preserves every magnetisation sector
   `V_k`; for `ĥ` the commutation is the axis-3 companion of the Gate E1b commutation
   `[ĥ, Ŝ⁺_tot] = 0`, obtained from the same production lemma family
   (`spinSDot_commutator_totalSpinSOp3`).  The scalar action of `Ŝ³_tot` on `V_k` is *derived* from
   the public Gate E3 results (`ladderCommutatorApplyE3` and `[Ŝ⁺,Ŝ⁻] = 2 Ŝ³`), and its converse
   (an eigenvector of `Ŝ³_tot` for the eigenvalue `|Λ|N/2 − k` lies in `V_k`) is proved here;
2. *descending induction* — if `v ∈ V_k` is a nonzero eigenvector of `ĥ`, then either
   `Ŝ⁺_tot v = 0`, in which case `v ∈ hw_k`, or `Ŝ⁺_tot v` is a nonzero eigenvector for the same
   eigenvalue inside `V_{k−1}`, and the induction descends.  No orthogonal decomposition and no
   self-adjointness of `ĥ` is needed: the ladder itself performs the reduction;
3. *the `2k > |Λ|N` side* — for those sectors the ladder norm identity `ladderNormSqE3` makes
   `Ŝ⁺_tot` injective on `V_k`, i.e. `hw_k = 0`, which is what confines the index `j` produced by
   the induction to `2j ≤ |Λ|N`, i.e. `j ≤ 4` for the window.  The total-spin-flip unitary of the
   design note §2.1 (E) is **not** needed;
4. *reduction to a sector* — a general eigenvector need not lie in a single `V_k`, so its
   magnetisation components `sectorProjE4 k v` are used; sector invariance makes each of them an
   eigenvector for the same eigenvalue, and at least one of them is nonzero.

The indexing convention is the one of Gate E3: `magSumS σ = Σ_x (σ x).val` is the *natural-number*
magnetisation index, the physical magnetic quantum number being `m = |Λ|N/2 − magSumS σ`, and
`Ŝ⁺_tot` *lowers* `magSumS` by one.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1 eq. (2.1.1) p. 15, §2.2 eq. (2.2.17) p. 24, §7.1.3 eq. (7.1.6) p. 182, §7.1.4
eq. (7.1.30) pp. 188–190; S. Knabe, *J. Stat. Phys.* **52**, 627–638 (1988).
-/

namespace LatticeSystem.Quantum.AKLTSl2WindowReductionE4

open LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTSl2SubmoduleProbeE2
open LatticeSystem.Quantum.AKLTSl2LadderSectorsE3
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## 1. Many-body matrices as operators on the Euclidean space -/

/-- A many-body matrix viewed as a linear endomorphism of the many-body Hilbert space.  This is the
general form of `totalPlusLinE2` / `totalMinusLinE2` of Gate E2, needed here because the window
`ĥ` has to travel through the same bridge as the ladder operators. -/
noncomputable def manyBodyLinE4 (A : ManyBodyOpS Λ N) :
    ManyBodyVecE2 Λ N →ₗ[ℂ] ManyBodyVecE2 Λ N :=
  Matrix.toEuclideanLin A

/-- Component description of `manyBodyLinE4`: applying it and forgetting the `ℓ²` structure is
matrix–vector multiplication. -/
theorem ofLp_manyBodyLinE4 (A : ManyBodyOpS Λ N) (v : ManyBodyVecE2 Λ N) :
    WithLp.ofLp (manyBodyLinE4 Λ N A v) = A.mulVec (WithLp.ofLp v) := rfl

/-- `manyBodyLinE4` of the total raising matrix is the Gate E2 operator `totalPlusLinE2`. -/
private theorem manyBodyLinE4_totalSpinSOpPlusE4 :
    manyBodyLinE4 Λ N (totalSpinSOpPlus Λ N) = totalPlusLinE2 Λ N := rfl

/-- Commuting matrices induce commuting operators on the many-body Hilbert space. -/
theorem manyBodyLinE4_commute (A B : ManyBodyOpS Λ N) (h : Commute A B) (v : ManyBodyVecE2 Λ N) :
    manyBodyLinE4 Λ N A (manyBodyLinE4 Λ N B v)
      = manyBodyLinE4 Λ N B (manyBodyLinE4 Λ N A v) := by
  refine WithLp.ofLp_injective 2 ?_
  change A.mulVec (B.mulVec (WithLp.ofLp v)) = B.mulVec (A.mulVec (WithLp.ofLp v))
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.eq]

/-! ## 2. The magnetisation sectors are the eigenspaces of `Ŝ³_tot` -/

/-- **Scalar action of `Ŝ³_tot` on a magnetisation sector**: on `V_k` the total `3`-axis operator
acts by `|Λ|N/2 − k`.  Derived from the public Gate E3 results — the ladder commutator scalar
(`ladderCommutatorApplyE3`) and the Cartan relation `[Ŝ⁺_tot, Ŝ⁻_tot] = 2 Ŝ³_tot` — so no matrix
entry of `Ŝ³_tot` is inspected here. -/
theorem manyBodyLinE4_totalSpinSOp3_apply_of_mem (k : ℕ) (v : ManyBodyVecE2 Λ N)
    (hv : v ∈ magSectorE2 Λ N k) :
    manyBodyLinE4 Λ N (totalSpinSOp3 Λ N) v
      = (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (k : ℂ)) • v := by
  have hcom := ladderCommutatorApplyE3 Λ N k v hv
  have e1 : WithLp.ofLp (totalPlusLinE2 Λ N (totalMinusLinE2 Λ N v)
        - totalMinusLinE2 Λ N (totalPlusLinE2 Λ N v))
      = (totalSpinSOpPlus Λ N * totalSpinSOpMinus Λ N
          - totalSpinSOpMinus Λ N * totalSpinSOpPlus Λ N).mulVec (WithLp.ofLp v) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rfl
  rw [totalSpinSOpPlus_commutator_totalSpinSOpMinus, Matrix.smul_mulVec] at e1
  rw [hcom] at e1
  refine WithLp.ofLp_injective 2 (funext fun σ => ?_)
  have hσ := congrFun e1 σ
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at hσ
  change (totalSpinSOp3 Λ N).mulVec (WithLp.ofLp v) σ
      = (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (k : ℂ)) * WithLp.ofLp v σ
  linear_combination -hσ / 2

/-- **Converse**: a vector on which `Ŝ³_tot` acts by the scalar `|Λ|N/2 − k` lies in the
magnetisation sector `V_k`.  This is the direction that turns the commutation `[ĥ, Ŝ³_tot] = 0`
into the invariance of `V_k` under `ĥ`. -/
theorem mem_magSectorE4_of_totalSpinSOp3_apply (k : ℕ) (w : ManyBodyVecE2 Λ N)
    (hw : manyBodyLinE4 Λ N (totalSpinSOp3 Λ N) w
      = (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (k : ℂ)) • w) :
    w ∈ magSectorE2 Λ N k := by
  refine (mem_magSectorE3_iff Λ N k w).mpr fun σ hσ => ?_
  have hσ' := congrFun (congrArg WithLp.ofLp hw) σ
  rw [ofLp_manyBodyLinE4] at hσ'
  have hdiag : (totalSpinSOp3 Λ N).mulVec (WithLp.ofLp w) σ
      = magEigenvalueS σ * WithLp.ofLp w σ := by
    change ∑ τ, totalSpinSOp3 Λ N σ τ * WithLp.ofLp w τ = magEigenvalueS σ * WithLp.ofLp w σ
    rw [Fintype.sum_eq_single σ (fun τ hτ => by
      rw [totalSpinSOp3_apply_off_diag (Ne.symm hτ), zero_mul]), totalSpinSOp3_apply_diag]
  rw [hdiag, magEigenvalueS_def] at hσ'
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at hσ'
  have hne : ((k : ℂ) - (magSumS σ : ℂ)) ≠ 0 := by
    intro h
    exact hσ (Nat.cast_injective (sub_eq_zero.mp h)).symm
  have hzero : ((k : ℂ) - (magSumS σ : ℂ)) * WithLp.ofLp w σ = 0 := by
    linear_combination hσ'
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hne
  · exact h

/-- **Design §2.1 (E), step 1**: an operator commuting with `Ŝ³_tot` preserves every magnetisation
sector `V_k`. -/
theorem manyBodyLinE4_mem_magSector (A : ManyBodyOpS Λ N) (hA : Commute A (totalSpinSOp3 Λ N))
    (k : ℕ) (v : ManyBodyVecE2 Λ N) (hv : v ∈ magSectorE2 Λ N k) :
    manyBodyLinE4 Λ N A v ∈ magSectorE2 Λ N k := by
  refine mem_magSectorE4_of_totalSpinSOp3_apply Λ N k _ ?_
  rw [← manyBodyLinE4_commute Λ N A (totalSpinSOp3 Λ N) hA v,
    manyBodyLinE4_totalSpinSOp3_apply_of_mem Λ N k v hv, map_smul]

/-! ## 3. The high sectors carry no highest-weight vector -/

/-- **Design §2.1 (E), the `m < 0` side**: for `2k > |Λ|N` the highest-weight space `hw_k` is
trivial.  Instead of the total-spin-flip unitary of the design note this is the *dual* of the Gate
E3 injectivity statement: the ladder norm identity `‖Ŝ⁻v‖² = ‖Ŝ⁺v‖² + (|Λ|N − 2k)‖v‖²` forces
`‖v‖ = 0` as soon as `Ŝ⁺v = 0` and `|Λ|N − 2k < 0`. -/
theorem eq_zero_of_mem_highestWeightE4 (k : ℕ) (hk : Fintype.card Λ * N < 2 * k)
    (v : ManyBodyVecE2 Λ N) (hv : v ∈ highestWeightE2 Λ N k) : v = 0 := by
  unfold highestWeightE2 at hv
  obtain ⟨hvk, hker⟩ := Submodule.mem_inf.mp hv
  have h0 : totalPlusLinE2 Λ N v = 0 := LinearMap.mem_ker.mp hker
  have h := ladderNormSqE3 Λ N k v hvk
  rw [h0, norm_zero] at h
  have hcast : ((Fintype.card Λ * N : ℕ) : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast hk
  push_cast at hcast
  have hc : (Fintype.card Λ : ℝ) * (N : ℝ) - 2 * (k : ℝ) < 0 := by linarith
  have hprod : (0 : ℝ) ≤ ((Fintype.card Λ : ℝ) * (N : ℝ) - 2 * (k : ℝ)) * ‖v‖ ^ 2 := by
    nlinarith [sq_nonneg ‖totalMinusLinE2 Λ N v‖]
  have hzero : ‖v‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hne)
    nlinarith [mul_pos hpos hpos]
  exact norm_eq_zero.mp hzero

/-! ## 4. The descending ladder induction -/

/-- **Design §2.1 (E), descending induction**: a nonzero eigenvector of `A` lying in the
magnetisation sector `V_k` produces a nonzero eigenvector of `A` for the *same* eigenvalue lying in
a highest-weight space `hw_j` with `j ≤ k`.

The induction is on `k`: either `Ŝ⁺_tot v = 0`, and then `v` itself lies in `hw_k`, or `Ŝ⁺_tot v` is
a nonzero eigenvector in `V_{k−1}` (sector transport `totalPlusLinE3_mem_magSector` plus the
commutation of `A` with `Ŝ⁺_tot`), and the induction hypothesis applies.  The base case `k = 0` is
Gate E3's `highestWeightE3_zero` (`hw_0 = V_0`). -/
theorem exists_mem_highestWeightE4_of_mem_magSector (A : ManyBodyOpS Λ N)
    (hA : Commute A (totalSpinSOpPlus Λ N)) (μ : ℂ) :
    ∀ (k : ℕ) (v : ManyBodyVecE2 Λ N), v ∈ magSectorE2 Λ N k → v ≠ 0 →
      manyBodyLinE4 Λ N A v = μ • v →
      ∃ j ≤ k, ∃ u ∈ highestWeightE2 Λ N j, u ≠ 0 ∧ manyBodyLinE4 Λ N A u = μ • u := by
  intro k
  induction k with
  | zero =>
    intro v hv hv0 heig
    refine ⟨0, le_rfl, v, ?_, hv0, heig⟩
    rw [highestWeightE3_zero Λ N]
    exact hv
  | succ k ih =>
    intro v hv hv0 heig
    by_cases hz : totalPlusLinE2 Λ N v = 0
    · refine ⟨k + 1, le_rfl, v, ?_, hv0, heig⟩
      unfold highestWeightE2
      exact Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr hz⟩
    · have heig' : manyBodyLinE4 Λ N A (totalPlusLinE2 Λ N v)
          = μ • totalPlusLinE2 Λ N v := by
        rw [← manyBodyLinE4_totalSpinSOpPlusE4 Λ N,
          manyBodyLinE4_commute Λ N A (totalSpinSOpPlus Λ N) hA v, heig, map_smul]
      obtain ⟨j, hjk, u, hu, hu0, hueig⟩ :=
        ih (totalPlusLinE2 Λ N v) (totalPlusLinE3_mem_magSector Λ N k v hv) hz heig'
      exact ⟨j, hjk.trans (Nat.le_succ k), u, hu, hu0, hueig⟩

/-! ## 5. Splitting a general vector into its magnetisation components -/

/-- The projection onto the magnetisation sector `V_k`: it keeps the components supported on the
configurations with `magSumS σ = k` and kills all the others. -/
noncomputable def sectorProjE4 (k : ℕ) : ManyBodyVecE2 Λ N →ₗ[ℂ] ManyBodyVecE2 Λ N where
  toFun v := WithLp.toLp 2 fun σ => if magSumS σ = k then WithLp.ofLp v σ else 0
  map_add' v w := by
    refine WithLp.ofLp_injective 2 (funext fun σ => ?_)
    change (if magSumS σ = k then WithLp.ofLp v σ + WithLp.ofLp w σ else 0)
        = (if magSumS σ = k then WithLp.ofLp v σ else 0)
          + (if magSumS σ = k then WithLp.ofLp w σ else 0)
    by_cases h : magSumS σ = k
    · rw [if_pos h, if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  map_smul' c v := by
    refine WithLp.ofLp_injective 2 (funext fun σ => ?_)
    change (if magSumS σ = k then c * WithLp.ofLp v σ else 0)
        = c * (if magSumS σ = k then WithLp.ofLp v σ else 0)
    by_cases h : magSumS σ = k
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, mul_zero]

/-- Component description of the sector projection. -/
private theorem ofLp_sectorProjE4 (k : ℕ) (v : ManyBodyVecE2 Λ N) (σ : Λ → Fin (N + 1)) :
    WithLp.ofLp (sectorProjE4 Λ N k v) σ = if magSumS σ = k then WithLp.ofLp v σ else 0 := rfl

/-- The sector projection lands in the sector. -/
theorem sectorProjE4_mem (k : ℕ) (v : ManyBodyVecE2 Λ N) :
    sectorProjE4 Λ N k v ∈ magSectorE2 Λ N k := by
  refine (mem_magSectorE3_iff Λ N k _).mpr fun σ hσ => ?_
  rw [ofLp_sectorProjE4, if_neg hσ]

/-- The sector projection is the identity on its own sector. -/
theorem sectorProjE4_of_mem (k : ℕ) (v : ManyBodyVecE2 Λ N) (hv : v ∈ magSectorE2 Λ N k) :
    sectorProjE4 Λ N k v = v := by
  have hv' := (mem_magSectorE3_iff Λ N k v).mp hv
  refine WithLp.ofLp_injective 2 (funext fun σ => ?_)
  rw [ofLp_sectorProjE4]
  by_cases h : magSumS σ = k
  · rw [if_pos h]
  · rw [if_neg h, hv' σ h]

/-- The sector projection kills every other sector. -/
theorem sectorProjE4_of_mem_ne (k j : ℕ) (hjk : j ≠ k) (v : ManyBodyVecE2 Λ N)
    (hv : v ∈ magSectorE2 Λ N j) : sectorProjE4 Λ N k v = 0 := by
  have hv' := (mem_magSectorE3_iff Λ N j v).mp hv
  refine WithLp.ofLp_injective 2 (funext fun σ => ?_)
  rw [ofLp_sectorProjE4]
  change (if magSumS σ = k then WithLp.ofLp v σ else 0) = 0
  by_cases h : magSumS σ = k
  · rw [if_pos h, hv' σ (by omega)]
  · rw [if_neg h]

omit [DecidableEq Λ] in
/-- The magnetisation index of a configuration is at most `|Λ|N`. -/
private theorem magSumS_leE4 (σ : Λ → Fin (N + 1)) : magSumS σ ≤ Fintype.card Λ * N := by
  unfold magSumS
  calc ∑ x : Λ, (σ x).val
      ≤ ∑ _x : Λ, N := Finset.sum_le_sum fun x _ => Nat.lt_succ_iff.mp (σ x).isLt
    _ = Fintype.card Λ * N := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Components of a finite sum of many-body vectors. -/
private theorem ofLp_sumE4 {ι : Type*} (s : Finset ι) (f : ι → ManyBodyVecE2 Λ N)
    (σ : Λ → Fin (N + 1)) :
    WithLp.ofLp (∑ i ∈ s, f i) σ = ∑ i ∈ s, WithLp.ofLp (f i) σ := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- **The magnetisation decomposition**: every many-body vector is the sum of its sector
components. -/
theorem sum_sectorProjE4 (v : ManyBodyVecE2 Λ N) :
    ∑ k ∈ Finset.range (Fintype.card Λ * N + 1), sectorProjE4 Λ N k v = v := by
  refine WithLp.ofLp_injective 2 (funext fun σ => ?_)
  rw [ofLp_sumE4]
  have hmem : magSumS σ ∈ Finset.range (Fintype.card Λ * N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (magSumS_leE4 Λ N σ))
  rw [Finset.sum_eq_single (magSumS σ)
    (fun j _ hj => by rw [ofLp_sectorProjE4, if_neg (Ne.symm hj)])
    (fun h => absurd hmem h), ofLp_sectorProjE4, if_pos rfl]

/-- A nonzero vector has a nonzero component in some sector of index at most `|Λ|N`. -/
theorem exists_sectorProjE4_ne_zero (v : ManyBodyVecE2 Λ N) (hv : v ≠ 0) :
    ∃ k, k ≤ Fintype.card Λ * N ∧ sectorProjE4 Λ N k v ≠ 0 := by
  by_cases hall : ∀ σ, WithLp.ofLp v σ = 0
  · have h0 : WithLp.ofLp v = WithLp.ofLp (0 : ManyBodyVecE2 Λ N) := funext hall
    exact absurd (WithLp.ofLp_injective 2 h0) hv
  · obtain ⟨σ, hσ⟩ := not_forall.mp hall
    refine ⟨magSumS σ, magSumS_leE4 Λ N σ, fun h => hσ ?_⟩
    have h' := congrFun (congrArg WithLp.ofLp h) σ
    rw [ofLp_sectorProjE4, if_pos rfl] at h'
    exact h'

/-- **Design §2.1 (E), step 4**: the sector components of an eigenvector are eigenvectors for the
same eigenvalue.  Only the sector invariance of `A` and the magnetisation decomposition are
used. -/
theorem sectorProjE4_eigen (A : ManyBodyOpS Λ N) (hA : Commute A (totalSpinSOp3 Λ N)) (μ : ℂ)
    (v : ManyBodyVecE2 Λ N) (heig : manyBodyLinE4 Λ N A v = μ • v) (k : ℕ)
    (hk : k ≤ Fintype.card Λ * N) :
    manyBodyLinE4 Λ N A (sectorProjE4 Λ N k v) = μ • sectorProjE4 Λ N k v := by
  have hkmem : k ∈ Finset.range (Fintype.card Λ * N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have key : sectorProjE4 Λ N k (manyBodyLinE4 Λ N A v)
      = manyBodyLinE4 Λ N A (sectorProjE4 Λ N k v) := by
    conv_lhs => rw [← sum_sectorProjE4 Λ N v]
    rw [map_sum, map_sum,
      Finset.sum_eq_single k
        (fun j _ hj => sectorProjE4_of_mem_ne Λ N k j hj _
          (manyBodyLinE4_mem_magSector Λ N A hA j _ (sectorProjE4_mem Λ N j v)))
        (fun h => absurd hkmem h),
      sectorProjE4_of_mem Λ N k _
        (manyBodyLinE4_mem_magSector Λ N A hA k _ (sectorProjE4_mem Λ N k v))]
  rw [← key, heig, map_smul]

/-! ## 6. The general spectral reduction -/

/-- **Design §2.1 (E), general form**: if `A` commutes with `Ŝ⁺_tot` and with `Ŝ³_tot`, then every
eigenvalue of `A` on the many-body Hilbert space is already an eigenvalue of `A` on one of the
highest-weight spaces `hw_j` with `2j ≤ |Λ|N`.

This is the dimensional reduction that makes the Knabe window inequality a finite problem: the
whole space is replaced by the highest-weight blocks, and the sectors with `2j > |Λ|N` are excluded
by `eq_zero_of_mem_highestWeightE4`. -/
theorem exists_mem_highestWeightE4 (A : ManyBodyOpS Λ N) (hAplus : Commute A (totalSpinSOpPlus Λ N))
    (hA3 : Commute A (totalSpinSOp3 Λ N)) (μ : ℂ) (v : ManyBodyVecE2 Λ N) (hv : v ≠ 0)
    (heig : manyBodyLinE4 Λ N A v = μ • v) :
    ∃ j, 2 * j ≤ Fintype.card Λ * N ∧
      ∃ u ∈ highestWeightE2 Λ N j, u ≠ 0 ∧ manyBodyLinE4 Λ N A u = μ • u := by
  obtain ⟨k, hk, hne⟩ := exists_sectorProjE4_ne_zero Λ N v hv
  obtain ⟨j, _, u, hu, hu0, hueig⟩ :=
    exists_mem_highestWeightE4_of_mem_magSector Λ N A hAplus μ k (sectorProjE4 Λ N k v)
      (sectorProjE4_mem Λ N k v) hne (sectorProjE4_eigen Λ N A hA3 μ v heig k hk)
  rcases Nat.lt_or_ge (Fintype.card Λ * N) (2 * j) with h | h
  · exact absurd (eq_zero_of_mem_highestWeightE4 Λ N j h u hu) hu0
  · exact ⟨j, h, u, hu, hu0, hueig⟩

/-! ## 7. The AKLT window: reduction to the five blocks of dimensions `1, 3, 6, 6, 3` -/

section Window

/-- **`SU(2)` invariance of a single bond operator against the total `3`-axis operator**,
`[Ŝ_x · Ŝ_y, Ŝ³_tot] = 0`; the axis-3 companion of the Gate E1b commutation, from the production
lemma `spinSDot_commutator_totalSpinSOp3` (Tasaki §2.2 eq. (2.2.17), p. 24, spin-`S` form). -/
private theorem spinSDot_commute_totalSpinSOp3E4 (x y : Λ) :
    Commute (spinSDot x y N) (totalSpinSOp3 Λ N) := by
  unfold Commute SemiconjBy
  exact sub_eq_zero.mp (spinSDot_commutator_totalSpinSOp3 x y N)

/-- **`SU(2)` invariance of the AKLT bond projection against `Ŝ³_tot`**: `[P̂_{x,y}, Ŝ³_tot] = 0`,
term by term in the polynomial `½ D + ⅙ D² + ⅓` of Tasaki eq. (7.1.6), p. 182. -/
private theorem bondSpin2ProjectionS_commute_totalSpinSOp3E4 {L : ℕ} (x y : Fin L) :
    Commute (bondSpin2ProjectionS x y : ManyBodyOpS (Fin L) 2) (totalSpinSOp3 (Fin L) 2) := by
  have h : Commute (spinSDot x y 2 : ManyBodyOpS (Fin L) 2) (totalSpinSOp3 (Fin L) 2) :=
    spinSDot_commute_totalSpinSOp3E4 (Fin L) 2 x y
  simp only [bondSpin2ProjectionS]
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact h.smul_left _
  · exact (h.mul_left h).smul_left _
  · exact (Commute.one_left _).smul_left _

/-- **The open three-bond AKLT window commutes with the total `3`-axis operator**,
`[ĥ, Ŝ³_tot] = 0` with `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃` on `(ℂ³)^{⊗4}` (Tasaki eq. (7.1.30) with `ℓ = 3`,
p. 189).  Together with the Gate E1b commutation `[ĥ, Ŝ⁺_tot] = 0` this is exactly the input of
`exists_mem_highestWeightE4`. -/
theorem akltWindow3H_commute_totalSpinSOp3E4 :
    Commute akltWindow3H (totalSpinSOp3 (Fin 4) 2) := by
  simp only [akltWindow3H]
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · exact bondSpin2ProjectionS_commute_totalSpinSOp3E4 _ _
  · exact bondSpin2ProjectionS_commute_totalSpinSOp3E4 _ _
  · exact bondSpin2ProjectionS_commute_totalSpinSOp3E4 _ _

/-- **Gate E4 target**: every eigenvalue of the open three-bond AKLT window `ĥ` on `(ℂ³)^{⊗4}` is
already an eigenvalue of `ĥ` restricted to one of the five highest-weight spaces `hw_k`,
`k = 0, 1, 2, 3, 4`, whose dimensions are `1, 3, 6, 6, 3` (Gate E3
`finrank_highestWeightE3_window`).

This is the dimensional reduction `81 → 1 + 3 + 6 + 6 + 3` announced in the design note §2.1 (E):
the Knabe inequality `ĥ² ≥ (2/5) ĥ` (Tasaki §7.1.4, pp. 188–190; Knabe 1988) now only has to be
checked on those five blocks, since a nonzero `u ∈ hw_k` with `ĥ u = μ u` gives
`⟪u, (ĥ² − (2/5)ĥ) u⟫ = (μ² − (2/5)μ) ‖u‖²`.

Cross-checked before formalisation by exact rational arithmetic on the full `81 × 81` matrices:
the squarefree polynomial built from the characteristic polynomials of the five blocks (degree 17)
annihilates `ĥ` exactly, while dropping any single block breaks that (negative controls at several
`k`). -/
theorem akltWindow3H_eigenvalue_reduction_highestWeightE4 (μ : ℂ) (v : ManyBodyVecE2 (Fin 4) 2)
    (hv : v ≠ 0) (heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H v = μ • v) :
    ∃ k ≤ 4, ∃ u ∈ highestWeightE2 (Fin 4) 2 k, u ≠ 0 ∧
      manyBodyLinE4 (Fin 4) 2 akltWindow3H u = μ • u := by
  obtain ⟨j, hj, u, hu, hu0, hueig⟩ :=
    exists_mem_highestWeightE4 (Fin 4) 2 akltWindow3H akltWindow3H_commute_totalSpinSOpPlus
      akltWindow3H_commute_totalSpinSOp3E4 μ v hv heig
  rw [Fintype.card_fin] at hj
  exact ⟨j, by omega, u, hu, hu0, hueig⟩

end Window

end LatticeSystem.Quantum.AKLTSl2WindowReductionE4
