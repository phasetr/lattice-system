import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveTotalSpinEigenstate
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveNormFoundation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGammaCoords

/-!
# The balanced ground state is a spin singlet `(Ŝ_tot)² = 0` (Tasaki §10.2.4)

Singlet step of **Tasaki Theorem 10.2** (Lieb's theorem for the attractive Hubbard model).  The
eigenstate step (`balancedGround_totalSpinSquared_eigenvector`, PR-C) shows the unique balanced
ground state `ψ` is a `(Ŝ_tot)²`-eigenstate with some real eigenvalue `μ`.  Here we identify
`μ = 0`, i.e. the balanced ground state is a spin singlet `S_tot = 0`.

Tasaki's argument (§10.2.4, p. 365): the reconciliation coefficient `W_GS` of the ground state is
sign-definite (Lemma 10.9), so its diagonal entry `(W_GS)_{A,A} ≠ 0` for any balanced sector index
`A`.  Hence the ground state has a nonzero component on the *doubly-occupied* reference state
`|Ξ_{A,A}⟩` (up and down electrons on the same sites), which is manifestly a singlet.  A pure
`(Ŝ_tot)²`-eigenstate with a nonzero overlap onto `ker (Ŝ_tot)²` must have eigenvalue `0`.

Concretely, for a fixed count-`k` configuration `u` we take the explicit reference
`ref := Γ(E_{u,u}) = gammaWState N (single u u 1)`.  Two elementary facts drive the proof:

* **`ref` is a singlet** (`fermionTotalSpinSquared_mulVec_basisVec_merge_self`): the doubly-occupied
  configuration `merge u u` has `Ŝ⁺` annihilating it (each occupied-down site has an occupied up, so
  `c†_↑ c_↓` vanishes) and `Ŝ³ = 0` (balanced), hence `(Ŝ_tot)² · ref = 0`.
* **Nonzero overlap** (`hermitianW_balanced_ground_signDefinite`, Lemma 10.9): the diagonal entry
  `(blockWCoeff φ)_{u,u}` of a Hermitian-`W` balanced ground `φ` is nonzero, and equals
  `⟨ref, φ⟩` through the coordinate isometry (`blockWCoeff_dotProduct_cross_eq`).

## Main results

* `gammaWState_single_diag` — `Γ(E_{u,u})` is a scalar multiple of the doubly-occupied basis config
  `basisVec (merge u u)`.
* `fermionTotalSpinSquared_mulVec_basisVec_merge_self` — the doubly-occupied config is a singlet:
  `(Ŝ_tot)² · |merge u u⟩ = 0`.
* `balancedGround_totalSpinSquared_eigenvalue_zero` — **the singlet capstone:** any nonzero balanced
  ground state `ψ` satisfies `(Ŝ_tot)² · ψ = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.4 (Theorem 10.2), pp. 363–366; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix Module LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-! ## The doubly-occupied reference configuration is a singlet -/

/-- **`Ŝ⁺` annihilates the doubly-occupied configuration.**  On `merge u u` every site is either
empty or doubly occupied, so each summand `c†_{i,↑} c_{i,↓}` vanishes: if the down orbital is empty
`c_{i,↓}` kills the state, and if it is occupied then (removing it) the up orbital is still
occupied, so `c†_{i,↑}` kills the state. -/
theorem fermionTotalSpinPlus_mulVec_basisVec_merge_self (u : hubbardSpinConfig N) :
    (fermionTotalSpinPlus N).mulVec (basisVec (hubbardMergeConfig N u u)) = 0 := by
  unfold fermionTotalSpinPlus
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [← Matrix.mulVec_mulVec]
  unfold fermionDownAnnihilation
  rw [fermionMultiAnnihilation_mulVec_basisVec]
  by_cases hui : hubbardMergeConfig N u u (spinfulIndex N i 1) = 1
  · rw [if_pos hui, Matrix.mulVec_smul]
    unfold fermionUpCreation
    rw [fermionMultiCreation_mulVec_basisVec]
    have hup_occ :
        Function.update (hubbardMergeConfig N u u) (spinfulIndex N i 1) 0 (spinfulIndex N i 0)
          ≠ 0 := by
      rw [Function.update_of_ne (spinfulIndex_up_ne_down N i i),
        hubbardMergeConfig_spinfulIndex_zero]
      rw [hubbardMergeConfig_spinfulIndex_one] at hui
      intro h0
      rw [h0] at hui
      exact absurd hui (by decide)
    rw [if_neg hup_occ, smul_zero]
  · rw [if_neg hui, Matrix.mulVec_zero]

/-- **`Ŝ³` annihilates the doubly-occupied configuration.**  On `merge u u` the up and down
occupation numbers agree site by site, so `Ŝ³ = (N̂_↑ − N̂_↓)/2` has eigenvalue `0`. -/
theorem fermionTotalSpinZ_mulVec_basisVec_merge_self (u : hubbardSpinConfig N) :
    (fermionTotalSpinZ N).mulVec (basisVec (hubbardMergeConfig N u u)) = 0 := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec]
  have hud : (fermionTotalUpNumber N).mulVec (basisVec (hubbardMergeConfig N u u))
      = (fermionTotalDownNumber N).mulVec (basisVec (hubbardMergeConfig N u u)) := by
    unfold fermionTotalUpNumber fermionTotalDownNumber
    rw [Matrix.sum_mulVec, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold fermionUpNumber fermionDownNumber
    rw [fermionMultiNumber_mulVec_basisVec, fermionMultiNumber_mulVec_basisVec,
      hubbardMergeConfig_spinfulIndex_zero, hubbardMergeConfig_spinfulIndex_one]
  rw [hud, sub_self, smul_zero]

/-- **The doubly-occupied configuration is a spin singlet:** `(Ŝ_tot)² · |merge u u⟩ = 0`.  Both
Casimir terms vanish: `Ŝ⁻Ŝ⁺` because `Ŝ⁺` annihilates it
(`fermionTotalSpinPlus_mulVec_basisVec_merge_self`), and `Ŝ³(Ŝ³ + 1)` because `Ŝ³` annihilates it
(`fermionTotalSpinZ_mulVec_basisVec_merge_self`). -/
theorem fermionTotalSpinSquared_mulVec_basisVec_merge_self (u : hubbardSpinConfig N) :
    (fermionTotalSpinSquared N).mulVec (basisVec (hubbardMergeConfig N u u)) = 0 := by
  unfold fermionTotalSpinSquared
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    fermionTotalSpinPlus_mulVec_basisVec_merge_self, Matrix.mulVec_zero, zero_add,
    ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    fermionTotalSpinZ_mulVec_basisVec_merge_self, zero_add,
    fermionTotalSpinZ_mulVec_basisVec_merge_self]

/-! ## The explicit singlet reference state -/

/-- **The Γ-realization of the diagonal elementary matrix is a doubly-occupied basis config.**  The
inverse coefficient isomorphism sends `E_{u,u} = single u u 1` to the delta at the block merge
`merge u u`, and the block↔interleaved permutation operator carries it (up to a Jordan–Wigner `±1`
sign) to the doubly-occupied interleaved configuration `hubbardMergeConfig u u`. -/
theorem gammaWState_single_diag (u : hubbardSpinConfig N) :
    gammaWState N (Matrix.single u u 1)
      = translationJwSign (hubbardBlockToSpinfulOrbitalEquiv N)
            (hubbardBlockMergeConfig N u u)
          • basisVec (hubbardMergeConfig N u u) := by
  unfold gammaWState
  have hLE : (hubbardBlockCoeffLinearEquiv N).symm (Matrix.single u u 1)
      = basisVec (hubbardBlockMergeConfig N u u) := by
    funext c
    change (Matrix.single u u 1) (hubbardBlockUpConfig N c) (hubbardBlockDownConfig N c)
      = basisVec (hubbardBlockMergeConfig N u u) c
    rw [Matrix.single_apply, basisVec_apply]
    by_cases hc : c = hubbardBlockMergeConfig N u u
    · rw [if_pos hc, if_pos ?_]
      subst hc
      exact ⟨(hubbardBlockUpConfig_merge N u u).symm, (hubbardBlockDownConfig_merge N u u).symm⟩
    · rw [if_neg hc, if_neg ?_]
      rintro ⟨h1, h2⟩
      exact hc (by rw [← hubbardBlockMergeConfig_up_down N c, ← h1, ← h2])
  rw [hLE, hubbardBlockToSpinfulPermutationOperator_mulVec_basisVec,
    hubbardBlockToSpinfulConfigEquiv_hubbardBlockMergeConfig]

/-! ## The singlet capstone -/

/-- Transpose of the diagonal elementary matrix `E_{u,u} = single u u 1` (with real unit entry) is
itself. -/
private theorem conjTranspose_single_diag (u : hubbardSpinConfig N) :
    (Matrix.single u u (1 : ℂ))ᴴ = Matrix.single u u 1 := by
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h : u = a ∧ u = b
  · obtain ⟨ha, hb⟩ := h
    rw [if_pos ⟨hb, ha⟩, if_pos ⟨ha, hb⟩, star_one]
  · rw [if_neg (fun hh => h ⟨hh.2, hh.1⟩), if_neg h, star_zero]

/-- **The balanced ground state is a spin singlet (Tasaki §10.2.4 Theorem 10.2).** For an attractive
Hubbard model with symmetric real hopping `T` whose support graph is connected and strictly
attractive on-site interaction `U > 0`, any nonzero balanced ground state `ψ` (a vector in
`balancedGroundEigenspace`) satisfies `(Ŝ_tot)² · ψ = 0`, i.e. has total spin `S_tot = 0`.

Proof (§10.2.4, p. 365): let `E = min_spec` and take the Hermitian-`W` balanced ground
representative `φ` of Lemma 10.9 (`exists_signDefiniteCompress_ground_in_balanced_sector`).  Since
the balanced ground eigenspace has `finrank ≤ 1` (`balanced_ground_eigenspace_finrank_le_one`) and
`ψ ≠ 0`, `φ = c • ψ`, so `φ` is also a `(Ŝ_tot)²`-eigenstate with the same eigenvalue `μ` (PR-C,
`balancedGround_totalSpinSquared_eigenvector`).  For a count-`k` sector index `s` with `u = s.val`,
the reference `ref = Γ(E_{u,u})` is a singlet
(`fermionTotalSpinSquared_mulVec_basisVec_merge_self` via `gammaWState_single_diag`) and its overlap
`⟨ref, φ⟩ = (blockWCoeff φ)_{u,u}` (`blockWCoeff_dotProduct_cross_eq`) is nonzero because the
compressed coefficient `Jᴴ (blockWCoeff φ) J` is sign-definite, so its diagonal is nonzero
(`Matrix.PosDef.diag_pos`).  Hermiticity of `(Ŝ_tot)²` gives
`μ ⟨ref, φ⟩ = ⟨ref, (Ŝ_tot)² φ⟩ = ⟨(Ŝ_tot)² ref, φ⟩ = 0`, hence `μ = 0` and
`(Ŝ_tot)² ψ = μ • ψ = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.4 (Theorem 10.2), pp. 363–366. -/
theorem balancedGround_totalSpinSquared_eigenvalue_zero (k : ℕ)
    [Nonempty (hubbardBalancedConfig N k)] [Nonempty (hubbardSpinCountSector N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hψ : ψ ∈ balancedGroundEigenspace k T U hT_symm) (hψ0 : ψ ≠ 0) :
    (fermionTotalSpinSquared N).mulVec ψ = 0 := by
  classical
  -- PR-C: `ψ` is a `(Ŝ_tot)²`-eigenstate with real eigenvalue `μ`.
  obtain ⟨μ, hμ⟩ :=
    balancedGround_totalSpinSquared_eigenvector k T U hT_symm hU_pos hT_conn hψ hψ0
  -- Lemma 10.9: a nonzero Hermitian-`W` balanced ground `φ` with sign-definite compressed `W_S`.
  obtain ⟨φ, hφ0, hφUp, hφDn, _hφHerm, hsign, hφeig⟩ :=
    exists_signDefiniteCompress_ground_in_balanced_sector k T U hT_symm hU_pos hT_conn
  have hφmem : φ ∈ balancedGroundEigenspace k T U hT_symm :=
    (mem_balancedGroundEigenspace_iff k T U hT_symm φ).mpr ⟨hφeig, hφUp, hφDn⟩
  -- `finrank ≤ 1` forces `φ = c • ψ`, so `φ` is a `μ`-eigenstate of `(Ŝ_tot)²` as well.
  have hle := balanced_ground_eigenspace_finrank_le_one k T U hT_symm hU_pos hT_conn
  obtain ⟨c, hc⟩ := exists_smul_of_mem_of_finrank_le_one hle hψ hφmem hψ0
  have hφeigS : (fermionTotalSpinSquared N).mulVec φ = (μ : ℂ) • φ := by
    rw [← hc, Matrix.mulVec_smul, hμ, smul_comm]
  -- The explicit singlet reference for a balanced sector index `u = s.val`.
  obtain ⟨s⟩ := ‹Nonempty (hubbardSpinCountSector N k)›
  set u : hubbardSpinConfig N := s.val with hu
  set ref := gammaWState N (Matrix.single u u 1) with href
  -- `ref` is a singlet (`(Ŝ_tot)² · ref = 0`).
  have href_ker : (fermionTotalSpinSquared N).mulVec ref = 0 := by
    rw [href, gammaWState_single_diag, Matrix.mulVec_smul,
      fermionTotalSpinSquared_mulVec_basisVec_merge_self, smul_zero]
  -- The overlap `⟨ref, φ⟩` reads off the diagonal `(blockWCoeff φ)_{u,u}`.
  have hbwref : blockWCoeff N ref = Matrix.single u u 1 := by
    rw [href, blockWCoeff, blockWCoeff_gammaWState]
  have hoverlap : dotProduct (star ref) φ = blockWCoeff N φ u u := by
    rw [blockWCoeff_dotProduct_cross_eq, hbwref, conjTranspose_single_diag,
      Matrix.trace_single_mul, one_smul]
  -- Lemma 10.9 sign-definiteness makes the diagonal `(blockWCoeff φ)_{u,u}` nonzero.
  have hdiag : blockWCoeff N φ u u ≠ 0 := by
    have hval : ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
        * hubbardCountSectorEmbedding N k) s s = blockWCoeff N φ u u := by
      rw [hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply, hu]
    rw [← hval]
    rcases hsign with hpos | hneg
    · exact ne_of_gt (hpos.diag_pos (i := s))
    · have hd := hneg.diag_pos (i := s)
      rw [Matrix.neg_apply] at hd
      intro hzero
      rw [hzero, neg_zero] at hd
      exact lt_irrefl 0 hd
  -- Hermiticity of `(Ŝ_tot)²` + `ref ∈ ker` give `μ · ⟨ref, φ⟩ = 0`.
  have hAB : (μ : ℂ) * dotProduct (star ref) φ = 0 := by
    have hA : dotProduct (star ref) ((fermionTotalSpinSquared N).mulVec φ) = 0 := by
      rw [dotProduct_mulVec]
      have hz : star ref ᵥ* (fermionTotalSpinSquared N) = 0 := by
        have hsm := star_mulVec (fermionTotalSpinSquared N) ref
        rw [(fermionTotalSpinSquared_isHermitian N).eq] at hsm
        rw [← hsm, href_ker, star_zero]
      rw [hz, zero_dotProduct]
    rw [hφeigS, dotProduct_smul, smul_eq_mul] at hA
    exact hA
  -- `⟨ref, φ⟩ ≠ 0` forces `μ = 0`, hence `(Ŝ_tot)² ψ = μ • ψ = 0`.
  rw [hoverlap] at hAB
  rcases mul_eq_zero.mp hAB with hμ0 | hcontra
  · rw [hμ, hμ0, zero_smul]
  · exact absurd hcontra hdiag

end LatticeSystem.Fermion

