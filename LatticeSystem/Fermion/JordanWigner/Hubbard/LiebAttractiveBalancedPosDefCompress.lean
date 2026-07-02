import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedPosSemidefGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInteractionTrace
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGroundLyapunov
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorConnectivity
import LatticeSystem.Math.PosSemidef.GroundKernelPropagation
import LatticeSystem.Math.PosSemidef.SeparatingProjectionKernel
import LatticeSystem.Math.PosSemidef.ConnectedSupportDichotomy
import LatticeSystem.Math.PosSemidef.LyapunovIsometryCompress

/-!
# Sector-compression glue for the balanced-sector positive-definite ground (Tasaki §10.2.4)

Layer toward discharging `theorem_10_2_lieb_attractive_unique_singlet` (Tasaki Lemma 10.10). The
abstract connected-support dichotomy (`posDef_or_eq_zero_of_connected_support`) and the separating
projection kernel argument (`basis_mem_ker_of_separating_projections`) run on the *sector* index
type `hubbardSpinCountSector N k`, whereas the concrete operators (kinetic matrix, site-occupation
diagonals) live on the full `W`-index space `hubbardSpinConfig N`. Bridging the two requires reading
off entries through the standard-basis isometry `J = hubbardCountSectorEmbedding N k`.

Since each column `J · s` of the embedding is the standard basis vector `|s.val⟩`, conjugation by
`Jᴴ · (−) · J` simply reads off the `(s.val, s'.val)` matrix entry:

* the **entry readoff** `(Jᴴ · M · J) s s' = M s.val s'.val` (`basisVec` selector-sum
  collapse), which makes the compressed kinetic matrix's adjacency match
  `hubbardKineticSectorGraph_adj_entry_ne`, and
* the **occupation diagonal compression** `Jᴴ · D_x · J = diagonal (s ↦ (s.val x))`, immediate from
  the readoff plus injectivity of the subtype value, feeding the separating-projection kernel step.

## Main results

* `hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply` — the entry readoff
  `(Jᴴ · M · J) s s' = M s.val s'.val`.
* `hubbardCountSectorEmbedding_conjTranspose_mul_upOccupationDiag_mul` — the site-`x` up-occupation
  diagonal compresses to the sector-restricted occupation diagonal
  `diagonal (s ↦ (s.val x))`.
* `blockWCoeff_sectorCompress_ne_zero_of_ne_zero` — for a nonzero balanced state `ψ`, the
  sector-compressed coefficient `R_k = Jᴴ · blockWCoeff ψ · J` is nonzero (the nonvanishing input
  to the connected-support dichotomy `R ≠ 0 ⟹ R.PosDef`).
* `exists_posDefCompress_ground_in_balanced_sector` — **the assembly capstone (Lemma 10.10).** For
  strictly attractive `U > 0` and connected symmetric hopping `T`, the balanced
  positive-semidefinite ground state `φ` of PR40f has a *positive-definite* sector-compressed
  coefficient `R_k = Jᴴ · blockWCoeff φ · J`.
* `exists_signDefiniteCompress_ground_in_balanced_sector` — **the assembly capstone (Lemma 10.9).**
  For strictly attractive `U > 0` and connected symmetric hopping `T`, there is a balanced
  Hermitian-`W` ground state `φ` whose compressed coefficient `W_S = Jᴴ · blockWCoeff φ · J` is
  *sign-definite*: `W_S.PosDef ∨ (−W_S).PosDef`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemmas 10.9–10.10), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- **Entry readoff through the sector embedding.** Since column `s` of the isometry
`J = hubbardCountSectorEmbedding N k` is the standard basis vector `|s.val⟩`, the conjugation
`Jᴴ · M · J` reads off the `(s.val, s'.val)` entry of `M`:
`(Jᴴ · M · J) s s' = M s.val s'.val`. Both collapses use `basisVec` selector sums. -/
theorem hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply (k : ℕ)
    (M : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ)
    (s s' : hubbardSpinCountSector N k) :
    ((hubbardCountSectorEmbedding N k)ᴴ * M * hubbardCountSectorEmbedding N k) s s'
      = M s.val s'.val := by
  set J := hubbardCountSectorEmbedding N k with hJ
  -- Entrywise readouts of `J` and `Jᴴ` (columns are standard basis vectors).
  have hJapply : ∀ (w : hubbardSpinConfig N) (t : hubbardSpinCountSector N k),
      J w t = basisVec t.val w := fun w t => by
    rw [hJ, hubbardCountSectorEmbedding, Matrix.of_apply]
  have hJHapply : ∀ (t : hubbardSpinCountSector N k) (w : hubbardSpinConfig N),
      Jᴴ t w = basisVec t.val w := fun t w => by
    rw [Matrix.conjTranspose_apply, hJapply,
      show star (basisVec t.val w) = basisVec t.val w from by
        rw [basisVec_apply]; split <;> simp]
  -- Outer product: collapse the right factor `J _ s' = basisVec s'.val _`.
  rw [Matrix.mul_apply,
    show (∑ w', (Jᴴ * M) s w' * J w' s')
        = ∑ w', (Jᴴ * M) s w' * basisVec s'.val w' from
      Finset.sum_congr rfl (fun w' _ => by rw [hJapply]),
    sum_mul_basisVec s'.val (fun w' => (Jᴴ * M) s w')]
  -- Inner product: collapse the left factor `Jᴴ s _ = basisVec s.val _`.
  rw [Matrix.mul_apply,
    show (∑ w, Jᴴ s w * M w s'.val) = ∑ w, basisVec s.val w * M w s'.val from
      Finset.sum_congr rfl (fun w _ => by rw [hJHapply]),
    basisVec_sum_mul s.val (fun w => M w s'.val)]

/-- **Occupation diagonal compression.** The full-space site-`x` up-occupation diagonal
`D_x = hubbardUpOccupationDiag N x` compresses through the sector embedding to the
sector-restricted occupation diagonal `diagonal (s ↦ (s.val x))`. Immediate from the entry
readoff plus injectivity of the subtype value. -/
theorem hubbardCountSectorEmbedding_conjTranspose_mul_upOccupationDiag_mul (k : ℕ)
    (x : Fin (N + 1)) :
    (hubbardCountSectorEmbedding N k)ᴴ * hubbardUpOccupationDiag N x
        * hubbardCountSectorEmbedding N k
      = Matrix.diagonal (fun s : hubbardSpinCountSector N k => ((s.val x).val : ℂ)) := by
  ext s s'
  rw [hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply, hubbardUpOccupationDiag,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : s = s'
  · rw [h, if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg (fun hc => h (Subtype.ext hc))]

/-- **Nonvanishing of the sector-compressed coefficient.** For a nonzero state `ψ` in the balanced
sector (`N̂_↑ ψ = N̂_↓ ψ = k·ψ`), its sector compression `R_k = Jᴴ · blockWCoeff ψ · J` through the
embedding `J = hubbardCountSectorEmbedding N k` is nonzero. Indeed, if `R_k = 0` then the balanced
principal-block rewrite `blockWCoeff ψ = J · R_k · Jᴴ` (`blockWCoeff_eq_embed_compress_of_balanced`)
collapses to `blockWCoeff ψ = 0`; but the coordinate map `ψ ↦ blockWCoeff ψ` is a norm isometry
(`blockWCoeff_dotProduct_eq`), so `⟨ψ, ψ⟩ = Σ |blockWCoeff ψ|² = 0` would force `ψ = 0`, a
contradiction. This is the nonvanishing input `R ≠ 0` feeding the connected-support dichotomy
`R ≠ 0 ⟹ R.PosDef` of Tasaki §10.2.4 Lemma 10.10. -/
theorem blockWCoeff_sectorCompress_ne_zero_of_ne_zero (k : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) (hψ : ψ ≠ 0)
    (hUp : (fermionTotalUpNumber N).mulVec ψ = (k : ℂ) • ψ)
    (hDn : (fermionTotalDownNumber N).mulVec ψ = (k : ℂ) • ψ) :
    (hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N ψ
        * hubbardCountSectorEmbedding N k ≠ 0 := by
  intro hRk0
  -- `R_k = 0` collapses the balanced principal-block rewrite to `blockWCoeff ψ = 0`.
  have hW0 : blockWCoeff N ψ = 0 := by
    have h := blockWCoeff_eq_embed_compress_of_balanced k ψ hUp hDn
    rw [hRk0] at h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]
  -- The isometry `⟨ψ, ψ⟩ = Σ |blockWCoeff ψ|²` then forces every coordinate of `ψ` to vanish.
  apply hψ
  funext c
  have hdot : dotProduct (star ψ) ψ = 0 := by
    rw [blockWCoeff_dotProduct_eq, hW0]
    simp
  rw [dotProduct_star_self_eq_sum_normSq] at hdot
  have hreal : (∑ c, Complex.normSq (ψ c)) = 0 := by
    have h2 : ((∑ c, Complex.normSq (ψ c) : ℝ) : ℂ) = 0 := by
      rw [Complex.ofReal_sum]; exact hdot
    exact_mod_cast h2
  have hc : Complex.normSq (ψ c) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => Complex.normSq_nonneg _)).mp hreal c
      (Finset.mem_univ c)
  exact Complex.normSq_eq_zero.mp hc

/-- **The compressed-coefficient dichotomy** (Tasaki §10.2.4, Lemma 10.10, reusable core). Let
`R = Jᴴ · (−) · J` be *any* positive-semidefinite matrix on the count sector
`hubbardSpinCountSector N k` that solves the compressed Lyapunov/Schrödinger equation
`A_k·R + R·A_kᴴ − Σ_x U_x·(I_x^k·R·I_x^k) = E·R`, where `A_k = Jᴴ·A₀·J` is the compressed kinetic
matrix (`A₀ = hubbardBlockKineticUpFixedMatrix N (T·)`) and `I_x^k = Jᴴ·D_x·J` are the compressed
site-`x` up-occupation projections (`D_x = hubbardUpOccupationDiag N x`), for strictly attractive
`U > 0` and connected symmetric hopping `T`. Then `R` is *positive definite or zero*:

* PSD `R` solving the equation has kernel invariant under `A_k` and each `I_x^k`
  (`posSemidef_ground_kernel_propagation`), the latter reading off as the sector occupation diagonal
  (`hubbardCountSectorEmbedding_conjTranspose_mul_upOccupationDiag_mul`); separation of site
  occupations forces basis vectors into `ker R` (`basis_mem_ker_of_separating_projections`);
* connectivity of the kinetic sector graph (`hubbardKineticSectorGraph_preconnected`), whose edges
  witness nonzero compressed kinetic entries (the entry readoff
  `hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply` plus
  `hubbardKineticSectorGraph_adj_entry_ne`), yields the dichotomy
  (`posDef_or_eq_zero_of_connected_support`).

This is the reusable core shared by the Lemma 10.10 capstone
(`exists_posDefCompress_ground_in_balanced_sector`, applied to the balanced ground coefficient) and
the Lemma 10.9 assembly (applied to `|W_S| − W_S`). -/
theorem posDefCompress_dichotomy (k : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    {R : Matrix (hubbardSpinCountSector N k) (hubbardSpinCountSector N k) ℂ}
    (hR : R.PosSemidef) {E : ℝ}
    (hEq : (hubbardCountSectorEmbedding N k)ᴴ
            * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ))
            * hubbardCountSectorEmbedding N k * R
          + R * ((hubbardCountSectorEmbedding N k)ᴴ
              * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ))
              * hubbardCountSectorEmbedding N k)ᴴ
          - ∑ x, (U x : ℂ) • ((hubbardCountSectorEmbedding N k)ᴴ
              * hubbardUpOccupationDiag N x * hubbardCountSectorEmbedding N k * R
              * ((hubbardCountSectorEmbedding N k)ᴴ * hubbardUpOccupationDiag N x
                * hubbardCountSectorEmbedding N k))
          = (E : ℂ) • R) :
    R.PosDef ∨ R = 0 := by
  classical
  set J := hubbardCountSectorEmbedding N k
  -- Hermiticity of the compressed kinetic matrix and occupation projections.
  have hA_herm : (hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ))).IsHermitian := by
    refine hubbardBlockKineticUpFixedMatrix_isHermitian N (fun a b => ?_)
    simp only [← starRingEnd_apply, Complex.conj_ofReal]
    exact_mod_cast hT_symm a b
  have hAk_herm :
      (Jᴴ * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * J).IsHermitian := by
    change (Jᴴ * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * J)ᴴ
      = Jᴴ * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * J
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hA_herm.eq, Matrix.mul_assoc]
  have hIk_herm : ∀ x, (Jᴴ * hubbardUpOccupationDiag N x * J).IsHermitian := fun x => by
    change (Jᴴ * hubbardUpOccupationDiag N x * J)ᴴ = Jᴴ * hubbardUpOccupationDiag N x * J
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (hubbardUpOccupationDiag_isHermitian x).eq, Matrix.mul_assoc]
  -- Compressed occupation projections read off as sector occupation diagonals.
  have hdiag : ∀ x, Jᴴ * hubbardUpOccupationDiag N x * J
      = Matrix.diagonal (fun s : hubbardSpinCountSector N k => ((s.val x).val : ℂ)) :=
    fun x => hubbardCountSectorEmbedding_conjTranspose_mul_upOccupationDiag_mul k x
  -- Kernel propagation for the PSD solution `R` of the compressed Lyapunov equation.
  have kp : ∀ v : hubbardSpinCountSector N k → ℂ, R.mulVec v = 0
      → (∀ x, R.mulVec ((Jᴴ * hubbardUpOccupationDiag N x * J).mulVec v) = 0)
        ∧ R.mulVec ((Jᴴ * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * J).mulVec
            v) = 0 :=
    fun v hv => posSemidef_ground_kernel_propagation
      (A := Jᴴ * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * J)
      (I := fun x => Jᴴ * hubbardUpOccupationDiag N x * J)
      hAk_herm hIk_herm hR hU_pos hEq hv
  -- Kernel is invariant under the compressed kinetic matrix.
  have hAinv : ∀ v : hubbardSpinCountSector N k → ℂ, R.mulVec v = 0
      → R.mulVec
          ((Jᴴ * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * J).mulVec v) = 0 :=
    fun v hv => (kp v hv).2
  -- Kernel vectors with a nonzero coordinate force the corresponding basis vector into the kernel.
  have hbasis : ∀ v : hubbardSpinCountSector N k → ℂ, R.mulVec v = 0
      → ∀ a, v a ≠ 0 → R.mulVec (Pi.single a 1) = 0 := by
    intro v hv a ha
    refine basis_mem_ker_of_separating_projections
      (d := fun x s => ((s.val x).val : ℂ)) ?_ ?_ ?_ hv ha
    · intro x s
      have hlt : (s.val x).val < 2 := (s.val x).isLt
      rcases (show (s.val x).val = 0 ∨ (s.val x).val = 1 from by omega) with h | h
      · exact Or.inl (show ((s.val x).val : ℂ) = 0 by exact_mod_cast h)
      · exact Or.inr (show ((s.val x).val : ℂ) = 1 by exact_mod_cast h)
    · intro s t hst
      refine Subtype.ext (funext (fun x => Fin.ext ?_))
      have h : ((s.val x).val : ℂ) = ((t.val x).val : ℂ) := hst x
      exact_mod_cast h
    · intro x w hw
      have h := (kp w hw).1 x
      rwa [hdiag x] at h
  -- Edges of the connected kinetic sector graph witness nonzero compressed kinetic entries.
  have hGadj : ∀ b a, (hubbardKineticSectorGraph N (fun x y => (T x y : ℂ)) k).Adj b a
      → (Jᴴ * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * J) b a ≠ 0 := by
    intro b a hadj
    have hentry : (Jᴴ * hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) * J) b a
        = hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)) b.val a.val :=
      hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply k _ b a
    rw [hentry]
    exact hubbardKineticSectorGraph_adj_entry_ne hadj
  have hGconn : (hubbardKineticSectorGraph N (fun x y => (T x y : ℂ)) k).Preconnected :=
    hubbardKineticSectorGraph_preconnected hT_symm hT_conn
  -- The connected-support dichotomy.
  exact posDef_or_eq_zero_of_connected_support hR hAinv hbasis hGadj hGconn

/-- **The balanced-sector positive-definite ground coefficient** (Tasaki §10.2.4, Lemma 10.10).
For symmetric real hopping `T` whose support graph is connected and strictly attractive on-site
interaction `U > 0`, the balanced (`Ŝ³ = 0`) positive-semidefinite ground state `φ` of PR40f
(`exists_posSemidefW_ground_in_balanced_sector`) has a *positive-definite* sector-compressed
coefficient `R_k = Jᴴ · blockWCoeff φ · J`, `J = hubbardCountSectorEmbedding N k`. This is the
assembly of Tasaki's Lemma 10.10 dichotomy `R ≠ 0 ⟹ R.PosDef`:

* the full-space Lyapunov/Schrödinger equation of `W = blockWCoeff φ`
  (`blockWCoeff_lyapunov_of_eigenvector`) compresses through the isometry `J`
  (`lyapunov_conjugate_isometry`) to the sector equation for `R_k`;
* PSD `R_k` (`Matrix.PosSemidef.conjTranspose_mul_mul_same`) solving that equation has kernel
  invariant under the compressed kinetic matrix and each compressed occupation projection
  (`posSemidef_ground_kernel_propagation`), the latter reading off as the sector occupation diagonal
  (`hubbardCountSectorEmbedding_conjTranspose_mul_upOccupationDiag_mul`); separation of site
  occupations then forces basis vectors into `ker R_k`
  (`basis_mem_ker_of_separating_projections`);
* connectivity of the kinetic sector graph (`hubbardKineticSectorGraph_preconnected`), whose edges
  witness nonzero compressed kinetic entries (the entry readoff
  `hubbardCountSectorEmbedding_conjTranspose_mul_mul_apply` plus
  `hubbardKineticSectorGraph_adj_entry_ne`), yields the dichotomy `R_k.PosDef ∨ R_k = 0`
  (`posDef_or_eq_zero_of_connected_support`);
* nonvanishing of `R_k` (`blockWCoeff_sectorCompress_ne_zero_of_ne_zero`) resolves the dichotomy to
  `R_k.PosDef`.

Both the positive-definiteness of `R_k` and the eigenvector relation at the balanced minimum
eigenvalue `E` are retained, as the downstream Lemma 10.9 consumes both. -/
theorem exists_posDefCompress_ground_in_balanced_sector (k : ℕ)
    [Nonempty (hubbardBalancedConfig N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected) :
    ∃ φ : (Fin (2 * N + 2) → Fin 2) → ℂ, φ ≠ 0
      ∧ (fermionTotalUpNumber N).mulVec φ = (k : ℂ) • φ
      ∧ (fermionTotalDownNumber N).mulVec φ = (k : ℂ) • φ
      ∧ ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
          * hubbardCountSectorEmbedding N k).PosDef
      ∧ (attractiveHubbardHamiltonian N T U).mulVec φ
          = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
              (hubbardBalancedSectorPred N k)
              (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) : ℝ) : ℂ) • φ := by
  classical
  obtain ⟨φ, hφ0, hφUp, hφDn, hWpsd, heig⟩ :=
    exists_posSemidefW_ground_in_balanced_sector k T U hT_symm (fun x => (hU_pos x).le)
  set E : ℝ := hermitianMinEigenvalue (configSectorCompress_isHermitian
    (hubbardBalancedSectorPred N k)
    (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) with hEdef
  refine ⟨φ, hφ0, hφUp, hφDn, ?_, heig⟩
  -- The sector isometry `J` and the balanced principal-block rewrite `W = J · R_k · Jᴴ`.
  have hJ : (hubbardCountSectorEmbedding N k)ᴴ * hubbardCountSectorEmbedding N k = 1 :=
    hubbardCountSectorEmbedding_conjTranspose_mul_self k
  have hemb := blockWCoeff_eq_embed_compress_of_balanced k φ hφUp hφDn
  -- `R_k` is positive semidefinite (isometry compression of the PSD coefficient `W`).
  have hRk_psd : ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
      * hubbardCountSectorEmbedding N k).PosSemidef :=
    hWpsd.conjTranspose_mul_mul_same _
  -- The full-space Lyapunov equation of `W`, compressed to the sector equation for `R_k`.
  have hfull := blockWCoeff_lyapunov_of_eigenvector T U φ E heig
  have hcomp := Math.lyapunov_conjugate_isometry hJ hemb hfull
  -- The reusable compressed-coefficient dichotomy, resolved by nonvanishing of `R_k`.
  rcases posDefCompress_dichotomy k T U hT_symm hU_pos hT_conn hRk_psd hcomp with hpd | hz
  · exact hpd
  · exact absurd hz (blockWCoeff_sectorCompress_ne_zero_of_ne_zero k φ hφ0 hφUp hφDn)

/-- **The balanced-sector sign-definite compressed coefficient** (Tasaki §10.2.4, Lemma 10.9).
For symmetric real hopping `T` whose support graph is connected and strictly attractive on-site
interaction `U > 0`, there is a nonzero balanced (`Ŝ³ = 0`) ground state `φ` of the attractive
Hubbard Hamiltonian, at the balanced-compression minimum eigenvalue `E`, with Hermitian
reconciliation coefficient `blockWCoeff φ`, whose sector-compressed coefficient
`W_S = Jᴴ · blockWCoeff φ · J`, `J = hubbardCountSectorEmbedding N k`, is *sign-definite*:
`W_S.PosDef ∨ (−W_S).PosDef`. This is Tasaki's Lemma 10.9, assembled from Lemma 10.10's dichotomy:

* take a balanced Hermitian-`W` ground `φ` (`exists_hermitianW_ground_in_balanced_sector`); its
  compressed matrix `W_S` (Hermitian) solves the compressed Lyapunov/Schrödinger equation via
  `blockWCoeff_lyapunov_of_eigenvector` and `lyapunov_conjugate_isometry`;
* its spectral absolute value `P = |W_S|` (`hermitianAbs`) is PSD (`hermitianAbs_posSemidef`) and
  solves the *same* compressed equation, because `Γ(J·P·Jᴴ)` is again a `Ĥ`-ground at `E`
  (`gammaWState_hermitianAbs_isEigenvector`), whose block coefficient compresses back to `P`;
* the reusable dichotomy `posDefCompress_dichotomy` applied to `P` gives `P.PosDef ∨ P = 0`,
  resolved to `P.PosDef` since `W_S ≠ 0` (`blockWCoeff_sectorCompress_ne_zero_of_ne_zero`) forces
  `P ≠ 0` (`|W_S|² = W_S²` via `hermitianAbs_mul_self`, `conjTranspose_mul_self_eq_zero`);
* the difference `P − W_S` is PSD (`hermitianAbs_sub_posSemidef`) and solves the same equation
  (`lyapunovEq_sub`), so the dichotomy gives `(P − W_S).PosDef ∨ P − W_S = 0`;
* since `(P − W_S)·(P + W_S) = P² − W_S² = 0` (`hermitianAbs_commute` cancels the cross terms), in
  the first case `IsUnit (P − W_S)` (`Matrix.PosDef.isUnit`) cancels to `P + W_S = 0`, i.e.
  `−W_S = P` is positive definite, and in the second case `W_S = P` is positive definite.

Both the sign-definiteness of `W_S` and the eigenvector relation at the balanced minimum eigenvalue
`E` are retained, as the downstream uniqueness step (`Tr(W'W) > 0`) consumes both. -/
theorem exists_signDefiniteCompress_ground_in_balanced_sector (k : ℕ)
    [Nonempty (hubbardBalancedConfig N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected) :
    ∃ φ : (Fin (2 * N + 2) → Fin 2) → ℂ, φ ≠ 0
      ∧ (fermionTotalUpNumber N).mulVec φ = (k : ℂ) • φ
      ∧ (fermionTotalDownNumber N).mulVec φ = (k : ℂ) • φ
      ∧ (blockWCoeff N φ).IsHermitian
      ∧ (((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
              * hubbardCountSectorEmbedding N k).PosDef
          ∨ (-((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
              * hubbardCountSectorEmbedding N k)).PosDef)
      ∧ (attractiveHubbardHamiltonian N T U).mulVec φ
          = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
              (hubbardBalancedSectorPred N k)
              (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) : ℝ) : ℂ) • φ := by
  classical
  -- The balanced Hermitian-`W` ground representative (PR40e-pre2b).
  obtain ⟨φ, hφ0, hφUp, hφDn, hφHerm, hφeig⟩ :=
    exists_hermitianW_ground_in_balanced_sector k T U hT_symm
  set E : ℝ := hermitianMinEigenvalue (configSectorCompress_isHermitian
    (hubbardBalancedSectorPred N k)
    (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) with hEdef
  refine ⟨φ, hφ0, hφUp, hφDn, hφHerm, ?_, hφeig⟩
  -- The sector isometry `J` and the compressed Hermitian coefficient `W_S`.
  have hJ : (hubbardCountSectorEmbedding N k)ᴴ * hubbardCountSectorEmbedding N k = 1 :=
    hubbardCountSectorEmbedding_conjTranspose_mul_self k
  set WS := (hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
    * hubbardCountSectorEmbedding N k with hWSdef
  have hWS : WS.IsHermitian := by
    rw [hWSdef]
    change ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
        * hubbardCountSectorEmbedding N k)ᴴ
      = (hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ * hubbardCountSectorEmbedding N k
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hφHerm.eq, Matrix.mul_assoc]
  -- `W_S` solves the compressed Lyapunov equation (from the Hermitian ground `φ`).
  have hemb : blockWCoeff N φ = hubbardCountSectorEmbedding N k * WS
      * (hubbardCountSectorEmbedding N k)ᴴ := by
    rw [hWSdef]; exact blockWCoeff_eq_embed_compress_of_balanced k φ hφUp hφDn
  have hWS_lyap := Math.lyapunov_conjugate_isometry hJ hemb
    (blockWCoeff_lyapunov_of_eigenvector T U φ E hφeig)
  -- `Γ(J·|W_S|·Jᴴ)` is again a `Ĥ`-ground at `E` (commit 4), so `|W_S|` solves the same equation.
  obtain ⟨-, -, -, -, hφ'eig⟩ :=
    gammaWState_hermitianAbs_isEigenvector k T U hT_symm (fun x => (hU_pos x).le)
      φ hφ0 hφUp hφDn hφHerm hWS hφeig
  set P := hermitianAbs hWS with hPdef
  have hemb' : blockWCoeff N (gammaWState N (hubbardCountSectorEmbedding N k * P
        * (hubbardCountSectorEmbedding N k)ᴴ))
      = hubbardCountSectorEmbedding N k * P * (hubbardCountSectorEmbedding N k)ᴴ := by
    rw [blockWCoeff, blockWCoeff_gammaWState]
  have hP_lyap := Math.lyapunov_conjugate_isometry hJ hemb'
    (blockWCoeff_lyapunov_of_eigenvector T U _ E hφ'eig)
  -- Squares and commutation of `P = |W_S|` with `W_S`.
  have hWSne : WS ≠ 0 :=
    blockWCoeff_sectorCompress_ne_zero_of_ne_zero k φ hφ0 hφUp hφDn
  have hsq : P * P = WS * WS := hermitianAbs_mul_self hWS
  have hcomm : P * WS = WS * P := hermitianAbs_commute hWS
  -- `P` is positive definite: PSD + compressed Lyapunov ⟹ `P.PosDef ∨ P = 0`, and `P ≠ 0`.
  have hP_pd : P.PosDef := by
    rcases posDefCompress_dichotomy k T U hT_symm hU_pos hT_conn
        (hermitianAbs_posSemidef hWS) hP_lyap with hpd | hp0
    · exact hpd
    · have hP0 : P = 0 := hPdef.trans hp0
      exact absurd (Matrix.conjTranspose_mul_self_eq_zero.mp
        (by rw [hWS.eq, ← hsq, hP0, Matrix.zero_mul])) hWSne
  -- `R' = P − W_S` is PSD and solves the same compressed equation.
  rcases posDefCompress_dichotomy k T U hT_symm hU_pos hT_conn
      (hermitianAbs_sub_posSemidef hWS) (Math.lyapunovEq_sub hP_lyap hWS_lyap) with hR'pd | hR'0
  · -- `(P − W_S)·(P + W_S) = 0` with `P − W_S` invertible ⟹ `−W_S = P` positive definite.
    right
    have hprod : (P - WS) * (P + WS) = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, hsq, hcomm]; abel
    have hPWS0 : P + WS = 0 :=
      (hR'pd.isUnit.mul_right_inj).mp (by rw [hprod, Matrix.mul_zero])
    have hnegP : -WS = P := by rw [neg_eq_iff_add_eq_zero, add_comm]; exact hPWS0
    rw [hnegP]; exact hP_pd
  · -- `P − W_S = 0` ⟹ `W_S = P` positive definite.
    left
    rw [← sub_eq_zero.mp hR'0]; exact hP_pd

end LatticeSystem.Fermion
