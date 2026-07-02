import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePosSemidefGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedThetaSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorConnectivity
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorVariational

/-!
# The balanced-sector PSD-`W` ground state (Tasaki §10.2.4, Lemma 10.9)

Capstone layer PR40f toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The Lieb
spin-reflection-positivity squeeze on the balanced (`Ŝ³ = 0`) sector is run against the
*compressed* coefficient matrix `W_S = Jᴴ · W · J`, where `J` embeds the fixed up-count sector
`hubbardSpinCountSector N k` (single-species configurations with `Σ_x u_x = k`) into the full
`W`-index space `hubbardSpinConfig N`. Only there is `blockWCoeff` supported on a *principal*
`S_k × S_k` block (the plain number sector gives an anti-diagonal band on which the
connected-block argument fails).

This module first supplies the concrete isometry pieces:

* the `W`-index isometry `J = hubbardCountSectorEmbedding` (standard-basis columns over the
  count-`k` configurations) and its orthonormality `Jᴴ · J = 1`, and
* the **block rewrite** `W = J · (Jᴴ · W · J) · Jᴴ` for `W = blockWCoeff ψ` with `ψ` in the
  balanced sector — the single place the balanced support of `blockWCoeff` is used.

Combined with the isometry-conjugation energy identity `liebSRPEnergy_conj_isometry`, the Frobenius
invariance `frobenius_conj_isometry`, the SRP monotonicity `liebSRPEnergy_abs_le`, the mathlib
PSD-conjugation `Matrix.PosSemidef.mul_mul_conjTranspose_same`, and the balanced variational lower
bound `configSector_minEnergy_mul_le_rayleighOnVec_of_isHermitian`, this transports the whole
squeeze onto the compressed sub-block and produces the terminal **PSD-`W`, balanced ground state**.

## Main results

* `hubbardCountSectorEmbedding` — the fixed up-count sector embedding `J`.
* `hubbardCountSectorEmbedding_conjTranspose_mul_self` — its orthonormality `Jᴴ · J = 1`.
* `blockWCoeff_eq_embed_compress_of_balanced` — the principal-block rewrite
  `blockWCoeff ψ = J · (Jᴴ · blockWCoeff ψ · J) · Jᴴ` for a balanced `ψ`.
* `gammaWState_hermitianAbs_isEigenvector` — the reusable SRP squeeze core: from a balanced
  Hermitian ground `φ` at `E`, the absolute-value state `Γ(J · |W_S| · Jᴴ)` is again a nonzero
  balanced ground vector at the same `E` with PSD block coefficient. It exposes the connection
  to the specific input `φ` (needed to show `|W_S|` solves the compressed Lyapunov equation).
* `exists_posSemidefW_ground_in_balanced_sector` — the terminal balanced (`Ŝ³ = 0`) ground state
  whose reconciliation coefficient `blockWCoeff` is *positive semidefinite*, at the
  balanced-compression minimum eigenvalue. This is the SRP half of Lemma 10.9.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.9), pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- **The fixed up-count sector embedding** `J : W-index → count-`k` sector`: its column at a
count-`k` configuration `s` is the standard basis vector `|s⟩` over the `W`-index space
`hubbardSpinConfig N`. This is the `W`-index analog of `configSectorEmbedding` (which embeds the
Fock configuration sector); the two act on different index types (see the `Ŝ³ = 0` two-sector
distinction in `LiebAttractiveBalancedThetaSector`). -/
noncomputable def hubbardCountSectorEmbedding (N k : ℕ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinCountSector N k) ℂ :=
  Matrix.of (fun w s => basisVec s.val w)

/-- **The sector embedding has orthonormal columns:** `Jᴴ · J = 1`. The `(s, s')` entry is
`Σ_w |s⟩(w) · |s'⟩(w) = [s' = s]`, using `basisVec_inner` and injectivity of the subtype value. -/
theorem hubbardCountSectorEmbedding_conjTranspose_mul_self (k : ℕ) :
    (hubbardCountSectorEmbedding N k)ᴴ * hubbardCountSectorEmbedding N k = 1 := by
  ext s s'
  rw [Matrix.mul_apply]
  rw [show (∑ w, (hubbardCountSectorEmbedding N k)ᴴ s w
        * hubbardCountSectorEmbedding N k w s')
      = ∑ w, basisVec s.val w * basisVec s'.val w from
    Finset.sum_congr rfl (fun w _ => by
      rw [Matrix.conjTranspose_apply, hubbardCountSectorEmbedding, Matrix.of_apply,
        Matrix.of_apply,
        show star (basisVec s.val w) = basisVec s.val w from by
          rw [basisVec_apply]; split <;> simp])]
  rw [basisVec_inner, Matrix.one_apply]
  by_cases h : s = s'
  · rw [h, if_pos rfl, if_pos rfl]
  · rw [if_neg (fun hc => h (Subtype.ext hc.symm)), if_neg h]

/-- **The principal-block rewrite.** For a state `ψ` in the balanced sector
(`N̂_↑ ψ = N̂_↓ ψ = k·ψ`), its reconciliation coefficient `W = blockWCoeff ψ` is supported on the
principal `S_k × S_k` block, hence equals the isometry conjugation of its own sector compression:
`W = J · (Jᴴ · W · J) · Jᴴ`. This is the single point where the balanced support of `blockWCoeff`
(`blockWCoeff_apply_eq_zero_of_updowncount_ne`) enters the PR40f squeeze. -/
theorem blockWCoeff_eq_embed_compress_of_balanced (k : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hUp : (fermionTotalUpNumber N).mulVec ψ = (k : ℂ) • ψ)
    (hDn : (fermionTotalDownNumber N).mulVec ψ = (k : ℂ) • ψ) :
    blockWCoeff N ψ
      = hubbardCountSectorEmbedding N k
          * ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N ψ
              * hubbardCountSectorEmbedding N k)
          * (hubbardCountSectorEmbedding N k)ᴴ := by
  set J := hubbardCountSectorEmbedding N k with hJ
  set W := blockWCoeff N ψ with hW
  -- Entrywise readouts of `J` and `Jᴴ`.
  have hJapply : ∀ (w : hubbardSpinConfig N) (s : hubbardSpinCountSector N k),
      J w s = basisVec s.val w := fun w s => by
    rw [hJ, hubbardCountSectorEmbedding, Matrix.of_apply]
  have hJHapply : ∀ (s : hubbardSpinCountSector N k) (w : hubbardSpinConfig N),
      Jᴴ s w = basisVec s.val w := fun s w => by
    rw [Matrix.conjTranspose_apply, hJapply,
      show star (basisVec s.val w) = basisVec s.val w from by
        rw [basisVec_apply]; split <;> simp]
  -- `J·Jᴴ` acts as the identity on count-`k`-supported vectors.
  have hproj : ∀ (v : hubbardSpinConfig N → ℂ),
      (∀ w : hubbardSpinConfig N, (∑ x : Fin (N + 1), (w x).val) ≠ k → v w = 0) →
      (J * Jᴴ).mulVec v = v := by
    intro v hv
    rw [← Matrix.mulVec_mulVec]
    funext u
    have hJH : ∀ s : hubbardSpinCountSector N k, (Jᴴ.mulVec v) s = v s.val := by
      intro s
      rw [Matrix.mulVec, dotProduct]
      rw [show (∑ w, Jᴴ s w * v w) = ∑ w, basisVec s.val w * v w from
          Finset.sum_congr rfl (fun w _ => by rw [hJHapply])]
      exact basisVec_sum_mul s.val v
    rw [Matrix.mulVec, dotProduct]
    rw [show (∑ s, J u s * (Jᴴ.mulVec v) s)
          = ∑ s : hubbardSpinCountSector N k, basisVec s.val u * v s.val from
        Finset.sum_congr rfl (fun s _ => by rw [hJH s, hJapply])]
    by_cases hu : (∑ x : Fin (N + 1), (u x).val) = k
    · rw [Finset.sum_eq_single (⟨u, hu⟩ : hubbardSpinCountSector N k)
          (fun s _ hs => by
            rw [basisVec_of_ne (fun heq => hs (Subtype.ext heq.symm)), zero_mul])
          (fun hmem => absurd (Finset.mem_univ _) hmem)]
      simp only [basisVec_self, one_mul]
    · rw [hv u hu]
      refine Finset.sum_eq_zero (fun s _ => ?_)
      rw [basisVec_of_ne (fun heq => hu (by rw [heq]; exact s.property)), zero_mul]
  -- `J·Jᴴ` left-fixes any matrix whose rows are supported on the count-`k` sector.
  have hLproj : ∀ (M : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ),
      (∀ w h : hubbardSpinConfig N, (∑ x : Fin (N + 1), (w x).val) ≠ k → M w h = 0) →
      (J * Jᴴ) * M = M := by
    intro M hM
    ext u h
    rw [Matrix.mul_apply]
    have hcol := congrFun (hproj (fun w => M w h) (fun w hw => hM w h hw)) u
    rw [Matrix.mulVec, dotProduct] at hcol
    exact hcol
  -- Hermiticity of the projector `J·Jᴴ`.
  have hJJherm : (J * Jᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  -- Balanced support of `W = blockWCoeff ψ` (both spin counts equal `k`).
  have hsupp : ∀ u h : hubbardSpinConfig N,
      (∑ x : Fin (N + 1), (u x).val) ≠ k ∨ (∑ x : Fin (N + 1), (h x).val) ≠ k →
      W u h = 0 := by
    intro u h hor
    rw [hW]
    refine blockWCoeff_apply_eq_zero_of_updowncount_ne k ψ hUp hDn u h ?_
    rcases hor with hu | hh
    · exact Or.inl (fun heq => hu (by exact_mod_cast heq))
    · exact Or.inr (fun heq => hh (by exact_mod_cast heq))
  have hL : (J * Jᴴ) * W = W := hLproj W (fun w h hw => hsupp w h (Or.inl hw))
  have hR : W * (J * Jᴴ) = W := by
    have hRsupp : ∀ w h : hubbardSpinConfig N,
        (∑ x : Fin (N + 1), (w x).val) ≠ k → Wᴴ w h = 0 := by
      intro w h hw
      rw [Matrix.conjTranspose_apply, hsupp h w (Or.inr hw), star_zero]
    have hLW : (J * Jᴴ) * Wᴴ = Wᴴ := hLproj Wᴴ hRsupp
    have hswap : ((J * Jᴴ) * Wᴴ)ᴴ = W * (J * Jᴴ) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJJherm.eq]
    rw [← hswap, hLW, Matrix.conjTranspose_conjTranspose]
  have expand : J * (Jᴴ * W * J) * Jᴴ = (J * Jᴴ) * W * (J * Jᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [expand, hL, hR]

/-- **The spectral-absolute-value state of a balanced Hermitian ground is itself a ground state
at the same energy.** Given a nonzero balanced (`Ŝ³ = 0`) eigenvector `φ` of the attractive
Hubbard Hamiltonian at the balanced-compression minimum eigenvalue `E`, with Hermitian
reconciliation coefficient `W = blockWCoeff φ` and Hermitian compressed matrix
`W_S = Jᴴ · W · J` (`J = hubbardCountSectorEmbedding N k`), the *absolute-value* candidate
`φ' := Γ(J · |W_S| · Jᴴ)` (`|W_S| = hermitianAbs hWS`) is again a nonzero balanced ground vector
of `Ĥ` at the *same* `E`, with positive-semidefinite `blockWCoeff φ'`. This is the reusable Lieb
spin-reflection-positivity squeeze core of Tasaki §10.2.4 Lemma 10.9: `φ'` has PSD block
coefficient (`Matrix.PosSemidef.mul_mul_conjTranspose_same`), stays in the balanced block (image
of `J`), has the same Frobenius norm (`frobenius_conj_isometry` + `hermitianAbs_sum_normSq_eq`)
and no larger energy (`liebSRPEnergy_conj_isometry` + `liebSRPEnergy_abs_le`, using `0 ≤ U`); the
balanced variational lower bound (`configSector_minEnergy_mul_le_rayleighOnVec_of_isHermitian`)
then forces `φ'` to be a ground vector at `E`. It exposes the connection to the specific input
`φ` (which the existential `exists_posSemidefW_ground_in_balanced_sector` discards) so that
`|W_S|` can be shown to satisfy the compressed Lyapunov equation at `E`. -/
theorem gammaWState_hermitianAbs_isEigenvector (k : ℕ)
    [Nonempty (hubbardBalancedConfig N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT : ∀ i j, T i j = T j i) (hU : ∀ x, 0 ≤ U x)
    (φ : (Fin (2 * N + 2) → Fin 2) → ℂ) (hφ0 : φ ≠ 0)
    (hφUp : (fermionTotalUpNumber N).mulVec φ = (k : ℂ) • φ)
    (hφDn : (fermionTotalDownNumber N).mulVec φ = (k : ℂ) • φ)
    (hφHerm : (blockWCoeff N φ).IsHermitian)
    (hWS : ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
        * hubbardCountSectorEmbedding N k).IsHermitian)
    (hφeig : (attractiveHubbardHamiltonian N T U).mulVec φ
        = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
            (hubbardBalancedSectorPred N k)
            (attractiveHubbardHamiltonian_isHermitian T U hT)) : ℝ) : ℂ) • φ) :
    gammaWState N (hubbardCountSectorEmbedding N k * hermitianAbs hWS
        * (hubbardCountSectorEmbedding N k)ᴴ) ≠ 0
      ∧ (fermionTotalUpNumber N).mulVec (gammaWState N (hubbardCountSectorEmbedding N k
          * hermitianAbs hWS * (hubbardCountSectorEmbedding N k)ᴴ))
          = (k : ℂ) • gammaWState N (hubbardCountSectorEmbedding N k * hermitianAbs hWS
              * (hubbardCountSectorEmbedding N k)ᴴ)
      ∧ (fermionTotalDownNumber N).mulVec (gammaWState N (hubbardCountSectorEmbedding N k
          * hermitianAbs hWS * (hubbardCountSectorEmbedding N k)ᴴ))
          = (k : ℂ) • gammaWState N (hubbardCountSectorEmbedding N k * hermitianAbs hWS
              * (hubbardCountSectorEmbedding N k)ᴴ)
      ∧ (blockWCoeff N (gammaWState N (hubbardCountSectorEmbedding N k * hermitianAbs hWS
          * (hubbardCountSectorEmbedding N k)ᴴ))).PosSemidef
      ∧ (attractiveHubbardHamiltonian N T U).mulVec (gammaWState N (hubbardCountSectorEmbedding N k
          * hermitianAbs hWS * (hubbardCountSectorEmbedding N k)ᴴ))
          = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
              (hubbardBalancedSectorPred N k)
              (attractiveHubbardHamiltonian_isHermitian T U hT)) : ℝ) : ℂ)
            • gammaWState N (hubbardCountSectorEmbedding N k * hermitianAbs hWS
                * (hubbardCountSectorEmbedding N k)ᴴ) := by
  classical
  set hA := attractiveHubbardHamiltonian_isHermitian T U hT with hAdef
  set E : ℝ := hermitianMinEigenvalue (configSectorCompress_isHermitian
    (hubbardBalancedSectorPred N k) hA) with hEdef
  -- The `W`-index isometry `J` and its orthonormality.
  set J := hubbardCountSectorEmbedding N k with hJdef
  have hJ : Jᴴ * J = 1 := hubbardCountSectorEmbedding_conjTranspose_mul_self k
  have hJapply : ∀ (w : hubbardSpinConfig N) (s : hubbardSpinCountSector N k),
      J w s = basisVec s.val w := fun w s => by
    rw [hJdef, hubbardCountSectorEmbedding, Matrix.of_apply]
  have hJHapply : ∀ (s : hubbardSpinCountSector N k) (w : hubbardSpinConfig N),
      Jᴴ s w = basisVec s.val w := fun s w => by
    rw [Matrix.conjTranspose_apply, hJapply,
      show star (basisVec s.val w) = basisVec s.val w from by
        rw [basisVec_apply]; split <;> simp]
  -- The compressed coefficient `W_S = Jᴴ·W·J` (Hermitian, supplied) and its spectral abs.
  set WS := Jᴴ * blockWCoeff N φ * J with hWSdef
  set absWS := hermitianAbs hWS with habsdef
  -- The PSD-`W` candidate `Wpsd = J·|W_S|·Jᴴ` and its realizing state `φ'`.
  set Wpsd := J * absWS * Jᴴ with hWpsddef
  set φ' := gammaWState N Wpsd with hφ'def
  have hbwφ' : blockWCoeff N φ' = J * absWS * Jᴴ := by
    rw [hφ'def, blockWCoeff, blockWCoeff_gammaWState]
  have hpsd : (J * absWS * Jᴴ).PosSemidef :=
    (hermitianAbs_posSemidef hWS).mul_mul_conjTranspose_same J
  have hφ'Herm : (blockWCoeff N φ').IsHermitian := by rw [hbwφ']; exact hpsd.1
  -- The principal-block rewrite `W = J·W_S·Jᴴ`.
  have hemb : blockWCoeff N φ = J * WS * Jᴴ := by
    rw [hWSdef]; exact blockWCoeff_eq_embed_compress_of_balanced k φ hφUp hφDn
  -- `Wpsd` is supported on the balanced block (image of `J`), hence `φ'` is balanced.
  have hφ'supp : ∀ u h : hubbardSpinConfig N,
      (∑ x : Fin (N + 1), ((u x).val : ℂ)) ≠ (k : ℂ)
        ∨ (∑ x : Fin (N + 1), ((h x).val : ℂ)) ≠ (k : ℂ) → Wpsd u h = 0 := by
    intro u h hor
    rw [hWpsddef, Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun t _ => ?_)
    rcases hor with hu | hh
    · rw [Matrix.mul_apply, Finset.sum_eq_zero (fun s _ => ?_), zero_mul]
      rw [hJapply u s,
        basisVec_of_ne (fun heq => hu (by rw [heq]; exact_mod_cast s.property)), zero_mul]
    · rw [hJHapply t h,
        basisVec_of_ne (fun heq => hh (by rw [heq]; exact_mod_cast t.property)), mul_zero]
  have hφ'balanced := gammaWState_mem_balancedSector_of_block_supported k Wpsd hφ'supp
  rw [← hφ'def] at hφ'balanced
  obtain ⟨hφ'up, hφ'dn⟩ := hφ'balanced
  -- Energy squeeze `E(φ') ≤ E(φ)` through the compressed sector.
  have hrayφ : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ
      = liebSRPEnergy (hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)))
          (fun x => hubbardUpOccupationDiag N x) (fun x => U x / 2) (blockWCoeff N φ) :=
    attractiveHubbardHamiltonian_energy_re_eq_liebSRPEnergy_of_blockW_isHermitian T U hT φ hφHerm
  have hrayφ' : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ'
      = liebSRPEnergy (hubbardBlockKineticUpFixedMatrix N (fun x y => (T x y : ℂ)))
          (fun x => hubbardUpOccupationDiag N x) (fun x => U x / 2) (blockWCoeff N φ') :=
    attractiveHubbardHamiltonian_energy_re_eq_liebSRPEnergy_of_blockW_isHermitian T U hT φ' hφ'Herm
  have hIS : ∀ x, (Jᴴ * hubbardUpOccupationDiag N x * J).IsHermitian := fun x => by
    change (Jᴴ * hubbardUpOccupationDiag N x * J)ᴴ = Jᴴ * hubbardUpOccupationDiag N x * J
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (hubbardUpOccupationDiag_isHermitian x).eq, Matrix.mul_assoc]
  have habs_le : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ'
      ≤ rayleighOnVec (attractiveHubbardHamiltonian N T U) φ := by
    rw [hrayφ', hrayφ, hbwφ', hemb, liebSRPEnergy_conj_isometry hJ,
      liebSRPEnergy_conj_isometry hJ]
    exact liebSRPEnergy_abs_le hWS _ hIS _ (fun x => by have := hU x; linarith)
  -- Norm invariance `⟨φ',φ'⟩ = ⟨φ,φ⟩`.
  have hnorm : dotProduct (star φ') φ' = dotProduct (star φ) φ := by
    rw [hφ'def, gammaWState_dotProduct_eq, hWpsddef, frobenius_conj_isometry hJ, habsdef,
      hermitianAbs_sum_normSq_eq hWS, ← frobenius_conj_isometry hJ WS, ← hemb,
      ← blockWCoeff_dotProduct_eq]
  -- `⟨φ|Ĥ|φ⟩ = E‖φ‖²`.
  have hrayφ_eq : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ
      = E * (dotProduct (star φ) φ).re := by
    rw [rayleighOnVec, hφeig, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  -- Balanced variational lower bound at `φ'`.
  have hφ'supp0 : ∀ w, ¬ hubbardBalancedSectorPred N k w → φ' w = 0 := by
    intro w hw
    by_cases hup : (∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val) = k
    · have hdn : (∑ i : Fin (N + 1), (w (spinfulIndex N i 1)).val) ≠ k := fun h => hw ⟨hup, h⟩
      exact mulVec_apply_eq_zero_of_downNumber_ne _ (k : ℂ) hφ'dn w
        (fun hcast => hdn (by exact_mod_cast hcast))
    · exact mulVec_apply_eq_zero_of_upNumber_ne _ (k : ℂ) hφ'up w
        (fun hcast => hup (by exact_mod_cast hcast))
  have hlb : E * (dotProduct (star φ') φ').re
      ≤ rayleighOnVec (attractiveHubbardHamiltonian N T U) φ' :=
    configSector_minEnergy_mul_le_rayleighOnVec_of_isHermitian
      (hubbardBalancedSectorPred N k) hA hφ'supp0
  -- Squeeze ⟹ equality; `Ĥ φ'` stays balanced-supported by charge conservation.
  have hsqueeze : rayleighOnVec (attractiveHubbardHamiltonian N T U) φ'
      = E * (dotProduct (star φ') φ').re := by
    refine le_antisymm ?_ hlb
    calc rayleighOnVec (attractiveHubbardHamiltonian N T U) φ'
        ≤ rayleighOnVec (attractiveHubbardHamiltonian N T U) φ := habs_le
      _ = E * (dotProduct (star φ) φ).re := hrayφ_eq
      _ = E * (dotProduct (star φ') φ').re := by rw [hnorm]
  have hHφ'up : (fermionTotalUpNumber N).mulVec ((attractiveHubbardHamiltonian N T U).mulVec φ')
      = (k : ℂ) • ((attractiveHubbardHamiltonian N T U).mulVec φ') := by
    rw [Matrix.mulVec_mulVec,
      ← (attractiveHubbardHamiltonian_commute_fermionTotalUpNumber T U).eq,
      ← Matrix.mulVec_mulVec, hφ'up, Matrix.mulVec_smul]
  have hHφ'dn : (fermionTotalDownNumber N).mulVec ((attractiveHubbardHamiltonian N T U).mulVec φ')
      = (k : ℂ) • ((attractiveHubbardHamiltonian N T U).mulVec φ') := by
    rw [Matrix.mulVec_mulVec,
      ← (attractiveHubbardHamiltonian_commute_fermionTotalDownNumber T U).eq,
      ← Matrix.mulVec_mulVec, hφ'dn, Matrix.mulVec_smul]
  have hApres' : ∀ w, ¬ hubbardBalancedSectorPred N k w →
      (attractiveHubbardHamiltonian N T U).mulVec φ' w = 0 := by
    intro w hw
    by_cases hup : (∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val) = k
    · have hdn : (∑ i : Fin (N + 1), (w (spinfulIndex N i 1)).val) ≠ k := fun h => hw ⟨hup, h⟩
      exact mulVec_apply_eq_zero_of_downNumber_ne _ (k : ℂ) hHφ'dn w
        (fun hcast => hdn (by exact_mod_cast hcast))
    · exact mulVec_apply_eq_zero_of_upNumber_ne _ (k : ℂ) hHφ'up w
        (fun hcast => hup (by exact_mod_cast hcast))
  -- Assemble the deliverable about `φ'`.
  have hpos : 0 < (dotProduct (star φ') φ').re := by
    rw [hnorm]; exact dotProduct_star_self_re_pos hφ0
  refine ⟨?_, hφ'up, hφ'dn, ?_, ?_⟩
  · intro h; rw [h] at hpos; simp [dotProduct] at hpos
  · rw [hbwφ']; exact hpsd
  · exact mulVec_eq_smul_of_configSector_rayleighOnVec_eq_min
      (hubbardBalancedSectorPred N k) hA hφ'supp0 hApres' hsqueeze

/-- **A positive-semidefinite-`W` ground state in the balanced (`Ŝ³ = 0`) sector.** For symmetric
real hopping `T` and nonnegative attraction `U`, there is a nonzero balanced ground vector `φ'`
(`N̂_↑ φ' = N̂_↓ φ' = k·φ'`) of the attractive Hubbard Hamiltonian, at the balanced-compression
minimum eigenvalue `E`, whose reconciliation coefficient `blockWCoeff φ'` is *positive
semidefinite*. It refines `exists_hermitianW_ground_in_balanced_sector` (`W` Hermitian) by running
the Lieb spin-reflection-positivity squeeze against the compressed coefficient `W_S = Jᴴ·W·J` and
its spectral absolute value `|W_S|`: the candidate `φ' := Γ(J·|W_S|·Jᴴ)` has PSD block coefficient
(`Matrix.PosSemidef.mul_mul_conjTranspose_same`), stays in the balanced block (image of `J`), has
the same Frobenius norm (`frobenius_conj_isometry` + `hermitianAbs_sum_normSq_eq`) and no larger
energy (`liebSRPEnergy_conj_isometry` + `liebSRPEnergy_abs_le`, using `0 ≤ U`); the balanced
variational lower bound (`configSector_minEnergy_mul_le_rayleighOnVec_of_isHermitian`) then forces
`φ'` to be a ground vector at `E`. This is the SRP (`Ŝ³ = 0`) half of Tasaki §10.2.4 Lemma 10.9. -/
theorem exists_posSemidefW_ground_in_balanced_sector (k : ℕ)
    [Nonempty (hubbardBalancedConfig N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT : ∀ i j, T i j = T j i) (hU : ∀ x, 0 ≤ U x) :
    ∃ φ : (Fin (2 * N + 2) → Fin 2) → ℂ, φ ≠ 0
      ∧ (fermionTotalUpNumber N).mulVec φ = (k : ℂ) • φ
      ∧ (fermionTotalDownNumber N).mulVec φ = (k : ℂ) • φ
      ∧ (blockWCoeff N φ).PosSemidef
      ∧ (attractiveHubbardHamiltonian N T U).mulVec φ
          = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
              (hubbardBalancedSectorPred N k)
              (attractiveHubbardHamiltonian_isHermitian T U hT)) : ℝ) : ℂ) • φ := by
  classical
  -- The balanced Hermitian-`W` ground representative (PR40e-pre2b).
  obtain ⟨φ, hφ0, hφUp, hφDn, hφHerm, hφeig⟩ :=
    exists_hermitianW_ground_in_balanced_sector k T U hT
  -- The compressed coefficient `W_S = Jᴴ·W·J` is Hermitian.
  have hWS : ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
      * hubbardCountSectorEmbedding N k).IsHermitian := by
    change ((hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ
        * hubbardCountSectorEmbedding N k)ᴴ
      = (hubbardCountSectorEmbedding N k)ᴴ * blockWCoeff N φ * hubbardCountSectorEmbedding N k
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hφHerm.eq, Matrix.mul_assoc]
  -- The absolute-value state `φ' = Γ(J·|W_S|·Jᴴ)` is a balanced ground vector at the same `E`.
  obtain ⟨hφ'0, hφ'up, hφ'dn, hφ'psd, hφ'eig⟩ :=
    gammaWState_hermitianAbs_isEigenvector k T U hT hU φ hφ0 hφUp hφDn hφHerm hWS hφeig
  exact ⟨_, hφ'0, hφ'up, hφ'dn, hφ'psd, hφ'eig⟩

end LatticeSystem.Fermion
