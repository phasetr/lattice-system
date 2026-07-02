import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePosSemidefGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedThetaSector
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorConnectivity
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorVariational

/-!
# The balanced-sector isometry and its principal-block compression (Tasaki §10.2.4)

Layer PR40f (commit 3) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The Lieb
spin-reflection-positivity squeeze on the balanced (`Ŝ³ = 0`) sector is run against the
*compressed* coefficient matrix `W_S = Jᴴ · W · J`, where `J` embeds the fixed up-count sector
`hubbardSpinCountSector N k` (single-species configurations with `Σ_x u_x = k`) into the full
`W`-index space `hubbardSpinConfig N`. Only there is `blockWCoeff` supported on a *principal*
`S_k × S_k` block (the plain number sector gives an anti-diagonal band on which the
connected-block argument fails).

This module supplies the concrete pieces the capstone (commit 4) consumes:

* the `W`-index isometry `J = hubbardCountSectorEmbedding` (standard-basis columns over the
  count-`k` configurations) and its orthonormality `Jᴴ · J = 1`, and
* the **block rewrite** `W = J · (Jᴴ · W · J) · Jᴴ` for `W = blockWCoeff ψ` with `ψ` in the
  balanced sector — the single place the balanced support of `blockWCoeff` is used. Combined with
  the isometry-conjugation energy identity `liebSRPEnergy_conj_isometry` (PR40f commit 2) and the
  mathlib PSD-conjugation `Matrix.PosSemidef.mul_mul_conjTranspose_same`, this transports the whole
  squeeze onto the compressed sub-block.

## Main results

* `hubbardCountSectorEmbedding` — the fixed up-count sector embedding `J`.
* `hubbardCountSectorEmbedding_conjTranspose_mul_self` — its orthonormality `Jᴴ · J = 1`.
* `blockWCoeff_eq_embed_compress_of_balanced` — the principal-block rewrite
  `blockWCoeff ψ = J · (Jᴴ · blockWCoeff ψ · J) · Jᴴ` for a balanced `ψ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.9), pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

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

end LatticeSystem.Fermion
