import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopActionCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.HopAction

/-!
# Uniform-sign hole-filling action in the Tasaki basis (11.2.4)

This file proves the boxed result of Tasaki eq. (11.2.4): in the ordered
creation-operator basis `|Φ_{x,σ}⟩` of (11.2.3), a hole-filling hopping term
`ĉ†_{(x,s)} ĉ_{(z,s)}` (creating at the hole `x`, annihilating the spin-`s`
electron at an occupied site `z`) acts with a *uniform* sign `-1`:

  `ĉ†_{(x,s)} ĉ_{(z,s)} |Φ_{x,σ}⟩ = - |Φ_{z, σ_{z→x}}⟩`.

In the sign-free `basisVec` convention (file `HopAction.lean`) the same term
carries a configuration-dependent Jordan–Wigner sign `jwSign · jwSign`; the
content here is that, once the states are taken in the Tasaki basis, the four
fermion signs (the two basis signs `ε` of `|Φ_{x,σ}⟩` and `|Φ_{z,σ_{z→x}}⟩`
and the two hop string signs) combine to the constant `-1`. This is exactly
Tasaki's stated reason for the redundant ordered-creation construction, and it
is the uniform off-diagonal sign needed for the Perron–Frobenius step
(Theorems 11.5/11.7).

The sign computation reduces, via `jwSign = (-1)^{(occupied modes below)}`, to
the parity count

  `E₁ + E₂ + E₃ + E₄ = x + z + (z - [x<z]) + (x - [z<x]) = 2(x+z) - 1`,

which is odd because `x ≠ z` forces exactly one of `[x<z]`, `[z<x]` to hold.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, eq. (11.2.4), pp. 383-384.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Uniform-sign hole-filling action (11.2.4) -/

/-- Tasaki eq. (11.2.4): in the Tasaki basis the hole-filling hopping term
`ĉ†_{(x,s)} ĉ_{(z,s)}` acts on `|Φ_{x,σ}⟩` with the uniform sign `-1`,
producing `-|Φ_{z, σ_{z→x}}⟩`. The four fermion signs (the two basis signs and
the two hop string signs) combine to the constant `-1` because the total parity
exponent `2(x+z) - 1` is odd. -/
theorem hubbardTasakiHop_mulVec (N : ℕ) (x z : Fin (N + 1)) (σ : Fin (N + 1) → Bool)
    (s : Fin 2) (hxz : x ≠ z)
    (hs : hubbardOneHoleConfig N x σ (spinfulIndex N z s) = 1) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N x s) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N z s)).mulVec
        (hubbardTasakiBasisState N x σ) =
      - hubbardTasakiBasisState N z (hubbardSpinMove N σ x z) := by
  rw [hubbardTasakiBasisState_eq_smul_basisVec, Matrix.mulVec_smul,
    show basisVec (hubbardOneHoleConfig N x σ) = hubbardHardcoreBasisState N x σ from rfl,
    hubbardHop_mulVec_hardcoreBasisState N x z σ s hxz hs, smul_smul,
    hubbardTasakiBasisState_eq_smul_basisVec N z (hubbardSpinMove N σ x z),
    show basisVec (hubbardOneHoleConfig N z (hubbardSpinMove N σ x z))
      = hubbardHardcoreBasisState N z (hubbardSpinMove N σ x z) from rfl,
    ← neg_smul]
  congr 1
  -- scalar identity: ε(x,σ) · (hopSign₁ · hopSign₂) = - ε(z, σ_{z→x})
  rw [hubbardTasakiBasisSign_eq, hop_jwSign_source N x z σ s hxz hs,
    hop_jwSign_target N x z σ s hxz hs, hubbardTasakiBasisSign_eq]
  have hz2 : (-1 : ℂ) ^ z.val * (-1) ^ z.val = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨z.val, rfl⟩
  have key : (-1 : ℂ) ^ x.val *
      ((-1) ^ (if x.val < z.val then z.val - 1 else z.val) *
        (-1) ^ (if z.val < x.val then x.val - 1 else x.val)) * (-1) ^ z.val = -1 := by
    rw [← pow_add, ← pow_add, ← pow_add]
    refine Odd.neg_one_pow ?_
    rw [Nat.odd_iff]
    rcases lt_or_gt_of_ne (fun h => hxz (Fin.ext h)) with h | h
    · rw [if_pos h, if_neg (by omega)]; omega
    · rw [if_neg (by omega), if_pos h]; omega
  calc (-1 : ℂ) ^ x.val *
        ((-1) ^ (if x.val < z.val then z.val - 1 else z.val) *
          (-1) ^ (if z.val < x.val then x.val - 1 else x.val))
      = (-1 : ℂ) ^ x.val *
        ((-1) ^ (if x.val < z.val then z.val - 1 else z.val) *
          (-1) ^ (if z.val < x.val then x.val - 1 else x.val)) *
          ((-1) ^ z.val * (-1) ^ z.val) := by rw [hz2, mul_one]
    _ = ((-1 : ℂ) ^ x.val *
        ((-1) ^ (if x.val < z.val then z.val - 1 else z.val) *
          (-1) ^ (if z.val < x.val then x.val - 1 else x.val)) * (-1) ^ z.val)
          * (-1) ^ z.val := by ring
    _ = -1 * (-1) ^ z.val := by rw [key]
    _ = -(-1 : ℂ) ^ z.val := by ring

end LatticeSystem.Fermion
