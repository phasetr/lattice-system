import LatticeSystem.Quantum.SpinS.VBSInversionParity
import LatticeSystem.Quantum.SpinS.AKLTUniqueness.GroundStateUnique
import LatticeSystem.Quantum.SpinS.AKLT

/-!
# §8.3.2 item (3) — `S = 1` bond-inversion parity (p. 257, unnumbered display)

Signature and capstone tests for the bond-inversion unitary `Û_inv` (Tasaki §8.3.2, eq. (8.3.5),
p. 257, defines `Û_inv`; the parity identity itself is the unnumbered display on the same page)
at `S = 1`, for the production module `LatticeSystem.Quantum.SpinS.VBSInversionParity`.
No production code lives here: every `example`/`theorem` below only pins down the intended
statement of that module (and its `ConfigPermMatrixS` dependency).

Covers:
1. the configuration map `bondInversionConfigS := σ ∘ Fin.rev` and its involutivity;
2. the unitary `bondInversionUnitaryS L N := configPermMatrixS bondInversionConfigS` and its
   `mulVec`/`mul_self` laws;
3. the capstone `tasaki_vbs_inversion_parity_spin_one` (MPS-vector eigenvalue identity, no
   hypothesis on `L`, including the vacuous `L = 1` case where `akltVBSState 1 = 0`);
4. the ground-state form via `aklt_ring_ground_state_unique` — every ring ground state of
   `akltHamiltonianS` has the same `(-1)^L` inversion parity, not just `akltVBSState` itself;
5. the book's own numeric cross-check (S.63), p. 505: at `L = 3` the eigenvalue is `-1`, both as a
   specialization of the capstone and as an independent direct evaluation of `akltVBSMatrices`
   products;
6. `akltVBSState_ne_smul_trivialProductState_spin_one` — the `(S3)` conclusion itself: on an odd
   ring with `2 ≤ L`, the VBS state and the trivial large-`D` product state are not proportional
   (the `Z₂` obstruction between the Haldane and large-`D` phases).
-/

namespace LatticeSystem.Tests.VBSInversionParitySpinOne

open LatticeSystem.Quantum

/-! ## 1. `bondInversionConfigS` -/

/-- (8.3.5): `σ^inv = σ ∘ Fin.rev`, i.e. list reversal of the configuration. -/
example {L N : ℕ} (σ : Fin L → Fin (N + 1)) :
    bondInversionConfigS σ = σ ∘ Fin.rev := rfl

example {L N : ℕ} :
    Function.Involutive (bondInversionConfigS (L := L) (N := N)) :=
  bondInversionConfigS_involutive

/-! ## 2. `bondInversionUnitaryS` -/

/-- `Û_inv` is the generic permutation-matrix layer applied to `bondInversionConfigS` — this is
the load-bearing definitional link that lets `configPermMatrixS`'s lemmas transfer for free
(no duplicated `manyBodyReversalS`-style proof). -/
example (L N : ℕ) :
    bondInversionUnitaryS L N =
      LatticeSystem.Quantum.configPermMatrixS (bondInversionConfigS (L := L) (N := N)) := rfl

/-- Book's `(Û_inv)² = 1̂`. -/
example (L N : ℕ) : bondInversionUnitaryS L N * bondInversionUnitaryS L N = 1 :=
  bondInversionUnitaryS_mul_self

example (L N : ℕ) (Φ : (Fin L → Fin (N + 1)) → ℂ) :
    (bondInversionUnitaryS L N).mulVec Φ = fun σ => Φ (σ ∘ Fin.rev) :=
  bondInversionUnitaryS_mulVec Φ

/-! ## 3. Capstone: `Û_inv |Φ_VBS⟩ = (-1)^L |Φ_VBS⟩`, no hypothesis on `L` -/

/-- Tasaki §8.3.2, p. 257, unnumbered display, at `S = 1`: the periodic VBS state is an
eigenstate of bond-centered inversion with eigenvalue `(-1)^L`, for every `L` (no parity
restriction; the statement is vacuously true at `L = 1` since `akltVBSState 1 = 0`). -/
example (L : ℕ) :
    (bondInversionUnitaryS L 2).mulVec (akltVBSState L) = ((-1 : ℂ) ^ L) • akltVBSState L :=
  tasaki_vbs_inversion_parity_spin_one L

/-- Non-vacuity control: the eigenvalue identity is carried by a nonzero vector as soon as
`2 ≤ L` (`akltVBSState_ne_zero`), so the capstone above is not "true because the vector is
zero" from `L = 2` onward. -/
example (L : ℕ) (hL : 2 ≤ L) : akltVBSState L ≠ 0 :=
  akltVBSState_ne_zero hL

/-! ## 4. Ground-state form (book's actual statement is about `|Φ_GS⟩`, not one vector) -/

/-- Book-faithful upgrade via `aklt_ring_ground_state_unique`: **every** ring ground state of
`akltHamiltonianS` (not just `akltVBSState` itself) has bond-inversion parity `(-1)^L`. This is
the book's "If the ground state is unique, we must have `Û_inv|Φ_GS⟩ = σ_inv|Φ_GS⟩`" with
`σ_inv = (-1)^L` pinned down at `S = 1`. -/
example (n : ℕ) (hn : 2 ≤ n) (Ψ : (Fin (n + 1) → Fin 3) → ℂ) (hΨ0 : Ψ ≠ 0)
    (hev : (akltHamiltonianS (n + 1)).mulVec Ψ
        = ((-(2 : ℝ) / 3 * ((n : ℝ) + 1) : ℝ) : ℂ) • Ψ) :
    (bondInversionUnitaryS (n + 1) 2).mulVec Ψ = ((-1 : ℂ) ^ (n + 1)) • Ψ :=
  tasaki_vbs_inversion_parity_ground_state_spin_one n hn Ψ hΨ0 hev

/-! ## 5. Book cross-check (S.63), p. 505: `L = 3` gives eigenvalue `-1` -/

/-- Specialization of the general capstone to `L = 3`, matching the book's own worked example
(S.63), p. 505: `Û_inv|Φ_VBS⟩ = -|Φ_VBS⟩` for the `L = 3` periodic ring. -/
example :
    (bondInversionUnitaryS 3 2).mulVec (akltVBSState 3) = (-1 : ℂ) • akltVBSState 3 := by
  have h := tasaki_vbs_inversion_parity_spin_one 3
  norm_num at h
  rw [neg_one_smul]
  exact h

/-- The book's `(+, −, 0)` configuration of (S.63), p. 505, in the library's `0, 1, 2 ↔ +1, 0, −1`
labelling. -/
private def bookExampleConfig : Fin 3 → Fin 3 := ![0, 2, 1]

/-- **Independent numeric instance.** Direct evaluation of the VBS coefficient at the book's
`(+, −, 0)` configuration, `Φ_VBS(+, −, 0) = 1/4`, matching (S.63), p. 505 term-by-term. This
computes `akltVBSMatrices` products directly and does *not* go through
`tasaki_vbs_inversion_parity_spin_one`, so it guards against a sign error surviving a vacuous or
accidentally-cancelling general proof. -/
example : akltVBSState 3 bookExampleConfig = (1 / 4 : ℂ) := by
  have hlist : List.ofFn bookExampleConfig = [0, 2, 1] := by decide
  unfold akltVBSState
  rw [hlist]
  simp [orderedProd, akltVBSMatrices, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diag, ← mul_assoc, sqrt2_inv_mul_sqrt2_inv]
  norm_num

/-! ## 6. Book's `(S3)` conclusion: `Φ_VBS` and the trivial product state are not proportional -/

/-- Signature and capstone test for `akltVBSState_ne_smul_trivialProductState_spin_one`: Tasaki
§8.3.2's `(S3)`, the `Z₂` obstruction between the Haldane and large-`D` phases. On an odd ring with
at least two sites, no scalar multiple of the trivial large-`D` product state (all sites in
magnetic label `m = 0`, i.e. library label `1`) equals the VBS state, because the two have opposite
bond-inversion parity. -/
example (L : ℕ) (hL : 2 ≤ L) (hodd : Odd L) (c : ℂ) :
    akltVBSState L ≠ c • (fun σ : Fin L → Fin 3 => if σ = fun _ => (1 : Fin 3) then (1 : ℂ)
      else 0) :=
  akltVBSState_ne_smul_trivialProductState_spin_one L hL hodd c

end LatticeSystem.Tests.VBSInversionParitySpinOne
