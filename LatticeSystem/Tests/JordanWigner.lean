/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner

/-!
# Test coverage for Jordan–Wigner basics

Backfill regression tests for the bulk of the JW algebra (PRs
#108-#132), all merged before any test infrastructure existed.

These are mostly shim tests (signature-preservation), since the
core CAR algebra theorems return matrix identities that are not
\`Decidable\` over ℂ. Where computational cross-check is feasible
(e.g. JW string at site 0), it is preferred.
-/

namespace LatticeSystem.Tests.JordanWigner

open LatticeSystem.Fermion LatticeSystem.Quantum

/-! ## JW string fundamentals -/

/-- JW string at site 0 is the identity, for any chain length. -/
example (N : ℕ) : jwString N (0 : Fin (N + 1)) = 1 :=
  jwString_zero N

/-- JW string squares to the identity. -/
example (N : ℕ) (i : Fin (N + 1)) : jwString N i * jwString N i = 1 :=
  jwString_sq N i

/-- JW string is Hermitian. -/
example (N : ℕ) (i : Fin (N + 1)) : (jwString N i).IsHermitian :=
  jwString_isHermitian N i

/-! ## Same-site CAR -/

/-- `c_i² = 0` (Pauli exclusion). -/
example (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiAnnihilation N i = 0 :=
  fermionMultiAnnihilation_sq N i

/-- `c_i†² = 0` (Pauli exclusion, dual). -/
example (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiCreation N i * fermionMultiCreation N i = 0 :=
  fermionMultiCreation_sq N i

/-- Same-site CAR: `{c_i, c_i†} = 1`. -/
example (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiCreation N i +
        fermionMultiCreation N i * fermionMultiAnnihilation N i = 1 :=
  fermionMultiAnticomm_self N i

/-! ## Number operator -/

/-- `n_i` is Hermitian. -/
example (N : ℕ) (i : Fin (N + 1)) :
    (fermionMultiNumber N i).IsHermitian :=
  fermionMultiNumber_isHermitian N i

/-- `n_i² = n_i` (idempotent). -/
example (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiNumber N i = fermionMultiNumber N i :=
  fermionMultiNumber_sq N i

/-- All number operators commute pairwise. -/
example (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionMultiNumber N i) (fermionMultiNumber N j) :=
  fermionMultiNumber_commute N i j

/-! ## 2-site cross-site CARs (Fin 2) -/

/-- `c_0 c_1 + c_1 c_0 = 0`. -/
example :
    fermionMultiAnnihilation 1 (0 : Fin 2) * fermionMultiAnnihilation 1 1 +
        fermionMultiAnnihilation 1 1 * fermionMultiAnnihilation 1 0 = 0 :=
  fermionMultiAnnihilation_anticomm_two_site_cross

/-- `c_0† c_1† + c_1† c_0† = 0`. -/
example :
    fermionMultiCreation 1 (0 : Fin 2) * fermionMultiCreation 1 1 +
        fermionMultiCreation 1 1 * fermionMultiCreation 1 0 = 0 :=
  fermionMultiCreation_anticomm_two_site_cross

/-- `c_0 c_1† + c_1† c_0 = 0`. -/
example :
    fermionMultiAnnihilation 1 (0 : Fin 2) * fermionMultiCreation 1 1 +
        fermionMultiCreation 1 1 * fermionMultiAnnihilation 1 0 = 0 :=
  fermionMultiAnnihilation_creation_anticomm_two_site_cross

/-! ## General cross-site CAR at site 0 (`{c_0, c_k} = 0`, `k ≥ 1`) -/

/-- `c_0 c_k + c_k c_0 = 0` for every `k : Fin (N + 1)` with
`0 < k.val`. -/
example (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N k +
      fermionMultiAnnihilation N k *
        fermionMultiAnnihilation N 0 = 0 :=
  fermionMultiAnnihilation_anticomm_zero_pos N k hk

/-- Dual: `c_0† c_k† + c_k† c_0† = 0` for every positive `k`. -/
example (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N k +
      fermionMultiCreation N k *
        fermionMultiCreation N 0 = 0 :=
  fermionMultiCreation_anticomm_zero_pos N k hk

/-- Instance check: `k = 3` on `Fin 4` (`N = 3`) — not covered by the
existing `_zero_one` or `_zero_two_general` specialisations. -/
example :
    fermionMultiAnnihilation 3 (0 : Fin 4) *
        fermionMultiAnnihilation 3 3 +
      fermionMultiAnnihilation 3 3 *
        fermionMultiAnnihilation 3 0 = 0 :=
  fermionMultiAnnihilation_anticomm_zero_pos 3 3 (by decide)

/-- Mixed `{c_0, c_k†} = 0` for every positive `k`. -/
example (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiCreation N k +
      fermionMultiCreation N k *
        fermionMultiAnnihilation N 0 = 0 :=
  fermionMultiAnnihilation_creation_anticomm_zero_pos N k hk

/-- Mixed dual `{c_0†, c_k} = 0` for every positive `k`. -/
example (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N k +
      fermionMultiAnnihilation N k *
        fermionMultiCreation N 0 = 0 :=
  fermionMultiCreation_annihilation_anticomm_zero_pos N k hk

/-- Mixed instance check: `k = 3` on `Fin 4` — not covered by the
existing `_zero_one` / `_zero_two_general` mixed specialisations. -/
example :
    fermionMultiAnnihilation 3 (0 : Fin 4) *
        fermionMultiCreation 3 3 +
      fermionMultiCreation 3 3 *
        fermionMultiAnnihilation 3 0 = 0 :=
  fermionMultiAnnihilation_creation_anticomm_zero_pos 3 3 (by decide)

/-! ## JW string anticommutator at interior site (#210) -/

/-- For every `i < j`, `{σ^+_i, jwString N j} = 0`. -/
example (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    onSite i spinHalfOpPlus * jwString N j +
      jwString N j * onSite i spinHalfOpPlus = 0 :=
  jwString_anticomm_onSite_pos_spinHalfOpPlus N i j hij

/-- Companion: `{σ^-_i, jwString N j} = 0` for every `i < j`. -/
example (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    onSite i spinHalfOpMinus * jwString N j +
      jwString N j * onSite i spinHalfOpMinus = 0 :=
  jwString_anticomm_onSite_pos_spinHalfOpMinus N i j hij

/-- Any two JW strings commute. -/
example (N : ℕ) (i j : Fin (N + 1)) :
    Commute (jwString N i) (jwString N j) :=
  jwString_commute_jwString N i j

/-- Instance check: `(i, j) = (1, 3)` on `Fin 4`. -/
example :
    onSite (1 : Fin 4) spinHalfOpPlus * jwString 3 3 +
      jwString 3 3 * onSite (1 : Fin 4) spinHalfOpPlus = 0 :=
  jwString_anticomm_onSite_pos_spinHalfOpPlus 3 1 3 (by decide)

/-! ## Fully general cross-site CAR `{c_i, c_j} = 0` for `i < j` (#210) -/

/-- `{c_i, c_j} = 0` for every `i j : Fin (N + 1)` with
`i.val < j.val`. -/
example (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    fermionMultiAnnihilation N i * fermionMultiAnnihilation N j +
      fermionMultiAnnihilation N j * fermionMultiAnnihilation N i = 0 :=
  fermionMultiAnnihilation_anticomm_lt N i j hij

/-- `{c_i†, c_j†} = 0` for every `i < j`. -/
example (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    fermionMultiCreation N i * fermionMultiCreation N j +
      fermionMultiCreation N j * fermionMultiCreation N i = 0 :=
  fermionMultiCreation_anticomm_lt N i j hij

/-- `{c_i, c_j†} = 0` for every `i < j`. -/
example (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    fermionMultiAnnihilation N i * fermionMultiCreation N j +
      fermionMultiCreation N j * fermionMultiAnnihilation N i = 0 :=
  fermionMultiAnnihilation_creation_anticomm_lt N i j hij

/-- `{c_i†, c_j} = 0` for every `i < j`. -/
example (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    fermionMultiCreation N i * fermionMultiAnnihilation N j +
      fermionMultiAnnihilation N j * fermionMultiCreation N i = 0 :=
  fermionMultiCreation_annihilation_anticomm_lt N i j hij

/-- Instance check: `(i, j) = (1, 3)` on `Fin 4` — general case
not covered by the `_zero_pos` specialisations. -/
example :
    fermionMultiAnnihilation 3 (1 : Fin 4) *
        fermionMultiAnnihilation 3 3 +
      fermionMultiAnnihilation 3 3 *
        fermionMultiAnnihilation 3 1 = 0 :=
  fermionMultiAnnihilation_anticomm_lt 3 1 3 (by decide)

/-- Instance check: mixed `(i, j) = (2, 3)` on `Fin 4`. -/
example :
    fermionMultiAnnihilation 3 (2 : Fin 4) *
        fermionMultiCreation 3 3 +
      fermionMultiCreation 3 3 *
        fermionMultiAnnihilation 3 2 = 0 :=
  fermionMultiAnnihilation_creation_anticomm_lt 3 2 3 (by decide)

/-! ## Adjoint relations -/

/-- `(c_i)ᴴ = c_i†`. -/
example (N : ℕ) (i : Fin (N + 1)) :
    Matrix.conjTranspose (fermionMultiAnnihilation N i) =
      fermionMultiCreation N i :=
  fermionMultiAnnihilation_conjTranspose N i

/-- `(c_i†)ᴴ = c_i`. -/
example (N : ℕ) (i : Fin (N + 1)) :
    Matrix.conjTranspose (fermionMultiCreation N i) =
      fermionMultiAnnihilation N i :=
  fermionMultiCreation_conjTranspose N i

/-! ## Total number operator commutator algebra (PRs #126-#131) -/

/-- `[n_i, c_i] = -c_i` (number-annihilation same-site). -/
example (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiAnnihilation N i -
        fermionMultiAnnihilation N i * fermionMultiNumber N i =
      -fermionMultiAnnihilation N i :=
  fermionMultiNumber_commutator_fermionMultiAnnihilation_self N i

/-- `[n_i, c_i†] = c_i†` (dual). -/
example (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiNumber N i * fermionMultiCreation N i -
        fermionMultiCreation N i * fermionMultiNumber N i =
      fermionMultiCreation N i :=
  fermionMultiNumber_commutator_fermionMultiCreation_self N i

/-- Cross-site n-c commute: `Commute n_i c_j` for `i ≠ j`. -/
example (N : ℕ) {i j : Fin (N + 1)} (hij : i ≠ j) :
    Commute (fermionMultiNumber N i) (fermionMultiAnnihilation N j) :=
  fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hij

/-- `[N̂, c_j] = -c_j` (total number / annihilation). -/
example (N : ℕ) (j : Fin (N + 1)) :
    fermionTotalNumber N * fermionMultiAnnihilation N j -
        fermionMultiAnnihilation N j * fermionTotalNumber N =
      -fermionMultiAnnihilation N j :=
  fermionTotalNumber_commutator_fermionMultiAnnihilation N j

/-- `[N̂, c_j†] = c_j†` (total number / creation, dual). -/
example (N : ℕ) (j : Fin (N + 1)) :
    fermionTotalNumber N * fermionMultiCreation N j -
        fermionMultiCreation N j * fermionTotalNumber N =
      fermionMultiCreation N j :=
  fermionTotalNumber_commutator_fermionMultiCreation N j

/-- Hopping commutes with N̂ (charge conservation of c_i† c_j). -/
example (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionTotalNumber N)
      (fermionMultiCreation N i * fermionMultiAnnihilation N j) :=
  fermionTotalNumber_commute_hopping N i j

/-! ## Total number Hermiticity -/

/-- `N̂` is Hermitian. -/
example (N : ℕ) : (fermionTotalNumber N).IsHermitian :=
  fermionTotalNumber_isHermitian N

end LatticeSystem.Tests.JordanWigner
