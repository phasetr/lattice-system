import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveConjHop
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveJwCocycle

/-!
# The conjugated single-hop operator equality (Tasaki §10.2.1)

Fifteenth layer (PR15) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

PR13 computed the basis action of a conjugated single hopping term
`U (ĉ†_p ĉ_q) Uᴴ` (with `U = permutationOperator π`) and kept the composite
Jordan–Wigner / permutation sign `permutationHopConjSign` explicit.  PR14 proved the
one-mode-update parity laws relating `translationJwSign π` to bare `jwSign` hop
signs.  This file combines them into the **operator identity**

  `U (ĉ†_p ĉ_q) Uᴴ = ĉ†_{π p} ĉ_{π q}`,

i.e. conjugating a single hop by the signed permutation operator is exactly the hop
at the permuted orbitals.  The cocycle collapses the composite sign to the single
permuted bare hop sign.

## Main results

* `permutationHopConjSign_eq` — the cocycle: under the hop-allowed condition,
  `permutationHopConjSign π p q σ = jwSign (π q) σ · jwSign (π p) (update σ (π q) 0)`.
* `permutationOperator_hop_conj_mulVec_basisVec` — the conjugated hop and the
  permuted bare hop have equal basis action.
* `permutationOperator_hop_conj_eq` — the operator identity
  `U (ĉ†_p ĉ_q) Uᴴ = ĉ†_{π p} ĉ_{π q}`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {M : ℕ}

/-- The Jordan–Wigner string sign squares to `1` (it is `±1`). -/
private theorem jwSign_mul_self (j : Fin (M + 1)) (c : Fin (M + 1) → Fin 2) :
    jwSign M j c * jwSign M j c = 1 := by
  rw [jwSign_eq_neg_one_pow, ← pow_add, ← two_mul, pow_mul]; norm_num

/-- A column of a matrix as a basis action: `A.mulVec (basisVec σ) τ = A τ σ`. -/
private theorem mulVec_basisVec_apply
    (A : Matrix (Fin (M + 1) → Fin 2) (Fin (M + 1) → Fin 2) ℂ)
    (σ τ : Fin (M + 1) → Fin 2) :
    A.mulVec (basisVec σ) τ = A τ σ :=
  sum_mul_basisVec σ (fun ρ => A τ ρ)

/-- **The Jordan–Wigner sign cocycle.**  Under the hop-allowed condition (source
`π q` occupied, target `π p` empty after the move), the PR13 composite conjugation
sign collapses to the single bare hop sign at the permuted orbitals:
`permutationHopConjSign π p q σ = jwSign (π q) σ · jwSign (π p) (update σ (π q) 0)`. -/
theorem permutationHopConjSign_eq (π : Equiv.Perm (Fin (M + 1))) (p q : Fin (M + 1))
    (σ : Fin (M + 1) → Fin 2) (hq : σ (π q) = 1)
    (hp : (Function.update σ (π q) 0) (π p) = 0) :
    permutationHopConjSign π p q σ
      = jwSign M (π q) σ * jwSign M (π p) (Function.update σ (π q) 0) := by
  -- the one-mode-update parity laws at `q` (remove) and `p` (add)
  have hI := translationJwSign_mul_update_zero_comp_eq_jwSign_mul π σ q
    (by rw [Function.comp_apply]; exact hq)
  have hII := translationJwSign_mul_update_one_comp_eq_jwSign_mul π
    (Function.update σ (π q) 0) p (by rw [Function.comp_apply]; exact hp)
  rw [← update_comp_perm π σ q 0] at hII
  -- ±1 squares
  have hb := translationJwSign_sq π (Function.update (σ ∘ π) q 0)
  have he := jwSign_mul_self q (σ ∘ π)
  have hf := jwSign_mul_self p (Function.update (σ ∘ π) q 0)
  -- abbreviate the seven ±1 scalars and close by the cocycle algebra
  unfold permutationHopConjSign
  set a := translationJwSign π (σ ∘ π)
  set b := translationJwSign π (Function.update (σ ∘ π) q 0)
  set d := translationJwSign π (Function.update (Function.update (σ ∘ π) q 0) p 1)
  set e := jwSign M q (σ ∘ π)
  set f := jwSign M p (Function.update (σ ∘ π) q 0)
  set g := jwSign M (π q) σ
  set h := jwSign M (π p) (Function.update σ (π q) 0)
  -- hI : a * b = e * g, hII : b * d = f * h
  have key : a * d = e * f * g * h := by
    have h1 : (a * b) * (b * d) = (e * g) * (f * h) := by rw [hI, hII]
    rw [show (a * b) * (b * d) = a * d * (b * b) by ring, hb, mul_one] at h1
    rw [h1]; ring
  calc a * (e * f) * d = (a * d) * (e * f) := by ring
    _ = (e * f * g * h) * (e * f) := by rw [key]
    _ = (e * e) * (f * f) * (g * h) := by ring
    _ = g * h := by rw [he, hf]; ring

/-- **The conjugated hop and the permuted bare hop have equal basis action.**
Combining the PR13 basis action with the cocycle (`permutationHopConjSign_eq`) and
the `update_comp_perm` relabeling. -/
theorem permutationOperator_hop_conj_mulVec_basisVec (π : Equiv.Perm (Fin (M + 1)))
    (p q : Fin (M + 1)) (σ : Fin (M + 1) → Fin 2) :
    ((permutationOperator π) *
        (fermionMultiCreation M p * fermionMultiAnnihilation M q) *
        (permutationOperator π)ᴴ).mulVec (basisVec σ)
      = (fermionMultiCreation M (π p) * fermionMultiAnnihilation M (π q)).mulVec
          (basisVec σ) := by
  rw [permutationOperator_hopping_conj_mulVec_basisVec,
    fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  -- the two hop conditions coincide
  have hcondq : (σ ∘ π) q = σ (π q) := rfl
  have hcondp : (Function.update (σ ∘ π) q 0) p = (Function.update σ (π q) 0) (π p) :=
    congrFun (update_comp_perm π σ q 0) p
  by_cases hc : σ (π q) = 1 ∧ (Function.update σ (π q) 0) (π p) = 0
  · rw [if_pos (by rw [hcondq, hcondp]; exact hc), if_pos hc]
    -- equal signs (cocycle) and equal target states
    have hstate :
        (Function.update (Function.update (σ ∘ π) q 0) p 1) ∘ π.symm
          = Function.update (Function.update σ (π q) 0) (π p) 1 := by
      rw [update_comp_perm π σ q 0, update_comp_perm π (Function.update σ (π q) 0) p 1,
        Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
    rw [permutationHopConjSign_eq π p q σ hc.1 hc.2, hstate]
  · rw [if_neg (by rw [hcondq, hcondp]; exact hc), if_neg hc]

/-- **The conjugated single-hop operator equality.**  Conjugating a single hopping
term by the signed permutation operator gives the hop at the permuted orbitals:
`U (ĉ†_p ĉ_q) Uᴴ = ĉ†_{π p} ĉ_{π q}`.  Established by matching columns (basis
actions) via `permutationOperator_hop_conj_mulVec_basisVec`. -/
theorem permutationOperator_hop_conj_eq (π : Equiv.Perm (Fin (M + 1)))
    (p q : Fin (M + 1)) :
    (permutationOperator π) *
        (fermionMultiCreation M p * fermionMultiAnnihilation M q) *
        (permutationOperator π)ᴴ
      = fermionMultiCreation M (π p) * fermionMultiAnnihilation M (π q) := by
  ext τ σ
  have h := congrFun (permutationOperator_hop_conj_mulVec_basisVec π p q σ) τ
  rwa [mulVec_basisVec_apply, mulVec_basisVec_apply] at h

end LatticeSystem.Fermion
