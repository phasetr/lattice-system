import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSuperexchangeReducedInverse
import LatticeSystem.Fermion.JordanWigner.Hubbard.SuperexchangeOperatorIdentity

/-!
# Hop-pair collapse for Theorem 10.4 (Tasaki §10.1, PR-8a)

Eighth installment of the Theorem 10.4 discharge arc (issue #5320); first of the two-PR
final-assembly split of the original PR-8 (PR-8a / PR-8b, per the fresh design round scoped to
PR-8, recorded in `.self-local/active/issue-5320.md`). PR-6 supplied the reduced-inverse layer and
its capstone `secondOrderEffectiveHamiltonian_liebPerturbation_eq`, which reduces the second-order
effective Hamiltonian to `−(P̂₀ · V̂|_K · V̂|_K · P̂₀)`; PR-7 supplied the model-independent
hop-return identity `fermionHopReturn_eq`. This file computes the entrywise expansion of
`V̂ · V̂` on the singly-occupied (half-filled hard-core) sector and collapses it to a sum of
`fermionHopReturn` terms — Tasaki's collapse argument (eq. (10.1.8), p. 344): "one electron must
hop from `x` to `y` to resolve the double occupancy so that the excited state returns to the
subspace `H₀`".

## Collapse argument

Expanding `V̂ · V̂ = Σ_{σ,i,j,τ,k,l} t_{ij} t_{kl} (ĉ†_{i,σ}ĉ_{j,σ})(ĉ†_{k,τ}ĉ_{l,τ})` and
evaluating a matrix entry between two singly-occupied configurations `c`, `e`: the right factor
`ĉ†_{k,τ}ĉ_{l,τ}` acts first, so (for `k ≠ l`) it produces an intermediate configuration `d` with
site `k` doubly occupied and site `l` empty, all other sites unchanged. The left factor
`ĉ†_{i,σ}ĉ_{j,σ}` (for `i ≠ j`) then requires `d`'s site `j` occupied and site `i` empty for the
result to reach a singly-occupied `e`; tracking the occupation numbers of `d` forces `j = k` (the
only site of `d` carrying two electrons) and `i = l` (the only site of `d` left empty). Hence the
whole double sum over `(i, j, k, l)` collapses to the diagonal `i = l ∧ j = k`, and the surviving
term at `(i, j, k, l) = (l, k, k, l)` is literally the `(τ', σ') = (σ, τ)` summand of
`fermionHopReturn N k l` (`SuperexchangeOperatorIdentity.lean`) — no Jordan–Wigner sign is computed
here, both sides carry the same operator and `jwSign` cancels by construction. The capstone
therefore needs no `hT` (symmetry of the hopping matrix `T`) at this stage: the surviving
coefficient is the *asymmetric* product `t_{yx} · t_{xy}`, and only PR-8b's reduction of that
product to the endpoint-graph indicator `t_{xy}²` (`liebEndpointHopping_sq_eq_indicator`'s `hT`
variant) needs the symmetry hypothesis. This file nevertheless records the provenance of that later
correction (`.self-local/active/issue-5320.md`, "Correction: `hT` ... is a *necessary* hypothesis"):
an asymmetric `T` with `T x y > 0 > T y x` would make `t_{yx} t_{xy}` and the endpoint indicator
`(liebEndpointHopping A T 1 x y)²` disagree in sign, which is why PR-8b — not this file — must
carry `hT` alongside `hbip`.

Both the `i = j` and `k = l` (same-site) sub-cases are number-operator terms; they are killed
upstream by `liebEndpointHopping_diag_eq_zero` (`LiebRepulsivePerturbationSetup.lean`), acting on
the *coefficient* `liebEndpointHopping A T 1 i j`, not on the fermion operators themselves, so the
sums in the capstone below range over *all* ordered pairs `(x, y)` with no off-diagonal filter.

## Per-site occupancy arithmetic (replaces nested `Function.update` combinatorics)

The collapse's case analysis is carried out via the **per-site** occupation count
`(f (spinfulIndex N z 0)).val + (f (spinfulIndex N z 1)).val` rather than a `def` (a new
definition would break defeq with the existing public statements
`liebHalfFilling_site_occupation`/`liebPerturbationV_intermediate_weight_eq_one`, which state the
occupation count on the raw expression). `sum_val_update_hop_site` is the per-site analogue of
PR-6's total-count lemma `sum_val_update_hop`
(`LiebRepulsiveSuperexchangeReducedInverse.lean:105`): for a hop `q = spinfulIndex N j σ → p =
spinfulIndex N i σ` with `i ≠ j`, `c q = 1`, `(update c q 0) p = 0`, and
`d := update (update c q 0) p 1`, the per-site occupation count at `d` gains one electron at `i`,
loses one at `j`, and is unchanged elsewhere.

## Debt

Nothing yet consumes the capstone `liebPerturbationV_sq_apply_eq_of_singly_occupied` (staged for
PR-8b, which reduces its right-hand side further via the half-filling diagonal collapse and lifts
it to the compressed sector).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1, eq. (10.1.8), p. 344.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped ComplexOrder

variable {N : ℕ}

/-! ## Per-site hop-occupancy transport -/

/-- **A hop transports one electron between two sites, per-site.** For a hop from the occupied
orbital `spinfulIndex N j σ` to the empty orbital `spinfulIndex N i σ` (`i ≠ j`), the resulting
configuration `d` gains exactly one electron of per-site occupation at `i`, loses exactly one at
`j`, and is unchanged at every other site. Stated on the raw occupation expression (no new `def`)
so it stays defeq with `liebHalfFilling_site_occupation` and
`liebPerturbationV_intermediate_weight_eq_one`. -/
private theorem sum_val_update_hop_site {N : ℕ} (c : Fin (2 * N + 2) → Fin 2)
    {i j : Fin (N + 1)} {σ : Fin 2} (hij : i ≠ j)
    (hq : c (spinfulIndex N j σ) = 1)
    (hp : (Function.update c (spinfulIndex N j σ) 0) (spinfulIndex N i σ) = 0) :
    (((Function.update (Function.update c (spinfulIndex N j σ) 0)
          (spinfulIndex N i σ) 1) (spinfulIndex N i 0)).val +
        ((Function.update (Function.update c (spinfulIndex N j σ) 0)
          (spinfulIndex N i σ) 1) (spinfulIndex N i 1)).val
      = (c (spinfulIndex N i 0)).val + (c (spinfulIndex N i 1)).val + 1) ∧
      (((Function.update (Function.update c (spinfulIndex N j σ) 0)
            (spinfulIndex N i σ) 1) (spinfulIndex N j 0)).val +
          ((Function.update (Function.update c (spinfulIndex N j σ) 0)
            (spinfulIndex N i σ) 1) (spinfulIndex N j 1)).val + 1
        = (c (spinfulIndex N j 0)).val + (c (spinfulIndex N j 1)).val) ∧
      (∀ z : Fin (N + 1), z ≠ i → z ≠ j →
        ((Function.update (Function.update c (spinfulIndex N j σ) 0)
              (spinfulIndex N i σ) 1) (spinfulIndex N z 0)).val +
            ((Function.update (Function.update c (spinfulIndex N j σ) 0)
              (spinfulIndex N i σ) 1) (spinfulIndex N z 1)).val
          = (c (spinfulIndex N z 0)).val + (c (spinfulIndex N z 1)).val) := by
  sorry

/-! ## The hop-pair collapse -/

/-- **Hop-pair collapse.** On the singly-occupied sector (both `c` and `e` carry exactly one
electron per site), the entry of a product of two hopping terms
`(ĉ†_{i,σ}ĉ_{j,σ}) · (ĉ†_{k,τ}ĉ_{l,τ})` between `e` and `c` vanishes unless `i = l ∧ j = k`: the
right factor (`k ≠ l`) forces the intermediate configuration to have site `k` doubly occupied and
site `l` empty (`sum_val_update_hop_site`); the left factor (`i ≠ j`) can then only reach a
singly-occupied `e` by hopping out of the doubly-occupied site and into the emptied one, i.e.
`j = k` and `i = l`. This is the heaviest combinatorial step of the collapse and is where the
per-site occupancy arithmetic (rather than nested `Function.update` case splits) pays off. -/
private theorem hop_pair_apply_eq_zero_of_ne {N : ℕ} {c e : Fin (2 * N + 2) → Fin 2}
    (hc : ∀ x : Fin (N + 1),
      (c (spinfulIndex N x 0)).val + (c (spinfulIndex N x 1)).val = 1)
    (he : ∀ x : Fin (N + 1),
      (e (spinfulIndex N x 0)).val + (e (spinfulIndex N x 1)).val = 1)
    {i j k l : Fin (N + 1)} (hij : i ≠ j) (hkl : k ≠ l) {σ τ : Fin 2}
    (hne : ¬ (i = l ∧ j = k)) :
    ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
          fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)) *
        (fermionMultiCreation (2 * N + 1) (spinfulIndex N k τ) *
          fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N l τ))) e c = 0 := by
  sorry

/-! ## The PR-8a capstone -/

/-- **PR-8a capstone: the hop-pair collapse for `V̂ · V̂`.** On the singly-occupied sector, the
entrywise expansion of `V̂ · V̂` (whole Fock space, unit coupling) collapses via
`hop_pair_apply_eq_zero_of_ne` to a sum of `fermionHopReturn` terms with coefficient
`t_{yx} · t_{xy}` (the *asymmetric* product, not yet reduced to the endpoint-graph indicator
`t_{xy}²` — that reduction is PR-8b's, and needs the additional symmetry hypothesis `hT`, not
required here). The sums range over all ordered pairs `(x, y)`; the `x = y` (number-operator) terms
vanish upstream via the coefficient `liebEndpointHopping_diag_eq_zero`, not via a filter on the sum.
-/
theorem liebPerturbationV_sq_apply_eq_of_singly_occupied {N : ℕ} {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    {c e : Fin (2 * N + 2) → Fin 2}
    (hc : ∀ x : Fin (N + 1),
      (c (spinfulIndex N x 0)).val + (c (spinfulIndex N x 1)).val = 1)
    (he : ∀ x : Fin (N + 1),
      (e (spinfulIndex N x 0)).val + (e (spinfulIndex N x 1)).val = 1) :
    (liebPerturbationV N A T * liebPerturbationV N A T) e c
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          ((liebEndpointHopping A T 1 y x * liebEndpointHopping A T 1 x y : ℝ) : ℂ) *
            (fermionHopReturn N x y) e c := by
  sorry

end LatticeSystem.Fermion
