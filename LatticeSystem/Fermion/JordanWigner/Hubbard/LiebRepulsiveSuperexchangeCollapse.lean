import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSuperexchangeReducedInverse
import LatticeSystem.Fermion.JordanWigner.Hubbard.SuperexchangeOperatorIdentity

/-!
# Hop-pair collapse for Theorem 10.4 (Tasaki §10.1, PR-8a)

Eighth installment of the Theorem 10.4 discharge arc (issue #5320); first of the two-PR
final-assembly split of the original PR-8 (PR-8a / PR-8b). PR-6 supplied the reduced-inverse layer
and its capstone `secondOrderEffectiveHamiltonian_liebPerturbation_eq`, which reduces the
second-order effective Hamiltonian to `−(P̂₀ · V̂|_K · V̂|_K · P̂₀)`; PR-7 supplied the
model-independent hop-return identity `fermionHopReturn_eq`. This file computes the entrywise
expansion of `V̂ · V̂` on the singly-occupied (half-filled hard-core) sector and collapses it to a
sum of `fermionHopReturn` terms — Tasaki's collapse argument (eq. (10.1.8), p. 344): "one electron
must hop from `x` to `y` to resolve the double occupancy so that the excited state returns to the
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
product to the endpoint-graph indicator `t_{xy}²` needs the symmetry hypothesis. There `hT` is
genuinely necessary rather than a convenience: an asymmetric `T` with `T x y > 0 > T y x` would
make `t_{yx} t_{xy}` and the endpoint indicator `(liebEndpointHopping A T 1 x y)²` disagree in
sign, which is why PR-8b — not this file — must carry `hT` alongside `hbip`.

Index-orientation caveat: the display above attaches `t_{ij}` to the *left* operator factor, while
the proof below (`hzero`/`hcollapse`) works in the `simp` normal form of the matrix product, where
`t_{ij}` sits with the *right* factor `ĉ†_{i,σ}ĉ_{j,σ}` (the one acting first) and `t_{kl}` with the
left factor. The two index pairs are thus interchanged relative to this paragraph — the surviving
diagonal is written `k = j ∧ l = i` there — but the condition and the resulting statement are the
same.

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
  have hsiteNe : ∀ (a b : Fin (N + 1)) (r s : Fin 2), a ≠ b →
      spinfulIndex N a r ≠ spinfulIndex N b s :=
    fun a b r s hab h => hab ((spinfulIndex_eq_iff N a b r s).mp h).1
  have hspinNe : ∀ (a b : Fin (N + 1)) (r s : Fin 2), r ≠ s →
      spinfulIndex N a r ≠ spinfulIndex N b s :=
    fun a b r s hrs h => hrs ((spinfulIndex_eq_iff N a b r s).mp h).2
  have hpq : spinfulIndex N i σ ≠ spinfulIndex N j σ := hsiteNe i j σ σ hij
  have hci : (c (spinfulIndex N i σ)).val = 0 := by
    rw [Function.update_of_ne hpq] at hp
    simp [hp]
  have hcj : (c (spinfulIndex N j σ)).val = 1 := by simp [hq]
  have hdi : ((Function.update (Function.update c (spinfulIndex N j σ) 0)
      (spinfulIndex N i σ) 1) (spinfulIndex N i σ)).val = 1 := by simp
  have hdj : ((Function.update (Function.update c (spinfulIndex N j σ) 0)
      (spinfulIndex N i σ) 1) (spinfulIndex N j σ)).val = 0 := by
    rw [Function.update_of_ne hpq.symm]
    simp
  have hdother : ∀ (z : Fin (N + 1)) (r : Fin 2),
      spinfulIndex N z r ≠ spinfulIndex N i σ → spinfulIndex N z r ≠ spinfulIndex N j σ →
      ((Function.update (Function.update c (spinfulIndex N j σ) 0)
            (spinfulIndex N i σ) 1) (spinfulIndex N z r)).val
        = (c (spinfulIndex N z r)).val := by
    intro z r h1 h2
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  refine ⟨?_, ?_, ?_⟩
  · rcases (show σ = 0 ∨ σ = 1 by omega) with rfl | rfl
    · have h1 := hdother i 1 (hspinNe i i 1 0 (by decide)) (hsiteNe i j 1 0 hij)
      omega
    · have h1 := hdother i 0 (hspinNe i i 0 1 (by decide)) (hsiteNe i j 0 1 hij)
      omega
  · rcases (show σ = 0 ∨ σ = 1 by omega) with rfl | rfl
    · have h1 := hdother j 1 (hsiteNe j i 1 0 (Ne.symm hij)) (hspinNe j j 1 0 (by decide))
      omega
    · have h1 := hdother j 0 (hsiteNe j i 0 1 (Ne.symm hij)) (hspinNe j j 0 1 (by decide))
      omega
  · intro z hzi hzj
    rw [hdother z 0 (hsiteNe z i 0 σ hzi) (hsiteNe z j 0 σ hzj),
      hdother z 1 (hsiteNe z i 1 σ hzi) (hsiteNe z j 1 σ hzj)]

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
  have hentry : ∀ M : ManyBodyOp (Fin (2 * N + 2)), M e c = M.mulVec (basisVec c) e :=
    fun M => (mulVec_basisVec_apply M e c).symm
  rw [hentry (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ) *
      (fermionMultiCreation (2 * N + 1) (spinfulIndex N k τ) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N l τ))),
    ← Matrix.mulVec_mulVec, fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  by_cases hcond : c (spinfulIndex N l τ) = 1 ∧
      (Function.update c (spinfulIndex N l τ) 0) (spinfulIndex N k τ) = 0
  · rw [if_pos hcond, Matrix.mulVec_smul,
      fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
    obtain ⟨hdk, hdl, hdz⟩ := sum_val_update_hop_site c hkl hcond.1 hcond.2
    set d := Function.update (Function.update c (spinfulIndex N l τ) 0)
      (spinfulIndex N k τ) 1
    by_cases hcond2 : d (spinfulIndex N j σ) = 1 ∧
        (Function.update d (spinfulIndex N j σ) 0) (spinfulIndex N i σ) = 0
    · have hene : e ≠ Function.update (Function.update d (spinfulIndex N j σ) 0)
          (spinfulIndex N i σ) 1 := by
        intro heq
        obtain ⟨hdi, hdj, -⟩ := sum_val_update_hop_site d hij hcond2.1 hcond2.2
        rw [← heq] at hdi hdj
        have hei := he i
        have hej := he j
        have hck := hc k
        have hcl := hc l
        have hjk : j = k := by
          by_contra hjk
          rcases eq_or_ne j l with rfl | hjl
          · omega
          · have hdzj := hdz j hjk hjl
            have hcj := hc j
            omega
        have hil : i = l := by
          by_contra hil
          rcases eq_or_ne i k with rfl | hik
          · omega
          · have hdzi := hdz i hik hil
            have hci := hc i
            omega
        exact hne ⟨hil, hjk⟩
      rw [if_pos hcond2]
      simp only [Pi.smul_apply, smul_eq_mul, basisVec_of_ne hene, mul_zero]
    · rw [if_neg hcond2, smul_zero, Pi.zero_apply]
  · rw [if_neg hcond, Matrix.mulVec_zero, Pi.zero_apply]

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
  have hzero : ∀ (σ τ : Fin 2) (i j k l : Fin (N + 1)), ¬ (k = j ∧ l = i) →
      (liebEndpointHopping A T 1 i j : ℂ) * (liebEndpointHopping A T 1 k l : ℂ) *
          ((fermionMultiCreation (2 * N + 1) (spinfulIndex N k τ) *
                fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N l τ) *
              (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
                fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))) e c) = 0 := by
    intro σ τ i j k l hne
    by_cases hij : i = j
    · subst hij
      rw [liebEndpointHopping_diag_eq_zero hbip i, Complex.ofReal_zero, zero_mul, zero_mul]
    · by_cases hkl : k = l
      · subst hkl
        rw [liebEndpointHopping_diag_eq_zero hbip k, Complex.ofReal_zero, mul_zero, zero_mul]
      · rw [hop_pair_apply_eq_zero_of_ne hc he hkl hij hne, mul_zero]
  have hcollapse : ∀ (σ τ : Fin 2) (i j : Fin (N + 1)),
      ∑ k : Fin (N + 1), ∑ l : Fin (N + 1),
          (liebEndpointHopping A T 1 i j : ℂ) * (liebEndpointHopping A T 1 k l : ℂ) *
            ((fermionMultiCreation (2 * N + 1) (spinfulIndex N k τ) *
                  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N l τ) *
                (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
                  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))) e c)
        = (liebEndpointHopping A T 1 i j : ℂ) * (liebEndpointHopping A T 1 j i : ℂ) *
            ((fermionMultiCreation (2 * N + 1) (spinfulIndex N j τ) *
                  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i τ) *
                (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
                  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))) e c) := by
    intro σ τ i j
    rw [Fintype.sum_eq_single j (fun k hkj =>
      Finset.sum_eq_zero fun l _ => hzero σ τ i j k l (fun h => hkj h.1))]
    exact Fintype.sum_eq_single i (fun l hli => hzero σ τ i j j l (fun h => hli h.2))
  have hreindex : ∀ G : Fin 2 → Fin (N + 1) → Fin (N + 1) → Fin 2 → ℂ,
      ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), ∑ σ : Fin 2, ∑ τ : Fin 2, G σ i j τ
        = ∑ σ : Fin 2, ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), ∑ τ : Fin 2, G σ i j τ := by
    intro G
    exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
  have hrhs : ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        ((liebEndpointHopping A T 1 y x * liebEndpointHopping A T 1 x y : ℝ) : ℂ) *
          (fermionHopReturn N x y) e c
      = ∑ σ : Fin 2, ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), ∑ τ : Fin 2,
          (liebEndpointHopping A T 1 i j : ℂ) * (liebEndpointHopping A T 1 j i : ℂ) *
            ((fermionMultiCreation (2 * N + 1) (spinfulIndex N j τ) *
                  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i τ) *
                (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
                  fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))) e c) := by
    rw [← hreindex (fun σ i j τ =>
      (liebEndpointHopping A T 1 i j : ℂ) * (liebEndpointHopping A T 1 j i : ℂ) *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N j τ) *
              fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i τ) *
            (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))) e c))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [fermionHopReturn, Matrix.sum_apply, Complex.ofReal_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Matrix.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun υ _ => ?_
    rw [mul_assoc (fermionMultiCreation (2 * N + 1) (spinfulIndex N y υ) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x υ)),
      mul_comm ((liebEndpointHopping A T 1 y x : ℝ) : ℂ)]
  rw [hrhs, liebPerturbationV, hubbardKinetic]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun τ _ => hcollapse σ τ i j

end LatticeSystem.Fermion
