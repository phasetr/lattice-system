import LatticeSystem.Quantum.SpinS.AndersonTowerLeviCivita
import LatticeSystem.Quantum.SpinS.AndersonTowerCartWord
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSq

/-!
# Tasaki §4.2.2 Proposition 4.10: swap-band telescoping of the Cartesian order word

This module is the algebraic heart of the swap-band contraction (Prop 4.10 arc PR-3.2b-ii).  It
pushes a total-spin generator `Ŝ^{(γ)}_tot` through the Cartesian order word `cartWord w`
(`AndersonTowerCartWord`) via the uniform single-letter rotation commutator
`[Ŝ^{(γ)}_tot, ô^{(β)}] = i Σ_δ ε_{γβδ} ô^{(δ)}` (`AndersonTowerLeviCivita`), producing a
length-preserving **telescoping identity**

`Ŝ^{(γ)}_tot · ô^{w} = ô^{w} · Ŝ^{(γ)}_tot + i Σ_k Σ_δ ε_{γ w_k δ} ô^{w[k ↦ δ]}`,

where `ô^{w[k ↦ δ]}` is the word with its `k`-th letter rotated from `w_k` to `δ`.  On a total-spin
singlet `Φ` (`Ŝ^{(γ)}_tot Φ = 0` for all three axes, via `AndersonTowerOrderSq`) the leading term
`ô^{w} · Ŝ^{(γ)}_tot Φ` vanishes, giving the **singlet corollary** for the vector action, and the
combination with the order×order commutator `[ô^{(α)}, ô^{(β)}] = i Σ_γ ε_{αβγ} Ŝ^{(γ)}_tot` and the
single-swap factorization `cartWord_swap_diff_eq` yields the **single-swap expectation identity**

`⟨Φ, ô^{pre α β suf} Φ⟩ − ⟨Φ, ô^{pre β α suf} Φ⟩
    = Σ_γ Σ_k Σ_δ (i ε_{αβγ})(i ε_{γ suf_k δ}) ⟨Φ, ô^{pre ++ suf[k ↦ δ]} Φ⟩`,

expressing the single adjacent swap as a signed triple sum over shorter (charge-removed) Cartesian
words.  This is the Cartesian analogue of the `Bool` eigenvalue telescoping
`orderWordProd_swap_dotProduct_eq` (Theorem 4.9); the `Bool` eigenvalue contraction is unavailable
here because `Ŝ^{(γ)}_tot` does not act diagonally on `cartWord w`.  Only the equalities are
established; the real-part band, operator-norm bound and `O(1/V)` estimate are the next step
(PR-3.3).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.58)–(4.2.59), p.108; cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### The uniform order×order commutator -/

/-- **Uniform order×order commutator** `[ô^{(α)}, ô^{(β)}] = i Σ_γ ε_{αβγ} Ŝ^{(γ)}_tot`.  The single
statement collecting the three off-diagonal order×order commutators
(`AndersonTowerEnergyBoundSU2`) and the three diagonal ones `[ô^{(α)}, ô^{(α)}] = 0`: the commutator
of two staggered axis operators is the Levi-Civita-weighted total-spin generator.  It contracts the
single-swap factorization `cartWord_swap_diff_eq` in the swap-band expectation identity. -/
theorem stagOpVec_commutator_eq (A : Λ → Bool) (α β : Fin 3) :
    stagOpVec A N α * stagOpVec A N β - stagOpVec A N β * stagOpVec A N α
      = Complex.I • ∑ γ : Fin 3, leviCivita3 α β γ • totalSpinSOpVec Λ N γ := by
  fin_cases α <;> fin_cases β <;>
    simp only [stagOpVec, totalSpinSOpVec, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Fin.sum_univ_three, leviCivita3]
  · module
  · rw [staggeredOrderOp1S_commutator_staggeredOrderOp2S]; module
  · rw [show staggeredOrderOp1S A N * staggeredOrderOpS A N
          - staggeredOrderOpS A N * staggeredOrderOp1S A N
        = -(staggeredOrderOpS A N * staggeredOrderOp1S A N
          - staggeredOrderOp1S A N * staggeredOrderOpS A N) by rw [neg_sub],
      staggeredOrderOpS_commutator_staggeredOrderOp1S]
    module
  · rw [show staggeredOrderOp2S A N * staggeredOrderOp1S A N
          - staggeredOrderOp1S A N * staggeredOrderOp2S A N
        = -(staggeredOrderOp1S A N * staggeredOrderOp2S A N
          - staggeredOrderOp2S A N * staggeredOrderOp1S A N) by rw [neg_sub],
      staggeredOrderOp1S_commutator_staggeredOrderOp2S]
    module
  · module
  · rw [staggeredOrderOp2S_commutator_staggeredOrderOpS]; module
  · rw [staggeredOrderOpS_commutator_staggeredOrderOp1S]; module
  · rw [show staggeredOrderOpS A N * staggeredOrderOp2S A N
          - staggeredOrderOp2S A N * staggeredOrderOpS A N
        = -(staggeredOrderOp2S A N * staggeredOrderOpS A N
          - staggeredOrderOpS A N * staggeredOrderOp2S A N) by rw [neg_sub],
      staggeredOrderOp2S_commutator_staggeredOrderOpS]
    module
  · module

/-! ### The operator telescoping identity -/

/-- Cons reindexing of the telescoping correction sum: splitting the length-`|w|+1` axis sum over
the head letter `β` (the `k = 0` term, rotating the head) and the tail (the `k = i+1` terms, which
factor the head operator `ô^{(β)}` out on the left).  This is the single bookkeeping step of the
cons induction proving `totalSpinSOpVec_mul_cartWord_eq`. -/
private theorem cartWord_telescope_sum_cons (A : Λ → Bool) (γ β : Fin 3) (w' : List (Fin 3)) :
    (∑ k : Fin (β :: w').length, ∑ δ : Fin 3,
        leviCivita3 γ ((β :: w').get k) δ • cartWord A N ((β :: w').set (k : ℕ) δ))
      = (∑ δ : Fin 3, leviCivita3 γ β δ • cartWord A N (δ :: w'))
        + stagOpVec A N β
            * ∑ k : Fin w'.length, ∑ δ : Fin 3,
                leviCivita3 γ (w'.get k) δ • cartWord A N (w'.set (k : ℕ) δ) := by
  change (∑ k : Fin (w'.length + 1), ∑ δ : Fin 3,
      leviCivita3 γ ((β :: w').get k) δ • cartWord A N ((β :: w').set (k : ℕ) δ)) = _
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [List.get_cons_zero, List.get_cons_succ', Fin.val_zero, Fin.val_succ,
    List.set_cons_zero, List.set_cons_succ, cartWord_cons, Finset.mul_sum, mul_smul_comm]

/-- **Operator telescoping identity** (Prop 4.10 arc, `Φ`-free): pushing a total-spin generator
`Ŝ^{(γ)}_tot` through the Cartesian order word `ô^{w}` rotates each letter in turn,

`Ŝ^{(γ)}_tot · ô^{w} = ô^{w} · Ŝ^{(γ)}_tot + i Σ_k Σ_δ ε_{γ w_k δ} ô^{w[k ↦ δ]}`,

where `w[k ↦ δ] = w.set k δ` is the axis word with its `k`-th letter replaced by `δ`.  The
correction is a length-preserving signed sum over single-letter rotations, generated letter by
letter through the uniform commutator `totalSpinSOpVec_commutator_stagOpVec`.  Proved by `cons`
induction on `w`; the leading commutator term is discharged on a singlet in
`totalSpinSOpVec_mulVec_cartWord_singlet`. -/
theorem totalSpinSOpVec_mul_cartWord_eq (A : Λ → Bool) (γ : Fin 3) (w : List (Fin 3)) :
    totalSpinSOpVec Λ N γ * cartWord A N w
      = cartWord A N w * totalSpinSOpVec Λ N γ
        + Complex.I • ∑ k : Fin w.length, ∑ δ : Fin 3,
            leviCivita3 γ (w.get k) δ • cartWord A N (w.set (k : ℕ) δ) := by
  induction w with
  | nil =>
    simp only [cartWord, List.map_nil, List.prod_nil, mul_one, one_mul, List.length_nil,
      Finset.univ_eq_empty, Finset.sum_empty, smul_zero, add_zero]
  | cons β w' ih =>
    have hcomm : totalSpinSOpVec Λ N γ * stagOpVec A N β
        = stagOpVec A N β * totalSpinSOpVec Λ N γ
          + Complex.I • ∑ δ : Fin 3, leviCivita3 γ β δ • stagOpVec A N δ := by
      rw [← totalSpinSOpVec_commutator_stagOpVec]; abel
    have hT3 : (Complex.I • ∑ δ : Fin 3, leviCivita3 γ β δ • stagOpVec A N δ) * cartWord A N w'
        = Complex.I • ∑ δ : Fin 3, leviCivita3 γ β δ • cartWord A N (δ :: w') := by
      rw [smul_mul_assoc, Finset.sum_mul]
      refine congrArg (Complex.I • ·) (Finset.sum_congr rfl fun δ _ => ?_)
      rw [smul_mul_assoc, cartWord_cons]
    rw [cartWord_telescope_sum_cons, cartWord_cons, ← mul_assoc, hcomm, add_mul, mul_assoc, ih,
      mul_add, hT3, mul_smul_comm, mul_assoc, smul_add]
    abel

/-! ### The singlet corollary and the single-swap expectation identity -/

/-- **Singlet corollary of the telescoping identity.**  For a total-spin singlet `Φ`
(`Ŝ³_tot Φ = 0`, `Ŝ¹_tot Φ = 0`, hence `Ŝ²_tot Φ = 0` by `totalSpinSOp2_mulVec_eq_zero_of_singlet`),
the leading term of the telescoping identity `totalSpinSOpVec_mul_cartWord_eq` drops, so the vector
action reduces to the pure rotation sum

`Ŝ^{(γ)}_tot (ô^{w} Φ) = i Σ_k Σ_δ ε_{γ w_k δ} (ô^{w[k ↦ δ]} Φ)`. -/
theorem totalSpinSOpVec_mulVec_cartWord_singlet (A : Λ → Bool) (γ : Fin 3) (w : List (Fin 3))
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    (totalSpinSOpVec Λ N γ).mulVec ((cartWord A N w).mulVec Φ)
      = Complex.I • ∑ k : Fin w.length, ∑ δ : Fin 3,
          leviCivita3 γ (w.get k) δ • (cartWord A N (w.set (k : ℕ) δ)).mulVec Φ := by
  have hγ : (totalSpinSOpVec Λ N γ).mulVec Φ = 0 := by
    fin_cases γ <;>
      simp only [totalSpinSOpVec, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    · exact h1
    · exact totalSpinSOp2_mulVec_eq_zero_of_singlet Φ h3 h1
    · exact h3
  rw [Matrix.mulVec_mulVec, totalSpinSOpVec_mul_cartWord_eq, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, hγ, Matrix.mulVec_zero, zero_add, Matrix.smul_mulVec]
  simp_rw [Matrix.sum_mulVec, Matrix.smul_mulVec]

/-- Vector form of the order×order commutator acting on a singlet-based word: combining the uniform
order×order commutator `stagOpVec_commutator_eq` with the telescoping singlet corollary
`totalSpinSOpVec_mulVec_cartWord_singlet`, the commutator `[ô^{(α)}, ô^{(β)}]` acting on `ô^{suf} Φ`
becomes the signed triple sum over shorter Cartesian words. -/
theorem orderComm_mulVec_cartWord_singlet (A : Λ → Bool) (α β : Fin 3) (suf : List (Fin 3))
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    (stagOpVec A N α * stagOpVec A N β - stagOpVec A N β * stagOpVec A N α).mulVec
        ((cartWord A N suf).mulVec Φ)
      = ∑ γ : Fin 3, ∑ k : Fin suf.length, ∑ δ : Fin 3,
          ((Complex.I * leviCivita3 α β γ) * (Complex.I * leviCivita3 γ (suf.get k) δ))
            • (cartWord A N (suf.set (k : ℕ) δ)).mulVec Φ := by
  rw [stagOpVec_commutator_eq, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp_rw [Matrix.smul_mulVec, totalSpinSOpVec_mulVec_cartWord_singlet A _ suf Φ h3 h1,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun δ _ => ?_
  congr 1
  ring

/-- **Single-swap expectation identity** (Prop 4.10 arc PR-3.2b-ii tip, `Φ` present, equality only).
For a total-spin singlet `Φ`, the expectation of a Cartesian order word changes under one adjacent
transposition of its letters by a signed triple sum over shorter (charge-removed) Cartesian words:

`⟨Φ, ô^{pre α β suf} Φ⟩ − ⟨Φ, ô^{pre β α suf} Φ⟩
    = Σ_γ Σ_k Σ_δ (i ε_{αβγ})(i ε_{γ suf_k δ}) ⟨Φ, ô^{pre ++ suf[k ↦ δ]} Φ⟩`.

This is the Cartesian analogue of the `Bool` eigenvalue telescoping
`orderWordProd_swap_dotProduct_eq` (Theorem 4.9); the double Levi-Civita weight stays as a scalar
product.  Only the identity is established; the real-part band and `O(1/V)` estimate are PR-3.3. -/
theorem cartWord_swap_dotProduct_eq (A : Λ → Bool) (pre suf : List (Fin 3)) (α β : Fin 3)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    (star Φ ⬝ᵥ (cartWord A N (pre ++ α :: β :: suf)).mulVec Φ)
        - (star Φ ⬝ᵥ (cartWord A N (pre ++ β :: α :: suf)).mulVec Φ)
      = ∑ γ : Fin 3, ∑ k : Fin suf.length, ∑ δ : Fin 3,
          ((Complex.I * leviCivita3 α β γ) * (Complex.I * leviCivita3 γ (suf.get k) δ))
            * (star Φ ⬝ᵥ (cartWord A N (pre ++ suf.set (k : ℕ) δ)).mulVec Φ) := by
  have hvec : (cartWord A N (pre ++ α :: β :: suf)).mulVec Φ
        - (cartWord A N (pre ++ β :: α :: suf)).mulVec Φ
      = ∑ γ : Fin 3, ∑ k : Fin suf.length, ∑ δ : Fin 3,
          ((Complex.I * leviCivita3 α β γ) * (Complex.I * leviCivita3 γ (suf.get k) δ))
            • (cartWord A N (pre ++ suf.set (k : ℕ) δ)).mulVec Φ := by
    rw [← Matrix.sub_mulVec, cartWord_swap_diff_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      orderComm_mulVec_cartWord_singlet A α β suf Φ h3 h1]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← cartWord_append]
  rw [← dotProduct_sub, hvec, dotProduct_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [dotProduct_smul, smul_eq_mul]

end LatticeSystem.Quantum
