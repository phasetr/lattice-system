import LatticeSystem.Quantum.IsingLowEnergyProblem33a

/-!
# The low-energy eigenvalue equation and its parity ansätze (Tasaki Problem 3.3.a)

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a (statement p. 59,
solution pp. 498-501) expands a low-energy state of the spin-`1/2` transverse-field Ising chain
of eq. (3.3.1), p. 56, in the `2L` low-energy configurations of
`LatticeSystem/Quantum/IsingLowEnergyProblem33a.lean` and solves the resulting scalar recursion.
With the convention `σ̂^α = 2 Ŝ^α` of §2.1, eqs. (2.1.7)-(2.1.8), p. 15, the Hamiltonian is
`quantumIsingHamiltonian N (1/4) (λ/2)` on `L = N + 1` sites and its compression to those
configurations is `lowEnergyMatrix N λ`.

This module carries the three steps that turn that compression into explicit eigenvectors:

* `lowEnergyMatrix_mulVec_eq_iff` is (S.28)-(S.30): the eigenvector equation
  `lowEnergyMatrix N λ *ᵥ φ = (E_GS^(0) + ε) • φ` holds exactly when the coefficients satisfy the
  tight-binding recursion `ε φ_j = -(λ/2)(φ_{j-1} + φ_{j+1}) + v_j φ_j` at every label;
* `tightBindingEnergy` is the eigenvalue (S.31) and `lowEnergyAnsatz` the two-branch ansatz
  (S.32), the sign parameter `s = ±1` selecting the symmetric resp. antisymmetric solution
  (`φ_L = s φ_0`);
* `rootEquation` is (S.34), and `lowEnergyAnsatz_isEigenvector` shows that under it the ansatz is
  a nonzero eigenvector of `lowEnergyMatrix N λ` with eigenvalue
  `E_GS^(0) + tightBindingEnergy λ κ`.

**The (S.30) ring is a ring of basis labels, not of lattice sites.** Labels have type
`ZMod (2 * (N + 1))` and sites have type `Fin (N + 1)`; the two are never identified, the chain
stays open, and no periodic lattice Hamiltonian occurs anywhere in this arc. Eq. (S.30) is printed
"for any `j = 1, …, 2L - 1`", but p. 500 uses it at `j = 0` to derive (S.33); the reading used
here is the eigenvector equation of the `2L × 2L` matrix, i.e. all `j : ZMod (2 * (N + 1))`.

`tightBindingEnergy λ κ` is an eigenvalue of the compression `lowEnergyMatrix N λ` only after the
shift by `E_GS^(0) = -N/4`; on its own it is an eigenvalue of the tight-binding part
`tightBindingRing N λ`. That the compression restricts `Ĥ` to an invariant subspace is not
established here, so the value is not asserted to be an energy of `Ĥ`, and the identifications
(S.36)-(S.38) of the source, which Tasaki writes with `≃`, are not asserted here. Tasaki notes on
p. 59 that the perturbative analysis of this problem is not mathematically rigorous.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ### The eigenvector equation as the (S.30) recursion -/

/-- Tasaki eqs. (S.28)-(S.30): a coefficient vector `φ` on the `2L` labels solves the
eigenvector equation `lowEnergyMatrix N λ *ᵥ φ = (E_GS^(0) + ε) • φ` exactly when it satisfies the
tight-binding recursion `ε φ_j = -(λ/2)(φ_{j-1} + φ_{j+1}) + v_j φ_j` at every label `j`, with the
potential `v_j = ringPotential N j` of (S.30).

The recursion is quantified over all labels, including `j = 0`: the source prints (S.30) for
`j = 1, …, 2L - 1` yet derives (S.33) from it at `j = 0` and `j = L`. The hypothesis `1 ≤ N`
(that is, `L ≥ 2`) enters twice: through `lowEnergyMatrix_eq_add_tightBindingRing`, and because
the two ring neighbours `j + 1` and `j - 1` of a label are distinct only when the label ring has
more than two elements. -/
theorem lowEnergyMatrix_mulVec_eq_iff (N : ℕ) (lam : ℝ) (hN : 1 ≤ N) (eps : ℝ)
    (phi : ZMod (2 * (N + 1)) → ℂ) :
    lowEnergyMatrix N lam *ᵥ phi = ((-(N : ℝ) / 4 + eps : ℝ) : ℂ) • phi ↔
      ∀ j : ZMod (2 * (N + 1)),
        (eps : ℂ) * phi j
          = -((lam : ℂ) / 2) * (phi (j - 1) + phi (j + 1)) + ringPotential N j * phi j := by
  have h2 : (2 : ZMod (2 * (N + 1))) ≠ 0 := by
    intro h
    have hv : ((2 : ℕ) : ZMod (2 * (N + 1))).val = 2 := ZMod.val_cast_of_lt (by omega)
    rw [show ((2 : ℕ) : ZMod (2 * (N + 1))) = 2 by push_cast; ring, h, ZMod.val_zero] at hv
    exact absurd hv (by omega)
  have hrow : ∀ j : ZMod (2 * (N + 1)), (tightBindingRing N lam *ᵥ phi) j
      = -((lam : ℂ) / 2) * (phi (j - 1) + phi (j + 1)) + ringPotential N j * phi j := by
    intro j
    have hsplit : ∀ b : ZMod (2 * (N + 1)), tightBindingRing N lam j b * phi b
        = (if b = j + 1 then -((lam : ℂ) / 2) * phi b else 0)
          + (if b = j - 1 then -((lam : ℂ) / 2) * phi b else 0)
          + (if b = j then ringPotential N j * phi b else 0) := by
      intro b
      have hne : j + 1 ≠ j - 1 := fun h => h2 (by linear_combination h)
      simp only [tightBindingRing]
      by_cases h1 : b = j + 1
      · have h2' : ¬ b = j - 1 := fun h => hne (h1 ▸ h)
        by_cases h3 : j = b
        · rw [if_pos (Or.inl h1), if_pos h1, if_neg h2', if_pos h3.symm, if_pos h3]
          ring
        · rw [if_pos (Or.inl h1), if_pos h1, if_neg h2', if_neg h3,
            if_neg (fun h => h3 h.symm)]
          ring
      · by_cases h2' : b = j - 1
        · by_cases h3 : j = b
          · rw [if_pos (Or.inr h2'), if_neg h1, if_pos h2', if_pos h3, if_pos h3.symm]
            ring
          · rw [if_pos (Or.inr h2'), if_neg h1, if_pos h2', if_neg h3,
              if_neg (fun h => h3 h.symm)]
            ring
        · by_cases h3 : j = b
          · rw [if_neg (by rintro (h | h) <;> [exact h1 h; exact h2' h]), if_neg h1, if_neg h2',
              if_pos h3, if_pos h3.symm]
            ring
          · rw [if_neg (by rintro (h | h) <;> [exact h1 h; exact h2' h]), if_neg h1, if_neg h2',
              if_neg h3, if_neg (fun h => h3 h.symm)]
            ring
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl fun b _ => hsplit b, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (j + 1) fun b => -((lam : ℂ) / 2) * phi b,
      Finset.sum_ite_eq' Finset.univ (j - 1) fun b => -((lam : ℂ) / 2) * phi b,
      Finset.sum_ite_eq' Finset.univ j fun b => ringPotential N j * phi b]
    simp only [Finset.mem_univ, if_pos]
    ring
  rw [lowEnergyMatrix_eq_add_tightBindingRing N lam hN, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, funext_iff]
  refine forall_congr' fun j => ?_
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hrow j]
  push_cast
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-! ### The (S.31) eigenvalue, the (S.32) ansatz and the (S.34) root equation -/

/-- Tasaki eq. (S.31): the eigenvalue `ε = -(λ/2)(e^κ + e^{-κ}) + 1/2` carried by the
ansatz `lowEnergyAnsatz` with decay rate `κ`.

This is an eigenvalue of the compressed matrix `lowEnergyMatrix` only after the shift by
`E_GS^(0)`; on its own it is an eigenvalue of the tight-binding part `tightBindingRing`. It is not
asserted to be an energy of the Hamiltonian itself. -/
noncomputable def tightBindingEnergy (lam kappa : ℝ) : ℝ :=
  -(lam / 2) * (Real.exp kappa + Real.exp (-kappa)) + 1 / 2

/-- Tasaki eq. (S.32): the two-branch ansatz for the coefficient vector, with
`φ_j = e^{-κ j} + s e^{-κ(L-j)}` on the labels `j = 0, …, L` and
`φ_j = s e^{-κ(j-L)} + e^{-κ(2L-j)}` on the labels `j = L, …, 2L`.

The sign `s = ±1` of the source selects the symmetric resp. antisymmetric solution, `φ_L = s φ_0`.
The two branches agree at the label `L`, and the second one returns at `j = 2L` to the value of
the first at `j = 0`, so the definition is consistent with the periodicity of the label ring. All
subtractions are performed in `ℝ` after casting the label's `ZMod.val`. -/
noncomputable def lowEnergyAnsatz (N : ℕ) (kappa s : ℝ) : ZMod (2 * (N + 1)) → ℂ :=
  fun j =>
    if j.val ≤ N + 1 then
      ((Real.exp (-kappa * (j.val : ℝ))
        + s * Real.exp (-kappa * (((N + 1 : ℕ) : ℝ) - (j.val : ℝ))) : ℝ) : ℂ)
    else
      ((s * Real.exp (-kappa * ((j.val : ℝ) - ((N + 1 : ℕ) : ℝ)))
        + Real.exp (-kappa * (2 * ((N + 1 : ℕ) : ℝ) - (j.val : ℝ))) : ℝ) : ℂ)

/-- Tasaki eq. (S.34): the equation determining the decay rate `κ` of the ansatz,
`e^κ - e^{-κ} = λ^{-1} (1 + s e^{-κL}) / (1 - s e^{-κL})`.

The source writes the numerator with `±` and the denominator with `∓`; both occurrences carry the
*same* sign `s = ±1` as the ansatz, so `s = 1` is the symmetric and `s = -1` the antisymmetric
root condition. -/
def rootEquation (N : ℕ) (lam kappa s : ℝ) : Prop :=
  Real.exp kappa - Real.exp (-kappa)
    = lam⁻¹ * ((1 + s * Real.exp (-kappa * (N + 1 : ℕ)))
        / (1 - s * Real.exp (-kappa * (N + 1 : ℕ))))

/-- Value of the ansatz on the first family of labels, Tasaki's `j = 0, …, L` branch of
(S.32), written through a pair of natural numbers `n + m = L` so that no `ℕ`-subtraction occurs.
At `n = L`, `m = 0` this is the label `L`, whose value `lowEnergyAnsatz_natCast_add` computes
through the second branch as well. -/
private theorem lowEnergyAnsatz_natCast (N : ℕ) (kappa s : ℝ) {n m : ℕ} (hnm : n + m = N + 1) :
    lowEnergyAnsatz N kappa s (n : ZMod (2 * (N + 1)))
      = ((Real.exp (-kappa * (n : ℝ)) + s * Real.exp (-kappa * (m : ℝ)) : ℝ) : ℂ) := by
  have hval : ((n : ZMod (2 * (N + 1)))).val = n := ZMod.val_cast_of_lt (by omega)
  have hsub : ((N + 1 : ℕ) : ℝ) - (n : ℝ) = (m : ℝ) := by
    have : ((n : ℕ) : ℝ) + (m : ℝ) = ((N + 1 : ℕ) : ℝ) := by exact_mod_cast congrArg Nat.cast hnm
    linarith
  simp only [lowEnergyAnsatz, hval, if_pos (show n ≤ N + 1 by omega), hsub]

/-- Value of the ansatz on the second family of labels, Tasaki's `j = L, …, 2L` branch of
(S.32), again written through `n + m = L` to avoid `ℕ`-subtraction. Because `s² = 1`, the branch
factors as `s` times the first-family profile at the same pair `n, m`, which is what makes the
recursion uniform across the two families.

The extreme labels are covered as well: `n = 0` is the label `L`, where the definition takes the
first branch, and `n = L` is the wrap `2L ≡ 0`, where it takes the first branch at the label `0`.
Both agree with the factored form, so the four labels adjacent to `0` and `L` need no separate
treatment. -/
private theorem lowEnergyAnsatz_natCast_add (N : ℕ) (kappa s : ℝ) (hs : s = 1 ∨ s = -1) {n m : ℕ}
    (hnm : n + m = N + 1) :
    lowEnergyAnsatz N kappa s (((N + 1) + n : ℕ) : ZMod (2 * (N + 1)))
      = (s : ℂ) * ((Real.exp (-kappa * (n : ℝ))
          + s * Real.exp (-kappa * (m : ℝ)) : ℝ) : ℂ) := by
  rcases Nat.lt_or_ge n (N + 1) with hn | hn
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hm : m = N + 1 := by omega
      have hval : (((N + 1 : ℕ)) : ZMod (2 * (N + 1))).val = N + 1 :=
        ZMod.val_cast_of_lt (by omega)
      simp only [Nat.add_zero, hm, lowEnergyAnsatz, hval, if_pos (le_refl (N + 1)), sub_self,
        mul_zero, Real.exp_zero, Nat.cast_zero]
      rw [← Complex.ofReal_mul, Complex.ofReal_inj]
      rcases hs with rfl | rfl <;> ring
    · have hval : ((((N + 1) + n : ℕ)) : ZMod (2 * (N + 1))).val = (N + 1) + n :=
        ZMod.val_cast_of_lt (by omega)
      have hnmR : (n : ℝ) + (m : ℝ) = (N : ℝ) + 1 := by
        have h := congrArg (Nat.cast (R := ℝ)) hnm
        push_cast at h
        linarith
      have h1 : ((((N + 1) + n : ℕ)) : ℝ) - ((N + 1 : ℕ) : ℝ) = (n : ℝ) := by push_cast; ring
      have h2 : 2 * ((N + 1 : ℕ) : ℝ) - ((((N + 1) + n : ℕ)) : ℝ) = (m : ℝ) := by
        push_cast
        linarith
      simp only [lowEnergyAnsatz, hval, if_neg (show ¬ (N + 1) + n ≤ N + 1 by omega), h1, h2]
      rw [← Complex.ofReal_mul, Complex.ofReal_inj]
      rcases hs with rfl | rfl <;> ring
  · have hnn : n = N + 1 := by omega
    have hm : m = 0 := by omega
    have hzero : ((((N + 1) + n : ℕ)) : ZMod (2 * (N + 1))) = 0 := by
      rw [show ((N + 1) + n : ℕ) = 2 * (N + 1) by omega, ZMod.natCast_self]
    rw [hzero, show (0 : ZMod (2 * (N + 1))) = ((0 : ℕ) : ZMod (2 * (N + 1))) by push_cast; ring,
      lowEnergyAnsatz_natCast N kappa s (n := 0) (m := N + 1) (by omega), hnn, hm,
      ← Complex.ofReal_mul, Complex.ofReal_inj]
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero]
    rcases hs with rfl | rfl <;> ring

/-- Tasaki eq. (S.30) at an interior label: away from the two aligned labels `0` and `L`
the ansatz satisfies `φ_{j-1} + φ_{j+1} = (e^κ + e^{-κ}) φ_j` for every `κ`, with no condition on
`κ` at all. Together with the potential `v_j = 1/2` this is exactly the eigenvalue (S.31), so the
root equation is needed only at the two aligned labels. -/
private theorem lowEnergyAnsatz_interior_recurrence (N : ℕ) (kappa s : ℝ) (hs : s = 1 ∨ s = -1)
    (j : ZMod (2 * (N + 1))) (h0 : j.val ≠ 0) (hL : j.val ≠ N + 1) :
    lowEnergyAnsatz N kappa s (j - 1) + lowEnergyAnsatz N kappa s (j + 1)
      = ((Real.exp kappa + Real.exp (-kappa) : ℝ) : ℂ) * lowEnergyAnsatz N kappa s j := by
  have hjlt : j.val < 2 * (N + 1) := ZMod.val_lt j
  have hjval : ((j.val : ℕ) : ZMod (2 * (N + 1))) = j := ZMod.natCast_zmod_val j
  have hexp : ∀ n : ℕ, Real.exp (-kappa * (n : ℝ)) = Real.exp (-kappa) ^ n := by
    intro n
    rw [mul_comm, Real.exp_nat_mul]
  have haE : Real.exp kappa * Real.exp (-kappa) = 1 := by
    rw [← Real.exp_add]
    simp
  rcases Nat.lt_or_ge j.val (N + 1) with hlt | hge
  · obtain ⟨k, hk⟩ : ∃ k, j.val = k + 1 := ⟨j.val - 1, by omega⟩
    obtain ⟨p, hp⟩ : ∃ p, N + 1 = k + 1 + (p + 1) := ⟨N - k - 1, by omega⟩
    have hj : j = ((k + 1 : ℕ) : ZMod (2 * (N + 1))) := by rw [← hjval, hk]
    have hjm : j - 1 = ((k : ℕ) : ZMod (2 * (N + 1))) := by rw [hj]; push_cast; ring
    have hjp : j + 1 = ((k + 2 : ℕ) : ZMod (2 * (N + 1))) := by rw [hj]; push_cast; ring
    rw [hjm, hjp, hj, lowEnergyAnsatz_natCast N kappa s (n := k) (m := p + 2) (by omega),
      lowEnergyAnsatz_natCast N kappa s (n := k + 2) (m := p) (by omega),
      lowEnergyAnsatz_natCast N kappa s (n := k + 1) (m := p + 1) (by omega),
      ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_inj]
    simp only [hexp]
    linear_combination (-(Real.exp (-kappa) ^ k) - s * Real.exp (-kappa) ^ p) * haE
  · obtain ⟨k, hk⟩ : ∃ k, j.val = (N + 1) + (k + 1) := ⟨j.val - (N + 1) - 1, by omega⟩
    obtain ⟨p, hp⟩ : ∃ p, N + 1 = k + 1 + (p + 1) := ⟨N - k - 1, by omega⟩
    have hj : j = (((N + 1) + (k + 1) : ℕ) : ZMod (2 * (N + 1))) := by rw [← hjval, hk]
    have hjm : j - 1 = (((N + 1) + k : ℕ) : ZMod (2 * (N + 1))) := by rw [hj]; push_cast; ring
    have hjp : j + 1 = (((N + 1) + (k + 2) : ℕ) : ZMod (2 * (N + 1))) := by
      rw [hj]; push_cast; ring
    rw [hjm, hjp, hj, lowEnergyAnsatz_natCast_add N kappa s hs (n := k) (m := p + 2) (by omega),
      lowEnergyAnsatz_natCast_add N kappa s hs (n := k + 2) (m := p) (by omega),
      lowEnergyAnsatz_natCast_add N kappa s hs (n := k + 1) (m := p + 1) (by omega)]
    simp only [hexp, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_inj]
    linear_combination (-(s * Real.exp (-kappa) ^ k) - s * s * Real.exp (-kappa) ^ p) * haE

/-- Tasaki eq. (S.34) is equivalent to eq. (S.33), the eigenvalue equation (S.30) at the
aligned label `j = 0` (equivalently, after multiplying by `s`, at `j = L`):
`ε (1 + s e^{-κL}) = -λ (e^{-κ} + s e^{-κ(L-1)})`.

Clearing the denominator of (S.34) is legitimate because `0 < κ` forces `e^{-κL} < 1`, so
`1 - s e^{-κL} > 0` for either sign, and `0 < λ`. -/
private theorem rootEquation_iff_boundary (N : ℕ) (lam kappa s : ℝ) (hlam : 0 < lam)
    (hk : 0 < kappa) (hs : s = 1 ∨ s = -1) :
    rootEquation N lam kappa s ↔
      tightBindingEnergy lam kappa * (1 + s * Real.exp (-kappa) ^ (N + 1))
        = -lam * (Real.exp (-kappa) + s * Real.exp (-kappa) ^ N) := by
  have hw : Real.exp (-kappa * ((N + 1 : ℕ) : ℝ)) = Real.exp (-kappa) ^ (N + 1) := by
    rw [mul_comm, Real.exp_nat_mul]
  have haE : Real.exp kappa * Real.exp (-kappa) = 1 := by
    rw [← Real.exp_add]
    simp
  have hLpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hwlt : Real.exp (-kappa) ^ (N + 1) < 1 := by
    rw [← hw]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hwpos : (0 : ℝ) < Real.exp (-kappa) ^ (N + 1) := pow_pos (Real.exp_pos _) _
  have hden : 1 - s * Real.exp (-kappa) ^ (N + 1) ≠ 0 := by
    rcases hs with rfl | rfl <;> intro hcon <;> linarith
  rw [rootEquation, hw, tightBindingEnergy]
  constructor
  · intro h
    have hcl : lam * (Real.exp kappa - Real.exp (-kappa))
        * (1 - s * Real.exp (-kappa) ^ (N + 1)) = 1 + s * Real.exp (-kappa) ^ (N + 1) := by
      rw [h]
      field_simp
    linear_combination (-1 / 2 : ℝ) * hcl - (lam * s * Real.exp (-kappa) ^ N) * haE
  · intro h
    have hcl : lam * (Real.exp kappa - Real.exp (-kappa))
        * (1 - s * Real.exp (-kappa) ^ (N + 1)) = 1 + s * Real.exp (-kappa) ^ (N + 1) := by
      linear_combination (-2 : ℝ) * h - (2 * lam * s * Real.exp (-kappa) ^ N) * haE
    field_simp
    linear_combination hcl

/-- The ansatz is not the zero vector: its value at the label `0` is
`φ_0 = 1 + s e^{-κL}`, which is positive for `0 < κ` and either sign `s = ±1`. -/
theorem lowEnergyAnsatz_ne_zero (N : ℕ) (kappa s : ℝ) (hk : 0 < kappa) (hs : s = 1 ∨ s = -1) :
    lowEnergyAnsatz N kappa s ≠ 0 := by
  have hw : Real.exp (-kappa * ((N + 1 : ℕ) : ℝ)) = Real.exp (-kappa) ^ (N + 1) := by
    rw [mul_comm, Real.exp_nat_mul]
  have hLpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hwlt : Real.exp (-kappa) ^ (N + 1) < 1 := by
    rw [← hw]
    exact Real.exp_lt_one_iff.mpr (by nlinarith)
  have hwpos : (0 : ℝ) < Real.exp (-kappa) ^ (N + 1) := pow_pos (Real.exp_pos _) _
  have hval : lowEnergyAnsatz N kappa s 0
      = ((1 + s * Real.exp (-kappa) ^ (N + 1) : ℝ) : ℂ) := by
    rw [show (0 : ZMod (2 * (N + 1))) = ((0 : ℕ) : ZMod (2 * (N + 1))) by push_cast; ring,
      lowEnergyAnsatz_natCast N kappa s (n := 0) (m := N + 1) (by omega), Complex.ofReal_inj, hw]
    norm_num
  intro hzero
  have h0 : lowEnergyAnsatz N kappa s 0 = 0 := by rw [hzero]; rfl
  rw [hval, Complex.ofReal_eq_zero] at h0
  rcases hs with rfl | rfl <;> linarith

/-- Tasaki eqs. (S.28)-(S.34): if the decay rate `κ` is positive and satisfies the root
equation (S.34) with a sign `s = ±1`, then the ansatz (S.32) is a nonzero eigenvector of the
compressed matrix, with eigenvalue `E_GS^(0) + ε` where `ε` is (S.31).

At the `2L - 2` labels carrying a domain wall the eigenvector equation holds for every `κ` (the
recursion of the ansatz cancels the potential `1/2` against (S.31)); the root equation is exactly
the remaining condition at the two aligned labels `0` and `L`, where the potential vanishes and
where the two branches of the ansatz meet.

The eigenvalue is `E_GS^(0) + tightBindingEnergy λ κ` with `E_GS^(0) = -N/4`, an eigenvalue of the
compression `lowEnergyMatrix`; that
the compression restricts the Hamiltonian to an invariant subspace is not established here, so no
claim is made about the spectrum of the Hamiltonian itself. -/
theorem lowEnergyAnsatz_isEigenvector (N : ℕ) (lam kappa s : ℝ) (hN : 1 ≤ N) (hlam : 0 < lam)
    (hk : 0 < kappa) (hs : s = 1 ∨ s = -1) (hroot : rootEquation N lam kappa s) :
    lowEnergyAnsatz N kappa s ≠ 0
      ∧ lowEnergyMatrix N lam *ᵥ lowEnergyAnsatz N kappa s
          = ((-(N : ℝ) / 4 + tightBindingEnergy lam kappa : ℝ) : ℂ)
            • lowEnergyAnsatz N kappa s := by
  refine ⟨lowEnergyAnsatz_ne_zero N kappa s hk hs, ?_⟩
  have h33 := (rootEquation_iff_boundary N lam kappa s hlam hk hs).mp hroot
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hexp : ∀ n : ℕ, Real.exp (-kappa * (n : ℝ)) = Real.exp (-kappa) ^ n := by
    intro n
    rw [mul_comm, Real.exp_nat_mul]
  have h33C := congrArg (fun t : ℝ => (t : ℂ)) h33
  have hs2C := congrArg (fun t : ℝ => (t : ℂ)) hs2
  push_cast at h33C hs2C
  rw [lowEnergyMatrix_mulVec_eq_iff N lam hN (tightBindingEnergy lam kappa)
    (lowEnergyAnsatz N kappa s)]
  intro j
  have hjlt : j.val < 2 * (N + 1) := ZMod.val_lt j
  have hjval : ((j.val : ℕ) : ZMod (2 * (N + 1))) = j := ZMod.natCast_zmod_val j
  by_cases h0 : j.val = 0
  · have hj : j = ((0 : ℕ) : ZMod (2 * (N + 1))) := by rw [← hjval, h0]
    have hpot : ringPotential N j = 0 := by
      rw [ringPotential, if_pos (Or.inl (by rw [hj]; push_cast; ring))]
    have hm1 : j - 1 = (((N + 1) + N : ℕ) : ZMod (2 * (N + 1))) := by
      have hc : ((((N + 1) + N : ℕ)) : ZMod (2 * (N + 1))) + 1
          = ((2 * (N + 1) : ℕ) : ZMod (2 * (N + 1))) := by push_cast; ring
      rw [ZMod.natCast_self] at hc
      rw [hj]
      push_cast at hc ⊢
      linear_combination -hc
    have hp1 : j + 1 = ((1 : ℕ) : ZMod (2 * (N + 1))) := by rw [hj]; push_cast; ring
    rw [hpot, hm1, hp1, hj,
      lowEnergyAnsatz_natCast_add N kappa s hs (n := N) (m := 1) (by omega),
      lowEnergyAnsatz_natCast N kappa s (n := 1) (m := N) (by omega),
      lowEnergyAnsatz_natCast N kappa s (n := 0) (m := N + 1) (by omega)]
    simp only [hexp]
    push_cast
    linear_combination h33C
      + ((lam : ℂ) / 2 * Complex.exp (-(kappa : ℂ))) * hs2C
  · by_cases hL : j.val = N + 1
    · have hj : j = (((N + 1 : ℕ)) : ZMod (2 * (N + 1))) := by rw [← hjval, hL]
      have hpot : ringPotential N j = 0 := by
        rw [ringPotential, if_pos (Or.inr hj)]
      have hm1 : j - 1 = ((N : ℕ) : ZMod (2 * (N + 1))) := by rw [hj]; push_cast; ring
      have hp1 : j + 1 = (((N + 1) + 1 : ℕ) : ZMod (2 * (N + 1))) := by rw [hj]; push_cast; ring
      rw [hpot, hm1, hp1, hj,
        lowEnergyAnsatz_natCast N kappa s (n := N) (m := 1) (by omega),
        lowEnergyAnsatz_natCast_add N kappa s hs (n := 1) (m := N) (by omega),
        lowEnergyAnsatz_natCast N kappa s (n := N + 1) (m := 0) (by omega)]
      simp only [hexp]
      push_cast
      linear_combination (s : ℂ) * h33C
        - (((tightBindingEnergy lam kappa : ℝ) : ℂ) * Complex.exp (-(kappa : ℂ)) ^ (N + 1)
          + (lam : ℂ) / 2 * Complex.exp (-(kappa : ℂ)) ^ N) * hs2C
    · have hpot : ringPotential N j = 1 / 2 := by
        rw [ringPotential, if_neg]
        rintro (h | h)
        · exact h0 (by rw [h, ZMod.val_zero])
        · exact hL (by rw [h, ZMod.val_cast_of_lt (by omega)])
      rw [hpot, lowEnergyAnsatz_interior_recurrence N kappa s hs j h0 hL, tightBindingEnergy]
      push_cast
      ring

end LatticeSystem.Quantum
