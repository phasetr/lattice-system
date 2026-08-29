import LatticeSystem.Quantum.IsingLowEnergyProblem33aSplitting

/-!
# The low-energy spectrum of Tasaki Problem 3.3.a

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a (statement p. 59,
solution pp. 498-501, eqs. (S.24)-(S.41)) asks to carry out the degenerate perturbation analysis
of the open Ising chain in its `2L`-fold low-energy sector and to confirm the conclusions of the
text for `L ≫ 1`. `tasaki_problem_3_3_a_low_energy_spectrum` is the single statement that answers
that request, assembling the four modules it depends on; its nine conjuncts and their sources are
listed in its own doc comment.

## What the formalisation asserts

The compression of the Hamiltonian to the span of the `2L` low-energy configurations is a
`2L × 2L` matrix over the label ring `ZMod (2 * (N + 1))`, and that compression equals a constant
diagonal plus a tight-binding ring, eqs. (S.24)-(S.27). Its eigenvalue equation is equivalent to
the recursion (S.30). Every positive root of the quantisation condition (S.34) in either parity
sector yields a nonzero eigenvector of the compression, eqs. (S.31)-(S.33), with eigenvalue
`-N/4 + tightBindingEnergy λ κ`; the symmetric sector always gives the strictly smaller
`tightBindingEnergy`, the ordering asserted below (S.40). The `L ↑ ∞` rate `κ∞` of (S.35) has the
closed-form energy (S.39), a positive symmetric root exists at every ring size, a positive
antisymmetric root exists at all sufficiently large ring sizes, and the ratio of the splitting
`ε_- - ε_+` to the middle expression `2 tanh κ∞ e^{-κ∞ L}` of (S.41) tends to `1` as the ring
grows with `λ` fixed. The final `≃ 2 λ^L` of (S.41) is rendered by its two exact `λ ↓ 0`
ingredients, `e^{-κ∞}/λ → 1` and `tanh κ∞ → 1`.

## What the formalisation does not assert

`tightBindingEnergy` values are eigenvalues of the compressed matrix, which is not the restriction
of the Hamiltonian to an invariant subspace: the Hamiltonian does not preserve the span of the
`2L` configurations. They are therefore never identified with the ground-state energy or the
first-excited energy of the Hamiltonian, and no claim is made that they are the least two
eigenvalues even of the compression. Tasaki notes on p. 59 that the analysis of this problem is
not mathematically rigorous.

The `≃` steps of the source are not asserted. The Taylor expansion (S.36)-(S.38) is replaced by
exact identities, so no lowest-order approximation appears; the `≃` forms of (S.40) and (S.41),
and the last step `≃ 2 λ^L`, are not stated, and the two `λ ↓ 0` limits standing in for that last
step are limits at no fixed ring size and are not combined with the `L ↑ ∞` limit of the
splitting conjunct. Uniqueness of the root in either sector is neither proved nor used, which is
why the splitting conjunct quantifies over arbitrary families of positive roots. The `∀ᶠ`
guarding the antisymmetric sector is what the proof establishes and not a weakening for
convenience: the defect of the cleared root equation at `κ ↓ 0` turns negative, which is what the
intermediate value theorem consumes, only once `L` exceeds a multiple of `λ`.

The ring `ZMod (2 * (N + 1))` indexes the `2L` low-energy basis labels, not lattice sites; the
chain itself is open, and no periodic chain occurs anywhere in this development.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Tasaki Problem 3.3.a** (statement p. 59, solution pp. 498-501): the low-energy analysis of
the open quantum Ising chain `quantumIsingHamiltonian N (1/4) (lam/2)` at `0 < lam`, in nine
conjuncts.

Under `1 ≤ N`, that is `L = N + 1 ≥ 2`:

1. the `2L` low-energy configurations `lowEnergyConfig N` are pairwise distinct, so the low-energy
   sector has the dimension `2L` named in the problem;
2. eqs. (S.24)-(S.27), p. 499: the compression `lowEnergyMatrix N lam` equals
   `(-N/4) • 1 + tightBindingRing N lam`;
3. eqs. (S.28)-(S.30), p. 499: the eigenvalue equation of the compression at `-N/4 + ε` is
   equivalent to the tight-binding recursion (S.30) at every label;
4. eqs. (S.31)-(S.34), pp. 499-500: for either parity `s = ±1`, a positive root of the
   quantisation condition `rootEquation N lam kappa s` makes `lowEnergyAnsatz N kappa s` a nonzero
   eigenvector of the compression with eigenvalue `-N/4 + tightBindingEnergy lam kappa`;
5. below eq. (S.40), p. 501: the symmetric sector lies strictly lower, `ε_+ < ε_-`, for any
   positive roots of the two sectors.

Without any restriction on the ring size:

6. eq. (S.39), p. 501: `tightBindingEnergy lam (kappaInf lam) = (1 - √(1 + 4 lam²))/2`, the energy
   at the `L ↑ ∞` rate `κ∞` of (S.35);
7. a positive symmetric root exists at every ring size, and a positive antisymmetric root exists
   at all sufficiently large ring sizes;
8. eq. (S.41), p. 501: for arbitrary families `kp`, `km` of eventually-positive roots of the two
   sectors, the ratio of `ε_- - ε_+` to `2 tanh κ∞ e^{-κ∞ L}` tends to `1` as `L ↑ ∞` at fixed
   `lam`, the order of limits of the source's footnote 1 on p. 500;
9. the two `λ ↓ 0` limits `e^{-κ∞(λ)}/λ → 1` and `tanh κ∞(λ) → 1`, the exact content of the
   two replacements made in the source's closing step `≃ 2 λ^L` of (S.41).

`tightBindingEnergy` is an eigenvalue of the compressed matrix `lowEnergyMatrix`, whose span the
Hamiltonian does not preserve; it is not identified here with a ground-state or first-excited
energy of the Hamiltonian. The `≃` relations (S.36)-(S.38), (S.40), (S.41) are not asserted, and
root uniqueness is neither proved nor used. -/
theorem tasaki_problem_3_3_a_low_energy_spectrum (lam : ℝ) (hlam : 0 < lam) :
    (∀ N : ℕ, 1 ≤ N →
        Function.Injective (lowEnergyConfig N)
        ∧ lowEnergyMatrix N lam
            = (-(N : ℂ) / 4) • (1 : Matrix (ZMod (2 * (N + 1))) (ZMod (2 * (N + 1))) ℂ)
              + tightBindingRing N lam
        ∧ (∀ (eps : ℝ) (phi : ZMod (2 * (N + 1)) → ℂ),
            lowEnergyMatrix N lam *ᵥ phi = ((-(N : ℝ) / 4 + eps : ℝ) : ℂ) • phi ↔
              ∀ j : ZMod (2 * (N + 1)),
                (eps : ℂ) * phi j
                  = -((lam : ℂ) / 2) * (phi (j - 1) + phi (j + 1)) + ringPotential N j * phi j)
        ∧ (∀ kappa s : ℝ, 0 < kappa → (s = 1 ∨ s = -1) → rootEquation N lam kappa s →
            lowEnergyAnsatz N kappa s ≠ 0
              ∧ lowEnergyMatrix N lam *ᵥ lowEnergyAnsatz N kappa s
                  = ((-(N : ℝ) / 4 + tightBindingEnergy lam kappa : ℝ) : ℂ)
                    • lowEnergyAnsatz N kappa s)
        ∧ (∀ kp km : ℝ, 0 < kp → 0 < km →
            rootEquation N lam kp 1 → rootEquation N lam km (-1) →
            tightBindingEnergy lam kp < tightBindingEnergy lam km))
    ∧ tightBindingEnergy lam (kappaInf lam) = (1 - Real.sqrt (1 + 4 * lam ^ 2)) / 2
    ∧ (∀ N : ℕ, ∃ kappa, 0 < kappa ∧ rootEquation N lam kappa 1)
    ∧ (∀ᶠ N : ℕ in Filter.atTop, ∃ kappa, 0 < kappa ∧ rootEquation N lam kappa (-1))
    ∧ (∀ kp km : ℕ → ℝ,
        (∀ᶠ N in Filter.atTop, 0 < kp N ∧ rootEquation N lam (kp N) 1) →
        (∀ᶠ N in Filter.atTop, 0 < km N ∧ rootEquation N lam (km N) (-1)) →
        Filter.Tendsto
          (fun N : ℕ => (tightBindingEnergy lam (km N) - tightBindingEnergy lam (kp N))
            / (2 * Real.tanh (kappaInf lam) * Real.exp (-(kappaInf lam)) ^ (N + 1)))
          Filter.atTop (nhds 1))
    ∧ Filter.Tendsto (fun l : ℝ => Real.exp (-(kappaInf l)) / l)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)
    ∧ Filter.Tendsto (fun l : ℝ => Real.tanh (kappaInf l))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
  ⟨fun N hN =>
      ⟨lowEnergyConfig_injective N,
        lowEnergyMatrix_eq_add_tightBindingRing N lam hN,
        fun eps phi => lowEnergyMatrix_mulVec_eq_iff N lam hN eps phi,
        fun kappa s hk hs hroot =>
          lowEnergyAnsatz_isEigenvector N lam kappa s hN hlam hk hs hroot,
        fun kp km hkp hkm hp hm => tightBindingEnergy_lt_of_roots N lam kp km hkp hkm hp hm⟩,
    tightBindingEnergy_kappaInf_eq hlam,
    fun N => exists_root_symmetric N lam hlam,
    eventually_exists_root_antisymmetric lam hlam,
    fun kp km hkp hkm => tendsto_splitting_ratio lam hlam kp km hkp hkm,
    tendsto_exp_neg_kappaInf_div_atZero,
    tendsto_tanh_kappaInf_atZero⟩

end LatticeSystem.Quantum
