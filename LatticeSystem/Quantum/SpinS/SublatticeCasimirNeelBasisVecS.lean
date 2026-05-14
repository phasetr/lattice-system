import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel
import LatticeSystem.Quantum.SpinS.MultiSiteMatrixElement

/-!
# Spin-`S` `(Ŝ_tot)²` Casimir on arbitrary `basisVecS σ`
(γ-4 step 218 and downstream)

This file is the build-speed companion to
`SublatticeCasimirNeel.lean`. It hosts the late section
"Spin-`S` `(Ŝ_tot)²` Casimir on arbitrary `basisVecS σ`"
(originally lines 2429..2811 of the parent file) — including
expectation formulas at the Néel configuration and complement
mirrors used by `NeelBipartiteWeight.lean` and
`NeelToyHamiltonianViaCasimir.lean`.

Splitting this trailing section out drops the parent file from
~2812 lines to ~2428 lines. The 16 theorems plus the private
helper `spinSDot_apply_diag_unified` are physically relocated
here, so consumers that previously did
`import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel` and
referred to these names must now import this companion module
instead. All in-repo callers
(`NeelBipartiteWeight.lean`, `NeelToyHamiltonianViaCasimir.lean`)
were updated in the same PR.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5 Theorem 2.3 (Marshall–Lieb–Mattis).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Spin-`S` `(Ŝ_tot)²` Casimir on arbitrary `basisVecS σ` (γ-4 step 218) -/

/-- Unified diagonal of `spinSDot x y` at `(σ, σ)` (spin-`S`):
`(spinSDot x y) σ σ = m_x m_y + (N(N+2)/4 - m_x²)·[x=y]` where
`m_x := N/2 - σ x.val`. Spin-`S` analogue of γ-4 step 216
helper for spin-`1/2`. -/
private theorem spinSDot_apply_diag_unified
    (x y : Λ) (N : ℕ) (σ : Λ → Fin (N + 1)) :
    (spinSDot x y N : ManyBodyOpS Λ N) σ σ =
      ((N : ℂ) / 2 - ((σ x).val : ℂ)) *
          ((N : ℂ) / 2 - ((σ y).val : ℂ)) +
        (if x = y then
          ((N : ℂ) * ((N : ℂ) + 2) / 4 -
            ((N : ℂ) / 2 - ((σ x).val : ℂ)) ^ 2) else 0) := by
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl, spinSDot_self]
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    ring
  · rw [if_neg hxy, add_zero, spinSDot_apply_diag_of_ne hxy]

/-- **Spin-`S` `(Ŝ_tot)²` Casimir expectation on arbitrary `basisVecS σ`**:
`<basisVecS σ | (Ŝ_tot)² | basisVecS σ> =
  |V|·N(N+2)/4 + magEigenvalueS(σ)² − Σ_x (N/2 − σx.val)²`
for any `σ : Λ → Fin (N + 1)`. Spin-`S` analogue of γ-4 step 216
(spin-`1/2` case has constant `(N/2 - σx.val)² = 1/4`, so
`Σ_x m_x² = |Λ|/4` and `|Λ|·N(N+2)/4 = 3|Λ|/4`, giving the formula
`(M(σ)/2)² + |Λ|/2`).

The per-site sum-of-squares term `Σ_x (N/2 - σx.val)²` is the
configuration-dependent "z-axis squared" contribution that doesn't
collapse for spin-`S` (unlike spin-`1/2`).

Proof: reduce to diagonal matrix element via
`basisVecS_expectation_eq_diagonal`, expand
`(Ŝ_tot)² = Σ_{x,y} spinSDot x y`, apply unified per-pair diagonal,
then split via separability of the double sum (γ-4 step 218). -/
theorem basisVecS_totalSpinSSquared_expectation_general
    (N : ℕ) (σ : Λ → Fin (N + 1)) :
    dotProduct (star (basisVecS σ : (Λ → Fin (N + 1)) → ℂ))
        ((totalSpinSSquared Λ N).mulVec (basisVecS σ)) =
      (Fintype.card Λ : ℂ) * ((N : ℂ) * ((N : ℂ) + 2) / 4) +
        (magEigenvalueS σ) ^ 2 -
        ∑ x : Λ, ((N : ℂ) / 2 - ((σ x).val : ℂ)) ^ 2 := by
  rw [basisVecS_expectation_eq_diagonal, totalSpinSSquared_eq_sum_spinSDot]
  rw [Matrix.sum_apply]
  simp_rw [Matrix.sum_apply, spinSDot_apply_diag_unified]
  rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_add_distrib)]
  rw [Finset.sum_add_distrib]
  -- Magnetization-squared piece: Σ_x Σ_y m_x m_y = (Σ m_x)² = magEigenvalueS².
  have hMag : (∑ x : Λ, ((N : ℂ) / 2 - ((σ x).val : ℂ))) =
      magEigenvalueS σ := by
    rw [magEigenvalueS_def]
    unfold magSumS
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    push_cast; ring
  rw [show (∑ x : Λ, ∑ y : Λ,
        ((N : ℂ) / 2 - ((σ x).val : ℂ)) *
          ((N : ℂ) / 2 - ((σ y).val : ℂ))) =
      (∑ x : Λ, ((N : ℂ) / 2 - ((σ x).val : ℂ))) *
        (∑ y : Λ, ((N : ℂ) / 2 - ((σ y).val : ℂ))) from by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]]
  rw [hMag]
  -- Diagonal correction piece: Σ_x Σ_y [if x = y then C - m_x² else 0]
  --                           = Σ_x (C - m_x²).
  rw [show (∑ x : Λ, ∑ y : Λ, (if x = y then
        ((N : ℂ) * ((N : ℂ) + 2) / 4 -
          ((N : ℂ) / 2 - ((σ x).val : ℂ)) ^ 2) else 0)) =
      ∑ x : Λ, ((N : ℂ) * ((N : ℂ) + 2) / 4 -
        ((N : ℂ) / 2 - ((σ x).val : ℂ)) ^ 2) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_ite_eq Finset.univ x (fun _ =>
      (N : ℂ) * ((N : ℂ) + 2) / 4 -
        ((N : ℂ) / 2 - ((σ x).val : ℂ)) ^ 2)]
    simp]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- **Spin-`S` transverse Casimir `(Ŝ_tot^(1))² + (Ŝ_tot^(2))²` on
arbitrary `basisVecS σ`** equals `|V|·N(N+2)/4 − Σ_x (N/2 − σx.val)²`.

Direct corollary of γ-4 step 218 (full Casimir) and γ-4 step 205
(z-axis squared = `magEigenvalueS(σ)²`): the `magEigenvalueS²` pieces
cancel.

For Néel state on a balanced bipartite graph (`|A| = |¬A|`,
`σx ∈ {0, N}`), this reduces to `|V|·N/2` (matches existing
`neelStateOfS_totalSpinSOp12_sq_expectation` from γ-4 step 156).

For spin-`1/2` (`N = 1`, `(N/2 - σx.val)² = 1/4` always), reduces to
`|Λ|·3/4 - |Λ|/4 = |Λ|/2` (γ-4 step 219, `_general` variant)
(γ-4 step 220). -/
theorem basisVecS_totalSpinSOp12_sq_expectation_general
    (N : ℕ) (σ : Λ → Fin (N + 1)) :
    dotProduct (star (basisVecS σ : (Λ → Fin (N + 1)) → ℂ))
        ((totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
            totalSpinSOp2 Λ N * totalSpinSOp2 Λ N).mulVec
          (basisVecS σ)) =
      (Fintype.card Λ : ℂ) * ((N : ℂ) * ((N : ℂ) + 2) / 4) -
        ∑ x : Λ, ((N : ℂ) / 2 - ((σ x).val : ℂ)) ^ 2 := by
  have hDecomp : totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
        totalSpinSOp2 Λ N * totalSpinSOp2 Λ N =
      totalSpinSSquared Λ N -
        totalSpinSOp3 Λ N * totalSpinSOp3 Λ N := by
    unfold totalSpinSSquared; abel
  rw [hDecomp, Matrix.sub_mulVec, dotProduct_sub,
    basisVecS_totalSpinSSquared_expectation_general,
    basisVecS_expectation_totalSpinSOp3_sq]
  ring

omit [DecidableEq Λ] in
/-- The per-site `(N/2 − σx.val)²` sum on the Néel configuration is
constant `|V|·(N/2)²`. Direct evaluation: `neelConfigOfS A N x` is
either `0` (giving `(N/2)²`) or `Fin.last N` (giving `(N/2 − N)² =
(N/2)²`); both contribute equally (γ-4 step 221). -/
theorem neelConfigOfS_z_eigenvalue_sq_sum (A : Λ → Bool) (N : ℕ) :
    (∑ x : Λ, ((N : ℂ) / 2 - ((neelConfigOfS A N x).val : ℂ)) ^ 2) =
      (Fintype.card Λ : ℂ) * ((N : ℂ) / 2) ^ 2 := by
  have hEach : ∀ x : Λ,
      ((N : ℂ) / 2 - ((neelConfigOfS A N x).val : ℂ)) ^ 2 =
        ((N : ℂ) / 2) ^ 2 := by
    intro x
    unfold neelConfigOfS
    by_cases hAx : A x
    · rw [if_pos hAx]
      simp
    · rw [if_neg hAx]
      have : ((Fin.last N).val : ℂ) = (N : ℂ) := by simp [Fin.last]
      rw [this]; ring
  simp_rw [hEach]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq Λ] in
/-- `magEigenvalueS (neelConfigOfS A N) = (|A| − |¬A|)·N/2`. The
Néel configuration's `Ŝ_tot^{(3)}` eigenvalue is the sublattice
imbalance times `N/2`. Direct from `magSumS_neelConfigOfS` and the
filter-card decomposition `|V| = |A| + |¬A|` (γ-4 step 224). -/
theorem magEigenvalueS_neelConfigOfS (A : Λ → Bool) (N : ℕ) :
    magEigenvalueS (neelConfigOfS A N) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
        ((N : ℂ) / 2) := by
  classical
  rw [magEigenvalueS_def, magSumS_neelConfigOfS]
  have hcard : ((Fintype.card Λ : ℂ)) =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) := by
    have h1 : (Finset.univ.filter (fun x : Λ => A x = true)).card +
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
        Finset.univ.card (α := Λ) := by
      have hfilter_eq : Finset.univ.filter (fun x : Λ => (! A x) = true) =
          Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
        congr 1
        funext x
        by_cases hA : A x = true
        · simp [hA]
        · simp [hA]
      rw [hfilter_eq]
      exact Finset.card_filter_add_card_filter_not (fun x : Λ => A x = true)
    have h2 : (Finset.univ.card (α := Λ) : ℂ) = (Fintype.card Λ : ℂ) := by
      rw [Finset.card_univ]
    rw [← h2]
    exact_mod_cast h1.symm
  rw [hcard]
  push_cast
  ring

/-- **Spin-`S` Néel Casimir** re-derived via the general
`basisVecS σ` Casimir formula (γ-4 step 218): combining γ-4 step 218
+ γ-4 step 221 + γ-4 step 224 yields
`<Φ_Néel | (Ŝ_tot)² | Φ_Néel> = ((|A|−|¬A|)·N/2)² + |V|·N/2`,
matching the existing closed-form
`neelStateOfS_totalSpinSSquared_expectation_card_Lambda` (γ-4 step 127).

Useful as a unification check: the general formula's `magEigenvalueS²
+ |V|·N(N+2)/4 − Σ_x m_x²` correctly reduces to the Néel-specific
result when applied to `neelConfigOfS A N` (γ-4 step 225). -/
theorem neelStateOfS_totalSpinSSquared_expectation_via_general
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
          ((N : ℂ) / 2)) ^ 2 +
        (Fintype.card Λ : ℂ) * ((N : ℂ) / 2) := by
  unfold neelStateOfS
  rw [basisVecS_totalSpinSSquared_expectation_general,
    magEigenvalueS_neelConfigOfS,
    neelConfigOfS_z_eigenvalue_sq_sum]
  ring

/-- **Spin-`S` allAligned-up Casimir** re-derived via the general
`basisVecS σ` Casimir formula (γ-4 step 218):
`<Φ_⊤ | (Ŝ_tot)² | Φ_⊤> = m_max·(m_max + 1)` where `m_max = |V|·N/2`.

Composition of γ-4 step 218 + γ-4 step 222 (at `c = 0`) +
`magEigenvalueS_allAlignedConfigS` + `ring`. Recovers
`allAlignedStateS_zero_expectation_totalSpinSSquared` (PR #882) from
the general framework (γ-4 step 226). -/
theorem allAlignedStateS_zero_totalSpinSSquared_via_general
    (N : ℕ) [Nonempty Λ] :
    dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
        ((totalSpinSSquared Λ N).mulVec
          (allAlignedStateS Λ N (0 : Fin (N + 1)))) =
      ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card Λ : ℂ) * (N : ℂ) / 2 + 1) := by
  unfold allAlignedStateS
  rw [basisVecS_totalSpinSSquared_expectation_general,
    magEigenvalueS_allAlignedConfigS,
    allAlignedConfigS_z_eigenvalue_sq_sum]
  rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp]
  ring

/-- **Spin-`S` allAligned-down Casimir** re-derived via the general
formula (γ-4 step 226). Same value as allAligned-up since the lowest
weight has eigenvalue `-|V|·N/2`, whose square equals `(|V|·N/2)²`. -/
theorem allAlignedStateS_last_totalSpinSSquared_via_general
    (N : ℕ) [Nonempty Λ] :
    dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
        ((totalSpinSSquared Λ N).mulVec
          (allAlignedStateS Λ N (Fin.last N))) =
      ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) *
        ((Fintype.card Λ : ℂ) * (N : ℂ) / 2 + 1) := by
  unfold allAlignedStateS
  rw [basisVecS_totalSpinSSquared_expectation_general,
    magEigenvalueS_allAlignedConfigS,
    allAlignedConfigS_z_eigenvalue_sq_sum]
  rw [show ((Fin.last N).val : ℂ) = (N : ℂ) from by simp [Fin.last]]
  ring

omit [DecidableEq Λ] in
/-- `magEigenvalueS (neelConfigOfS (¬A) N) = (|¬A| − |A|)·N/2`. The
sublattice-swap symmetry of the Néel `Ŝ_tot^{(3)}` eigenvalue: flipping
A ↔ ¬A negates the eigenvalue (γ-4 step 229, complement of γ-4 step 224). -/
theorem magEigenvalueS_neelConfigOfS_complement (A : Λ → Bool) (N : ℕ) :
    magEigenvalueS (neelConfigOfS (fun x => ! A x) N) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! ! A x) = true)).card : ℂ)) *
        ((N : ℂ) / 2) := by
  exact magEigenvalueS_neelConfigOfS (fun x => ! A x) N

omit [DecidableEq Λ] in
/-- **Cleaner form** of γ-4 step 229:
`magEigenvalueS (neelConfigOfS (¬A) N) = (|¬A| − |A|)·N/2`
with the `!!A` double-negation simplified to `A` (γ-4 step 230). -/
theorem magEigenvalueS_neelConfigOfS_complement_simplified
    (A : Λ → Bool) (N : ℕ) :
    magEigenvalueS (neelConfigOfS (fun x => ! A x) N) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ)) *
        ((N : ℂ) / 2) := by
  rw [magEigenvalueS_neelConfigOfS_complement]
  congr 2
  have hSet : (Finset.univ.filter (fun x : Λ => (! ! A x) = true)) =
      (Finset.univ.filter (fun x : Λ => A x = true)) := by
    apply Finset.filter_congr
    intros x _
    simp [Bool.not_not]
  rw [hSet]

omit [DecidableEq Λ] in
/-- **Negation relation**: `magEigenvalueS (neelConfigOfS (¬A) N) =
−magEigenvalueS (neelConfigOfS A N)`. Direct from γ-4 step 224 + γ-4 step 230
+ `ring`. The complement Néel sits at the opposite `Ŝ_tot^(3)` eigenvalue
(γ-4 step 231). -/
theorem magEigenvalueS_neelConfigOfS_complement_eq_neg
    (A : Λ → Bool) (N : ℕ) :
    magEigenvalueS (neelConfigOfS (fun x => ! A x) N) =
      -magEigenvalueS (neelConfigOfS A N) := by
  rw [magEigenvalueS_neelConfigOfS_complement_simplified,
    magEigenvalueS_neelConfigOfS]
  ring

/-- **Spin-`S` Casimir is sublattice-swap invariant on Néel states**:
`<Φ_Néel(¬A) | (Ŝ_tot)² | Φ_Néel(¬A)> = <Φ_Néel(A) | (Ŝ_tot)² | Φ_Néel(A)>`.

Direct corollary of γ-4 step 218 (Casimir general formula) +
γ-4 step 221 (`Σ_x m_x² = |V|·(N/2)²` valid for both A and ¬A) +
γ-4 step 231 (`magEigenvalueS (¬A) = −magEigenvalueS A`): the
`magEigenvalueS²` piece is sign-flip invariant, the rest is
A-independent. Spin-`S` mirror of γ-4 step 233 (γ-4 step 234). -/
theorem neelStateOfS_totalSpinSSquared_complement_eq
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
        ((totalSpinSSquared Λ N).mulVec
          (neelStateOfS (fun x : Λ => ! A x) N)) =
      dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N)) := by
  unfold neelStateOfS
  rw [basisVecS_totalSpinSSquared_expectation_general,
    basisVecS_totalSpinSSquared_expectation_general,
    neelConfigOfS_z_eigenvalue_sq_sum,
    neelConfigOfS_z_eigenvalue_sq_sum,
    magEigenvalueS_neelConfigOfS_complement_eq_neg]
  ring

/-- **Spin-`S` `(Ŝ_tot^(3))²` is sublattice-swap invariant on Néel
states**:
`<Φ_Néel(¬A) | (Ŝ_tot^(3))² | Φ_Néel(¬A)> = <Φ_Néel(A) | (Ŝ_tot^(3))² | Φ_Néel(A)>`.

Direct corollary of γ-4 step 205 (`(Ŝ_tot^(3))² | basisVecS σ⟩` =
`(magEigenvalueS σ)² | σ⟩`) + γ-4 step 231
(`magEigenvalueS (¬A) = −magEigenvalueS A`): the squared eigenvalue
is sign-flip invariant (γ-4 step 235). -/
theorem neelStateOfS_totalSpinSOp3_sq_complement_eq
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
        ((totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec
          (neelStateOfS (fun x : Λ => ! A x) N)) =
      dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec
          (neelStateOfS A N)) := by
  unfold neelStateOfS
  rw [basisVecS_expectation_totalSpinSOp3_sq,
    basisVecS_expectation_totalSpinSOp3_sq,
    magEigenvalueS_neelConfigOfS_complement_eq_neg]
  ring

/-- **Spin-`S` transverse Casimir `(Ŝ_tot^(1))²+(Ŝ_tot^(2))²` is
sublattice-swap invariant on Néel states**:
`<Φ_Néel(¬A)|(Ŝ^1)²+(Ŝ^2)²|Φ_Néel(¬A)> = <Φ_Néel(A)|(Ŝ^1)²+(Ŝ^2)²|Φ_Néel(A)>`.

Direct corollary of γ-4 step 220 (`= |V|·N(N+2)/4 − Σ_x m_x²`) +
γ-4 step 221 (`Σ_x m_x² = |V|·(N/2)²` for both A and ¬A): both
sides reduce to the same `|V|·N/2` (γ-4 step 237). -/
theorem neelStateOfS_totalSpinSOp12_sq_complement_eq
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
        ((totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
            totalSpinSOp2 Λ N * totalSpinSOp2 Λ N).mulVec
          (neelStateOfS (fun x : Λ => ! A x) N)) =
      dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp1 Λ N * totalSpinSOp1 Λ N +
            totalSpinSOp2 Λ N * totalSpinSOp2 Λ N).mulVec
          (neelStateOfS A N)) := by
  unfold neelStateOfS
  rw [basisVecS_totalSpinSOp12_sq_expectation_general,
    basisVecS_totalSpinSOp12_sq_expectation_general,
    neelConfigOfS_z_eigenvalue_sq_sum,
    neelConfigOfS_z_eigenvalue_sq_sum]

/-- **Spin-`S` linear `Ŝ_tot^(3)` expectation negation under sublattice swap**:
`<Φ_Néel(¬A) | Ŝ_tot^(3) | Φ_Néel(¬A)> = −<Φ_Néel(A) | Ŝ_tot^(3) | Φ_Néel(A)>`.

Direct from γ-4 step 206 (general expectation = `magEigenvalueS σ`) +
γ-4 step 231 (`magEigenvalueS (¬A) = −magEigenvalueS A`)
(γ-4 step 239). -/
theorem neelStateOfS_totalSpinSOp3_complement_eq_neg
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
        ((totalSpinSOp3 Λ N).mulVec
          (neelStateOfS (fun x : Λ => ! A x) N)) =
      -dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp3 Λ N).mulVec (neelStateOfS A N)) := by
  unfold neelStateOfS
  rw [basisVecS_expectation_totalSpinSOp3,
    basisVecS_expectation_totalSpinSOp3,
    magEigenvalueS_neelConfigOfS_complement_eq_neg]

/-- **Spin-`S` `Ŝ_tot^(1)` zero expectation on Néel**:
`<Φ_Néel | Ŝ_tot^(1) | Φ_Néel> = 0`. Direct corollary of γ-4 step 214
applied to `σ = neelConfigOfS A N` (γ-4 step 241). -/
theorem neelStateOfS_totalSpinSOp1_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp1 Λ N).mulVec (neelStateOfS A N)) = 0 := by
  unfold neelStateOfS
  exact basisVecS_expectation_totalSpinSOp1 _

/-- **Spin-`S` `Ŝ_tot^(2)` zero expectation on Néel**:
`<Φ_Néel | Ŝ_tot^(2) | Φ_Néel> = 0`. Direct corollary of γ-4 step 214
applied to `σ = neelConfigOfS A N` (γ-4 step 241). -/
theorem neelStateOfS_totalSpinSOp2_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp2 Λ N).mulVec (neelStateOfS A N)) = 0 := by
  unfold neelStateOfS
  exact basisVecS_expectation_totalSpinSOp2 _

end LatticeSystem.Quantum
