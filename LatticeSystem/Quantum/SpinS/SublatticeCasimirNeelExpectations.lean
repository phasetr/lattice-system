import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel

/-!
# Sublattice 12sq / cross-pair expectations and Néel norm/span
properties (build-speed companion)

Build-speed companion to `SublatticeCasimirNeel.lean`. Hosts the
mid-late block on sublattice transverse-Casimir `(Ŝ_A^(1))² +
(Ŝ_A^(2))²` action and complement variants, sublattice ladder
cross-product actions, the Néel state's norm self-inner-product,
and the various `magSubspaceS`-nontriviality / `_span_le_*`
results (originally lines 713..1179 of the pre-#36 parent file).

Splitting this self-contained block out drops the parent from
~1179 lines to ~712 lines.

No in-repo downstream consumers of the moved names.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `((Ŝ_A^(1))² + (Ŝ_A^(2))²) · |Φ_Néel⟩ = (|A|·N/2) · |Φ_Néel⟩`.

Direct from `(Ŝ_A)² = (Ŝ_A^(1))² + (Ŝ_A^(2))² + (Ŝ_A^(3))²` and the
known eigenvalues:
- `(Ŝ_A)² · Néel = c_A · Néel` with `c_A = (|A|·N/2)((|A|·N/2)+1)`,
- `(Ŝ_A^(3))² · Néel = (|A|·N/2)² · Néel`,
so `((Ŝ_A^(1))² + (Ŝ_A^(2))²) · Néel = (c_A − (|A|·N/2)²) · Néel = (|A|·N/2) · Néel`. -/
theorem sublatticeSpinSOp12sq_mulVec_neelStateOfS (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N A +
        sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N A).mulVec
        (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) •
        neelStateOfS A N := by
  have hCasimir := sublatticeSpinSquaredS_mulVec_neelStateOfS A N
  rw [sublatticeSpinSquaredS_def] at hCasimir
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at hCasimir
  have hSq3 := sublatticeSpinSOp3_sq_mulVec_neelStateOfS A N
  -- hCasimir: ((Ŝ^(1))² + (Ŝ^(2))²).mulVec + (Ŝ^(3))².mulVec = c_A • Néel
  -- hSq3: (Ŝ^(3))².mulVec = (|A|·N/2)² • Néel
  rw [hSq3] at hCasimir
  set k : ℂ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
      ((N : ℂ) / 2)
  -- Need: ((Ŝ^(1))² + (Ŝ^(2))²) · Néel = k · Néel
  rw [Matrix.add_mulVec]
  -- hCasimir: (Ŝ^(1))² · Néel + (Ŝ^(2))² · Néel + k² · Néel = (k · (k+1)) · Néel
  have h := hCasimir
  have hab : (sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N A).mulVec
        (neelStateOfS A N) +
      (sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N A).mulVec
        (neelStateOfS A N) =
      (k * (k + 1)) • neelStateOfS A N - k ^ 2 • neelStateOfS A N := by
    rw [eq_sub_iff_add_eq]; exact h
  rw [hab, ← sub_smul]
  congr 1
  ring

/-- `Ŝ_A^+ · Ŝ_A^- · |Φ_Néel⟩ = |A|·N · |Φ_Néel⟩`. Via the Cartan identity
`Ŝ_A^+·Ŝ_A^- = (Ŝ_A^(1))² + (Ŝ_A^(2))² + Ŝ_A^(3)` (PR #1146):
`Ŝ_A^+·Ŝ_A^- · Néel = (|A|·N/2) · Néel + (|A|·N/2) · Néel = |A|·N · Néel`. -/
theorem sublatticeSpinSOpPlus_minus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpPlus N A * sublatticeSpinSOpMinus N A).mulVec
        (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          (N : ℂ)) •
        neelStateOfS A N := by
  rw [sublatticeSpinSOpPlus_mul_sublatticeSpinSOpMinus_eq]
  rw [Matrix.add_mulVec]
  rw [sublatticeSpinSOp12sq_mulVec_neelStateOfS]
  rw [sublatticeSpinSOp3_mulVec_neelStateOfS]
  rw [← add_smul]
  congr 1
  ring

/-- `((Ŝ_¬A^(1))² + (Ŝ_¬A^(2))²) · |Φ_Néel⟩ = (|¬A|·N/2) · |Φ_Néel⟩`. Complement
version of `sublatticeSpinSOp12sq_mulVec_neelStateOfS`. -/
theorem sublatticeSpinSOp12sq_complement_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOp1 N (fun x => ! A x) *
        sublatticeSpinSOp1 N (fun x => ! A x) +
      sublatticeSpinSOp2 N (fun x => ! A x) *
        sublatticeSpinSOp2 N (fun x => ! A x)).mulVec
        (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) •
        neelStateOfS A N := by
  have hCasimir := sublatticeSpinSquaredS_complement_mulVec_neelStateOfS A N
  rw [sublatticeSpinSquaredS_def] at hCasimir
  rw [Matrix.add_mulVec, Matrix.add_mulVec] at hCasimir
  have hSq3 := sublatticeSpinSOp3_complement_sq_mulVec_neelStateOfS A N
  rw [hSq3] at hCasimir
  set k : ℂ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
      ((N : ℂ) / 2)
  rw [Matrix.add_mulVec]
  have h := hCasimir
  have hab : (sublatticeSpinSOp1 N (fun x => ! A x) *
        sublatticeSpinSOp1 N (fun x => ! A x)).mulVec
        (neelStateOfS A N) +
      (sublatticeSpinSOp2 N (fun x => ! A x) *
        sublatticeSpinSOp2 N (fun x => ! A x)).mulVec
        (neelStateOfS A N) =
      (k * (k + 1)) • neelStateOfS A N - k ^ 2 • neelStateOfS A N := by
    rw [eq_sub_iff_add_eq]; exact h
  rw [hab, ← sub_smul]
  congr 1
  ring

/-- `Ŝ_¬A^- · Ŝ_¬A^+ · |Φ_Néel⟩ = |¬A|·N · |Φ_Néel⟩`. Via dual Cartan
identity (PR #1150) applied to `¬A`:
`Ŝ_¬A^-·Ŝ_¬A^+ · Néel = ((Ŝ_¬A^(1))² + (Ŝ_¬A^(2))²) · Néel - Ŝ_¬A^(3) · Néel
                       = (|¬A|·N/2) · Néel - (-(|¬A|·N/2)) · Néel
                       = |¬A|·N · Néel`. -/
theorem sublatticeSpinSOpComplementMinus_complement_plus_mulVec_neelStateOfS
    (A : Λ → Bool) (N : ℕ) :
    (sublatticeSpinSOpMinus N (fun x => ! A x) *
        sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
        (neelStateOfS A N) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          (N : ℂ)) •
        neelStateOfS A N := by
  rw [sublatticeSpinSOpMinus_mul_sublatticeSpinSOpPlus_eq]
  rw [Matrix.sub_mulVec]
  rw [sublatticeSpinSOp12sq_complement_mulVec_neelStateOfS]
  rw [sublatticeSpinSOp3_complement_mulVec_neelStateOfS]
  rw [← sub_smul]
  congr 1
  ring

/-- The spin-`S` Néel state is non-zero. Direct from `basisVecS_self = 1`. -/
theorem neelStateOfS_ne_zero (A : Λ → Bool) (N : ℕ) :
    neelStateOfS A N ≠ 0 := by
  intro h
  have h1 : neelStateOfS A N (neelConfigOfS A N) = 1 := by
    unfold neelStateOfS
    exact basisVecS_self _
  have h0 : neelStateOfS A N (neelConfigOfS A N) = 0 := by
    rw [h]; rfl
  rw [h1] at h0
  exact one_ne_zero h0

/-- The spin-`S` magnetization-`(|A|-|¬A|)·N/2` subspace is non-trivial:
it contains the non-zero Néel state. Spin-`S` analog of
`magnetizationSubspace_nontrivial_via_neel` (γ-4 step 177). -/
theorem magSubspaceS_nontrivial_via_neel (A : Λ → Bool) (N : ℕ) :
    magSubspaceS Λ N
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) ≠ ⊥ := by
  intro hbot
  have hmem := neelStateOfS_mem_magSubspaceS A N
  rw [hbot, Submodule.mem_bot] at hmem
  exact neelStateOfS_ne_zero A N hmem

/-- The line spanned by the spin-`S` Néel state is contained in the
magnetization subspace at `M = (|A|-|¬A|)·N/2`. Spin-`S` analog of
`neelStateOf_span_le_magnetizationSubspace`. -/
theorem neelStateOfS_span_le_magSubspaceS (A : Λ → Bool) (N : ℕ) :
    Submodule.span ℂ {neelStateOfS A N} ≤
      magSubspaceS Λ N
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact neelStateOfS_mem_magSubspaceS A N

/-- The line spanned by the spin-`S` complement Néel state is contained
in the magnetization subspace at `-M = (|¬A|-|A|)·N/2` (γ-4 step 194). -/
theorem neelStateOfS_complement_span_le_magSubspaceS (A : Λ → Bool) (N : ℕ) :
    Submodule.span ℂ {neelStateOfS (fun x : Λ => ! A x) N} ≤
      magSubspaceS Λ N
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact neelStateOfS_complement_mem_magSubspaceS A N

/-- The Néel pair span sits inside the supremum of the two opposite-sign
magnetization subspaces: `span ℂ {Φ_Néel(A), Φ_Néel(¬A)} ≤ magSubspace
M_pos ⊔ magSubspace M_neg`, with `M_pos = (|A|-|¬A|)·N/2` and
`M_neg = (|¬A|-|A|)·N/2`. Direct from γ-4 step 176 + 194 via
`Submodule.mem_sup_left/right` (γ-4 step 197). -/
theorem neelStateOfS_pair_span_le_magSubspaceS_sup (A : Λ → Bool) (N : ℕ) :
    Submodule.span ℂ
        ({neelStateOfS A N, neelStateOfS (fun x : Λ => ! A x) N} : Set _) ≤
      magSubspaceS Λ N
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) ⊔
        magSubspaceS Λ N
          (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) := by
  rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, ?_⟩
  · exact Submodule.mem_sup_left (neelStateOfS_mem_magSubspaceS A N)
  · exact Submodule.mem_sup_right (neelStateOfS_complement_mem_magSubspaceS A N)

/-- **Spin-S complement magnetization subspace non-triviality**: the
opposite-sign sector `(|¬A|-|A|)·N/2` is also non-trivial, witnessed by
the non-zero complement Néel state `Φ_Néel(¬A)`. Combined with γ-4 step
177, when `0 < N` and `|A| ≠ |¬A|` (so the original `M_neel` and its
negation are distinct), the original and complement Néel states certify
two distinct non-trivial sectors (γ-4 step 178). -/
theorem magSubspaceS_complement_nontrivial_via_neel (A : Λ → Bool) (N : ℕ) :
    magSubspaceS Λ N
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) ≠ ⊥ := by
  intro hbot
  have hmem := neelStateOfS_complement_mem_magSubspaceS A N
  rw [hbot, Submodule.mem_bot] at hmem
  exact neelStateOfS_ne_zero (fun x : Λ => ! A x) N hmem

/-- The spin-`S` Néel state has norm-squared 1:
`<Φ_Néel | Φ_Néel> = 1`. Direct from `basisVecS_inner_self`. -/
theorem neelStateOfS_inner_self (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N)) (neelStateOfS A N) = 1 := by
  unfold neelStateOfS
  exact basisVecS_inner_self _

/-- **State-level distinctness** of `Φ_Néel(A)` and `Φ_Néel(¬A)` (spin-S):
when `Λ` is non-empty and `0 < N`, the two Néel states are distinct as
elements of the multi-site Hilbert space. Direct from γ-4 step 171
orthogonality combined with norm-squared = 1: equality would force
`<Φ_Néel(¬A) | Φ_Néel(¬A)> = 0`, contradicting `inner_self = 1`. -/
theorem neelStateOfS_ne_complement
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N) :
    neelStateOfS A N ≠ neelStateOfS (fun x : Λ => ! A x) N := by
  intro h
  have horth := neelStateOfS_complement_orthogonal A N hN
  rw [h] at horth
  rw [neelStateOfS_inner_self] at horth
  exact one_ne_zero horth

/-- **Néel-complement linear independence** (spin-S): a linear combination
`c1 • Φ_Néel(A) + c2 • Φ_Néel(¬A) = 0` forces `c1 = c2 = 0`, when `Λ` is
non-empty and `0 < N`. Direct consequence of γ-4 step 171 (orthogonality)
plus norm-squared = 1 (`neelStateOfS_inner_self`). The pair spans a
2-dimensional subspace of the many-body Hilbert space. -/
theorem neelStateOfS_complement_pair_independent
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) (hN : 0 < N)
    {c1 c2 : ℂ}
    (h : c1 • neelStateOfS A N + c2 • neelStateOfS (fun x : Λ => ! A x) N = 0) :
    c1 = 0 ∧ c2 = 0 := by
  have horth_AcA := neelStateOfS_complement_orthogonal A N hN
  have horth_cAA :
      dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))
          (neelStateOfS A N) = 0 := by
    have := neelStateOfS_complement_orthogonal (fun x : Λ => ! A x) N hN
    simpa [Bool.not_not] using this
  have hc1 : c1 = 0 := by
    have := congrArg (dotProduct (star (neelStateOfS A N))) h
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul,
        neelStateOfS_inner_self, horth_AcA, dotProduct_zero] at this
    simp at this
    exact this
  have hc2 : c2 = 0 := by
    have := congrArg
      (dotProduct (star (neelStateOfS (fun x : Λ => ! A x) N))) h
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul,
        neelStateOfS_inner_self, horth_cAA, dotProduct_zero] at this
    simp at this
    exact this
  exact ⟨hc1, hc2⟩

/-- `<Φ_Néel | Ŝ_A^+ · Ŝ_¬A^+ | Φ_Néel> = 0`. Trivially via γ-4 step 89. -/
theorem neelStateOfS_sublattice_plus_complement_plus_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((sublatticeSpinSOpPlus N A *
            sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
          (neelStateOfS A N)) = 0 := by
  rw [sublatticeSpinSOpPlus_complement_plus_mulVec_neelStateOfS]
  exact dotProduct_zero _

/-- `<Φ_Néel | Ŝ_A^- · Ŝ_¬A^- | Φ_Néel> = 0`. Trivially via γ-4 step 83. -/
theorem neelStateOfS_sublattice_minus_complement_minus_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((sublatticeSpinSOpMinus N A *
            sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
          (neelStateOfS A N)) = 0 := by
  rw [sublatticeSpinSOpMinus_complement_minus_mulVec_neelStateOfS]
  exact dotProduct_zero _

/-- `<Φ_Néel | Ŝ_A^+ · Ŝ_¬A^- | Φ_Néel> = 0`. Trivially via
`Ŝ_A^+ · Ŝ_¬A^- · Néel = 0` (γ-4 step 81). -/
theorem neelStateOfS_sublattice_plus_complement_minus_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((sublatticeSpinSOpPlus N A *
            sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
          (neelStateOfS A N)) = 0 := by
  rw [sublatticeSpinSOpPlus_complement_minus_mulVec_neelStateOfS]
  exact dotProduct_zero _

/-- `<Φ_Néel | Ŝ_A^- · Ŝ_¬A^+ | Φ_Néel> = 0`. The cross-flip expectation
vanishes by taking the Hermitian conjugate: `<Ŝ_A^+ Φ_Néel | Ŝ_¬A^+ Φ_Néel>`,
and `Ŝ_A^+ · Φ_Néel = 0`. -/
theorem neelStateOfS_sublattice_minus_plus_cross_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((sublatticeSpinSOpMinus N A *
            sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
          (neelStateOfS A N)) = 0 := by
  -- <Néel | (Ŝ_A^-)(Ŝ_¬A^+) | Néel> = (Ŝ_¬A^+ Néel)ᴴ ⬝ Ŝ_A^- Néelᴴ⁻¹ ... too complex
  -- Direct route: compute via star_dotProduct and Ŝ_A^- = conjTranspose Ŝ_A^+
  rw [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  rw [show sublatticeSpinSOpMinus N A =
      (sublatticeSpinSOpPlus N A).conjTranspose from
    (sublatticeSpinSOpPlus_conjTranspose N A).symm]
  rw [← Matrix.star_mulVec]
  rw [sublatticeSpinSOpPlus_mulVec_neelStateOfS]
  rw [star_zero]
  exact zero_dotProduct _

/-- `<Φ_Néel | Ŝ_A^(3) · Ŝ_¬A^(3) | Φ_Néel> = -|A|·|¬A|·(N/2)²`. Direct from
γ-4 step 79 (eigenvector property) and norm-squared = 1. -/
theorem neelStateOfS_sublattice3_cross_complement3_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x)).mulVec
          (neelStateOfS A N)) =
      (-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2) ^ 2)) := by
  rw [sublatticeSpinSOp3_cross_complement_mulVec_neelStateOfS]
  rw [dotProduct_smul]
  rw [neelStateOfS_inner_self, smul_eq_mul, mul_one]

/-- `<Φ_Néel | Ŝ_A · Ŝ_¬A | Φ_Néel> = -|A|·|¬A|·(N/2)²`. Combines:
- `<Néel | Ŝ_A^(3) Ŝ_¬A^(3) | Néel> = -|A|·|¬A|·(N/2)²` (γ-4 step 116)
- `<Néel | Ŝ_A^(1) Ŝ_¬A^(1) + Ŝ_A^(2) Ŝ_¬A^(2) | Néel>
    = (1/2)(<...Ŝ_A^+ Ŝ_¬A^-...> + <...Ŝ_A^- Ŝ_¬A^+...>) = 0`
  (γ-4 step 122 ladder identity + steps 118, 114). -/
theorem neelStateOfS_sublatticeSpinSDot_expectation (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((sublatticeSpinSDot N A (fun x => ! A x)).mulVec (neelStateOfS A N)) =
      (-(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2) ^ 2)) := by
  unfold sublatticeSpinSDot
  rw [Matrix.add_mulVec, Matrix.add_mulVec]
  rw [dotProduct_add, dotProduct_add]
  rw [neelStateOfS_sublattice3_cross_complement3_expectation]
  -- Now need <Néel | Ŝ_A^(1) Ŝ_¬A^(1) | Néel> + <Néel | Ŝ_A^(2) Ŝ_¬A^(2) | Néel> = 0
  rw [show
      dotProduct (star (neelStateOfS A N))
          ((sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N (fun x => ! A x)).mulVec
            (neelStateOfS A N)) +
        dotProduct (star (neelStateOfS A N))
          ((sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N (fun x => ! A x)).mulVec
            (neelStateOfS A N)) = 0 from ?_]
  · ring
  -- Use ladder identity: 1·1 + 2·2 = (1/2)(+·- + -·+).
  rw [← dotProduct_add, ← Matrix.add_mulVec]
  rw [sublatticeSpinSOp1_mul_op1_add_op2_mul_op2_eq_ladder]
  rw [Matrix.smul_mulVec, dotProduct_smul]
  rw [Matrix.add_mulVec, dotProduct_add]
  rw [neelStateOfS_sublattice_plus_complement_minus_expectation]
  rw [neelStateOfS_sublattice_minus_plus_cross_expectation]
  simp

/-- `<Φ_Néel | Ŝ_tot^(3) | Φ_Néel> = (|A| - |¬A|)·N/2`. The Néel state is
an `Ŝ_tot^(3)` eigenvector with magnetization `(|A| - |¬A|)·N/2`. -/
theorem neelStateOfS_totalSpinSOp3_expectation (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp3 Λ N).mulVec (neelStateOfS A N)) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) := by
  rw [totalSpinSOp3_mulVec_neelStateOfS]
  rw [dotProduct_smul]
  rw [neelStateOfS_inner_self, smul_eq_mul, mul_one]

/-- `(Ŝ_tot^(3))² · |Φ_Néel⟩ = ((|A|-|¬A|)·N/2)² · |Φ_Néel⟩`. Square of γ-4
step 68 (`totalSpinSOp3_mulVec_neelStateOfS`); the Néel state is an exact
eigenvector of `(Ŝ_tot^(3))²` at eigenvalue `M²` where
`M = (|A|-|¬A|)·N/2`. -/
theorem totalSpinSOp3_sq_mulVec_neelStateOfS (A : Λ → Bool) (N : ℕ) :
    (totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec (neelStateOfS A N) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
          ((N : ℂ) / 2)) ^ 2 •
        neelStateOfS A N := by
  rw [← Matrix.mulVec_mulVec]
  rw [totalSpinSOp3_mulVec_neelStateOfS]
  rw [Matrix.mulVec_smul]
  rw [totalSpinSOp3_mulVec_neelStateOfS]
  rw [smul_smul]
  congr 1
  ring

/-- `<Φ_Néel | (Ŝ_tot^(3))² | Φ_Néel> = ((|A|-|¬A|)·N/2)²`. Direct from
γ-4 step 128 (eigenvector at M²) plus `neelStateOfS_inner_self`. -/
theorem neelStateOfS_totalSpinSOp3_sq_expectation (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec (neelStateOfS A N)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
          ((N : ℂ) / 2)) ^ 2 := by
  rw [totalSpinSOp3_sq_mulVec_neelStateOfS]
  rw [dotProduct_smul, neelStateOfS_inner_self, smul_eq_mul, mul_one]

/-- `<Φ_Néel | (Ŝ_tot)² | Φ_Néel> = ((|A|-|¬A|)·N/2)² + (|A|+|¬A|)·N/2`.

The full total-spin Casimir expectation on the Néel state. By the Casimir
identity `(Ŝ_tot)² = (Ŝ_A)² + 2 (Ŝ_A · Ŝ_¬A) + (Ŝ_¬A)²`:
- `<Néel|(Ŝ_A)²|Néel> = (|A|·N/2)((|A|·N/2)+1)` (γ-4 step 79 + norm 1)
- `<Néel|(Ŝ_¬A)²|Néel> = (|¬A|·N/2)((|¬A|·N/2)+1)` (complement)
- `<Néel|Ŝ_A·Ŝ_¬A|Néel> = -|A|·|¬A|·(N/2)²` (γ-4 step 124)

Sum simplifies to `((|A|-|¬A|)·N/2)² + (|A|+|¬A|)·N/2`. -/
theorem neelStateOfS_totalSpinSSquared_expectation (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
          ((N : ℂ) / 2)) ^ 2 +
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
          ((N : ℂ) / 2) := by
  rw [totalSpinSSquared_eq_sublattice_casimir N A]
  simp only [Matrix.add_mulVec, dotProduct_add,
    sublatticeSpinSquaredS_mulVec_neelStateOfS,
    sublatticeSpinSquaredS_complement_mulVec_neelStateOfS,
    Matrix.smul_mulVec, dotProduct_smul,
    neelStateOfS_sublatticeSpinSDot_expectation,
    neelStateOfS_inner_self, smul_eq_mul, mul_one]
  ring

/-- `<Φ_Néel | (Ŝ_tot)² | Φ_Néel> = ((|A|-|¬A|)·N/2)² + |Λ|·N/2`. Reformulation
of γ-4 step 126 using `|A| + |¬A| = |Λ|`. -/
theorem neelStateOfS_totalSpinSSquared_expectation_card_Lambda
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N)) =
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
          ((N : ℂ) / 2)) ^ 2 +
        (Fintype.card Λ : ℂ) * ((N : ℂ) / 2) := by
  rw [neelStateOfS_totalSpinSSquared_expectation]
  congr 1
  have h : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) =
      (Fintype.card Λ : ℂ) := by
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
    exact_mod_cast h1
  rw [h]

/-- `<Φ_Néel | Ĥ_toy_S | Φ_Néel> = -|A|·|¬A|·N²/2`. The toy-Hamiltonian
expectation value on the Néel state. Combines the generic basis-vector
expectation lemma `basisVecS_expectation_eq_diagonal` (γ-4 step 132) with
`heisenbergToyHamiltonianS_apply_diag_neel`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec (neelStateOfS A N)) =
      - (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) := by
  unfold neelStateOfS
  rw [basisVecS_expectation_eq_diagonal]
  exact heisenbergToyHamiltonianS_apply_diag_neel A N

end LatticeSystem.Quantum
