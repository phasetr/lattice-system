import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGlobalMin
import LatticeSystem.Math.PerronFrobenius
import LatticeSystem.Math.PerronFrobeniusFinrank

/-!
# Magnetization sectors of the one-hole Tasaki basis (Tasaki §11.2.2)

Foundations for **Tasaki Theorem 11.7** (Nagaoka's theorem): the `S_z^{(3)}`
magnetization grading of the one-hole Tasaki basis, the block-diagonality of the
effective-Hamiltonian Tasaki matrix `M` across sectors, **Definition 11.6**
(`nagaokaConnectivity`, per-sector irreducibility of `−M`), and the per-sector
Perron–Frobenius non-degenerate ground state.

* [`configMag`] / [`holeSpinMag`] — total `S_z^{(3)}` read off the occupation
  configuration.
* [`tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne`] — `M` is block-diagonal.
* [`HoleMagSector`] / [`tasakiEffReMatrixOnSector`] / [`nagaokaPFMatrixOnSector`]
  / [`nagaokaConnectivity`] (Definition 11.6).
* [`tasakiEffReMatrixOnSector_ground_finrank_le_one`] — per-sector PF.

Split from `NagaokaConnectivity.lean` (refactor, 2026-06-04).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Definition 11.6 and Theorem 11.7.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math.PerronFrobenius Module

/-- The (doubled) total `S_z^{(3)}` magnetization read off an occupation
configuration `c : Fin (2N+2) → Fin 2` of the spinful chain: each site `i`
contributes `(occupation of its ↑-orbital) − (occupation of its ↓-orbital)`.
For a singly-occupied site this is `±1`; for an empty (hole) or doubly-occupied
site it is `0`.  Because it depends only on the occupations, two configurations
that are *equal as functions* have equal `configMag`. -/
def configMag (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : ℤ :=
  ∑ i : Fin (N + 1),
    (((c (spinfulIndex N i 0)).val : ℤ) - ((c (spinfulIndex N i 1)).val : ℤ))

/-- The (doubled) total `S_z^{(3)}` magnetization of the one-hole Tasaki basis
index `⟨x, σ⟩`, defined through its occupation configuration so that it depends
only on that configuration. -/
def holeSpinMag (N : ℕ) (p : (x : Fin (N + 1)) × HoleSpin N x) : ℤ :=
  configMag N (hubbardOneHoleConfig N p.1 p.2.val)

/-- The magnetization of a one-hole configuration, expressed sitewise: the hole
site contributes `0`, every other site contributes `+1` for spin `↑` and `−1`
for spin `↓`. -/
theorem configMag_hubbardOneHoleConfig (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) :
    configMag N (hubbardOneHoleConfig N x σ) =
      ∑ i : Fin (N + 1), (if i = x then (0 : ℤ) else if σ i then 1 else -1) := by
  unfold configMag
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hubbardOneHoleConfig_apply_up, hubbardOneHoleConfig_apply_down]
  simp only [Fin.val_inj]
  by_cases h : i = x
  · simp [h]
  · rw [if_neg h]
    by_cases hσ : σ i <;> simp [h, hσ]

/-- `holeSpinMag ⟨x, σ⟩ = 2·(electron ↑-count) − N`: each of the `N` occupied
sites contributes `±1` to `S_z^{(3)}`, and `(#↑) + (#↓) = N`.  Hence the
magnetization is determined by the number of up-electrons, which lies in
`{0, …, N}`. -/
theorem holeSpinMag_eq_two_mul_upCount_sub (N : ℕ)
    (p : (x : Fin (N + 1)) × HoleSpin N x) :
    holeSpinMag N p =
      2 * ((Finset.univ.filter (fun i => i ≠ p.1 ∧ p.2.val i = true)).card : ℤ)
        - N := by
  obtain ⟨x, σ⟩ := p
  rw [holeSpinMag, configMag_hubbardOneHoleConfig]
  have hsum : ∑ i : Fin (N + 1), (if i = x then (0 : ℤ) else if σ.val i then 1 else -1)
      = ∑ i ∈ Finset.univ.erase x, (if σ.val i then (1 : ℤ) else -1) := by
    rw [← Finset.sum_erase Finset.univ (a := x) (by simp)]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [if_neg (Finset.ne_of_mem_erase hi)]
  rw [hsum]
  have hsplit : ∑ i ∈ Finset.univ.erase x, (if σ.val i then (1 : ℤ) else -1)
      = ((Finset.univ.erase x).filter (fun i => σ.val i = true)).card
        - ((Finset.univ.erase x).filter (fun i => ¬ σ.val i = true)).card := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    ring
  rw [hsplit]
  have hcard : ((Finset.univ.erase x).filter (fun i => σ.val i = true)).card
      + ((Finset.univ.erase x).filter (fun i => ¬ σ.val i = true)).card
      = N := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hfilter : ((Finset.univ.erase x).filter (fun i => σ.val i = true))
      = Finset.univ.filter (fun i => i ≠ x ∧ σ.val i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
  rw [← hfilter]
  omega

/-- **There are at most `N + 1` non-empty magnetization sectors.**  Since
`holeSpinMag = 2·(↑-count) − N` with the `↑`-count in `{0, …, N}`, the set of
magnetization values taken by the one-hole basis has at most `N + 1` elements.
This is the combinatorial bound behind the `2 S_max + 1 = N + 1` ground-state
degeneracy of Theorem 11.7. -/
theorem holeSpinMag_image_card_le (N : ℕ) :
    (Finset.univ.image (holeSpinMag N)).card ≤ N + 1 := by
  have hsub : Finset.univ.image (holeSpinMag N)
      ⊆ (Finset.range (N + 1)).image (fun j : ℕ => 2 * (j : ℤ) - N) := by
    intro m hm
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_image]
    refine ⟨(Finset.univ.filter (fun i => i ≠ p.1 ∧ p.2.val i = true)).card, ?_,
      (holeSpinMag_eq_two_mul_upCount_sub N p).symm⟩
    rw [Finset.mem_range]
    have hsub2 : Finset.univ.filter (fun i => i ≠ p.1 ∧ p.2.val i = true)
        ⊆ Finset.univ.erase p.1 := by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact Finset.mem_erase.mpr ⟨hi.2.1, Finset.mem_univ i⟩
    have hle : (Finset.univ.filter (fun i => i ≠ p.1 ∧ p.2.val i = true)).card ≤ N := by
      refine le_trans (Finset.card_le_card hsub2) (le_of_eq ?_)
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    omega
  calc (Finset.univ.image (holeSpinMag N)).card
      ≤ ((Finset.range (N + 1)).image (fun j : ℕ => 2 * (j : ℤ) - N)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range (N + 1)).card := Finset.card_image_le
    _ = N + 1 := Finset.card_range _

/-- **Hopping the hole preserves magnetization** (Tasaki (11.2.4)).  Moving the
electron at `y` into the hole at `x` (turning `|Φ_{x,σ}⟩` into a basis state at
hole `y`) does not change the total `S_z^{(3)}`: the electrons merely rearrange.
-/
theorem configMag_hubbardSpinMove (N : ℕ) (x y : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) (hxy : x ≠ y) :
    configMag N (hubbardOneHoleConfig N y (hubbardSpinMove N σ x y)) =
      configMag N (hubbardOneHoleConfig N x σ) := by
  rw [configMag_hubbardOneHoleConfig, configMag_hubbardOneHoleConfig,
    ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have key : ∀ i : Fin (N + 1),
      ((if i = y then (0 : ℤ) else if hubbardSpinMove N σ x y i then 1 else -1)
        - (if i = x then (0 : ℤ) else if σ i then 1 else -1))
      = (if i = x then (if σ y then (1 : ℤ) else -1) else 0)
        + (if i = y then -(if σ y then (1 : ℤ) else -1) else 0) := by
    intro i
    by_cases hix : i = x <;> by_cases hiy : i = y
    · exact absurd (hix ▸ hiy : x = y) hxy
    · subst hix; simp [hiy, hubbardSpinMove]
    · simp_all
    · simp [hubbardSpinMove, hix, hiy]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ x, Finset.sum_ite_eq' Finset.univ y]
  simp

/-- **The Tasaki matrix is block-diagonal in magnetization.**  A matrix element
`M_{⟨y,τ⟩, ⟨x,σ⟩}` between one-hole basis states of different total `S_z^{(3)}`
vanishes — `Ĥ_eff` conserves `S_z^{(3)}`, so it preserves each magnetization
sector.  (Here `M = `[`tasakiEffReMatrix`].) -/
theorem tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (q p : (x : Fin (N + 1)) × HoleSpin N x)
    (h : holeSpinMag N q ≠ holeSpinMag N p) :
    tasakiEffReMatrix N t q p = 0 := by
  obtain ⟨y, τ⟩ := q
  obtain ⟨x, σ⟩ := p
  unfold tasakiEffReMatrix
  by_cases hxy : x = y
  · -- diagonal block (same hole site) is unreachable here, but the entry is 0
    simp [hxy]
  · rw [if_neg (by simpa using hxy)]
    rw [if_neg ?_, mul_zero]
    intro hcfg
    apply h
    change configMag N (hubbardOneHoleConfig N y τ.val) =
      configMag N (hubbardOneHoleConfig N x σ.val)
    rw [← hcfg, configMag_hubbardSpinMove N x y σ.val hxy]

/-- **The real Tasaki matrix is symmetric.**  For symmetric hopping with zero
diagonal it equals its own transpose (derived from the complex Hermitian form
`tasakiEffMatrix_isHermitian` through `M = M_ℝ.map ofReal`). -/
theorem tasakiEffReMatrix_isSymm (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) :
    (tasakiEffReMatrix N t).IsSymm := by
  have hmap := tasakiEffMatrix_eq_map_tasakiEffReMatrix N t 0 htdiag
  simp only [Complex.ofReal_zero] at hmap
  have hH := tasakiEffMatrix_isHermitian N (fun i j => (t i j : ℂ)) (0 : ℂ)
    (tasakiEffMatrix_hJ_of_real htsym) (by simp)
  rw [hmap] at hH
  ext p q
  rw [Matrix.transpose_apply]
  have h := congr_fun₂ hH p q
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def,
    Complex.conj_ofReal] at h
  exact_mod_cast h

/-- **The off-diagonal entries of `−M` are non-negative** when the hopping is
non-negative (`t ≥ 0`).  Since `M_{q,p} = −t_{x,y}·[indicator] ≤ 0` off the
diagonal and `M` vanishes on the diagonal, `−M` is entrywise non-negative. -/
theorem neg_tasakiEffReMatrix_nonneg (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hpos : ∀ i j, 0 ≤ t i j)
    (q p : (x : Fin (N + 1)) × HoleSpin N x) :
    0 ≤ (-tasakiEffReMatrix N t) q p := by
  obtain ⟨y, τ⟩ := q
  obtain ⟨x, σ⟩ := p
  rw [Matrix.neg_apply]
  unfold tasakiEffReMatrix
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg (by simpa using hxy), neg_mul, neg_neg]
    apply mul_nonneg (hpos x y)
    split <;> norm_num

/-- The magnetization sector `m`: one-hole Tasaki basis indices whose total
`S_z^{(3)}` (doubled) equals `m`.  `M` is block-diagonal across these sectors
(`tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne`). -/
abbrev HoleMagSector (N : ℕ) (m : ℤ) :=
  {p : (x : Fin (N + 1)) × HoleSpin N x // holeSpinMag N p = m}

/-- The Tasaki matrix `M` restricted to a single magnetization sector `m`. -/
noncomputable def tasakiEffReMatrixOnSector (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ) :
    Matrix (HoleMagSector N m) (HoleMagSector N m) ℝ :=
  (tasakiEffReMatrix N t).submatrix Subtype.val Subtype.val

/-- The matrix `−M` restricted to a sector `m`: the entrywise non-negative
(for `t ≥ 0`) symmetric matrix to which Perron–Frobenius is applied in the
proof of Theorem 11.7. -/
noncomputable def nagaokaPFMatrixOnSector (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ) :
    Matrix (HoleMagSector N m) (HoleMagSector N m) ℝ :=
  -tasakiEffReMatrixOnSector N t m

/-- **Tasaki Definition 11.6 (connectivity condition).**  The one-hole system
is *connected* if, within every fixed total-`S_z^{(3)}` sector `m`, the basis
states are joined through non-vanishing `Ĥ_eff` matrix elements — formalized as
irreducibility (in the Perron–Frobenius sense) of `−M` restricted to that
sector.  This is the hypothesis of Tasaki Theorem 11.7.

Reference: Tasaki §11.2.2, Definition 11.6. -/
def nagaokaConnectivity (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) : Prop :=
  ∀ m : ℤ, (nagaokaPFMatrixOnSector N t m).IsIrreducible

/-- The sector restriction of `−M` is symmetric. -/
theorem nagaokaPFMatrixOnSector_isSymm (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) :
    (nagaokaPFMatrixOnSector N t m).IsSymm := by
  unfold nagaokaPFMatrixOnSector tasakiEffReMatrixOnSector
  ext p q
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.submatrix_apply]
  rw [(tasakiEffReMatrix_isSymm N t htsym htdiag).apply]

/-- **Per-sector Perron–Frobenius (the heart of Theorem 11.7).**  On a non-empty
magnetization sector `m` satisfying the connectivity condition (Definition
11.6), `−M` has a strictly positive eigenvector at its Perron eigenvalue `μ`,
and that eigenspace is at most one-dimensional — i.e. the sector ground state is
*non-degenerate*.  (Recall `−M v = μ v ↔ M v = −μ v`, so this is the unique
ground state of `M` in the sector.) -/
theorem nagaokaPFMatrixOnSector_exists_pos_eigenvec (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    [Nonempty (HoleMagSector N m)]
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hconn : (nagaokaPFMatrixOnSector N t m).IsIrreducible) :
    ∃ (μ : ℝ) (v : HoleMagSector N m → ℝ),
      nagaokaPFMatrixOnSector N t m *ᵥ v = μ • v ∧ (∀ i, 0 < v i) ∧
      finrank ℝ (End.eigenspace
        (Matrix.toLin' (nagaokaPFMatrixOnSector N t m)) μ) ≤ 1 := by
  have hHerm : (nagaokaPFMatrixOnSector N t m).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact nagaokaPFMatrixOnSector_isSymm N t m htsym htdiag
  obtain ⟨μ, v, hAv, _hvne, hv_pos⟩ := exists_pos_eigenvec_max hHerm hconn
  exact ⟨μ, v, hAv, hv_pos,
    eigenspace_finrank_le_one_of_pos_eigenvec hconn hAv hv_pos⟩

/-- The `(-μ)`-eigenspace of `M` (on a sector) coincides with the `μ`-eigenspace
of `−M`: `−M v = μ v ↔ M v = −μ v`. -/
theorem eigenspace_tasakiEffReMatrixOnSector_eq_neg (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ) (μ : ℝ) :
    End.eigenspace (Matrix.toLin' (tasakiEffReMatrixOnSector N t m)) (-μ)
      = End.eigenspace (Matrix.toLin' (nagaokaPFMatrixOnSector N t m)) μ := by
  ext x
  rw [End.mem_eigenspace_iff, End.mem_eigenspace_iff, toLin'_apply, toLin'_apply]
  unfold nagaokaPFMatrixOnSector
  rw [neg_mulVec]
  constructor
  · intro h; rw [h, neg_smul, neg_neg]
  · intro h; rw [neg_smul]; exact neg_eq_iff_eq_neg.mp h

/-- **The sector ground state of `M` is non-degenerate (Theorem 11.7 core).**
On a non-empty connected magnetization sector, `M` has a strictly positive
eigenvector at the eigenvalue `−μ` (`μ` the Perron eigenvalue of `−M`), and that
eigenspace is at most one-dimensional.  Since `−μ = min spec M|_sector`, this is
the unique ground state of `M` within the sector. -/
theorem tasakiEffReMatrixOnSector_ground_finrank_le_one (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    [Nonempty (HoleMagSector N m)]
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0)
    (hconn : (nagaokaPFMatrixOnSector N t m).IsIrreducible) :
    ∃ (lam : ℝ) (v : HoleMagSector N m → ℝ),
      tasakiEffReMatrixOnSector N t m *ᵥ v = lam • v ∧ (∀ i, 0 < v i) ∧
      finrank ℝ (End.eigenspace
        (Matrix.toLin' (tasakiEffReMatrixOnSector N t m)) lam) ≤ 1 := by
  obtain ⟨μ, v, hAv, hv_pos, hfin⟩ :=
    nagaokaPFMatrixOnSector_exists_pos_eigenvec N t m htsym htdiag hconn
  refine ⟨-μ, v, ?_, hv_pos, ?_⟩
  · have hthis : (-tasakiEffReMatrixOnSector N t m) *ᵥ v = μ • v := hAv
    rw [neg_mulVec] at hthis
    rw [neg_smul]; exact neg_eq_iff_eq_neg.mp hthis
  · rw [eigenspace_tasakiEffReMatrixOnSector_eq_neg]; exact hfin

/-- **Block invariance: restricting a coefficient eigenvector to a sector gives a
sector eigenvector.**  If `M c = E c` in the full one-hole coefficient space and
`c|_m` is the restriction of `c` to sector `m`, then `M_m (c|_m) = E (c|_m)` —
because `M` is block-diagonal in magnetization
(`tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne`).  This lets the global
`E`-eigenspace decompose over sectors. -/
theorem tasakiEffReMatrixOnSector_mulVec_restriction_of_eigen (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) {m : ℤ} {E : ℝ}
    {c : (x : Fin (N + 1)) × HoleSpin N x → ℝ}
    (hc : tasakiEffReMatrix N t *ᵥ c = E • c) :
    tasakiEffReMatrixOnSector N t m *ᵥ (fun p : HoleMagSector N m => c p.val) =
      E • (fun p : HoleMagSector N m => c p.val) := by
  classical
  funext q
  have hrhs : (E • fun p : HoleMagSector N m => c p.val) q = E * c q.val := rfl
  rw [hrhs]
  change ∑ p : HoleMagSector N m,
      tasakiEffReMatrixOnSector N t m q p * c p.val = E * c q.val
  have hsec : (∑ p : HoleMagSector N m,
        tasakiEffReMatrixOnSector N t m q p * c p.val) =
      ∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
        tasakiEffReMatrix N t q.val p' * c p' := by
    rw [Finset.sum_subtype
      (Finset.univ.filter (fun p' => holeSpinMag N p' = m))
      (p := fun p' => holeSpinMag N p' = m)
      (fun p' => by simp [Finset.mem_filter])
      (fun p' => tasakiEffReMatrix N t q.val p' * c p')]
    refine Finset.sum_congr rfl (fun p' _ => ?_)
    unfold tasakiEffReMatrixOnSector
    rw [Matrix.submatrix_apply]
  rw [hsec]
  have hfull : ∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
        tasakiEffReMatrix N t q.val p' * c p' =
      ∑ p' : (x : Fin (N + 1)) × HoleSpin N x,
        tasakiEffReMatrix N t q.val p' * c p' := by
    refine Finset.sum_filter_of_ne (p := fun p' => holeSpinMag N p' = m) ?_
    intro p' _ hne
    by_contra hp'm
    apply hne
    have hmag_ne : holeSpinMag N q.val ≠ holeSpinMag N p' :=
      fun heq => hp'm (heq.symm.trans q.2)
    rw [tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne N t q.val p' hmag_ne, zero_mul]
  rw [hfull]
  change (tasakiEffReMatrix N t *ᵥ c) q.val = _
  rw [hc]
  rfl

/-- Zero-extension of a sector vector to the full one-hole coefficient space:
`sectorEmbed v p = v p` if `p` is in sector `m`, else `0`. -/
def sectorEmbed (N : ℕ) (m : ℤ)
    (v : HoleMagSector N m → ℝ) : (x : Fin (N + 1)) × HoleSpin N x → ℝ :=
  fun p => if h : holeSpinMag N p = m then v ⟨p, h⟩ else 0

/-- **Block invariance, embedding direction: a sector eigenvector lifts to a full
eigenvector.**  If `M_m v = lam v` then `M (sectorEmbed v) = lam (sectorEmbed v)`
— because `M` is block-diagonal in magnetization, the zero-extended vector is a
genuine eigenvector of the full coefficient-space matrix at the same eigenvalue.
Hence every sector eigenvalue is a full-matrix eigenvalue (so `≥ min M`). -/
theorem tasakiEffReMatrix_mulVec_sectorEmbed_of_eigen (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) {m : ℤ} {lam : ℝ}
    {v : HoleMagSector N m → ℝ}
    (hv : tasakiEffReMatrixOnSector N t m *ᵥ v = lam • v) :
    tasakiEffReMatrix N t *ᵥ sectorEmbed N m v = lam • sectorEmbed N m v := by
  classical
  funext q
  change (∑ p', tasakiEffReMatrix N t q p' * sectorEmbed N m v p') = lam * sectorEmbed N m v q
  have hzero : ∀ p' : (x : Fin (N + 1)) × HoleSpin N x,
      holeSpinMag N p' ≠ m → tasakiEffReMatrix N t q p' * sectorEmbed N m v p' = 0 := by
    intro p' hp'
    simp [sectorEmbed, hp']
  by_cases hq : holeSpinMag N q = m
  · -- q in sector m: full sum collapses to the sector sum = (M_m v) ⟨q⟩.
    have hfilter : (∑ p', tasakiEffReMatrix N t q p' * sectorEmbed N m v p') =
        ∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
          tasakiEffReMatrix N t q p' * sectorEmbed N m v p' := by
      refine (Finset.sum_filter_of_ne (fun p' _ hne => ?_)).symm
      by_contra h; exact hne (hzero p' h)
    have hsub : (∑ p' ∈ Finset.univ.filter (fun p' => holeSpinMag N p' = m),
          tasakiEffReMatrix N t q p' * sectorEmbed N m v p') =
        ∑ p : HoleMagSector N m, tasakiEffReMatrixOnSector N t m ⟨q, hq⟩ p * v p := by
      rw [Finset.sum_subtype
        (Finset.univ.filter (fun p' => holeSpinMag N p' = m))
        (p := fun p' => holeSpinMag N p' = m)
        (fun p' => by simp [Finset.mem_filter])
        (fun p' => tasakiEffReMatrix N t q p' * sectorEmbed N m v p')]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      simp only [sectorEmbed, dif_pos p.property, Subtype.coe_eta]
      unfold tasakiEffReMatrixOnSector
      rw [Matrix.submatrix_apply]
    rw [hfilter, hsub]
    have heig := congrFun hv ⟨q, hq⟩
    change (∑ p, tasakiEffReMatrixOnSector N t m ⟨q, hq⟩ p * v p) = lam * v ⟨q, hq⟩ at heig
    rw [heig]
    simp [sectorEmbed, dif_pos hq]
  · -- q outside sector m: both sides are 0.
    have hlhs : (∑ p', tasakiEffReMatrix N t q p' * sectorEmbed N m v p') = 0 := by
      refine Finset.sum_eq_zero (fun p' _ => ?_)
      by_cases hp' : holeSpinMag N p' = m
      · rw [tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne N t q p' (by rw [hp']; exact hq),
          zero_mul]
      · exact hzero p' hp'
    rw [hlhs]
    simp [sectorEmbed, dif_neg hq]

/-- The real Tasaki matrix restricted to a sector is symmetric. -/
theorem tasakiEffReMatrixOnSector_isSymm (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ) (m : ℤ)
    (htsym : ∀ i j, t i j = t j i) (htdiag : ∀ i, t i i = 0) :
    (tasakiEffReMatrixOnSector N t m).IsSymm := by
  unfold tasakiEffReMatrixOnSector
  ext p q
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
  rw [(tasakiEffReMatrix_isSymm N t htsym htdiag).apply]

end LatticeSystem.Fermion
