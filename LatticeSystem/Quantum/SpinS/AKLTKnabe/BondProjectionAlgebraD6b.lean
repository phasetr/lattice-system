import LatticeSystem.Quantum.SpinS.AKLTKnabe.SiteBlockEmbeddingD5b
import LatticeSystem.Math.MatrixAnalysis.HermitianSum

/-!
# Gate D6b Stage A: the operator algebra of the AKLT bond projection

This module (Issue #5094; Tasaki §7.1.4, Knabe's argument, pp. 188–190) supplies the purely
*bond-local* algebra that the window-transport (Stage B) and the Knabe aggregation (Stage C)
consume:

* **idempotence** `P̂_{x,y} P̂_{x,y} = P̂_{x,y}` for any two distinct sites of a chain — Tasaki uses
  `P̂² = P̂` to pass from `(Ĥ')²` to eq. (7.1.26);
* **Hermiticity** of `P̂_{x,y}`;
* **commutation** of two bond projections supported on four *distinct* sites — Tasaki's remark
  after eq. (7.1.29) ("if `r ≥ 2`, the two projection operators … commute");
* **positive semidefiniteness of the product** of two such disjoint bond projections, which is the
  reason the offset sums `D_d` with `d ∉ {0, 1, −1}` may be discarded in eq. (7.1.36);
* the **conjugate transpose** of a block embedding and, as its corollary, the transport of positive
  semidefiniteness along `onEmbS` (design item B5f), which is what turns the four-site window
  certificate `ε₃ ≥ 2/5` into a certificate for every window of a long chain.

## Periodic ring versus open window (design risk R3 — read before consuming this file)

Tasaki's §7.1.4 argument is stated for a **periodic** chain: `Ĥ'_AKLT = Σ_{x=1}^{L} P̂_{x,x+1}`
of eq. (7.1.7) **includes the wrap bond** `{L−1, 0}`, whereas the Knabe window
`ĥ_{x,x+ℓ} = Σ_{j=1}^{ℓ} P̂_{x+j−1,x+j}` of eq. (7.1.30) is the Hamiltonian of the **open** chain
on `ℓ+1` sites and therefore has **exactly `ℓ` bonds** (three, for `ℓ = 3`) — never a fourth.
Getting either side wrong is fatal, and the two errors pull in opposite directions.

Everything in *this* file is deliberately on **neither** side: each lemma speaks about one or two
bonds `{x, y}`, `{a, b}`, `{c, d}` given by *arbitrary* sites of `Fin L`, with only distinctness
hypotheses. No lemma here mentions `ringSucc`, `y + 1`, a bond sum, or a window, so no lemma here
can silently add or drop the wrap bond. The periodic/open distinction is made — and must be made —
by the *callers*: the ring sum `Ĥ'` (Stage C) ranges over all `y : Fin L` including the wrap bond,
while the window `ĥ_x` (Stage B) is three explicit bond projections.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.4, eqs. (7.1.7), (7.1.26)–(7.1.30), pp. 188–190.
-/

namespace LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

open Matrix
open scoped ComplexOrder

/-! ## A1: idempotence of the frozen rational two-site table -/

/-- The `(a b), (c d)` entry of the **square** of the frozen rational table `sector2P2Entry`,
with the nine-term fibre sum over the intermediate two-site configuration written out
explicitly. Expanding the sum here, in the *statement*, is what keeps each of the `81` entry
goals of `sector2P2Sq_eq` shallow enough for `norm_num` inside the default recursion depth (the
same device as `p2Rat_expand` of Gate D5b Stage 2); it also matches the shape produced by
`sum_fin2_fin3` verbatim, so no `Finset` sum is ever manipulated inside a matrix goal. -/
private def sector2P2Sq (a b c d : Fin 3) : ℚ :=
  sector2P2Entry a b 0 0 * sector2P2Entry 0 0 c d
    + sector2P2Entry a b 0 1 * sector2P2Entry 0 1 c d
    + sector2P2Entry a b 0 2 * sector2P2Entry 0 2 c d
    + sector2P2Entry a b 1 0 * sector2P2Entry 1 0 c d
    + sector2P2Entry a b 1 1 * sector2P2Entry 1 1 c d
    + sector2P2Entry a b 1 2 * sector2P2Entry 1 2 c d
    + sector2P2Entry a b 2 0 * sector2P2Entry 2 0 c d
    + sector2P2Entry a b 2 1 * sector2P2Entry 2 1 c d
    + sector2P2Entry a b 2 2 * sector2P2Entry 2 2 c d

/-- The `27` entries of `sector2P2Sq = sector2P2Entry` with first row label `0`. -/
private theorem sector2P2Sq_eq_zero (b c d : Fin 3) :
    sector2P2Sq 0 b c d = sector2P2Entry 0 b c d := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [sector2P2Sq, sector2P2Entry, Fin.mk.injEq, Fin.ext_iff]

/-- The `27` entries of `sector2P2Sq = sector2P2Entry` with first row label `1`. -/
private theorem sector2P2Sq_eq_one (b c d : Fin 3) :
    sector2P2Sq 1 b c d = sector2P2Entry 1 b c d := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [sector2P2Sq, sector2P2Entry, Fin.mk.injEq, Fin.ext_iff]

/-- The `27` entries of `sector2P2Sq = sector2P2Entry` with first row label `2`. -/
private theorem sector2P2Sq_eq_two (b c d : Fin 3) :
    sector2P2Sq 2 b c d = sector2P2Entry 2 b c d := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [sector2P2Sq, sector2P2Entry, Fin.mk.injEq, Fin.ext_iff]

/-- **The frozen rational two-site table is idempotent** (design item A1). All `81` entries of the
square of `sector2P2Entry`, as a `9 × 9` rational matrix indexed by the two-site labels `(a, b)`
and `(c, d)`, agree with `sector2P2Entry` itself: the table really is the matrix of a projection,
which is Tasaki's `P̂² = P̂` for the bond projector `P̂₂[Ŝ_x + Ŝ_y]` of eq. (7.1.6). -/
private theorem sector2P2Sq_eq (a b c d : Fin 3) :
    sector2P2Sq a b c d = sector2P2Entry a b c d := by
  fin_cases a
  · exact sector2P2Sq_eq_zero b c d
  · exact sector2P2Sq_eq_one b c d
  · exact sector2P2Sq_eq_two b c d

/-! ## A2–A3: idempotence of the bond projection -/

/-- **The two-site bond projection is idempotent** (design item A2). On the two-site chain
`Fin 2` the operator `P̂₂[Ŝ₀ + Ŝ₁]` satisfies `P̂ P̂ = P̂`. The `9`-term fibre sum produced by
`Matrix.mul_apply` is enumerated once by `sum_fin2_fin3` and then matched against the rational
identity `sector2P2Sq_eq`; the spectator guard is vacuous because the chain has only the two bond
sites. -/
theorem bondSpin2ProjectionS_fin2_mul_self :
    (bondSpin2ProjectionS (0 : Fin 2) 1 * bondSpin2ProjectionS (0 : Fin 2) 1 :
        ManyBodyOpS (Fin 2) 2) = bondSpin2ProjectionS (0 : Fin 2) 1 := by
  ext σ' σ
  rw [Matrix.mul_apply, sum_fin2_fin3]
  simp only [bondSpin2ProjectionS_fin2_apply_eq_sector2P2Entry, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [← sector2P2Sq_eq (σ' 0) (σ' 1) (σ 0) (σ 1)]
  simp only [sector2P2Sq]
  push_cast
  ring

/-- **Every bond projection of a chain is idempotent** (design item A3, Tasaki `P̂² = P̂`, used to
pass from `(Ĥ')²` to eq. (7.1.26)). For any two *distinct* sites `x ≠ y` of `Fin L` — adjacent or
not, wrap bond or not — `P̂₂[Ŝ_x + Ŝ_y]` is a projection. The proof transports the two-site
statement along the block embedding, whose multiplicativity `onEmbS_mul` needs exactly the
injectivity of the site list `![x, y]`. -/
theorem bondSpin2ProjectionS_mul_self {L : ℕ} {x y : Fin L} (hxy : x ≠ y) :
    (bondSpin2ProjectionS x y * bondSpin2ProjectionS x y : ManyBodyOpS (Fin L) 2)
      = bondSpin2ProjectionS x y := by
  rw [bondSpin2ProjectionS_eq_onEmbS hxy, onEmbS_mul (injective_bondEmb hxy),
    bondSpin2ProjectionS_fin2_mul_self]

/-! ## A4: Hermiticity of the bond projection -/

/-- **The bond projection is Hermitian** (design item A4). It is the polynomial
`½ D + ⅙ D² + ⅓` in the Hermitian bond operator `D = Ŝ_x · Ŝ_y` with real coefficients, and `D`
commutes with itself, so every summand is Hermitian. -/
theorem bondSpin2ProjectionS_isHermitian {L : ℕ} (x y : Fin L) :
    (bondSpin2ProjectionS x y : ManyBodyOpS (Fin L) 2).IsHermitian := by
  have hD : (spinSDot x y 2 : ManyBodyOpS (Fin L) 2).IsHermitian := spinSDot_isHermitian x y 2
  have hsq : (spinSDot x y 2 * spinSDot x y 2 : ManyBodyOpS (Fin L) 2).IsHermitian :=
    hD.mul_of_commute hD rfl
  have h2 : IsSelfAdjoint ((1 : ℂ) / 2) := by
    rw [isSelfAdjoint_iff, Complex.star_def]; simp [Complex.conj_ofNat]
  have h6 : IsSelfAdjoint ((1 : ℂ) / 6) := by
    rw [isSelfAdjoint_iff, Complex.star_def]; simp [Complex.conj_ofNat]
  have h3 : IsSelfAdjoint ((1 : ℂ) / 3) := by
    rw [isSelfAdjoint_iff, Complex.star_def]; simp [Complex.conj_ofNat]
  exact ((hD.smul h2).add (hsq.smul h6)).add (Matrix.isHermitian_one.smul h3)

/-! ## A5–A6: commutation of bond operators on disjoint site pairs -/

/-- **Two bond Heisenberg operators on disjoint site pairs commute** (design item A5). The four
cross conditions `a ≠ c`, `a ≠ d`, `b ≠ c`, `b ≠ d` say that the bonds `{a, b}` and `{c, d}` share
no site; `a = b` or `c = d` is *not* excluded and is not needed. Each of the nine axis pairs is a
product of four site embeddings at pairwise distinct sites, which commute by
`onSiteS_mul_onSiteS_of_ne`. -/
theorem spinSDot_commute_of_disjoint {L : ℕ} {a b c d : Fin L}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (spinSDot a b 2 : ManyBodyOpS (Fin L) 2) (spinSDot c d 2) := by
  have key : ∀ (A B : Matrix (Fin 3) (Fin 3) ℂ) {i j : Fin L}, i ≠ j →
      Commute (onSiteS i A : ManyBodyOpS (Fin L) 2) (onSiteS j B) :=
    fun A B _ _ hij => onSiteS_mul_onSiteS_of_ne hij A B
  have step : ∀ A B C D : Matrix (Fin 3) (Fin 3) ℂ,
      Commute ((onSiteS a A : ManyBodyOpS (Fin L) 2) * onSiteS b B)
        (onSiteS c C * onSiteS d D) :=
    fun A B C D =>
      ((key A C hac).mul_right (key A D had)).mul_left
        ((key B C hbc).mul_right (key B D hbd))
  simp only [spinSDot]
  exact Commute.add_left (Commute.add_left
      (Commute.add_right (Commute.add_right (step _ _ _ _) (step _ _ _ _)) (step _ _ _ _))
      (Commute.add_right (Commute.add_right (step _ _ _ _) (step _ _ _ _)) (step _ _ _ _)))
    (Commute.add_right (Commute.add_right (step _ _ _ _) (step _ _ _ _)) (step _ _ _ _))

/-- **Two bond projections on disjoint site pairs commute** (design item A6). This is Tasaki's
remark after eq. (7.1.29): for offsets `r ≥ 2` the two projections in `Ĉ_r` act on disjoint bonds
and commute. Each projection is the polynomial `½ D + ⅙ D² + ⅓` in its own bond operator, so
commutation follows from `spinSDot_commute_of_disjoint` term by term. -/
theorem bondSpin2ProjectionS_commute_of_disjoint {L : ℕ} {a b c d : Fin L}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (bondSpin2ProjectionS a b : ManyBodyOpS (Fin L) 2) (bondSpin2ProjectionS c d) := by
  have h : Commute (spinSDot a b 2 : ManyBodyOpS (Fin L) 2) (spinSDot c d 2) :=
    spinSDot_commute_of_disjoint hac had hbc hbd
  have h2 : Commute (spinSDot a b 2 : ManyBodyOpS (Fin L) 2) (spinSDot c d 2 * spinSDot c d 2) :=
    h.mul_right h
  have h3 : Commute (spinSDot a b 2 * spinSDot a b 2 : ManyBodyOpS (Fin L) 2) (spinSDot c d 2) :=
    h.mul_left h
  have h4 : Commute (spinSDot a b 2 * spinSDot a b 2 : ManyBodyOpS (Fin L) 2)
      (spinSDot c d 2 * spinSDot c d 2) := h2.mul_left h2
  simp only [bondSpin2ProjectionS]
  refine Commute.add_left (Commute.add_left ?_ ?_) ?_
  · refine Commute.add_right (Commute.add_right ?_ ?_) ?_
    · exact (h.smul_left _).smul_right _
    · exact (h2.smul_left _).smul_right _
    · exact ((Commute.one_right _).smul_left _).smul_right _
  · refine Commute.add_right (Commute.add_right ?_ ?_) ?_
    · exact (h3.smul_left _).smul_right _
    · exact (h4.smul_left _).smul_right _
    · exact ((Commute.one_right _).smul_left _).smul_right _
  · refine Commute.add_right (Commute.add_right ?_ ?_) ?_
    · exact ((Commute.one_left _).smul_left _).smul_right _
    · exact ((Commute.one_left _).smul_left _).smul_right _
    · exact ((Commute.one_left _).smul_left _).smul_right _

/-! ## A7: the product of two disjoint bond projections is positive semidefinite -/

/-- **The product of two bond projections on four distinct sites is positive semidefinite**
(design item A7). Under the six distinctness hypotheses the two projections commute, so their
product `M = P̂_{a,b} P̂_{c,d}` is again a Hermitian idempotent, whence `M = Mᴴ M ≥ 0`. This is the
fact that lets Stage C discard the offset sums `D_d` with `d ∉ {0, 1, −1}` from Tasaki's
eq. (7.1.36) — precisely the sums whose two bonds are disjoint. It is *not* available for
`d = ±1`, where the two bonds overlap in one site and the product is not even Hermitian. -/
theorem posSemidef_bondSpin2ProjectionS_mul {L : ℕ} {a b c d : Fin L}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d :
        ManyBodyOpS (Fin L) 2).PosSemidef := by
  have hcomm : Commute (bondSpin2ProjectionS a b : ManyBodyOpS (Fin L) 2)
      (bondSpin2ProjectionS c d) := bondSpin2ProjectionS_commute_of_disjoint hac had hbc hbd
  have hH : (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d :
      ManyBodyOpS (Fin L) 2).IsHermitian :=
    (bondSpin2ProjectionS_isHermitian a b).mul_of_commute
      (bondSpin2ProjectionS_isHermitian c d) hcomm.eq
  have hidem : (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d :
        ManyBodyOpS (Fin L) 2) * (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d)
      = bondSpin2ProjectionS a b * bondSpin2ProjectionS c d := by
    calc (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d :
            ManyBodyOpS (Fin L) 2) * (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d)
        = bondSpin2ProjectionS a b * (bondSpin2ProjectionS c d * bondSpin2ProjectionS a b)
            * bondSpin2ProjectionS c d := by simp only [mul_assoc]
      _ = bondSpin2ProjectionS a b * (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d)
            * bondSpin2ProjectionS c d := by rw [hcomm.eq]
      _ = (bondSpin2ProjectionS a b * bondSpin2ProjectionS a b)
            * (bondSpin2ProjectionS c d * bondSpin2ProjectionS c d) := by simp only [mul_assoc]
      _ = bondSpin2ProjectionS a b * bondSpin2ProjectionS c d := by
            rw [bondSpin2ProjectionS_mul_self hab, bondSpin2ProjectionS_mul_self hcd]
  have key : Matrix.conjTranspose (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d :
        ManyBodyOpS (Fin L) 2) * (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d)
      = bondSpin2ProjectionS a b * bondSpin2ProjectionS c d := by
    rw [hH.eq, hidem]
  exact key ▸ Matrix.posSemidef_conjTranspose_mul_self
    (bondSpin2ProjectionS a b * bondSpin2ProjectionS c d : ManyBodyOpS (Fin L) 2)

/-! ## A8–A9 (design item B5f): the block embedding preserves positive semidefiniteness -/

section Embedding

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N m : ℕ}

/-- **The block embedding commutes with the conjugate transpose** (design item A8). The spectator
guard `∀ k ∉ range ι, σ' k = σ k` of `onEmbS` is symmetric in its two configurations, so
transposing the embedded operator is the same as embedding the transposed one. No injectivity is
needed. (The `ᴴ` postfix does not parse inside this namespace, so `Matrix.conjTranspose` is
spelled out.) -/
theorem onEmbS_conjTranspose (ι : Fin m → Λ)
    (A : Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ) :
    (onEmbS ι (Matrix.conjTranspose A) : ManyBodyOpS Λ N)
      = Matrix.conjTranspose (onEmbS ι A) := by
  ext σ' σ
  simp only [Matrix.conjTranspose_apply, onEmbS_apply]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (fun k hk => (h1 k hk).symm) h2
  · exact absurd (fun k hk => (h2 k hk).symm) h1
  · exact (star_zero ℂ).symm

/-- **The block embedding preserves positive semidefiniteness** (design item B5f/A9). If the
`m`-site operator `A` is positive semidefinite, so is the many-body operator `onEmbS ι A` obtained
by letting `A` act on the sites listed by an injective `ι` and the identity elsewhere. The proof
does *not* decompose the embedding into blocks: it writes `A = Cᴴ C` with `C = √A` (Tasaki
Lemma A.6) and transports the product through the ring homomorphism property `onEmbS_mul`, so
that `onEmbS ι A = (onEmbS ι C)ᴴ (onEmbS ι C)`. Injectivity of `ι` enters exactly once, inside
`onEmbS_mul`.

This is what carries the four-site Knabe certificate `ĥ² − (2/5) ĥ ≥ 0` (Tasaki eq. (7.1.30),
`ℓ = 3`) to every window of a chain of any length. -/
theorem onEmbS_posSemidef {ι : Fin m → Λ} (hι : Function.Injective ι)
    {A : Matrix (Fin m → Fin (N + 1)) (Fin m → Fin (N + 1)) ℂ} (hA : A.PosSemidef) :
    (onEmbS ι A : ManyBodyOpS Λ N).PosSemidef := by
  obtain ⟨C, hC, rfl⟩ := LatticeSystem.Math.exists_posSemidef_sq_eq_of_posSemidef hA
  have hCH : Matrix.conjTranspose C = C := hC.isHermitian
  have key : (onEmbS ι (C * C) : ManyBodyOpS Λ N)
      = Matrix.conjTranspose (onEmbS ι C) * onEmbS ι C := by
    rw [← onEmbS_conjTranspose, onEmbS_mul hι, hCH]
  rw [key]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end Embedding

end LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
