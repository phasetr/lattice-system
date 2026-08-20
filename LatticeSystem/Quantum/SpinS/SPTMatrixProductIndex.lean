import LatticeSystem.Quantum.SpinS.MPSInvarianceGauge
import LatticeSystem.Quantum.SpinS.SpinSPiRotation

/-!
# Tasaki §8.3.4–§8.3.5: the matrix-product SPT index (Theorem 8.7)

For matrix product states the heuristic entanglement indices of §8.3.3 become a precise invariant.
A protecting symmetry `g ∈ G` acts on a spin chain through a unitary or antiunitary operator
`v̂(g)` on the **single-spin** space `h₀ ≅ ℂ^{2S+1}` (p. 277: "take a unitary operator `û(g)` on
the single-spin Hilbert space"), and these operators compose only up to a phase,
`û(g) C_g[û(h)] = e^{iφ̃(g,h)} û(gh)` (eq. (8.3.42)).  The projective representation is **trivial**
exactly when its phase function is a coboundary, `φ̃(g,h) = ψ̃(g) + s(g)ψ̃(h) − ψ̃(gh)`
(eq. (8.3.43)); the cohomology class of `φ̃` is the matrix-product SPT index.  The definitions and
that equivalence live in `LatticeSystem.Math.ProjectiveRepresentation`.

**Theorem 8.7** (Tachikawa, p. 278): if an injective matrix product state is invariant up to a phase
under the symmetry, `V̂(g)|Φ_L⟩ = e^{iη_L(g)}|Φ_L⟩` for all `g` and all `L`, then the on-site
projective representation is trivial.

**Corollary 8.5** (p. 276): for half-odd-integer spin the `Z₂ × Z₂` representation by the `π`
rotations `{1̂, û₁, û₂, û₃}` is nontrivial (eq. (2.1.31)), so no `Z₂ × Z₂`-invariant injective
matrix product state exists — the matrix-product form of the Lieb–Schultz–Mattis no-go.  The
closed-form rotations live in `LatticeSystem.Quantum.SpinSPiRotation` and the generic `Z₂ × Z₂`
package in `LatticeSystem.Math.ProjectiveRepresentation`.

## The route taken here

The book inverts the gauge relation (8.3.48) into (8.3.50), substitutes that relation into itself
and reads off (8.3.54).  The same conclusion is reached here by running the chase **forwards**,
which needs neither antilinear operators nor the conventions of Appendix A.4.3:

* `symmetryTransportMPS_mul_of_isProjectiveRep` — transporting by `h` and then by `g` is
  transporting by `gh` up to the phase `φ(g,h)` (this replaces (8.3.51)–(8.3.52));
* `symmetryTransportMPS_conj` (in `SPTSymmetryTransportedMPS`) — a transport moves through the
  gauge relation (8.3.48), producing per-`σ` equalities rather than the book's equality of two sums
  over `σ'`, which would additionally need the mixing matrix to be invertible;
* comparing the two evaluations conjugates `A^σ` by one unitary `W = U(g) C_g[U(h)] U†(gh)` and
  rescales it by one phase `c`, the `W†A^σW = cA^σ` of footnote 52 (p. 280);
* `eq_one_of_unitary_conj_smul` — that phase is `1`.  Footnote 52 gets there through
  Theorem 7.5(i) plus the centrality of `W`; using Theorem 7.5(ii) instead, `c^ℓ = 1` holds at two
  consecutive lengths, which already forces `c = 1`.

The conclusion `φ(g,h) = ζ(g) ζ(h)^{s(g)} ζ(gh)⁻¹` is eq. (8.3.54), i.e. literally
`IsPhaseCoboundary`, so `isTrivialProjectiveRep_iff_isPhaseCoboundary` closes Theorem 8.7.  The
group is an arbitrary group rather than the book's finite `G` (p. 277): finiteness is never used.
The invariance hypothesis is recorded on the periodic trace coefficients rather than as an operator
identity on `⊗_x h_x`, which is the convention of the whole MPS layer (Theorem 7.6,
`GeneratesPhasedMPS`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.4, eqs. (8.3.13)–(8.3.16), pp. 264–265; §8.3.5, Theorem 8.7, eqs. (8.3.40)–(8.3.54) and
footnotes 50–52, pp. 276–280; §7.2.2, Theorems 7.5 and 7.6, pp. 202–203; F. Pollmann, A. M. Turner,
E. Berg, M. Oshikawa, Phys. Rev. B **85**, 075125 (2012); X. Chen, Z.-C. Gu, X.-G. Wen, Phys. Rev.
B **83**, 035107 (2011).
-/

namespace LatticeSystem.Quantum

open Matrix
open LatticeSystem.Math (IsProjectiveRep IsTrivialProjectiveRep IsPhaseCoboundary signConjMatrix
  signConjMatrix_mem_unitaryGroup isTrivialProjectiveRep_iff_isPhaseCoboundary anticommPairRep
  exists_isProjectiveRep_anticommPairRep not_isTrivialProjectiveRep_anticommPairRep)

variable {D N : ℕ}

/-! ## Footnote 52 (p. 280): the leftover phase is `1` -/

/-- Conjugation by a unitary `T` that rescales every matrix of an MPS family by a phase `c`
rescales every ordered product by `c` to the power of the word length. -/
private theorem conj_orderedProd_of_conj_smul {A : MPSMatrices D N}
    {T : Matrix (Fin D) (Fin D) ℂ} (hT : T ∈ Matrix.unitaryGroup (Fin D) ℂ) {c : Circle}
    (h : ∀ σ, T.conjTranspose * A σ * T = (c : ℂ) • A σ) (w : List (Fin (N + 1))) :
    T.conjTranspose * orderedProd A w * T = ((c ^ w.length : Circle) : ℂ) • orderedProd A w := by
  have hTT : T * T.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hT
  have hTT' : T.conjTranspose * T = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hT
  induction w with
  | nil =>
      change T.conjTranspose * 1 * T = ((c ^ 0 : Circle) : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ)
      rw [Matrix.mul_one, hTT', pow_zero, Circle.coe_one, one_smul]
  | cons σ ss ih =>
      change T.conjTranspose * (A σ * orderedProd A ss) * T = _
      calc T.conjTranspose * (A σ * orderedProd A ss) * T
          = T.conjTranspose * A σ * T * (T.conjTranspose * orderedProd A ss * T) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc T T.conjTranspose, hTT, Matrix.one_mul]
        _ = ((c : ℂ) • A σ) * (((c ^ ss.length : Circle) : ℂ) • orderedProd A ss) := by
            rw [h σ, ih]
        _ = ((c ^ (σ :: ss).length : Circle) : ℂ) • (A σ * orderedProd A ss) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, List.length_cons, pow_succ,
              Circle.coe_mul, mul_comm]

/-- **Tasaki footnote 52, p. 280.**  A unitary that conjugates every matrix of an injective MPS
family into one and the same multiple `c` of itself has `c = 1`.

The printed argument runs `W†A^{σ_1}⋯A^{σ_{ℓ_0}}W = c^{ℓ_0}A^{σ_1}⋯A^{σ_{ℓ_0}}`, invokes
Theorem 7.5(i) to get `W†MW = c^{ℓ_0}M` for **every** matrix `M`, concludes `W = t·1̂` and reads
`c = 1` off `W†A^σW = cA^σ`.  Theorem 7.5(ii) — spanning at every sufficiently large length — makes
the centrality step unnecessary: taking `M = 1` gives `c^ℓ = 1` at two consecutive lengths. -/
theorem eq_one_of_unitary_conj_smul {A : MPSMatrices D N} {lam : ℝ} (hA : IsInjectiveMPS A lam)
    {T : Matrix (Fin D) (Fin D) ℂ} (hT : T ∈ Matrix.unitaryGroup (Fin D) ℂ) {c : Circle}
    (h : ∀ σ, T.conjTranspose * A σ * T = (c : ℂ) • A σ) : c = 1 := by
  have hTT' : T.conjTranspose * T = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hT
  haveI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (pos_of_isInjectiveMPS hA)
  have hpow : ∀ ℓ : ℕ, mpsProductsSpanAt A ℓ → c ^ ℓ = 1 := by
    intro ℓ hspan
    have hspan' : Submodule.span ℂ {P : Matrix (Fin D) (Fin D) ℂ |
        ∃ σs : List (Fin (N + 1)), σs.length = ℓ ∧ P = orderedProd A σs} = ⊤ := hspan
    have hall : ∀ M : Matrix (Fin D) (Fin D) ℂ,
        T.conjTranspose * M * T = ((c ^ ℓ : Circle) : ℂ) • M := by
      intro M
      have hM : M ∈ Submodule.span ℂ {P : Matrix (Fin D) (Fin D) ℂ |
          ∃ σs : List (Fin (N + 1)), σs.length = ℓ ∧ P = orderedProd A σs} := by
        rw [hspan']
        exact Submodule.mem_top
      induction hM using Submodule.span_induction with
      | mem P hP =>
          obtain ⟨σs, hlen, rfl⟩ := hP
          subst hlen
          exact conj_orderedProd_of_conj_smul hT h σs
      | zero => simp
      | add X Y _ _ hX hY => rw [Matrix.mul_add, Matrix.add_mul, hX, hY, smul_add]
      | smul a X _ hX => rw [Matrix.mul_smul, Matrix.smul_mul, hX, smul_comm]
    have hone := hall 1
    rw [Matrix.mul_one, hTT'] at hone
    obtain ⟨i⟩ := ‹Nonempty (Fin D)›
    have hentry := congrFun (congrFun hone i) i
    simp only [Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one] at hentry
    exact Circle.coe_injective (by rw [Circle.coe_one]; exact hentry.symm)
  obtain ⟨ℓ₀, hlarge⟩ := hA.2.2.1
  have h1 : c ^ ℓ₀ = 1 := hpow ℓ₀ (hlarge ℓ₀ le_rfl)
  have h2 : c ^ (ℓ₀ + 1) = 1 := hpow (ℓ₀ + 1) (hlarge (ℓ₀ + 1) (Nat.le_succ ℓ₀))
  rwa [pow_succ, h1, one_mul] at h2

/-! ## The forward cocycle chase (eqs. (8.3.49)–(8.3.54)) -/

/-- **The composition law of the symmetry transport.**  For a projective representation,
transporting by `h` and then by `g` is transporting by `gh`, up to the phase `φ(g,h)` of
eq. (8.3.42).  This replaces the book's (8.3.51)–(8.3.52): the mixing matrices compose as
`û(g) C_g[û(h)]`, the signs compose because `s` is a homomorphism, and eq. (8.3.42) turns the
composite into a multiple of `û(gh)`. -/
theorem symmetryTransportMPS_mul_of_isProjectiveRep {G : Type*} [Group G] {N : ℕ}
    {u : G → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} {s : G →* ℤˣ} {φ : G → G → Circle}
    (hrep : IsProjectiveRep u s φ) (g h : G) {D : ℕ} (A : MPSMatrices D N) :
    symmetryTransportMPS (s g) (u g) (symmetryTransportMPS (s h) (u h) A) =
      fun σ => (φ g h : ℂ) • symmetryTransportMPS (s (g * h)) (u (g * h)) A σ := by
  rw [symmetryTransportMPS_symmetryTransportMPS, hrep.2.2 g h, ← map_mul s g h,
    symmetryTransportMPS, mpsMix_smul]
  rfl

/-- Two unitary gauges realising the same family up to phases differ by a single conjugation that
rescales every matrix by one phase — the `W†A^σW = cA^σ` of footnote 52 (p. 280), with
`W = U(g) C_g[U(h)] U†(gh)`. -/
private theorem conj_smul_of_gauge_eq {A : MPSMatrices D N} {a b : Circle}
    {X Y : Matrix (Fin D) (Fin D) ℂ} (hX : X ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (h : ∀ σ, (a : ℂ) • (X.conjTranspose * A σ * X) =
      (b : ℂ) • (Y.conjTranspose * A σ * Y)) (σ : Fin (N + 1)) :
    (Y * X.conjTranspose).conjTranspose * A σ * (Y * X.conjTranspose) =
      ((a * b⁻¹ : Circle) : ℂ) • A σ := by
  have hXX : X * X.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hX
  have hcancel : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      X * (X.conjTranspose * M * X) * X.conjTranspose = M := by
    intro M
    simp only [Matrix.mul_assoc]
    rw [hXX, Matrix.mul_one, ← Matrix.mul_assoc, hXX, Matrix.one_mul]
  have hTconj : (Y * X.conjTranspose).conjTranspose * A σ * (Y * X.conjTranspose) =
      X * (Y.conjTranspose * A σ * Y) * X.conjTranspose := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hscaled : (b : ℂ) •
      ((Y * X.conjTranspose).conjTranspose * A σ * (Y * X.conjTranspose)) = (a : ℂ) • A σ := by
    rw [hTconj, ← Matrix.smul_mul, ← Matrix.mul_smul, ← h σ, Matrix.mul_smul, Matrix.smul_mul,
      hcancel]
  have hZ : (Y * X.conjTranspose).conjTranspose * A σ * (Y * X.conjTranspose) =
      ((b⁻¹ * a : Circle) : ℂ) • A σ := by
    rw [Circle.coe_mul, ← smul_smul, ← hscaled, smul_smul, ← Circle.coe_mul, inv_mul_cancel,
      Circle.coe_one, one_smul]
  rw [hZ, mul_comm b⁻¹ a]

/-- **Tasaki eqs. (8.3.49)–(8.3.54), run forwards.**  If a projective representation leaves an
injective matrix product state invariant up to a phase — the hypothesis (8.3.45) of Theorem 8.7,
recorded on the periodic trace coefficients — then its phase function is a coboundary, which is
eq. (8.3.54) with `ψ̃ = ζ`.

The gauge `ζ(g), U(g)` of eq. (8.3.48) is chosen once per group element
(`exists_unitary_gauge_of_invariance`); no coherence between the choices is needed, because the
ambiguity is exactly what `eq_one_of_unitary_conj_smul` removes. -/
theorem isPhaseCoboundary_of_invariantInjectiveMPS {G : Type*} [Group G] {N : ℕ}
    {u : G → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} {s : G →* ℤˣ} {φ : G → G → Circle}
    {D : ℕ} {A : MPSMatrices D N} {lam : ℝ} (hrep : IsProjectiveRep u s φ)
    (hA : IsInjectiveMPS A lam)
    (hinv : ∀ g, ∃ η : ℕ → Circle,
      GeneratesPhasedMPS A (symmetryTransportMPS (s g) (u g) A) η) :
    IsPhaseCoboundary s φ := by
  have hgaugeEx : ∀ g : G, ∃ (z : Circle) (U : Matrix (Fin D) (Fin D) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        ∀ σ, symmetryTransportMPS (s g) (u g) A σ =
          (z : ℂ) • (U.conjTranspose * A σ * U) := by
    intro g
    obtain ⟨η, hη⟩ := hinv g
    obtain ⟨z, U, hU⟩ := exists_unitary_gauge_of_invariance A lam hA (s g) (u g) (hrep.1 g) η hη
    exact ⟨z, (U : Matrix (Fin D) (Fin D) ℂ), U.2, hU⟩
  choose ζ V hV hgauge using hgaugeEx
  refine ⟨ζ, fun g h => ?_⟩
  have hgh : ∀ σ, symmetryTransportMPS (s g) (u g) (symmetryTransportMPS (s h) (u h) A) σ =
      ((φ g h * ζ (g * h) : Circle) : ℂ) •
        ((V (g * h)).conjTranspose * A σ * V (g * h)) := by
    intro σ
    rw [congrFun (symmetryTransportMPS_mul_of_isProjectiveRep hrep g h A) σ, hgauge (g * h) σ,
      smul_smul, Circle.coe_mul]
  have hW : ∀ σ, symmetryTransportMPS (s g) (u g) (symmetryTransportMPS (s h) (u h) A) σ =
      ((ζ g * ζ h ^ (s g : ℤ) : Circle) : ℂ) •
        ((V g * signConjMatrix (s g) (V h)).conjTranspose * A σ *
          (V g * signConjMatrix (s g) (V h))) := by
    intro σ
    have hstep : symmetryTransportMPS (s h) (u h) A =
        fun τ => ((ζ h : Circle) : ℂ) • ((V h).conjTranspose * A τ * V h) :=
      funext (hgauge h)
    rw [hstep, congrFun (symmetryTransportMPS_conj (s g) (u g) (ζ h) (V h) A) σ, hgauge g σ,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, Circle.coe_mul, Matrix.conjTranspose_mul,
      mul_comm ((ζ h ^ (s g : ℤ) : Circle) : ℂ)]
    simp only [Matrix.mul_assoc]
  have hTmem : V g * signConjMatrix (s g) (V h) * (V (g * h)).conjTranspose ∈
      Matrix.unitaryGroup (Fin D) ℂ := by
    refine mul_mem (mul_mem (hV g) (signConjMatrix_mem_unitaryGroup _ (hV h))) ?_
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (hV (g * h))
  have hone : φ g h * ζ (g * h) * (ζ g * ζ h ^ (s g : ℤ))⁻¹ = 1 :=
    eq_one_of_unitary_conj_smul hA hTmem
      (conj_smul_of_gauge_eq (hV (g * h)) fun σ => (hgh σ).symm.trans (hW σ))
  have hbal : φ g h * ζ (g * h) = ζ g * ζ h ^ (s g : ℤ) := by
    rwa [mul_inv_eq_one] at hone
  rw [← hbal, mul_inv_cancel_right]

/-! ## The statement of Theorem 8.7 -/

/-- **Tasaki eq. (8.3.45).**  There is a translation-invariant injective matrix product state that
is invariant, up to a length-dependent phase, under every element of the symmetry group acting by
`u` with sign character `s`.

Two conventions are inherited from the MPS layer: the invariance is recorded on the periodic trace
coefficients (`GeneratesPhasedMPS`) rather than as an operator identity for `V̂(g)` on `⊗_x h_x`,
and the matrices are site-independent, matching (8.3.11) and the "translation invariant injective
matrix product states" of p. 276.  No `0 < D` conjunct is needed: `IsInjectiveMPS` already forces
it (`pos_of_isInjectiveMPS`), and adding it by hand would silently weaken the theorem. -/
def SymmetricInjectiveMPSExists {G : Type*} [Group G] {N : ℕ}
    (u : G → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (s : G →* ℤˣ) : Prop :=
  ∃ (D : ℕ) (A : MPSMatrices D N) (lam : ℝ), IsInjectiveMPS A lam ∧
    ∀ g, ∃ η : ℕ → Circle, GeneratesPhasedMPS A (symmetryTransportMPS (s g) (u g) A) η

/-- **Tasaki Theorem 8.7 (matrix-product SPT index, Tachikawa), p. 278.**  If there is an injective
matrix product state invariant up to a phase under the symmetry, then the on-site projective
representation is **trivial**.  Contrapositive: a nontrivial projective representation forbids any
symmetric injective MPS, the defining obstruction of a nontrivial SPT phase. -/
theorem tasaki_theorem_8_7 {G : Type*} [Group G] {N : ℕ}
    {u : G → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} {s : G →* ℤˣ} {φ : G → G → Circle}
    (hrep : IsProjectiveRep u s φ) :
    SymmetricInjectiveMPSExists u s → IsTrivialProjectiveRep u s := by
  rintro ⟨D, A, lam, hA, hinv⟩
  exact (isTrivialProjectiveRep_iff_isPhaseCoboundary hrep).mpr
    (isPhaseCoboundary_of_invariantInjectiveMPS hrep hA hinv)

/-! ## Corollary 8.5: no `Z₂ × Z₂`-symmetric injective MPS at half-odd-integer spin -/

/-- **The on-site `Z₂ × Z₂` projective representation of eq. (2.1.29)** for spin `S = N/2`: the
group acts by the `π` rotations `û₁` and `û₃` and by their product, a multiple of `û₂`. -/
noncomputable def z2z2SpinRep (N : ℕ) :
    Multiplicative (ZMod 2 × ZMod 2) → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  anticommPairRep (spinSPiRotation1 N) (spinSPiRotation3 N)

/-- **Tasaki Corollary 8.5 (the matrix-product Lieb–Schultz–Mattis no-go), p. 276.**  For
half-odd-integer spin (`S = N/2` with `N` odd) there is **no** `Z₂ × Z₂`-invariant injective matrix
product state.

This is the contrapositive of Theorem 8.7: a symmetric injective MPS would force the on-site
`Z₂ × Z₂` projective representation to be trivial, whereas at odd `N` the `π` rotations anticommute
(eq. (2.1.31)) while a trivial representation of a commutative group has commuting images. -/
theorem tasaki_corollary_8_5 (N : ℕ) (hN : Odd N) :
    ¬ SymmetricInjectiveMPSExists (z2z2SpinRep N)
      (1 : Multiplicative (ZMod 2 × ZMod 2) →* ℤˣ) := by
  obtain ⟨φ, hrep⟩ := exists_isProjectiveRep_anticommPairRep
    (spinSPiRotation1_mem_unitaryGroup N) (spinSPiRotation3_mem_unitaryGroup N)
    (spinSPiRotation1_mul_self_of_odd hN) (spinSPiRotation3_mul_self_of_odd hN)
    (spinSPiRotation3_mul_spinSPiRotation1_of_odd hN)
  exact fun hMPS => not_isTrivialProjectiveRep_anticommPairRep
    (spinSPiRotation1_mem_unitaryGroup N) (spinSPiRotation3_mem_unitaryGroup N)
    (spinSPiRotation3_mul_spinSPiRotation1_of_odd hN) (tasaki_theorem_8_7 hrep hMPS)

end LatticeSystem.Quantum
