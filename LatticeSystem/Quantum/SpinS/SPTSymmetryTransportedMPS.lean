import LatticeSystem.Math.ProjectiveRepresentation
import LatticeSystem.Quantum.SpinS.MPSTheorem75Defs

/-!
# Symmetry-transported matrix product states

Tasaki's symmetry transformation of an MPS family: a symmetry operation `v̂(g)` acting on the
single-site space sends the matrices `(A^σ)_{σ}` to
`Ã_g^σ = Σ_{σ'} ⟨ψ^σ|û(g)|ψ^{σ'}⟩ C_g[A^{σ'}]` (eq. (8.3.47)), where `C_g` is the entrywise
conjugation of eq. (8.3.40), trivial for a unitary `v̂(g)` and complex conjugation for an
antiunitary one.  For `s = 1` this is eq. (8.3.13), and for the `S = 1` time reversal it is
eq. (8.3.33).

The transformation is staged as a conjugation `mpsConjugate` followed by a mixing `mpsMix` of the
single-site index, because each of the four conditions defining `IsInjectiveMPS` is transported one
stage at a time: the transport is inverted by a second transport, with the adjoint of the
conjugated mixing matrix (which is what makes the spanning conditions transport), while the
conjugation acts on the transfer matrix and hence on its spectrum and eigenspaces.  The result is
the book's repeated but unproved assertion that the transported family is again injective.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.4, eqs. (8.3.13)–(8.3.14), pp. 264–265; §8.3.5, eq. (8.3.33), p. 273, and eq. (8.3.47),
p. 279.
-/

namespace LatticeSystem.Quantum

open Matrix Module
open LatticeSystem.Math (signConj signConjMatrix signConj_one_apply signConj_neg_one_apply
  signConj_circle signConj_signConj signConjMatrix_smul signConjMatrix_one_apply
  signConjMatrix_signConjMatrix signConjMatrix_signConjMatrix_mul
  signConjMatrix_conjTranspose signConjMatrix_mem_unitaryGroup mem_spectrum_signConjMatrix_iff
  norm_signConj finrank_ker_mulVecLin_signConjMatrix)

variable {D N : ℕ}

/-! ## The transformation and its algebra -/

/-- The entrywise conjugation `C_g` of eq. (8.3.40) applied to a whole MPS family. -/
noncomputable def mpsConjugate (ε : ℤˣ) (A : MPSMatrices D N) : MPSMatrices D N :=
  fun σ => signConjMatrix ε (A σ)

/-- Mixing of an MPS family along the single-site index, `(mpsMix u A)^σ = Σ_{σ'} u_{σσ'} A^{σ'}`.
The row index of `u` carries the *new* spin label, matching the book's coefficient
`⟨ψ^σ|û(g)|ψ^{σ'}⟩` in eq. (8.3.47). -/
noncomputable def mpsMix (u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (A : MPSMatrices D N) :
    MPSMatrices D N :=
  fun σ => ∑ σ' : Fin (N + 1), u σ σ' • A σ'

/-- **Tasaki eq. (8.3.47)**: the symmetry-transported MPS family
`Ã_g^σ = Σ_{σ'} ⟨ψ^σ|û(g)|ψ^{σ'}⟩ C_g[A^{σ'}]`, with `ε = s(g)` recording whether the symmetry
operation is unitary (`ε = 1`, eq. (8.3.13)) or antiunitary (`ε = -1`, eq. (8.3.33)). -/
noncomputable def symmetryTransportMPS (ε : ℤˣ) (u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (A : MPSMatrices D N) : MPSMatrices D N :=
  mpsMix u (mpsConjugate ε A)

/-- Mixing is a left action of the matrix ring on MPS families: mixing by `v` and then by `u` is
mixing by `u * v` (covariant composition). -/
lemma mpsMix_mpsMix (u v : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (A : MPSMatrices D N) :
    mpsMix u (mpsMix v A) = mpsMix (u * v) A := by
  funext σ
  simp only [mpsMix, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

/-- Mixing by the identity matrix leaves the family unchanged. -/
lemma mpsMix_one (A : MPSMatrices D N) : mpsMix 1 A = A := by
  funext σ
  simp [mpsMix, Matrix.one_apply, ite_smul]

/-- Mixing is homogeneous in the mixing matrix: rescaling `u` rescales the mixed family.  This is
what turns the phase of eq. (8.3.42) into a phase of the transported family. -/
lemma mpsMix_smul (z : ℂ) (u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (A : MPSMatrices D N) :
    mpsMix (z • u) A = fun σ => z • mpsMix u A σ := by
  funext σ
  simp only [mpsMix, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

/-- The conjugation moves past a mixing at the cost of conjugating the mixing matrix. -/
lemma mpsConjugate_mpsMix (ε : ℤˣ) (u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (A : MPSMatrices D N) :
    mpsConjugate ε (mpsMix u A) = mpsMix (signConjMatrix ε u) (mpsConjugate ε A) := by
  funext σ
  change signConjMatrix ε (∑ σ' : Fin (N + 1), u σ σ' • A σ') =
    ∑ σ' : Fin (N + 1), signConjMatrix ε u σ σ' • signConjMatrix ε (A σ')
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  rw [signConjMatrix_smul]
  congr 1

/-- Iterating the conjugation multiplies the signs, `C_ε ∘ C_δ = C_{εδ}`, on MPS families. -/
lemma mpsConjugate_mpsConjugate_mul (ε δ : ℤˣ) (A : MPSMatrices D N) :
    mpsConjugate ε (mpsConjugate δ A) = mpsConjugate (ε * δ) A :=
  funext fun σ => signConjMatrix_signConjMatrix_mul ε δ (A σ)

/-- The conjugation is an involution on MPS families. -/
lemma mpsConjugate_mpsConjugate (ε : ℤˣ) (A : MPSMatrices D N) :
    mpsConjugate ε (mpsConjugate ε A) = A := by
  rw [mpsConjugate_mpsConjugate_mul, Int.units_mul_self]
  exact funext fun σ => signConjMatrix_one_apply (A σ)

/-- Transporting twice multiplies the signs and composes the mixing matrices, the second one
twisted by the outer sign.  Taking `δ = ε` and `u` to be the adjoint of `C_g[v]` recovers the
original family; this inverse transport is what `mpsProductsSpanAt_symmetryTransportMPS` runs
backwards along to pull the spanning conditions from `A` to `Ã_g`.  For a projective
representation the composed mixing matrix is again a member of the family, up to the phase of
eq. (8.3.42). -/
lemma symmetryTransportMPS_symmetryTransportMPS (ε δ : ℤˣ)
    (u v : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (A : MPSMatrices D N) :
    symmetryTransportMPS ε u (symmetryTransportMPS δ v A) =
      symmetryTransportMPS (ε * δ) (u * signConjMatrix ε v) A := by
  simp only [symmetryTransportMPS]
  rw [mpsConjugate_mpsMix, mpsConjugate_mpsConjugate_mul, mpsMix_mpsMix]

/-- **Transport of a phased conjugate family** (the computation behind eqs. (8.3.49)–(8.3.50)).
The transport passes through an overall phase `z` and a gauge conjugation by `V`: the phase picks
up the sign twist `z ↦ z^{s(g)}` and the gauge matrix is conjugated to `C_g[V]`.  Applied to the
gauge relation (8.3.48) this is what lets two transports be compared without ever inverting
it. -/
lemma symmetryTransportMPS_conj (ε : ℤˣ) (u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (z : Circle)
    (V : Matrix (Fin D) (Fin D) ℂ) (A : MPSMatrices D N) :
    symmetryTransportMPS ε u (fun σ => (z : ℂ) • (V.conjTranspose * A σ * V)) =
      fun σ => ((z ^ (ε : ℤ) : Circle) : ℂ) •
        ((signConjMatrix ε V).conjTranspose * symmetryTransportMPS ε u A σ *
          signConjMatrix ε V) := by
  funext σ
  have hterm : ∀ σ' : Fin (N + 1),
      u σ σ' • signConjMatrix ε ((z : ℂ) • (V.conjTranspose * A σ' * V)) =
        ((z ^ (ε : ℤ) : Circle) : ℂ) • ((signConjMatrix ε V).conjTranspose *
          (u σ σ' • signConjMatrix ε (A σ')) * signConjMatrix ε V) := by
    intro σ'
    rw [signConjMatrix_smul, signConj_circle, map_mul, map_mul, ← signConjMatrix_conjTranspose,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
  have hmix : symmetryTransportMPS ε u A σ =
      ∑ σ' : Fin (N + 1), u σ σ' • signConjMatrix ε (A σ') := rfl
  change (∑ σ' : Fin (N + 1),
      u σ σ' • signConjMatrix ε ((z : ℂ) • (V.conjTranspose * A σ' * V))) = _
  rw [hmix, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun σ' _ => hterm σ'

/-! ## Transport of the spanning conditions -/

/-- Ordered products of a conjugated family are the conjugates of the ordered products. -/
lemma orderedProd_mpsConjugate (ε : ℤˣ) (A : MPSMatrices D N) (w : List (Fin (N + 1))) :
    orderedProd (mpsConjugate ε A) w = signConjMatrix ε (orderedProd A w) := by
  induction w with
  | nil => simp [orderedProd]
  | cons σ ss ih =>
      change mpsConjugate ε A σ * orderedProd (mpsConjugate ε A) ss = _
      rw [ih, show orderedProd A (σ :: ss) = A σ * orderedProd A ss from rfl, map_mul]
      rfl

/-- Ordered products of a mixed family lie in the span of the ordered products of the original
family of the same length. -/
private lemma orderedProd_mpsMix_mem_span (u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (A : MPSMatrices D N) (w : List (Fin (N + 1))) :
    orderedProd (mpsMix u A) w ∈ Submodule.span ℂ {P : Matrix (Fin D) (Fin D) ℂ |
      ∃ σs : List (Fin (N + 1)), σs.length = w.length ∧ P = orderedProd A σs} := by
  induction w with
  | nil => exact Submodule.subset_span ⟨[], rfl, rfl⟩
  | cons σ ss ih =>
      have hstep : orderedProd (mpsMix u A) (σ :: ss) =
          ∑ σ' : Fin (N + 1), u σ σ' • (A σ' * orderedProd (mpsMix u A) ss) := by
        change (∑ σ' : Fin (N + 1), u σ σ' • A σ') * orderedProd (mpsMix u A) ss = _
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun σ' _ => Matrix.smul_mul _ _ _
      rw [hstep, List.length_cons]
      exact Submodule.sum_mem _ fun σ' _ =>
        Submodule.smul_mem _ _ (orderedProd_mul_mem_span_succ A ss.length σ' ih)

/-- Spanning at a given length is inherited by a conjugated family, since entrywise conjugation is
a conjugate-linear involution of the matrix space. -/
private lemma mpsProductsSpanAt_mpsConjugate (ε : ℤˣ) {A : MPSMatrices D N} {ℓ : ℕ}
    (hspan : mpsProductsSpanAt A ℓ) : mpsProductsSpanAt (mpsConjugate ε A) ℓ := by
  unfold mpsProductsSpanAt at hspan ⊢
  rw [Submodule.eq_top_iff'] at hspan ⊢
  intro M
  set W : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Submodule.span ℂ {P : Matrix (Fin D) (Fin D) ℂ |
      ∃ σs : List (Fin (N + 1)), σs.length = ℓ ∧ P = orderedProd (mpsConjugate ε A) σs}
  have key : ∀ Y ∈ Submodule.span ℂ {P : Matrix (Fin D) (Fin D) ℂ |
      ∃ σs : List (Fin (N + 1)), σs.length = ℓ ∧ P = orderedProd A σs},
      signConjMatrix ε Y ∈ W := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem P hP =>
        obtain ⟨σs, hlen, rfl⟩ := hP
        exact Submodule.subset_span ⟨σs, hlen, (orderedProd_mpsConjugate ε A σs).symm⟩
    | zero => simpa only [map_zero] using W.zero_mem
    | add X Y _ _ hX hY => simpa only [map_add] using W.add_mem hX hY
    | smul c X _ hX => simpa only [signConjMatrix_smul] using W.smul_mem (signConj ε c) hX
  have hM := key (signConjMatrix ε M) (hspan _)
  rwa [signConjMatrix_signConjMatrix] at hM

/-- Spanning at a given length is inherited by the symmetry-transported family, for every unitary
mixing matrix.  The proof runs backwards along the inverse transport: transporting `Ã_g` once more,
with the adjoint of the (again unitary) conjugated mixing matrix `C_g[u]`, returns `A`, so every
ordered product of `A` already lies in the span of the ordered products of `C_g[Ã_g]` of the same
length; the leftover conjugation is then removed by its own involutivity. -/
theorem mpsProductsSpanAt_symmetryTransportMPS {ε : ℤˣ}
    {u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ)
    {A : MPSMatrices D N} {ℓ : ℕ} (hspan : mpsProductsSpanAt A ℓ) :
    mpsProductsSpanAt (symmetryTransportMPS ε u A) ℓ := by
  have hback : mpsMix (star (signConjMatrix ε u))
      (mpsConjugate ε (symmetryTransportMPS ε u A)) = A := by
    have hone : symmetryTransportMPS (1 : ℤˣ) (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) A = A := by
      rw [symmetryTransportMPS, mpsMix_one]
      exact funext fun σ => signConjMatrix_one_apply (A σ)
    have hinv := symmetryTransportMPS_symmetryTransportMPS ε ε (star (signConjMatrix ε u)) u A
    rw [Matrix.mem_unitaryGroup_iff'.mp (signConjMatrix_mem_unitaryGroup ε hu),
      Int.units_mul_self, hone] at hinv
    exact hinv
  have hconj : mpsProductsSpanAt (mpsConjugate ε (symmetryTransportMPS ε u A)) ℓ := by
    unfold mpsProductsSpanAt at hspan ⊢
    refine eq_top_iff.mpr ?_
    rw [← hspan, Submodule.span_le]
    rintro P ⟨σs, hlen, rfl⟩
    subst hlen
    have hmem := orderedProd_mpsMix_mem_span (star (signConjMatrix ε u))
      (mpsConjugate ε (symmetryTransportMPS ε u A)) σs
    rw [hback] at hmem
    exact hmem
  have hfinal := mpsProductsSpanAt_mpsConjugate ε hconj
  rwa [mpsConjugate_mpsConjugate] at hfinal

/-! ## Transport of the normalization and of the transfer spectrum -/

/-- The scalar twist fixes real numbers, so the normalization eigenvalue `λ` is unchanged by the
transport. -/
private lemma signConj_ofReal (ε : ℤˣ) (lam : ℝ) : signConj ε (lam : ℂ) = (lam : ℂ) := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h
  · exact signConj_one_apply _
  · rw [signConj_neg_one_apply, Complex.conj_ofReal]

/-- The unitarity of the mixing matrix, in the entrywise form used by the normalization and
transfer-matrix computations. -/
private lemma sum_star_mul_of_mem_unitaryGroup {u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ) (σ' σ'' : Fin (N + 1)) :
    (∑ σ : Fin (N + 1), star (u σ σ'') * u σ σ') = if σ'' = σ' then 1 else 0 := by
  have h1 : u.conjTranspose * u = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  have h2 := congrFun (congrFun h1 σ'') σ'
  rw [Matrix.mul_apply] at h2
  simpa only [Matrix.conjTranspose_apply, Matrix.one_apply] using h2

/-- **Tasaki eq. (8.3.14)**: the symmetry-transported family satisfies the same normalization
`Σ_σ Ã^σ (Ã^σ)† = λ I`, with the *same* `λ`. -/
theorem isMPSNormalized_symmetryTransportMPS {ε : ℤˣ}
    {u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ)
    {A : MPSMatrices D N} {lam : ℝ} (hnorm : IsMPSNormalized A lam) :
    IsMPSNormalized (symmetryTransportMPS ε u A) lam := by
  obtain ⟨hlam, hA⟩ := hnorm
  refine ⟨hlam, ?_⟩
  set B : MPSMatrices D N := mpsConjugate ε A
  have hB : (∑ σ : Fin (N + 1), B σ * (B σ).conjTranspose) =
      (lam : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have hstage : (∑ σ : Fin (N + 1), B σ * (B σ).conjTranspose) =
        signConjMatrix ε (∑ σ : Fin (N + 1), A σ * (A σ).conjTranspose) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      change signConjMatrix ε (A σ) * (signConjMatrix ε (A σ)).conjTranspose = _
      rw [signConjMatrix_conjTranspose, ← map_mul]
    rw [hstage, hA, signConjMatrix_smul, map_one, signConj_ofReal]
  have hexp : ∀ σ : Fin (N + 1),
      mpsMix u B σ * (mpsMix u B σ).conjTranspose =
        ∑ σ' : Fin (N + 1), ∑ σ'' : Fin (N + 1),
          (u σ σ' * star (u σ σ'')) • (B σ' * (B σ'').conjTranspose) := by
    intro σ
    change (∑ σ' : Fin (N + 1), u σ σ' • B σ') *
      (∑ σ'' : Fin (N + 1), u σ σ'' • B σ'').conjTranspose = _
    rw [Matrix.conjTranspose_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [Matrix.smul_mul, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ'' _ => ?_
    rw [Matrix.conjTranspose_smul, Matrix.mul_smul, smul_smul]
  change (∑ σ : Fin (N + 1), mpsMix u B σ * (mpsMix u B σ).conjTranspose) = _
  calc (∑ σ : Fin (N + 1), mpsMix u B σ * (mpsMix u B σ).conjTranspose)
      = ∑ σ' : Fin (N + 1), ∑ σ'' : Fin (N + 1), ∑ σ : Fin (N + 1),
          (u σ σ' * star (u σ σ'')) • (B σ' * (B σ'').conjTranspose) := by
        rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => hexp σ, Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ' _ => Finset.sum_comm
    _ = ∑ σ' : Fin (N + 1), B σ' * (B σ').conjTranspose := by
        refine Finset.sum_congr rfl fun σ' _ => ?_
        have hinner : ∀ σ'' : Fin (N + 1), (∑ σ : Fin (N + 1),
            (u σ σ' * star (u σ σ'')) • (B σ' * (B σ'').conjTranspose)) =
            (if σ'' = σ' then (1 : ℂ) else 0) • (B σ' * (B σ'').conjTranspose) := by
          intro σ''
          rw [← Finset.sum_smul, ← sum_star_mul_of_mem_unitaryGroup hu σ' σ'']
          exact congrArg (· • (B σ' * (B σ'').conjTranspose))
            (Finset.sum_congr rfl fun σ _ => mul_comm _ _)
        rw [Finset.sum_congr rfl fun σ'' (_ : σ'' ∈ Finset.univ) => hinner σ'']
        simp
    _ = (lam : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) := hB

/-- **Tasaki §8.3.4, p. 265**: the transfer matrix of the symmetry-transported family is the
entrywise conjugate of the original one — literally "identical" in the unitary case `ε = 1`. -/
theorem mpsTransferMatrix_symmetryTransportMPS {ε : ℤˣ}
    {u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ)
    (A : MPSMatrices D N) :
    mpsTransferMatrix (symmetryTransportMPS ε u A) = signConjMatrix ε (mpsTransferMatrix A) := by
  have hstar : ∀ z : ℂ, signConj ε (star z) = star (signConj ε z) := by
    rcases Int.units_eq_one_or ε with h | h <;> subst h
    · intro z
      rw [signConj_one_apply, signConj_one_apply]
    · intro z
      rw [signConj_neg_one_apply, signConj_neg_one_apply]
      simp only [starRingEnd_apply]
  ext p q
  have hentry : ∀ (σ : Fin (N + 1)) (i j : Fin D),
      symmetryTransportMPS ε u A σ i j = ∑ σ' : Fin (N + 1), u σ σ' * signConj ε (A σ' i j) := by
    intro σ i j
    change (∑ σ' : Fin (N + 1), u σ σ' • signConjMatrix ε (A σ')) i j = _
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun σ' _ => by
      simp [signConjMatrix, RingHom.mapMatrix_apply]
  have hexpand : ∀ σ : Fin (N + 1),
      star (∑ σ' : Fin (N + 1), u σ σ' * signConj ε (A σ' p.1 q.1)) *
          (∑ σ'' : Fin (N + 1), u σ σ'' * signConj ε (A σ'' p.2 q.2)) =
        ∑ σ' : Fin (N + 1), ∑ σ'' : Fin (N + 1), (star (u σ σ') * u σ σ'') *
          (star (signConj ε (A σ' p.1 q.1)) * signConj ε (A σ'' p.2 q.2)) := by
    intro σ
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ'' _ => ?_
    rw [star_mul']
    ring
  simp only [mpsTransferMatrix, Matrix.of_apply, signConjMatrix, RingHom.mapMatrix_apply,
    Matrix.map_apply, hentry]
  calc (∑ σ : Fin (N + 1), star (∑ σ' : Fin (N + 1), u σ σ' * signConj ε (A σ' p.1 q.1)) *
          ∑ σ'' : Fin (N + 1), u σ σ'' * signConj ε (A σ'' p.2 q.2))
      = ∑ σ' : Fin (N + 1), ∑ σ'' : Fin (N + 1), ∑ σ : Fin (N + 1),
          (star (u σ σ') * u σ σ'') *
            (star (signConj ε (A σ' p.1 q.1)) * signConj ε (A σ'' p.2 q.2)) := by
        rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => hexpand σ, Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ' _ => Finset.sum_comm
    _ = ∑ σ' : Fin (N + 1),
          star (signConj ε (A σ' p.1 q.1)) * signConj ε (A σ' p.2 q.2) := by
        refine Finset.sum_congr rfl fun σ' _ => ?_
        have hinner : ∀ σ'' : Fin (N + 1), (∑ σ : Fin (N + 1), (star (u σ σ') * u σ σ'') *
            (star (signConj ε (A σ' p.1 q.1)) * signConj ε (A σ'' p.2 q.2))) =
            (if σ' = σ'' then (1 : ℂ) else 0) *
              (star (signConj ε (A σ' p.1 q.1)) * signConj ε (A σ'' p.2 q.2)) := by
          intro σ''
          rw [← Finset.sum_mul, sum_star_mul_of_mem_unitaryGroup hu σ'' σ']
        rw [Finset.sum_congr rfl fun σ'' (_ : σ'' ∈ Finset.univ) => hinner σ'']
        simp
    _ = signConj ε (∑ σ' : Fin (N + 1), star (A σ' p.1 q.1) * A σ' p.2 q.2) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun σ' _ => ?_
        rw [map_mul, hstar]

/-- Tasaki Theorem 7.5(iii) is inherited by the symmetry-transported family: the transfer matrix is
conjugated, so `λ` stays a simple eigenvalue and the spectral gap to the rest of the spectrum is
preserved. -/
theorem hasPrimitiveTransferSpectrum_symmetryTransportMPS {ε : ℤˣ}
    {u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ)
    {A : MPSMatrices D N} {lam : ℝ} (hprim : HasPrimitiveTransferSpectrum A lam) :
    HasPrimitiveTransferSpectrum (symmetryTransportMPS ε u A) lam := by
  obtain ⟨hmem, hker, hgap⟩ := hprim
  have hreal := signConj_ofReal ε lam
  have htransfer := mpsTransferMatrix_symmetryTransportMPS (ε := ε) hu A
  refine ⟨?_, ?_, ?_⟩
  · rw [htransfer, mem_spectrum_signConjMatrix_iff, hreal]
    exact hmem
  · have hbridge : ∀ M : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
        M.mulVecLin - (lam : ℂ) • LinearMap.id = (M - (lam : ℂ) • 1).mulVecLin := by
      intro M
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hsub : signConjMatrix ε (mpsTransferMatrix A) -
          (lam : ℂ) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) =
        signConjMatrix ε (mpsTransferMatrix A - (lam : ℂ) • 1) := by
      rw [map_sub, signConjMatrix_smul, map_one, hreal]
    rw [htransfer, hbridge, hsub, finrank_ker_mulVecLin_signConjMatrix, ← hbridge]
    exact hker
  · intro μ hμ hne
    rw [htransfer, mem_spectrum_signConjMatrix_iff] at hμ
    have hne' : signConj ε μ ≠ (lam : ℂ) := by
      intro h
      exact hne (by rw [← signConj_signConj ε μ, h, hreal])
    simpa only [norm_signConj] using hgap _ hμ hne'

/-- **Tasaki §8.3.4, p. 265 and §8.3.5, p. 279**: injectivity of an MPS family is inherited by
every symmetry-transported family `Ã_g^σ = Σ_{σ'} ⟨ψ^σ|û(g)|ψ^{σ'}⟩ C_g[A^{σ'}]` (eq. (8.3.47))
built from a unitary mixing matrix, with the same normalization eigenvalue `λ`.  The book asserts
this three times — for eq. (8.3.13), for the `S = 1` time reversal (8.3.33), and for the general
`g` — without proof. -/
theorem isInjectiveMPS_symmetryTransportMPS {ε : ℤˣ}
    {u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ)
    {A : MPSMatrices D N} {lam : ℝ} (hA : IsInjectiveMPS A lam) :
    IsInjectiveMPS (symmetryTransportMPS ε u A) lam := by
  obtain ⟨hnorm, ⟨ℓ₀, hspan⟩, ⟨ℓ₁, hlarge⟩, hprim⟩ := hA
  exact ⟨isMPSNormalized_symmetryTransportMPS hu hnorm,
    ⟨ℓ₀, mpsProductsSpanAt_symmetryTransportMPS hu hspan⟩,
    ⟨ℓ₁, fun ℓ hℓ => mpsProductsSpanAt_symmetryTransportMPS hu (hlarge ℓ hℓ)⟩,
    hasPrimitiveTransferSpectrum_symmetryTransportMPS hu hprim⟩

end LatticeSystem.Quantum
