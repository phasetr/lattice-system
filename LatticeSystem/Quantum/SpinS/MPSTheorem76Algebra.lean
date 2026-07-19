import LatticeSystem.Quantum.SpinS.MPSTheorem76Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

/-!
# Algebra transport for Tasaki Theorem 7.6

This file constructs the algebra equivalence induced by equality of every periodic MPS trace
coefficient at a common spanning length. The fixed-length word substrate remains private.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.6, eq. (7.2.43), p. 203.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {D N : ℕ}

/-- A fixed-length physical word. -/
private abbrev Word (N ℓ : ℕ) :=
  Fin ℓ → Fin (N + 1)

/-- The matrix obtained by evaluating a fixed-length word. -/
private noncomputable def wordEval (A : MPSMatrices D N) {ℓ : ℕ}
    (w : Word N ℓ) : Matrix (Fin D) (Fin D) ℂ :=
  orderedProd A (List.ofFn w)

/-- The linear combination map which evaluates formal fixed-length words. -/
private noncomputable def evalWords (A : MPSMatrices D N) (ℓ : ℕ) :
    (Word N ℓ →₀ ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  Finsupp.linearCombination ℂ (wordEval A)

/-- Ordered MPS products turn list concatenation into matrix multiplication. -/
private theorem orderedProd_append (A : MPSMatrices D N)
    (u v : List (Fin (N + 1))) :
    orderedProd A (u ++ v) = orderedProd A u * orderedProd A v := by
  induction u with
  | nil => simp [orderedProd]
  | cons σ u ih =>
      simp only [List.cons_append, orderedProd]
      rw [ih, Matrix.mul_assoc]

/-- Function-indexed trace equality implies trace equality for every list word. -/
private theorem trace_eq_list {A B : MPSMatrices D N}
    (h : GeneratesSameMPS A B) (u : List (Fin (N + 1))) :
    Matrix.trace (orderedProd A u) = Matrix.trace (orderedProd B u) := by
  simpa only [List.ofFn_get] using h u.length u.get

/-- Fixed-length spanning is equivalent to surjectivity of the word evaluation map. -/
private theorem evalWords_surjective {A : MPSMatrices D N} {ℓ : ℕ}
    (hspan : mpsProductsSpanAt A ℓ) :
    Function.Surjective (evalWords A ℓ) := by
  rw [← LinearMap.range_eq_top]
  rw [evalWords, Finsupp.range_linearCombination]
  rw [← hspan]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro M ⟨w, rfl⟩
    exact ⟨List.ofFn w, by simp, rfl⟩
  · apply Submodule.span_mono
    rintro M ⟨u, hu, rfl⟩
    subst ℓ
    exact ⟨u.get, by simp [wordEval]⟩

/-- Trace equality preserves every linear relation among fixed-length words. -/
private theorem evalWords_ker_le {A B : MPSMatrices D N} {ℓ : ℕ}
    (hsame : GeneratesSameMPS A B)
    (hspanB : mpsProductsSpanAt B ℓ) :
    LinearMap.ker (evalWords A ℓ) ≤ LinearMap.ker (evalWords B ℓ) := by
  classical
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have hpair (t : Word N ℓ) :
      (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          ((LinearMap.mulRight ℂ (wordEval A t)).comp (evalWords A ℓ)) =
        (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          ((LinearMap.mulRight ℂ (wordEval B t)).comp (evalWords B ℓ)) := by
    apply Finsupp.lhom_ext'
    intro w
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, evalWords,
      Finsupp.linearCombination_single, Matrix.traceLinearMap_apply,
      LinearMap.mulRight_apply, Matrix.smul_mul, Matrix.trace_smul, wordEval]
    congr 1
    rw [← orderedProd_append A (List.ofFn w) (List.ofFn t)]
    rw [← orderedProd_append B (List.ofFn w) (List.ofFn t)]
    exact trace_eq_list hsame _
  have hzero (t : Word N ℓ) :
      Matrix.trace (evalWords B ℓ c * wordEval B t) = 0 := by
    have h := LinearMap.congr_fun (hpair t) c
    simpa only [LinearMap.comp_apply, Matrix.traceLinearMap_apply,
      LinearMap.mulRight_apply, hc, Matrix.zero_mul, Matrix.trace_zero] using h.symm
  have hsurjB := evalWords_surjective hspanB
  rw [Matrix.ext_iff_trace_mul_right]
  intro X
  obtain ⟨d, rfl⟩ := hsurjB X
  have hfunctional :
      (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          ((LinearMap.mulLeft ℂ (evalWords B ℓ c)).comp (evalWords B ℓ)) = 0 := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, evalWords,
      Finsupp.linearCombination_single, Matrix.traceLinearMap_apply,
      LinearMap.mulLeft_apply, LinearMap.zero_apply, Matrix.mul_smul, Matrix.trace_smul, wordEval]
    change z • Matrix.trace (evalWords B ℓ c * wordEval B t) = 0
    rw [hzero t, smul_zero]
  have h := LinearMap.congr_fun hfunctional d
  simpa only [LinearMap.comp_apply, Matrix.traceLinearMap_apply, LinearMap.mulLeft_apply,
    LinearMap.zero_apply, Matrix.zero_mul, Matrix.trace_zero] using h

/-- The two fixed-length word evaluation maps have the same kernel. -/
private theorem evalWords_ker_eq {A B : MPSMatrices D N} {ℓ : ℕ}
    (hsame : GeneratesSameMPS A B)
    (hspanA : mpsProductsSpanAt A ℓ) (hspanB : mpsProductsSpanAt B ℓ) :
    LinearMap.ker (evalWords A ℓ) = LinearMap.ker (evalWords B ℓ) := by
  apply le_antisymm
  · exact evalWords_ker_le hsame hspanB
  · exact evalWords_ker_le (fun L ss => (hsame L ss).symm) hspanA

/-- Equality against every fixed-length word in a spanning family determines a matrix. -/
private theorem eq_of_trace_mul_words {A : MPSMatrices D N} {ℓ : ℕ}
    (hspan : mpsProductsSpanAt A ℓ)
    {X Y : Matrix (Fin D) (Fin D) ℂ}
    (htrace : ∀ w : Word N ℓ,
      Matrix.trace (X * wordEval A w) = Matrix.trace (Y * wordEval A w)) :
    X = Y := by
  classical
  rw [Matrix.ext_iff_trace_mul_right]
  intro Z
  obtain ⟨c, rfl⟩ := evalWords_surjective hspan Z
  have hfunctional :
      (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          ((LinearMap.mulLeft ℂ X).comp (evalWords A ℓ)) =
        (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          ((LinearMap.mulLeft ℂ Y).comp (evalWords A ℓ)) := by
    apply Finsupp.lhom_ext'
    intro w
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, evalWords,
      Finsupp.linearCombination_single, Matrix.traceLinearMap_apply,
      LinearMap.mulLeft_apply, Matrix.mul_smul, Matrix.trace_smul, wordEval]
    change z • Matrix.trace (X * wordEval A w) =
      z • Matrix.trace (Y * wordEval A w)
    rw [htrace w]
  exact LinearMap.congr_fun hfunctional c

namespace MPSTheorem76.Internal

/-- A common spanning length and all-word trace equality induce the algebra equivalence transporting
every word in `A` to the corresponding word in `B`. The exact consumer is
`MPSTheorem76.Internal.exists_unitary_gauge_data`. -/
theorem exists_word_transport_algEquiv
    (A B : MPSMatrices D N) (ℓ : ℕ) (_hℓ : 1 ≤ ℓ)
    (hsame : GeneratesSameMPS A B)
    (hspanA : mpsProductsSpanAt A ℓ) (hspanB : mpsProductsSpanAt B ℓ) :
    ∃ e : Matrix (Fin D) (Fin D) ℂ ≃ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      (∀ u : List (Fin (N + 1)), e (orderedProd A u) = orderedProd B u) ∧
      (∀ u : List (Fin (N + 1)), e.symm (orderedProd B u) = orderedProd A u) ∧
      (∀ σ : Fin (N + 1), e (A σ) = B σ) := by
  classical
  let evalA := evalWords A ℓ
  let evalB := evalWords B ℓ
  have hsurjA : Function.Surjective evalA := evalWords_surjective hspanA
  have hsurjB : Function.Surjective evalB := evalWords_surjective hspanB
  obtain ⟨sectionA, hsectionA⟩ :=
    evalA.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurjA)
  let f : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    evalB.comp sectionA
  have hker : LinearMap.ker evalA = LinearMap.ker evalB := by
    exact evalWords_ker_eq hsame hspanA hspanB
  have hsectionA_apply (X : Matrix (Fin D) (Fin D) ℂ) :
      evalA (sectionA X) = X := by
    have h := LinearMap.congr_fun hsectionA X
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  have hf_eval (c : Word N ℓ →₀ ℂ) : f (evalA c) = evalB c := by
    have hdiffA : sectionA (evalA c) - c ∈ LinearMap.ker evalA := by
      rw [LinearMap.mem_ker, map_sub, hsectionA_apply, sub_self]
    have hdiffB : sectionA (evalA c) - c ∈ LinearMap.ker evalB := by
      rwa [← hker]
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hdiffB
    simpa only [f, LinearMap.comp_apply] using hdiffB
  have hf_zero {X : Matrix (Fin D) (Fin D) ℂ} (hX : f X = 0) : X = 0 := by
    obtain ⟨c, rfl⟩ := hsurjA X
    rw [hf_eval] at hX
    have hcB : c ∈ LinearMap.ker evalB := by
      rwa [LinearMap.mem_ker]
    have hcA : c ∈ LinearMap.ker evalA := by
      rwa [hker]
    exact LinearMap.mem_ker.mp hcA
  have hfinj : Function.Injective f := by
    intro X Y hXY
    apply sub_eq_zero.mp
    apply hf_zero
    rw [map_sub, hXY, sub_self]
  have hfsurj : Function.Surjective f := by
    intro Y
    obtain ⟨c, rfl⟩ := hsurjB Y
    exact ⟨evalA c, hf_eval c⟩
  let eLin : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have eLin_apply (X : Matrix (Fin D) (Fin D) ℂ) : eLin X = f X := rfl
  have eLin_eval (c : Word N ℓ →₀ ℂ) : eLin (evalA c) = evalB c := by
    rw [eLin_apply, hf_eval]
  have hpair (t : Word N ℓ) :
      (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          ((LinearMap.mulRight ℂ (wordEval A t)).comp evalA) =
        (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          ((LinearMap.mulRight ℂ (wordEval B t)).comp evalB) := by
    apply Finsupp.lhom_ext'
    intro w
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, evalA, evalB, evalWords,
      Finsupp.linearCombination_single, Matrix.traceLinearMap_apply,
      LinearMap.mulRight_apply, Matrix.smul_mul, Matrix.trace_smul, wordEval]
    congr 1
    rw [← orderedProd_append A (List.ofFn w) (List.ofFn t)]
    rw [← orderedProd_append B (List.ofFn w) (List.ofFn t)]
    exact trace_eq_list hsame _
  have eLin_word (u : List (Fin (N + 1))) :
      eLin (orderedProd A u) = orderedProd B u := by
    obtain ⟨c, hc⟩ := hsurjA (orderedProd A u)
    have he : eLin (orderedProd A u) = evalB c := by
      rw [← hc, eLin_eval]
    rw [he]
    apply eq_of_trace_mul_words hspanB
    intro t
    have hp := LinearMap.congr_fun (hpair t) c
    simp only [LinearMap.comp_apply, Matrix.traceLinearMap_apply,
      LinearMap.mulRight_apply] at hp
    calc
      Matrix.trace (evalB c * wordEval B t) =
          Matrix.trace (evalA c * wordEval A t) := hp.symm
      _ = Matrix.trace (orderedProd A u * wordEval A t) := by rw [hc]
      _ = Matrix.trace (orderedProd A (u ++ List.ofFn t)) := by
          rw [orderedProd_append]
          rfl
      _ = Matrix.trace (orderedProd B (u ++ List.ofFn t)) := trace_eq_list hsame _
      _ = Matrix.trace (orderedProd B u * wordEval B t) := by
          rw [orderedProd_append]
          rfl
  have eLin_one : eLin (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    simpa only [orderedProd] using eLin_word ([] : List (Fin (N + 1)))
  have eLin_mul (X Y : Matrix (Fin D) (Fin D) ℂ) :
      eLin (X * Y) = eLin X * eLin Y := by
    obtain ⟨c, rfl⟩ := hsurjA X
    obtain ⟨d, rfl⟩ := hsurjA Y
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c₁ c₂ hc₁ hc₂ =>
        simp only [map_add, Matrix.add_mul, hc₁, hc₂, Matrix.add_mul]
    | single w z =>
        induction d using Finsupp.induction_linear with
        | zero => simp
        | add d₁ d₂ hd₁ hd₂ =>
            simp only [map_add, Matrix.mul_add, hd₁, hd₂, Matrix.mul_add]
        | single v q =>
            simp only [evalA, evalWords, Finsupp.linearCombination_single,
              Matrix.smul_mul, Matrix.mul_smul, map_smul, smul_smul, wordEval]
            rw [← orderedProd_append A (List.ofFn w) (List.ofFn v)]
            rw [eLin_word]
            rw [orderedProd_append]
            rw [eLin_word, eLin_word]
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    AlgEquiv.ofLinearEquiv eLin eLin_one eLin_mul
  refine ⟨e, ?_, ?_, ?_⟩
  · intro u
    exact eLin_word u
  · intro u
    apply e.injective
    simpa only [AlgEquiv.apply_symm_apply] using (eLin_word u).symm
  · intro σ
    simpa only [orderedProd, Matrix.mul_one] using eLin_word [σ]

end MPSTheorem76.Internal

end LatticeSystem.Quantum
