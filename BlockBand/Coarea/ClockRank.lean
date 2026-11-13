module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Coarea.SchurEigenpair
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSchurDecoderEnergySeparation

/-!
# The coarea theorem: the deterministic clauses `clock` and `reconstructed_rank`

Both statements are exact, pointwise and finite-dimensional: no measure, norm bound,
limit or uniformity occurs. Every admissible `Parameters` (`n ≥ 4`, `W ≥ 1`), every
increasing rank `α` (zero-based) and every adjacent pair `S = {i, i+1}` is covered.
Vector norms are Euclidean (`l2Norm`, `EuclideanSpace`).

* `coarea_clock` (`CoareaContract.clock`): for every Hermitian `H` with
  `det(H_R - λ_α) ≠ 0`. Degenerate ranks are handled exactly: the measurable selection
  `physicalOrderedEigenvector` is the first-positive-chart normalized column of the
  Lagrange product `orderedProjector`. If `λ_α` is a simple eigenvalue (other eigenvalues
  may be repeated) the product is the eigenline projector (`RankSimple`,
  `orderedProjector_eq_outerProduct_of_rankSimple`), so `ψ` is a unit-phase multiple of
  a unit eigenvector and the clock identity is the Schur elimination of
  `physical_eigenpair_structural_identities`. If `λ_α` is repeated one Lagrange factor
  is `0⁻¹ • (H - λ_α) = 0`, so `ψ = 0`, the pair mass is `0`, `v = (√0)⁻¹ ψ_S = 0`, and the
  three identities hold with Lean's conventions `0⁻¹ = 0`.
* `coarea_reconstructed_rank` (`CoareaContract.reconstructed_rank`): with
  `G = E vv* + U_v(F_v + G') U_v* - F(E)`, the frame completeness `vv* + U_vU_v* = 1`
  (`frame_complete`, from `U_v*U_v = 1`, `U_v*v = 0`, `‖v‖ = 1`, `card S = 2W`) gives the
  Schur complement `A(E) = U_v M U_v*` (`reconstructed_schur`). Haynsworth inertia
  (`haynsworth`, from `negativeEigenvalueCount_hermitianSchur` after the
  permutation `S ⊕ R ≃ Site`) and the frame congruence (`negCount_frame`) give
  `N_-(H - E) = N_-(H_R - E) + N_-(M) = α`. Since `M` and `H_R - E` are invertible the
  kernel of `H - E` is exactly `ℂ · L_E v` (`kernel_frame`), so `E` is a simple eigenvalue
  of `H` with exactly `α` eigenvalues below it: `λ_α(H) = E` (`rank_of_simple`), and the
  selected eigenvector is a unit multiple of `L_E v/‖L_E v‖`, whence
  `ψψ* = L L*/‖L‖²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.ClockRank

open Matrix BlockBand.Model.Construction BlockBand.Foundations.Spectral
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea
open scoped ComplexConjugate

section Pair
variable (p : Parameters) (i : ZMod p.n)

/-- The pair/exterior decomposition `S ⊕ R ≃ Site`. -/
def pairEquiv : PairSite p i ⊕ ExteriorSite p i ≃ p.Site :=
  Equiv.sumCompl (fun x : p.Site => x.1 = i ∨ x.1 = i + 1)

@[simp] theorem pairEquiv_inl (s : PairSite p i) : pairEquiv p i (Sum.inl s) = s.1 := rfl
@[simp] theorem pairEquiv_inr (r : ExteriorSite p i) : pairEquiv p i (Sum.inr r) = r.1 := rfl

theorem comp_pairEquiv (y : p.Site → ℂ) :
    y ∘ pairEquiv p i = (fun s : PairSite p i => y s.1) ⊕ᵥ (fun r : ExteriorSite p i => y r.1) := by
  funext a; cases a <;> rfl

theorem submatrix_assemble (ω : SplitState p i) (G : PairMatrix p i) :
    (assemble p i ω G).submatrix (pairEquiv p i) (pairEquiv p i) =
      fromBlocks (ω.2.2 + G) (ω.2.1)ᴴ ω.2.1 ω.1 := by
  ext (a | a) (b | b)
  · simp [assemble, a.2, b.2]
  · simp [assemble, a.2, b.2]
  · simp [assemble, a.2, b.2]
  · simp [assemble, a.2, b.2]

theorem submatrix_assemble_shift (ω : SplitState p i) (G : PairMatrix p i) (E : ℝ) :
    (assemble p i ω G - (E : ℂ) • 1).submatrix (pairEquiv p i) (pairEquiv p i) =
      fromBlocks (ω.2.2 + G - (E : ℂ) • 1) (ω.2.1)ᴴ ω.2.1 (ω.1 - (E : ℂ) • 1) := by
  have h : (assemble p i ω G - (E : ℂ) • 1).submatrix (pairEquiv p i) (pairEquiv p i) =
      (assemble p i ω G).submatrix (pairEquiv p i) (pairEquiv p i) -
        (E : ℂ) • (1 : p.SiteMatrix).submatrix (pairEquiv p i) (pairEquiv p i) := rfl
  rw [h, submatrix_assemble, Matrix.submatrix_one_equiv,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp [sub_eq_add_neg]

theorem assemble_blocks (H : p.SiteMatrix) (hH : H.IsHermitian) :
    assemble p i (exteriorBlock p i H, couplingBlock p i H, pairBlock p i H) 0 = H := by
  ext x y
  unfold assemble
  by_cases hx : x.1 = i ∨ x.1 = i + 1 <;> by_cases hy : y.1 = i ∨ y.1 = i + 1
  · simp [hx, hy, pairBlock]
  · simp only [hx, hy, dite_true, dite_false, couplingBlock]
    rw [← Matrix.conjTranspose_apply, hH.eq]
  · simp [hx, hy, couplingBlock]
  · simp [hx, hy, exteriorBlock]

theorem sum_site (f : p.Site → ℂ) :
    ∑ x, f x = ∑ s : PairSite p i, f s.1 + ∑ r : ExteriorSite p i, f r.1 := by
  rw [← Equiv.sum_comp (pairEquiv p i), Fintype.sum_sum_type]
  rfl

theorem sum_site_real (f : p.Site → ℝ) :
    ∑ x, f x = ∑ s : PairSite p i, f s.1 + ∑ r : ExteriorSite p i, f r.1 := by
  rw [← Equiv.sum_comp (pairEquiv p i), Fintype.sum_sum_type]
  rfl

private theorem pair_ne_succ : i ≠ i + 1 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod p.n) = 0 := by
    have : (1 : ZMod p.n) = 0 := by
      have := congrArg (fun x => x - i) h
      simpa using this.symm
    exact_mod_cast this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd one_pos h1
  have := p.n_ge_four
  omega

theorem pairMass_eq (α : Fin p.N) (H : p.SiteMatrix) :
    pairMass p i α H = ∑ s : PairSite p i, ‖physicalOrderedEigenvector p H α s.1‖ ^ 2 := by
  have hs : ∀ x : p.Site, x ∈ ({i, i + 1} : Finset (ZMod p.n)) ×ˢ (Finset.univ : Finset (Fin p.W)) ↔
      (x.1 = i ∨ x.1 = i + 1) := by
    intro x; simp
  rw [← Finset.sum_subtype _ hs (fun x => ‖physicalOrderedEigenvector p H α x‖ ^ 2),
    Finset.sum_product, Finset.sum_pair (pair_ne_succ p i)]
  rfl

private theorem card_pairSite : Fintype.card (PairSite p i) = 2 * p.W := by
  classical
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun x : p.Site => x.1 = i ∨ x.1 = i + 1) =
      ({i, i + 1} : Finset (ZMod p.n)) ×ˢ (Finset.univ : Finset (Fin p.W)) := by
    ext x
    simp
  rw [hfilter, Finset.card_product, Finset.card_pair (pair_ne_succ p i), Finset.card_univ,
    Fintype.card_fin]

theorem blocks_mulVec_eq_zero {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (x : m → ℂ) (y : n → ℂ) :
    fromBlocks A B C D *ᵥ (x ⊕ᵥ y) = 0 ↔ A *ᵥ x + B *ᵥ y = 0 ∧ C *ᵥ x + D *ᵥ y = 0 := by
  rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
  constructor
  · intro h
    exact ⟨funext fun a => congrFun h (Sum.inl a), funext fun a => congrFun h (Sum.inr a)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    funext a; cases a <;> rfl

theorem shift_mulVec_eq_zero_iff (ω : SplitState p i) (G : PairMatrix p i) (E : ℝ)
    (y : p.Site → ℂ) :
    (assemble p i ω G - (E : ℂ) • 1) *ᵥ y = 0 ↔
      (ω.2.2 + G - (E : ℂ) • 1) *ᵥ (fun s : PairSite p i => y s.1) +
          (ω.2.1)ᴴ *ᵥ (fun r : ExteriorSite p i => y r.1) = 0 ∧
        ω.2.1 *ᵥ (fun s : PairSite p i => y s.1) +
          (ω.1 - (E : ℂ) • 1) *ᵥ (fun r : ExteriorSite p i => y r.1) = 0 := by
  rw [← blocks_mulVec_eq_zero, ← comp_pairEquiv, ← submatrix_assemble_shift,
    Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    funext x
    have := congrFun h ((pairEquiv p i).symm x)
    simpa using this

theorem l2Norm_eq_norm (y : p.Site → ℂ) :
    l2Norm y = ‖WithLp.toLp 2 (y ∘ pairEquiv p i)‖ := by
  rw [EuclideanSpace.norm_eq, l2Norm]
  congr 1
  rw [← Equiv.sum_comp (pairEquiv p i)]
  rfl

theorem schurLift_comp (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ) :
    schurLift p i H_R C E v ∘ pairEquiv p i = schurGraph (physicalCoareaT H_R C E) v := by
  funext a
  cases a with
  | inl s => simp [schurLift, schurGraph, s.2]
  | inr r => simp [schurLift, schurGraph, r.2]

theorem clock_of_kernel (H : p.SiteMatrix) (hH : H.IsHermitian) (E : ℝ)
    (hdet : (exteriorBlock p i H - (E : ℂ) • 1).det ≠ 0) (ψ : p.Site → ℂ)
    (hψ : (H - (E : ℂ) • 1) *ᵥ ψ = 0) (hunit : ∑ x, ‖ψ x‖ ^ 2 = 1) (m : ℝ)
    (hm : m = ∑ s : PairSite p i, ‖ψ s.1‖ ^ 2) :
    let v : PairSite p i → ℂ := fun x => ((Real.sqrt m)⁻¹ : ℂ) * ψ x.1
    let H_R := exteriorBlock p i H
    let C := couplingBlock p i H
    physicalCoareaA H_R C (pairBlock p i H) 0 E *ᵥ v = 0 ∧
      star v ⬝ᵥ (physicalCoareaD H_R C E *ᵥ v) = ((m⁻¹ : ℝ) : ℂ) ∧
      ∀ x, ψ x = ((l2Norm (schurLift p i H_R C E v))⁻¹ : ℂ) * schurLift p i H_R C E v x := by
  intro v H_R C
  set ψS : PairSite p i → ℂ := fun s => ψ s.1
  set ψR : ExteriorSite p i → ℂ := fun r => ψ r.1
  rw [← assemble_blocks p i H hH] at hψ
  obtain ⟨hPair, hExt⟩ := (shift_mulVec_eq_zero_iff p i _ 0 E ψ).mp hψ
  have hUnit : ‖WithLp.toLp 2 (ψS ⊕ᵥ ψR)‖ = 1 := by
    rw [comp_pairEquiv p i ψ |>.symm, ← l2Norm_eq_norm, l2Norm, hunit, Real.sqrt_one]
  have hmass : m = retainedMass ψS := by
    rw [hm, retainedMass]
    simp [ψS, Complex.normSq_eq_norm_sq]
  have hv : v = physicalRetainedDirection ψS := by
    funext s
    simp [v, physicalRetainedDirection, hmass, ψS]
  obtain ⟨_, _, h1, h2, h3⟩ := physical_eigenpair_structural_identities H_R C (pairBlock p i H) 0 E
    hdet ψS ψR hExt hPair hUnit
  rw [hv, hmass]
  refine ⟨h1, h2, ?_⟩
  intro x
  have hx := congrFun h3 ((pairEquiv p i).symm x)
  rw [← comp_pairEquiv, ← schurLift_comp p i H_R C E, ← l2Norm_eq_norm] at hx
  simpa using hx

section Frame
variable {S F : Type*} [Fintype S] [Fintype F] [DecidableEq S] [DecidableEq F]

theorem frame_complete (U : Matrix S F ℂ) (v : S → ℂ) (hUU : Uᴴ * U = 1) (hUv : Uᴴ *ᵥ v = 0)
    (hvv : star v ⬝ᵥ v = 1) (hcard : Fintype.card S = Fintype.card (Unit ⊕ F)) :
    vecMulVec v (star v) + U * Uᴴ = 1 := by
  let W : Matrix S (Unit ⊕ F) ℂ := Matrix.of fun s a => Sum.elim (fun _ => v s) (fun f => U s f) a
  have hWW : Wᴴ * W = 1 := by
    ext (a | f) (b | g)
    · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.of_apply, Sum.elim_inl,
        Matrix.one_apply_eq]
      simpa [dotProduct, mul_comm] using hvv
    · have := congrFun hUv g
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.zero_apply] at this
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.of_apply, Sum.elim_inl,
        Sum.elim_inr]
      rw [Matrix.one_apply_ne (by simp)]
      have h2 := congrArg star this
      simp only [star_sum, star_mul, star_star, star_zero] at h2
      simpa [mul_comm] using h2
    · have := congrFun hUv f
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.zero_apply] at this
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.of_apply, Sum.elim_inl,
        Sum.elim_inr]
      rw [Matrix.one_apply_ne (by simp)]
      exact this
    · have := congrFun (congrFun hUU f) g
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at this
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.of_apply, Sum.elim_inr]
      rw [this]
      by_cases hfg : f = g
      · subst hfg; simp
      · rw [Matrix.one_apply_ne hfg, Matrix.one_apply_ne (by simpa using hfg)]
  have hWW' : W * Wᴴ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard.symm)).mp hWW
  rw [← hWW']
  ext s t
  simp [Matrix.mul_apply, W, Fintype.sum_sum_type, vecMulVec, Matrix.conjTranspose_apply]

end Frame

theorem reconstructed_schur (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ)
    (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ)
    (hc : vecMulVec v (star v) + U v * (U v)ᴴ = 1) :
    physicalCoareaA ω.1 ω.2.1 ω.2.2 (reconstructedGaussian p i U ω E v G') E =
      U v * frameM p i U ω E v G' * (U v)ᴴ := by
  have hc' : vecMulVec v (star v) = 1 - U v * (U v)ᴴ := eq_sub_of_add_eq hc
  simp only [physicalCoareaA, reconstructedGaussian, frameM, hc', Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_sub, Matrix.mul_add, Matrix.add_mul]
  abel

section Inertia
open CoareaNative.BlockBand (negativeEigenvalueCount hermitianQuadraticValue)
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem quad_eq (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
    hermitianQuadraticValue A x = (star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp)).re := by
  unfold hermitianQuadraticValue
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp

theorem quad_congr (P : Matrix n n ℂ) (f : Matrix n m ℂ) (x : EuclideanSpace ℂ m) :
    hermitianQuadraticValue (fᴴ * P * f) x =
      hermitianQuadraticValue P (Matrix.toEuclideanLin f x) := by
  rw [quad_eq, quad_eq]
  simp [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem negCount_congruence_le (P : Matrix n n ℂ) (f : Matrix n m ℂ) (hP : P.IsHermitian)
    (hQ : (fᴴ * P * f).IsHermitian) :
    negativeEigenvalueCount hQ ≤ negativeEigenvalueCount hP := by
  set W := CoareaNative.BlockBand.negativeSpectralSubspace hQ
  set g := Matrix.toEuclideanLin f
  have hneg : ∀ x ∈ W, x ≠ 0 → hermitianQuadraticValue (fᴴ * P * f) x < 0 :=
    fun x hx hx0 =>
      CoareaNative.BlockBand.hermitianQuadraticValue_neg_of_mem_negativeSpectralSubspace hQ hx hx0
  have hinj : Function.Injective (g.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra h0
    have hx0 : (x : EuclideanSpace ℂ m) ≠ 0 := fun h => h0 (Subtype.ext h)
    have := hneg x x.2 hx0
    rw [quad_congr] at this
    have hgx : g x = 0 := hx
    rw [hgx] at this
    simp [quad_eq] at this
  have hrank := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_domRestrict] at hrank
  rw [← CoareaNative.BlockBand.finrank_negativeSpectralSubspace hQ]
  change Module.finrank ℂ W ≤ _
  rw [← hrank]
  apply CoareaNative.BlockBand.finrank_le_negativeEigenvalueCount_of_neg hP
  intro y hy hy0
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  rw [← quad_congr]
  exact hneg x hx (fun h => hy0 (by rw [h, map_zero]))

theorem negCount_congr {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : negativeEigenvalueCount hA = negativeEigenvalueCount hB := by
  subst h; rfl

/-- `A = U M Uᴴ` with `UᴴU = 1`: equal negative inertia. -/
theorem negCount_frame (U : Matrix n m ℂ) (M : Matrix m m ℂ) (hUU : Uᴴ * U = 1)
    (hA : (U * M * Uᴴ).IsHermitian) (hM : M.IsHermitian) :
    negativeEigenvalueCount hA = negativeEigenvalueCount hM := by
  apply le_antisymm
  · have h : (Uᴴ)ᴴ * M * Uᴴ = U * M * Uᴴ := by rw [conjTranspose_conjTranspose]
    have hQ : ((Uᴴ)ᴴ * M * Uᴴ).IsHermitian := by rw [h]; exact hA
    rw [negCount_congr hA hQ h.symm]
    exact negCount_congruence_le M Uᴴ hM hQ
  · have h : Uᴴ * (U * M * Uᴴ) * U = M := by
      rw [show Uᴴ * (U * M * Uᴴ) * U = (Uᴴ * U) * M * (Uᴴ * U) by
        simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one]
    have hQ : (Uᴴ * (U * M * Uᴴ) * U).IsHermitian := by rw [h]; exact hM
    rw [negCount_congr hM hQ h.symm]
    exact negCount_congruence_le _ U hA hQ

theorem negativeCount_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    negativeCount A = negativeEigenvalueCount hA := by
  unfold negativeCount negativeEigenvalueCount
  rw [dite_eq_left_of_eq_true (eq_true hA)]

section Perm
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Permutation matrix of an equivalence `e : β ≃ α`. -/
def permMat (e : β ≃ α) : Matrix α β ℂ := (1 : Matrix α α ℂ).submatrix id e

omit [Fintype β] [DecidableEq β] in
theorem permMat_conj (e : β ≃ α) (K : Matrix α α ℂ) :
    (permMat e)ᴴ * K * permMat e = K.submatrix e e := by
  ext a b
  simp [permMat, Matrix.mul_apply, Matrix.one_apply]

omit [Fintype β] in
theorem permMat_ct_mul (e : β ≃ α) : (permMat e)ᴴ * permMat e = 1 := by
  ext a b
  simp [permMat, Matrix.mul_apply, Matrix.one_apply, eq_comm]

theorem permMat_mul_ct (e : β ≃ α) : permMat e * (permMat e)ᴴ = 1 := by
  rw [Matrix.mul_eq_one_comm_of_equiv e.symm]
  exact permMat_ct_mul e

theorem negCount_submatrix (e : β ≃ α) {K : Matrix α α ℂ} (hK : K.IsHermitian) :
    CoareaNative.BlockBand.negativeEigenvalueCount (hK.submatrix e) =
      CoareaNative.BlockBand.negativeEigenvalueCount hK := by
  have h : permMat e * K.submatrix e e * (permMat e)ᴴ = K := by
    rw [← permMat_conj, show permMat e * ((permMat e)ᴴ * K * permMat e) * (permMat e)ᴴ =
      (permMat e * (permMat e)ᴴ) * K * (permMat e * (permMat e)ᴴ) by simp only [Matrix.mul_assoc],
      permMat_mul_ct, Matrix.one_mul, Matrix.mul_one]
  have hA : (permMat e * K.submatrix e e * (permMat e)ᴴ).IsHermitian := by rw [h]; exact hK
  rw [← negCount_congr hA hK h]
  exact (negCount_frame (permMat e) _ (permMat_ct_mul e) hA (hK.submatrix e)).symm

end Perm

end Inertia

section Rank
open CoareaNative.BlockBand (negativeEigenvalueCount)

theorem shift_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (E : ℝ) : (A - (E : ℂ) • 1).IsHermitian :=
  hA.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))

theorem blocks_isHermitian (ω : SplitState p i) (G : PairMatrix p i) (E : ℝ)
    (hH : (assemble p i ω G).IsHermitian) :
    (ω.2.2 + G - (E : ℂ) • 1).IsHermitian ∧ (ω.1 - (E : ℂ) • 1).IsHermitian := by
  have hK := (shift_isHermitian hH E).submatrix (pairEquiv p i)
  rw [submatrix_assemble_shift] at hK
  obtain ⟨h11, _, _, h22⟩ := Matrix.isHermitian_fromBlocks_iff.mp hK
  exact ⟨h11, h22⟩

theorem schurA_eq (ω : SplitState p i) (G : PairMatrix p i) (E : ℝ)
    [Invertible (ω.1 - (E : ℂ) • 1)] :
    ω.2.2 + G - (E : ℂ) • 1 - (ω.2.1)ᴴ * ⅟(ω.1 - (E : ℂ) • 1) * (ω.2.1)ᴴᴴ =
      physicalCoareaA ω.1 ω.2.1 ω.2.2 G E := by
  rw [Matrix.invOf_eq_nonsing_inv, conjTranspose_conjTranspose]
  simp only [physicalCoareaA, physicalCoareaF, physicalCoareaResolvent]
  abel

theorem schurA_isHermitian (ω : SplitState p i) (G : PairMatrix p i) (E : ℝ)
    (hH : (assemble p i ω G).IsHermitian) :
    (physicalCoareaA ω.1 ω.2.1 ω.2.2 G E).IsHermitian := by
  obtain ⟨h11, h22⟩ := blocks_isHermitian p i ω G E hH
  have h : physicalCoareaA ω.1 ω.2.1 ω.2.2 G E =
      ω.2.2 + G - (E : ℂ) • 1 - (ω.2.1)ᴴ * (ω.1 - (E : ℂ) • 1)⁻¹ * ω.2.1 := by
    simp only [physicalCoareaA, physicalCoareaF, physicalCoareaResolvent]
    abel
  rw [h]
  exact h11.sub (Matrix.isHermitian_conjTranspose_mul_mul ω.2.1 h22.inv)

theorem haynsworth (ω : SplitState p i) (G : PairMatrix p i) (E : ℝ)
    (hH : (assemble p i ω G).IsHermitian) (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0) :
    negativeCount (assemble p i ω G - (E : ℂ) • 1) =
      negativeCount (physicalCoareaA ω.1 ω.2.1 ω.2.2 G E) + negativeCount (ω.1 - (E : ℂ) • 1) := by
  obtain ⟨h11, h22⟩ := blocks_isHermitian p i ω G E hH
  let _ : Invertible (ω.1 - (E : ℂ) • 1) :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hD)
  have hS := CoareaNative.BlockBand.negativeEigenvalueCount_hermitianSchur
    (ω.2.2 + G - (E : ℂ) • 1) (ω.2.1)ᴴ (ω.1 - (E : ℂ) • 1) h11 h22
  dsimp only at hS
  have hK := shift_isHermitian hH E
  have hK' := hK.submatrix (pairEquiv p i)
  rw [negativeCount_eq hK, negativeCount_eq (schurA_isHermitian p i ω G E hH), negativeCount_eq h22]
  have hcount : negativeEigenvalueCount hK' = negativeEigenvalueCount hK :=
    negCount_submatrix (pairEquiv p i) hK
  refine hcount.symm.trans
    ((negCount_congr hK' _ ((submatrix_assemble_shift p i ω G E).trans
      (by rw [conjTranspose_conjTranspose]))).trans (hS.trans ?_))
  congr 1
  exact negCount_congr _ _ (schurA_eq p i ω G E)

end Rank

theorem schurA_eq_transfer (ω : SplitState p i) (G : PairMatrix p i) (E : ℝ) :
    physicalCoareaA ω.1 ω.2.1 ω.2.2 G E =
      (ω.2.2 + G - (E : ℂ) • 1) - (ω.2.1)ᴴ * physicalCoareaT ω.1 ω.2.1 E := by
  simp only [physicalCoareaA, physicalCoareaF, physicalCoareaT, Matrix.mul_assoc]
  abel

theorem schurLift_pair (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ) :
    (fun s : PairSite p i => schurLift p i H_R C E v s.1) = v := by
  funext s; simp [schurLift, s.2]

theorem schurLift_ext (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ) :
    (fun r : ExteriorSite p i => schurLift p i H_R C E v r.1) = -(physicalCoareaT H_R C E *ᵥ v) := by
  funext r; simp [schurLift, r.2]

theorem kernel_frame {F : Type*} [Fintype F] [DecidableEq F]
    (ω : SplitState p i) (G : PairMatrix p i) (E : ℝ)
    (v : PairSite p i → ℂ) (U : Matrix (PairSite p i) F ℂ) (M : Matrix F F ℂ)
    (hA : physicalCoareaA ω.1 ω.2.1 ω.2.2 G E = U * M * Uᴴ) (hUU : Uᴴ * U = 1)
    (hUv : Uᴴ *ᵥ v = 0) (hc : vecMulVec v (star v) + U * Uᴴ = 1)
    (hD : (ω.1 - (E : ℂ) • 1).det ≠ 0) (hM : M.det ≠ 0) :
    (assemble p i ω G - (E : ℂ) • 1) *ᵥ schurLift p i ω.1 ω.2.1 E v = 0 ∧
      ∀ y : p.Site → ℂ, (assemble p i ω G - (E : ℂ) • 1) *ᵥ y = 0 →
        y = (star v ⬝ᵥ (fun s : PairSite p i => y s.1)) • schurLift p i ω.1 ω.2.1 E v := by
  constructor
  · rw [shift_mulVec_eq_zero_iff, schurLift_pair, schurLift_ext]
    constructor
    · rw [Matrix.mulVec_neg, ← sub_eq_add_neg, Matrix.mulVec_mulVec, ← Matrix.sub_mulVec,
        ← schurA_eq_transfer, hA, ← Matrix.mulVec_mulVec, hUv, Matrix.mulVec_zero]
    · have hInv : (ω.1 - (E : ℂ) • 1) * physicalCoareaResolvent ω.1 E = 1 :=
        mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hD)
      rw [Matrix.mulVec_neg, physicalCoareaT, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hInv,
        Matrix.one_mul, add_neg_cancel]
  · intro y hy
    obtain ⟨hPair, hExt⟩ := (shift_mulVec_eq_zero_iff p i ω G E y).mp hy
    set yS : PairSite p i → ℂ := fun s => y s.1
    set yR : ExteriorSite p i → ℂ := fun r => y r.1
    have hR := physical_exterior_eigenvector_eq_graph ω.1 ω.2.1 E hD yS yR hExt
    have hS := physical_schur_eigenvector_equation ω.1 ω.2.1 ω.2.2 G E hD yS yR hExt hPair
    rw [hA] at hS
    have hMU : M *ᵥ (Uᴴ *ᵥ yS) = 0 := by
      have h := congrArg (fun x => Uᴴ *ᵥ x) hS
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h
      rw [Matrix.mulVec_mulVec]
      rwa [show Uᴴ * (U * M * Uᴴ) = (Uᴴ * U) * M * Uᴴ by simp only [Matrix.mul_assoc], hUU,
        Matrix.one_mul] at h
    have hUy : Uᴴ *ᵥ yS = 0 := by
      by_contra h0
      exact hM ((Matrix.exists_mulVec_eq_zero_iff (M := M)).mp ⟨_, h0, hMU⟩)
    obtain ⟨c, hcdef⟩ : ∃ c, c = star v ⬝ᵥ yS := ⟨_, rfl⟩
    rw [← hcdef]
    have hyS : yS = c • v := by
      have h := congrArg (fun X => X *ᵥ yS) hc
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hUy,
        Matrix.mulVec_zero, add_zero, Matrix.vecMulVec_mulVec, ← hcdef] at h
      rw [← h]
      ext s
      simp [mul_comm]
    have hcomp : y ∘ pairEquiv p i = (c • schurLift p i ω.1 ω.2.1 E v) ∘ pairEquiv p i := by
      funext a
      cases a with
      | inl s =>
        have := congrFun hyS s
        simpa [schurLift, s.2] using this
      | inr r =>
        have := congrFun hR r
        rw [hyS, Matrix.mulVec_smul] at this
        simpa [schurLift, r.2] using this
    exact (pairEquiv p i).surjective.injective_comp_right hcomp

section Simple
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def RankSimple (A : HermitianMatrix ι) (i : Fin (Fintype.card ι)) : Prop :=
  ∀ j, orderedEigenvalue A j = orderedEigenvalue A i → j = i

theorem orderedProjectorScalar_prod_of_rankSimple (i r : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hi : RankSimple A i) :
    ((List.finRange (Fintype.card ι)).map
      (fun j => orderedProjectorScalar i j r A)).prod = if r = i then 1 else 0 := by
  classical
  by_cases hri : r = i
  · subst r
    simp only [ite_true]
    apply List.prod_eq_one
    intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    by_cases hji : j = i
    · simp [orderedProjectorScalar, hji]
    · have hne : ((orderedEigenvalue A i - orderedEigenvalue A j : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr (fun h => hji (hi j h.symm))
      simpa [orderedProjectorScalar, hji, Complex.ofReal_sub] using inv_mul_cancel₀ hne
  · simp only [hri, ite_false]
    apply List.prod_eq_zero
    apply List.mem_map.mpr
    refine ⟨r, by simp, ?_⟩
    simp [orderedProjectorScalar, hri]

theorem orderedProjector_eq_outerProduct_of_rankSimple (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hi : RankSimple A i) :
    orderedProjector i A =
      fun x y => increasingEigenvector A.property i x *
        starRingEnd ℂ (increasingEigenvector A.property i y) := by
  apply matrix_eq_of_mulVec_increasingEigenvector_eq A
  intro r
  have hmul : (orderedProjector i A).mulVec (increasingEigenvector A.property r) =
      (if r = i then (1 : ℂ) else 0) • increasingEigenvector A.property r := by
    unfold orderedProjector
    rw [orderedProjectorProduct_mulVec, orderedProjectorScalar_prod_of_rankSimple i r A hi]
  rw [hmul]
  ext x
  change (if r = i then (1 : ℂ) else 0) * increasingEigenvector A.property r x =
    ∑ y, (increasingEigenvector A.property i x *
      starRingEnd ℂ (increasingEigenvector A.property i y)) * increasingEigenvector A.property r y
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, increasingEigenvector_orthonormal]
  by_cases hri : r = i
  · simp [hri]
  · simp [hri, Ne.symm hri]

theorem orderedProjector_diagonal_re_of_rankSimple (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hi : RankSimple A i) (x : ι) :
    (orderedProjector i A x x).re = ‖increasingEigenvector A.property i x‖ ^ 2 := by
  rw [orderedProjector_eq_outerProduct_of_rankSimple i A hi]
  simp only [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem exists_orderedColumnRegion_of_rankSimple (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hi : RankSimple A i) :
    ∃ j, A ∈ orderedColumnRegion i j := by
  classical
  have hav : ∃ j, orderedColumnAvailable i j A := by
    have hx : ∃ x : ι, 0 < ‖increasingEigenvector A.property i x‖ ^ 2 := by
      by_contra h
      push Not at h
      have hh := Finset.sum_nonpos (s := Finset.univ) (fun x _ => h x)
      rw [sum_norm_sq_increasingEigenvector] at hh
      norm_num at hh
    obtain ⟨x, hx⟩ := hx
    refine ⟨increasingIndex.symm x, ?_⟩
    unfold orderedColumnAvailable
    rw [Equiv.apply_symm_apply, orderedProjector_diagonal_re_of_rankSimple i A hi]
    exact hx
  let charts := Finset.univ.filter (fun j => orderedColumnAvailable i j A)
  have hn : charts.Nonempty := by
    obtain ⟨j, hj⟩ := hav
    exact ⟨j, by simp [charts, hj]⟩
  refine ⟨charts.min' hn, ?_⟩
  have hmem := Finset.min'_mem charts hn
  refine ⟨(Finset.mem_filter.mp hmem).2, ?_⟩
  intro k hk hka
  have hkmem : k ∈ charts := by simp [charts, hka]
  exact (not_le_of_gt hk) (Finset.min'_le charts k hkmem)

theorem orderedColumnSelection_eq_phase_of_rankSimple (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hi : RankSimple A i) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      orderedColumnSelection i A = z • increasingEigenvector A.property i := by
  obtain ⟨j, hj⟩ := exists_orderedColumnRegion_of_rankSimple i A hi
  have hpos : 0 < ‖increasingEigenvector A.property i (increasingIndex j)‖ := by
    have h := hj.1
    unfold orderedColumnAvailable at h
    rw [orderedProjector_diagonal_re_of_rankSimple i A hi] at h
    nlinarith [norm_nonneg (increasingEigenvector A.property i (increasingIndex j))]
  refine ⟨starRingEnd ℂ (increasingEigenvector A.property i (increasingIndex j)) /
      (‖increasingEigenvector A.property i (increasingIndex j)‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos, div_self hpos.ne']
  · funext x
    rw [orderedColumnSelection_eq_column i j A hj x]
    unfold orderedNormalizedColumn
    rw [orderedProjector_diagonal_re_of_rankSimple i A hi,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      orderedProjector_eq_outerProduct_of_rankSimple i A hi]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem orderedProjector_eq_zero_of_not_rankSimple (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hi : ¬ RankSimple A i) : orderedProjector i A = 0 := by
  unfold RankSimple at hi
  push Not at hi
  obtain ⟨j, hj, hji⟩ := hi
  unfold orderedProjector orderedProjectorProduct
  apply List.prod_eq_zero
  apply List.mem_map.mpr
  refine ⟨j, List.mem_finRange j, ?_⟩
  simp [orderedProjectorFactor, hji, hj]

theorem orderedColumnSelection_eq_zero_of_not_rankSimple (i : Fin (Fintype.card ι))
    (A : HermitianMatrix ι) (hi : ¬ RankSimple A i) : orderedColumnSelection i A = 0 := by
  funext x
  have h0 := orderedProjector_eq_zero_of_not_rankSimple i A hi
  unfold orderedColumnSelection
  apply Finset.sum_eq_zero
  intro j _
  have hj : A ∉ orderedColumnRegion i j := by
    intro h
    have h1 := h.1
    unfold orderedColumnAvailable at h1
    rw [h0] at h1
    simp at h1
  simp [hj]
end Simple

theorem dotProduct_self_of_l2Norm {ι : Type*} [Fintype ι] (v : ι → ℂ) (hv : l2Norm v = 1) :
    star v ⬝ᵥ v = 1 := by
  have h : ∑ k, ‖v k‖ ^ 2 = 1 := by
    have h0 : 0 ≤ ∑ k, ‖v k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    unfold l2Norm at hv
    have := Real.sq_sqrt h0
    rw [hv] at this
    linarith
  have h' : star v ⬝ᵥ v = ((∑ k, ‖v k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RCLike.star_def, Complex.conj_mul']
  rw [h', h, Complex.ofReal_one]

theorem card_frame : Fintype.card (PairSite p i) = Fintype.card (Unit ⊕ FrameIndex p) := by
  rw [card_pairSite, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  have := p.W_pos
  omega

end Pair

section Spectral
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A simple eigenvalue sits at the rank given by the number of eigenvalues below it. -/
theorem rank_of_simple {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (E : ℝ)
    (j0 : Fin (Fintype.card ι)) (hj0 : increasingEigenvalue hH j0 = E)
    (hsimple : ∀ j, increasingEigenvalue hH j = E → j = j0) :
    CoareaNative.BlockBand.eigenCount (⟨H, hH⟩ : CoareaNative.BlockBand.HermitianMatrix ι)
      (Set.Iio E) = j0.val := by
  classical
  rw [CoareaNative.BlockBand.eigenCount_def]
  have hfilter : (Finset.univ.filter fun j => CoareaNative.BlockBand.orderedEigenvalue
      (⟨H, hH⟩ : CoareaNative.BlockBand.HermitianMatrix ι) j ∈ Set.Iio E) = Finset.Iio j0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iio, Finset.mem_Iio]
    change increasingEigenvalue hH j < E ↔ j < j0
    constructor
    · intro h
      by_contra hj
      push Not at hj
      have := increasingEigenvalue_monotone hH hj
      linarith
    · intro h
      have hle := increasingEigenvalue_monotone hH h.le
      rcases hle.lt_or_eq with hlt | heq
      · linarith
      · exact absurd (hsimple j (heq.trans hj0)) (ne_of_lt h)
  rw [← Fin.card_Iio j0, ← hfilter]
  congr 1

end Spectral

section Contract
open CoareaNative.BlockBand (negativeEigenvalueCount)

/-- `CoareaContract.clock`. -/
theorem coarea_clock : ∀ (p : Parameters) (α : Fin p.N) (i : ZMod p.n) (H : p.SiteMatrix),
    H.IsHermitian →
    (exteriorBlock p i H - ((physicalOrderedEigenvalue p H α : ℝ) : ℂ) • 1).det ≠ 0 →
    ClockReconstruction p i α H := by
  intro p α i H hH hdet
  unfold ClockReconstruction
  dsimp only
  set r := physicalSpectralRank p α
  have hE : physicalOrderedEigenvalue p H α = increasingEigenvalue hH r :=
    rawIncreasingEigenvalue_eq r H hH
  have hψ : physicalOrderedEigenvector p H α = orderedColumnSelection r ⟨H, hH⟩ :=
    funext (rawOrderedColumnSelection_eq r H hH)
  by_cases hs : RankSimple (⟨H, hH⟩ : HermitianMatrix p.Site) r
  · obtain ⟨z, hz, hsel⟩ := orderedColumnSelection_eq_phase_of_rankSimple r _ hs
    apply clock_of_kernel p i H hH _ hdet _ ?_ ?_ _ (pairMass_eq p i α H)
    · rw [hψ, hsel, hE, Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, mulVec_increasingEigenvector, sub_self, smul_zero]
    · rw [hψ, hsel]
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [norm_sq_phase_mul z hz]
      exact sum_norm_sq_increasingEigenvector hH r
  · have hψ0 : physicalOrderedEigenvector p H α = 0 := by
      rw [hψ]; exact orderedColumnSelection_eq_zero_of_not_rankSimple r _ hs
    have hm0 : pairMass p i α H = 0 := by
      rw [pairMass_eq, hψ0]; simp
    simp only [hm0, hψ0, Pi.zero_apply, mul_zero, Real.sqrt_zero, _root_.inv_zero]
    simp only [← Pi.zero_def]
    refine ⟨Matrix.mulVec_zero _, by simp, fun x => ?_⟩
    simp [schurLift]

/-- `CoareaContract.reconstructed_rank`. -/
theorem coarea_reconstructed_rank : ∀ (p : Parameters) (α : Fin p.N) (i : ZMod p.n)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ),
    IsPairFrame p i U →
    ∀ (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ)
      (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ),
      (assemble p i ω (reconstructedGaussian p i U ω E v G')).IsHermitian →
      l2Norm v = 1 → (ω.1 - (E : ℂ) • 1).det ≠ 0 → (frameM p i U ω E v G').det ≠ 0 →
      negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val →
      let H := assemble p i ω (reconstructedGaussian p i U ω E v G')
      let L := schurLift p i ω.1 ω.2.1 E v
      physicalOrderedEigenvalue p H α = E ∧
        ∀ x y, physicalOrderedEigenvector p H α x * conj (physicalOrderedEigenvector p H α y) =
          ((l2Norm L ^ 2)⁻¹ : ℂ) * (L x * conj (L y)) := by
  intro p α i U hU ω E v G' hH hv hD hM hcnt H L
  set G := reconstructedGaussian p i U ω E v G'
  set M := frameM p i U ω E v G'
  obtain ⟨hUU, hUv⟩ := hU.2 v hv
  have hvv := dotProduct_self_of_l2Norm v hv
  have hc := frame_complete (U v) v hUU hUv hvv (card_frame p i)
  have hAeq : physicalCoareaA ω.1 ω.2.1 ω.2.2 G E = U v * M * (U v)ᴴ :=
    reconstructed_schur p i U ω E v G' hc
  have hAh := schurA_isHermitian p i ω G E hH
  -- inertia
  have hMeq : (U v)ᴴ * physicalCoareaA ω.1 ω.2.1 ω.2.2 G E * U v = M := by
    rw [hAeq, show (U v)ᴴ * (U v * M * (U v)ᴴ) * U v = ((U v)ᴴ * U v) * M * ((U v)ᴴ * U v) by
      simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one]
  have hMh : M.IsHermitian := by
    rw [← hMeq]; exact Matrix.isHermitian_conjTranspose_mul_mul (U v) hAh
  have hUMU : (U v * M * (U v)ᴴ).IsHermitian := by rw [← hAeq]; exact hAh
  have hcntA : negativeCount (physicalCoareaA ω.1 ω.2.1 ω.2.2 G E) = negativeCount M := by
    rw [negativeCount_eq hAh, negativeCount_eq hMh, negCount_congr hAh hUMU hAeq]
    exact negCount_frame (U v) M hUU hUMU hMh
  have hK := shift_isHermitian hH E
  have hcntK : negativeEigenvalueCount hK = α.val := by
    rw [← negativeCount_eq hK, haynsworth p i ω G E hH hD, hcntA, hcnt]
  have hEC : CoareaNative.BlockBand.eigenCount
      (⟨H, hH⟩ : CoareaNative.BlockBand.HermitianMatrix p.Site) (Set.Iio E) = α.val := by
    rw [← hcntK]
    exact (CoareaNative.BlockBand.negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
      ⟨H, hH⟩ E).symm
  -- kernel
  obtain ⟨hL0, hker⟩ := kernel_frame p i ω G E v (U v) M hAeq hUU hUv hc hD hM
  have hLne : L ≠ 0 := by
    intro h
    have h1 := schurLift_pair p i ω.1 ω.2.1 E v
    change (fun s : PairSite p i => L s.1) = v at h1
    rw [h] at h1
    rw [← h1] at hvv
    simp at hvv
  obtain ⟨j0, hj0⟩ :=
    CoareaNative.BlockBand.exists_orderedEigenvalue_eq_of_shift_mulVec_eq_zero
      (⟨H, hH⟩ : CoareaNative.BlockBand.HermitianMatrix p.Site) hLne hL0
  change increasingEigenvalue hH j0 = E at hj0
  -- eigenvectors at `E` are multiples of `L`
  have hmult : ∀ j, increasingEigenvalue hH j = E →
      increasingEigenvector hH j = (star v ⬝ᵥ (fun s : PairSite p i =>
        increasingEigenvector hH j s.1)) • L := by
    intro j hj
    apply hker
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mulVec_increasingEigenvector,
      hj, sub_self]
  have hsimple : ∀ j, increasingEigenvalue hH j = E → j = j0 := by
    intro j hj
    by_contra hne
    set cj := star v ⬝ᵥ (fun s : PairSite p i => increasingEigenvector hH j s.1)
    set ck := star v ⬝ᵥ (fun s : PairSite p i => increasingEigenvector hH j0 s.1)
    set s := ∑ x, starRingEnd ℂ (L x) * L x
    have horth := increasingEigenvector_orthonormal hH
    have h0 := horth j j0
    have h1 := horth j j
    have h2 := horth j0 j0
    rw [hmult j hj] at h0 h1
    rw [hmult j0 hj0] at h0 h2
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hne, ↓reduceIte] at h0 h1 h2
    have e0 : starRingEnd ℂ cj * ck * s = 0 := by
      rw [← h0, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have e1 : starRingEnd ℂ cj * cj * s = 1 := by
      rw [← h1, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have e2 : starRingEnd ℂ ck * ck * s = 1 := by
      rw [← h2, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    have : (1 : ℂ) = 0 := by
      linear_combination (cj * starRingEnd ℂ ck * s) * e0 - (starRingEnd ℂ ck * ck * s) * e1 - e2
    exact one_ne_zero this
  -- the rank
  have hrank := rank_of_simple hH E j0 hj0 hsimple
  rw [hEC] at hrank
  set r := physicalSpectralRank p α
  have hr : r = j0 := Fin.ext (by simp [r, physicalSpectralRank, hrank])
  have hEr : physicalOrderedEigenvalue p H α = E := by
    rw [show physicalOrderedEigenvalue p H α = increasingEigenvalue hH r from
      rawIncreasingEigenvalue_eq r H hH, hr, hj0]
  refine ⟨hEr, ?_⟩
  -- the eigenline
  have hsr : RankSimple (⟨H, hH⟩ : HermitianMatrix p.Site) r := by
    intro j hj
    change increasingEigenvalue hH j = increasingEigenvalue hH r at hj
    rw [hr, hj0] at hj
    rw [hr]; exact hsimple j hj
  obtain ⟨z, hz, hsel⟩ := orderedColumnSelection_eq_phase_of_rankSimple r _ hsr
  have hψ : physicalOrderedEigenvector p H α = z • increasingEigenvector hH r :=
    (funext (rawOrderedColumnSelection_eq r H hH)).trans hsel
  set c := star v ⬝ᵥ (fun s : PairSite p i => increasingEigenvector hH r s.1)
  have hur : increasingEigenvector hH r = c • L := hmult r (by rw [hr, hj0])
  have hnorm := sum_norm_sq_increasingEigenvector hH r
  rw [hur] at hnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow] at hnorm
  rw [← Finset.mul_sum] at hnorm
  have hL2 : l2Norm L ^ 2 = ∑ x, ‖L x‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _)
  have hzz : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  have hcc : c * starRingEnd ℂ c = ((l2Norm L ^ 2)⁻¹ : ℝ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hL2, eq_inv_of_mul_eq_one_left hnorm]
  intro x y
  rw [hψ, hur]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  have : z * (c * L x) * (starRingEnd ℂ z * (starRingEnd ℂ c * starRingEnd ℂ (L y))) =
      (z * starRingEnd ℂ z) * (c * starRingEnd ℂ c) * (L x * starRingEnd ℂ (L y)) := by ring
  rw [this, hzz, hcc, one_mul]
  push_cast
  rfl

end Contract

end BlockBand.Coarea.ClockRank
