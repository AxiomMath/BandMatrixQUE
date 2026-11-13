module

public import BlockBand.SourceProcess.PhysApprox.B3GramUpdAlg

/-!
# Every old frame column is an interior source

The closed Gram step is stated for columns `x = 𝒰_jᴴg`, `x' = 𝒰_{j+1}ᴴg'`
with `g'` the old-block embedding of `g`. Here every column of the open frame that is not newborn
at `j` has this form:

* probe columns: `g` is the probe column of `𝒥_j` (`probeColumns_comp_ne`, also for unborn tags);
* current columns: `𝒰_j` is injective for `j ≥ 2` with invertible end bonds
  (`boundaryToInterior_mulVec_injective`), so `𝒰_jᴴ` has a right inverse
  (`exists_conj_right_inv`) and `g = Rx`; the current column is transported by `N_jᴴ`
  (`gramCol_inl_succ`) and the transport bridge gives `N_jᴴ𝒰_jᴴg = 𝒰_{j+1}ᴴg'` (`conj_succ_mulVec`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.Bridge
open scoped ComplexOrder

variable {W np K : ℕ}

namespace GramUpd

/-!
## Injectivity of `𝒰`
-/

theorem eq_zero_of_isUnit_mulVec {M : Matrix (Fin W) (Fin W) ℂ} (hM : IsUnit M) {w : Fin W → ℂ}
    (h : M *ᵥ w = 0) : w = 0 :=
  (mulVec_injective_iff_isUnit.mpr hM) (h.trans (mulVec_zero M).symm)

/-- The port coupling of a path of length `n ≥ 2` with invertible end bonds is injective. -/
theorem coupling_mulVec_injective {n : ℕ} (hn : 2 ≤ n) (ω : GrowthPath W)
    (h0 : IsUnit (ω.2 0)) (hN : IsUnit (ω.2 n)) {v : Fin 2 × Fin W → ℂ}
    (hv : pathPortCoupling (pathAt W n ω) *ᵥ v = 0) : v = 0 := by
  have hfirst : (ω.2 n *ᵥ fun y => v (0, y)) = 0 := by
    funext x
    have := congrFun hv ((⟨0, by omega⟩ : Fin n), x)
    rw [Pi.zero_apply] at this ⊢
    rw [← this]
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, pathPortCoupling,
      pathAt]
    have hne : ¬ (0 + 1 = n) := by omega
    simp [hne]
  have hlast : (ω.2 0 *ᵥ fun y => v (1, y)) = 0 := by
    funext x
    have := congrFun hv ((⟨n - 1, by omega⟩ : Fin n), x)
    rw [Pi.zero_apply] at this ⊢
    rw [← this]
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, pathPortCoupling,
      pathAt]
    have hne : ¬ (n - 1 = 0) := by omega
    have he : n - 1 + 1 = n := by omega
    simp [hne, he]
  have e0 := eq_zero_of_isUnit_mulVec hN hfirst
  have e1 := eq_zero_of_isUnit_mulVec h0 hlast
  funext ⟨c, y⟩
  fin_cases c
  · exact congrFun e0 y
  · exact congrFun e1 y

/-- **`𝒰_n` is injective** for `n ≥ 2` with invertible end bonds. -/
theorem boundaryToInterior_mulVec_injective (b E : ℝ) {n : ℕ} (hn : 2 ≤ n) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1))
    (h0 : IsUnit (ω.2 0)) (hN : IsUnit (ω.2 n)) {v : Fin 2 × Fin W → ℂ}
    (hv : boundaryToInterior b E W n ω *ᵥ v = 0) : v = 0 := by
  obtain ⟨h1, h2⟩ := full_solution b E n ω (isUnit_fullPathMatrix b E n ω hA hη hF)
  have hR : boundaryResolvent b E W n ω *ᵥ v = 0 := by
    apply coupling_mulVec_injective hn ω h0 hN
    have := congrArg (· *ᵥ v) h1
    simp only [add_mulVec, ← mulVec_mulVec, hv, mulVec_zero, zero_add, zero_mulVec] at this
    exact this
  have := congrArg (· *ᵥ v) h2
  simp only [add_mulVec, ← mulVec_mulVec, hv, mulVec_zero, zero_add, smul_mulVec, hR,
    smul_zero, one_mulVec] at this
  exact this.symm

/-- **`𝒰_nᴴ` has a right inverse** for `n ≥ 2` with invertible end bonds. -/
theorem exists_conj_right_inv (b E : ℝ) {n : ℕ} (hn : 2 ≤ n) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1))
    (h0 : IsUnit (ω.2 0)) (hN : IsUnit (ω.2 n)) :
    ∃ Rr : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ, (boundaryToInterior b E W n ω)ᴴ * Rr = 1 := by
  set U := boundaryToInterior b E W n ω
  have hdet : IsUnit (Uᴴ * U).det := by
    rw [isUnit_iff_ne_zero]
    intro hd
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr hd
    apply hv0
    apply boundaryToInterior_mulVec_injective b E hn ω hA hη hF h0 hN
    have h1 : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = 0 := by
      rw [dotProduct_mulVec, star_mulVec, vecMul_vecMul, ← dotProduct_mulVec, hv,
        dotProduct_zero]
    exact dotProduct_star_self_eq_zero.mp h1
  exact ⟨U * (Uᴴ * U)⁻¹, by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hdet]⟩

/-!
## The columns
-/

theorem probeColumns_comp_ne (τ m : Fin np → ℝ) (g : Fin np → Fin W → ℂ) {l : ℕ} {k : Fin np}
    (hk : ⌊(W : ℝ) * τ k⌋₊ ≠ l) :
    (fun x => probeColumns W (l + 1) τ m g x k) ∘ headEquiv l W =
      Sum.elim (0 : Fin W → ℂ) (fun x => probeColumns W l τ m g x k) := by
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · exact probeColumns_comp_old τ m g hlt
  · funext x
    rcases x with x | ⟨i, x⟩
    · simp only [Function.comp_apply, Sum.elim_inl, Pi.zero_apply, probeColumns]
      rw [ite_eq_right_iff]
      omega
    · simp only [Function.comp_apply, Sum.elim_inr, probeColumns]
      rw [ite_eq_right_iff.mpr (fun h => by omega), ite_eq_right_iff.mpr (fun h => by omega)]

theorem gramCol_inr (b E s : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (i : Fin np)
    (x : ProbedPath W np) :
    gramCol b E s τ m W j Vs (Sum.inr i) x =
      (boundaryToInterior b E W j x.1)ᴴ *ᵥ fun a => probeColumns W j τ m x.2 a i := by
  rw [← probeCol_eq]
  rfl

/-- The current columns are transported by `N_jᴴ`. -/
theorem gramCol_inl_succ (b E s : ℝ) (τ m : Fin np → ℝ) {j : ℕ} (hs : closeLen s W ≤ j)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (k : Fin K × Fin 2)
    (x : ProbedPath W np) :
    gramCol b E s τ m W (j + 1) Vs (Sum.inl k) x =
      (transportN b E W j x.1)ᴴ *ᵥ gramCol b E s τ m W j Vs (Sum.inl k) x := by
  have e : j + 1 - closeLen s W = (j - closeLen s W) + 1 := by omega
  have e' : closeLen s W + (j - closeLen s W) = j := by omega
  funext a
  simp only [gramCol, b3OpenFrameAt, Matrix.of_apply, Sum.elim_inl, e, stepProd, e',
    conjTranspose_mul, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, mulVec, dotProduct]
  rfl

/-- The transport bridge on interior sources: `N_jᴴ𝒰_jᴴg = 𝒰_{j+1}ᴴg'` for the old-block embedding
`g'`. -/
theorem conj_succ_mulVec (b E : ℝ) {j : ℕ} (ω : GrowthPath W)
    (hT : (boundaryToInterior b E W (j + 1) ω).submatrix (headEquiv j W) id =
      Matrix.fromRows (nearSel W * boundaryResolvent b E W j ω * transportN b E W j ω)
        (boundaryToInterior b E W j ω * transportN b E W j ω))
    (g : Fin j × Fin W → ℂ) :
    (boundaryToInterior b E W (j + 1) ω)ᴴ *ᵥ (Sum.elim (0 : Fin W → ℂ) g ∘ (headEquiv j W).symm) =
      (transportN b E W j ω)ᴴ *ᵥ ((boundaryToInterior b E W j ω)ᴴ *ᵥ g) := by
  rw [conj_mulVec_reindex (headEquiv j W), Function.comp_assoc, Equiv.symm_comp_self,
    Function.comp_id, hT, fromRows_conj_mulVec_elim, conjTranspose_mul, mulVec_mulVec]

theorem comp_symm_headEquiv {j : ℕ} (g : Fin j × Fin W → ℂ) :
    (Sum.elim (0 : Fin W → ℂ) g ∘ (headEquiv j W).symm) ∘ headEquiv j W =
      Sum.elim (0 : Fin W → ℂ) g := by
  rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

/-- **Every column that is not newborn at `j` is an interior source**, at a sample with the
almost-sure facts, `j ≥ n_s`, `j ≥ 2`. -/
theorem gramCol_rep (b E s : ℝ) (τ m : Fin np → ℝ) {j : ℕ} (hs : closeLen s W ≤ j) (hj : 2 ≤ j)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : ProbedPath W np)
    (hA : ∀ k, (x.1.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W j x.1) - (E : ℂ) • 1))
    (h0 : IsUnit (x.1.2 0)) (hN : IsUnit (x.1.2 j))
    (hT : (boundaryToInterior b E W (j + 1) x.1).submatrix (headEquiv j W) id =
      Matrix.fromRows (nearSel W * boundaryResolvent b E W j x.1 * transportN b E W j x.1)
        (boundaryToInterior b E W j x.1 * transportN b E W j x.1))
    (d : SrcCol K (Fin np)) (hd : ¬ IsNewCol τ W j d) :
    ∃ (g : Fin j × Fin W → ℂ) (g' : Fin (j + 1) × Fin W → ℂ),
      g' ∘ headEquiv j W = Sum.elim (0 : Fin W → ℂ) g ∧
      gramCol b E s τ m W j Vs d x = (boundaryToInterior b E W j x.1)ᴴ *ᵥ g ∧
      gramCol b E s τ m W (j + 1) Vs d x = (boundaryToInterior b E W (j + 1) x.1)ᴴ *ᵥ g' := by
  rcases d with k | i
  · obtain ⟨Rr, hRr⟩ := exists_conj_right_inv b E hj x.1 hA hη hF h0 hN
    have hx : (boundaryToInterior b E W j x.1)ᴴ *ᵥ
        (Rr *ᵥ gramCol b E s τ m W j Vs (Sum.inl k) x) =
          gramCol b E s τ m W j Vs (Sum.inl k) x := by
      rw [mulVec_mulVec, hRr, one_mulVec]
    refine ⟨Rr *ᵥ gramCol b E s τ m W j Vs (Sum.inl k) x,
      Sum.elim (0 : Fin W → ℂ) (Rr *ᵥ gramCol b E s τ m W j Vs (Sum.inl k) x) ∘
        (headEquiv j W).symm, comp_symm_headEquiv _, ?_, ?_⟩
    · exact hx.symm
    · rw [conj_succ_mulVec b E x.1 hT, hx, gramCol_inl_succ b E s τ m hs]
  · have hi : ⌊(W : ℝ) * τ i⌋₊ ≠ j := hd
    exact ⟨_, _, probeColumns_comp_ne τ m x.2 hi, gramCol_inr b E s τ m W j Vs i x,
      gramCol_inr b E s τ m W (j + 1) Vs i x⟩

end GramUpd

end BlockBand.SourceProcess.PhysApprox.B3
