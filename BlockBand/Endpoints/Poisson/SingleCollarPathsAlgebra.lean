module

public import BlockBand.Endpoints.Poisson.SingleCollarWard

/-!
# The source Gram matrix of a network with decoupled path components

Setting. A network matrix `H` on sites `X`, with an ordering `σ : Pt ⊕ In ≃ X` into input ports
and interior; a source predicate on the interior. Components `i ∈ T`: injective site maps
`Φ i : FullSite W (r i) → X` (path sites and two port sites) on which `H` is the matrix `M i`,
and which `H` couples to no other site. Every network port is a port of some component, the path
sites of a component are interior and its port sites are network ports.

* `scp_fracTrace_mul_comm_rect`: `Tr (AB)^q = Tr (BA)^q` for rectangular `A`, `B` and `q > 0`.
* `scp_inv_block`: if `H` is invertible, so is `M i`, `H⁻¹` restricted to the component is
  `(M i)⁻¹`, and `H⁻¹` couples the component to no other site.
* `scp_gram_le`: **`Tr Q^q ≤ Σ_{i ∈ T} Tr Q_i^q`** (`0 < q ≤ 1`) for the source Gram matrix
  `Q = (D𝒰)*(D𝒰)` of `H` (`𝒰 = (H⁻¹)_{In,Pt}`, `D` the source projection) and the component
  Gram matrices `Q_i = 𝒰_i* P_{C_i} 𝒰_i`, `𝒰_i = ((M i)⁻¹)_{path,ports}`, `P_{C_i}` the source
  sites of component `i`. (Rows outside every component vanish; the remaining rows are grouped by
  component, which only overcounts; subadditivity of `x ↦ x^q`; the port embedding of each
  component is an isometry.)
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix Function
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace FullSite)
open scoped ComplexOrder

/-!
## Rectangular commutation
-/

section Rect

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- `Tr (AB)^q = Tr (BA)^q` for `A : m × n`, `B : n × m` and `q > 0` (the spectra differ by
zeros). -/
theorem scp_fracTrace_mul_comm_rect (A : Matrix m n ℂ) (B : Matrix n m ℂ) {q : ℝ} (hq : 0 < q) :
    fracTrace q (A * B) = fracTrace q (B * A) := by
  have h := charpoly_mul_comm' A B
  have hr := congrArg Polynomial.roots h
  rw [Polynomial.roots_mul ((Polynomial.monic_X_pow _).mul (charpoly_monic _)).ne_zero,
    Polynomial.roots_mul ((Polynomial.monic_X_pow _).mul (charpoly_monic _)).ne_zero,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hr
  have h2 := congrArg (fun s : Multiset ℂ => (s.map fun z => (max z.re 0) ^ q).sum) hr
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul,
    Multiset.map_singleton, Multiset.sum_singleton, Complex.zero_re, max_self,
    Real.zero_rpow hq.ne', smul_zero, zero_add] at h2
  exact h2

end Rect

/-!
## The inverse of a network with a decoupled block
-/

section Block

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [DecidableEq X] [DecidableEq Y] in
theorem scp_sum_range {Φ : Y → X} (hΦ : Injective Φ) (f : X → ℂ)
    (hf : ∀ y ∉ Set.range Φ, f y = 0) : ∑ x, f x = ∑ a, f (Φ a) :=
  (Fintype.sum_of_injective Φ hΦ (fun a => f (Φ a)) f hf fun _ => rfl).symm

/-- **Inverse of a network with a decoupled block.** -/
theorem scp_inv_block {H : Matrix X X ℂ} {Φ : Y → X} (hΦ : Injective Φ) {M : Matrix Y Y ℂ}
    (hblock : ∀ a b, H (Φ a) (Φ b) = M a b)
    (hdec : ∀ a y, y ∉ Set.range Φ → H (Φ a) y = 0 ∧ H y (Φ a) = 0) (hH : IsUnit H.det) :
    (∀ a b, H⁻¹ (Φ a) (Φ b) = M⁻¹ a b) ∧
      ∀ a y, y ∉ Set.range Φ → H⁻¹ (Φ a) y = 0 ∧ H⁻¹ y (Φ a) = 0 := by
  set N : Matrix Y Y ℂ := Matrix.of fun a b => H⁻¹ (Φ a) (Φ b)
  have hHH := mul_nonsing_inv H hH
  have hHH' := nonsing_inv_mul H hH
  -- the left block row of `H` only sees the block
  have hrow : ∀ a (g : X → ℂ), ∑ x, H (Φ a) x * g x = ∑ a', M a a' * g (Φ a') := by
    intro a g
    rw [scp_sum_range hΦ _ fun y hy => by rw [(hdec a y hy).1, zero_mul]]
    simp only [hblock]
  have hcol : ∀ a' (g : X → ℂ), ∑ x, g x * H x (Φ a') = ∑ a, g (Φ a) * M a a' := by
    intro a' g
    rw [scp_sum_range hΦ _ fun y hy => by rw [(hdec a' y hy).2, mul_zero]]
    simp only [hblock]
  have hMN : M * N = 1 := by
    ext a b
    have h := congrFun (congrFun hHH (Φ a)) (Φ b)
    rw [Matrix.mul_apply, hrow a (fun x => H⁻¹ x (Φ b))] at h
    rw [Matrix.mul_apply]
    simp only [N, of_apply]
    rw [h]
    by_cases hab : a = b
    · subst hab; simp
    · have : Φ a ≠ Φ b := fun he => hab (hΦ he)
      simp [one_apply, hab, this]
  have hNM : N * M = 1 := mul_eq_one_comm.mp hMN
  have hinv : M⁻¹ = N := inv_eq_right_inv hMN
  refine ⟨fun a b => by rw [hinv]; rfl, fun a y hy => ⟨?_, ?_⟩⟩
  · set v : Y → ℂ := fun a => H⁻¹ (Φ a) y
    have hv : M *ᵥ v = 0 := by
      funext a'
      have h := congrFun (congrFun hHH (Φ a')) y
      rw [Matrix.mul_apply, hrow a' (fun x => H⁻¹ x y)] at h
      have hne : Φ a' ≠ y := fun he => hy ⟨a', he⟩
      rw [one_apply_ne hne] at h
      simpa only [mulVec, dotProduct, Pi.zero_apply] using h
    have h0 : v = 0 := by
      rw [← one_mulVec v, ← hNM, ← mulVec_mulVec, hv, mulVec_zero]
    exact congrFun h0 a
  · set u : Y → ℂ := fun a => H⁻¹ y (Φ a)
    have hu : u ᵥ* M = 0 := by
      funext a'
      have h := congrFun (congrFun hHH' y) (Φ a')
      rw [Matrix.mul_apply, hcol a' (fun x => H⁻¹ y x)] at h
      have hne : y ≠ Φ a' := fun he => hy ⟨a', he.symm⟩
      rw [one_apply_ne hne] at h
      simpa only [vecMul, dotProduct, Pi.zero_apply] using h
    have h0 : u = 0 := by
      rw [← vecMul_one u, ← hMN, ← vecMul_vecMul, hu, zero_vecMul]
    exact congrFun h0 a

end Block

/-!
## The source Gram matrix
-/

section Gram

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem scp_conj_diag_apply (A : Matrix ι κ ℂ) (w : ι → ℂ) (p p' : κ) :
    (Aᴴ * diagonal w * A) p p' = ∑ a, star (A a p) * w a * A a p' := by
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply]

omit [DecidableEq κ] in
theorem scp_posSemidef_conj_diag (A : Matrix ι κ ℂ) {w : ι → ℝ} (hw : ∀ a, 0 ≤ w a) :
    (Aᴴ * diagonal (fun a => (w a : ℂ)) * A).PosSemidef := by
  refine PosSemidef.conjTranspose_mul_mul_same ?_ A
  rw [posSemidef_diagonal_iff]
  intro a
  exact_mod_cast hw a

/-- The `0/1` indicator as a real number. -/
def scpInd (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

theorem scp_ind_nonneg (P : Prop) [Decidable P] : 0 ≤ scpInd P := by
  unfold scpInd; split_ifs <;> norm_num

end Gram

section Main

variable {X Pt In : Type} [Fintype X] [DecidableEq X] [Fintype Pt] [DecidableEq Pt] [Fintype In]
  [DecidableEq In] {W m : ℕ}

open Classical in
/-- The component Gram weight: `1` on the path sites of component `i` that are source sites. -/
def scpWeight (σ : Pt ⊕ In ≃ X) (src : In → Prop) {r : ℕ} (Φ : FullSite W r → X)
    (a : Fin r × Fin W) : ℝ :=
  scpInd (∃ u, src u ∧ σ (Sum.inr u) = Φ (Sum.inl a))

/-- The component Gram matrix `𝒰_i* P_{C_i} 𝒰_i`, `𝒰_i = ((M i)⁻¹)_{path,ports}`. -/
def scpCompGram (σ : Pt ⊕ In ≃ X) (src : In → Prop) {r : ℕ} (Φ : FullSite W r → X)
    (M : Matrix (FullSite W r) (FullSite W r) ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (M⁻¹.toBlocks₁₂)ᴴ * diagonal (fun a => (scpWeight σ src Φ a : ℂ)) * M⁻¹.toBlocks₁₂

open Classical in
/-- **The source Gram matrix of a network with decoupled path components.** -/
theorem scp_gram_le (σ : Pt ⊕ In ≃ X) (H : Matrix X X ℂ) (src : In → Prop)
    (T : Finset (Fin m)) (r : Fin m → ℕ) (Φ : ∀ i, FullSite W (r i) → X)
    (M : ∀ i, Matrix (FullSite W (r i)) (FullSite W (r i)) ℂ)
    (hinj : ∀ i ∈ T, Injective (Φ i))
    (hblock : ∀ i ∈ T, ∀ a b, H (Φ i a) (Φ i b) = M i a b)
    (hdec : ∀ i ∈ T, ∀ a y, y ∉ Set.range (Φ i) → H (Φ i a) y = 0 ∧ H y (Φ i a) = 0)
    (hint : ∀ i ∈ T, ∀ a, ∃ u, σ (Sum.inr u) = Φ i (Sum.inl a))
    (hport : ∀ i ∈ T, ∀ c, ∃ p, σ (Sum.inl p) = Φ i (Sum.inr c))
    (hcov : ∀ p, ∃ i ∈ T, ∃ c, σ (Sum.inl p) = Φ i (Sum.inr c)) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≤ 1) :
    fracTrace q (scwGram (diagonal fun u => if src u then (1 : ℂ) else 0) (H.submatrix σ σ)⁻¹) ≤
      ∑ i ∈ T, fracTrace q (scpCompGram σ src (Φ i) (M i)) := by
  set D : Matrix In In ℂ := diagonal fun u => if src u then (1 : ℂ) else 0
  have hnonneg : 0 ≤ ∑ i ∈ T, fracTrace q (scpCompGram σ src (Φ i) (M i)) :=
    Finset.sum_nonneg fun i _ => fracTrace_nonneg _ _
  by_cases hH : IsUnit H.det
  swap
  · have h0 : (H.submatrix σ σ)⁻¹ = 0 := by
      apply nonsing_inv_apply_not_isUnit
      rwa [det_submatrix_equiv_self]
    rw [h0]
    have hg : scwGram D (0 : Matrix (Pt ⊕ In) (Pt ⊕ In) ℂ) = 0 := by
      have h0 : (0 : Matrix (Pt ⊕ In) (Pt ⊕ In) ℂ).toBlocks₂₁ = 0 := by ext; rfl
      simp [scwGram, h0]
    rw [hg, rh_fracTrace_zero hq0]
    exact hnonneg
  have hGs : (H.submatrix σ σ)⁻¹ = H⁻¹.submatrix σ σ := inv_submatrix_equiv H σ σ
  set U : Matrix In Pt ℂ := Matrix.of fun u p => H⁻¹ (σ (Sum.inr u)) (σ (Sum.inl p))
  have hU : (H⁻¹.submatrix σ σ).toBlocks₂₁ = U := rfl
  have hσl : ∀ p u, σ (Sum.inl p) ≠ σ (Sum.inr u) := fun p u h => by
    have := σ.injective h; simp at this
  set inRun : Fin m → In → Prop := fun i u => ∃ a, σ (Sum.inr u) = Φ i (Sum.inl a)
  -- rows outside every component vanish
  have hK1 : ∀ u, (¬ ∃ i ∈ T, inRun i u) → ∀ p, U u p = 0 := by
    intro u hu p
    obtain ⟨i, hi, c, hc⟩ := hcov p
    have hnr : σ (Sum.inr u) ∉ Set.range (Φ i) := by
      rintro ⟨x | x, hx⟩
      · exact hu ⟨i, hi, x, hx.symm⟩
      · obtain ⟨p', hp'⟩ := hport i hi x
        exact hσl p' u (hp'.trans hx)
    have h := ((scp_inv_block (hinj i hi) (hblock i hi) (hdec i hi) hH).2 (Sum.inr c) _ hnr).2
    simp only [U, of_apply, hc]
    exact h
  -- the port embedding of a component
  set E : ∀ i, Matrix (Fin 2 × Fin W) Pt ℂ :=
    fun i => Matrix.of fun c p => if σ (Sum.inl p) = Φ i (Sum.inr c) then 1 else 0
  set B : ∀ i, Matrix (Fin (r i) × Fin W) (Fin 2 × Fin W) ℂ := fun i => (M i)⁻¹.toBlocks₁₂
  -- rows of a component
  have hK2 : ∀ i ∈ T, ∀ a p, H⁻¹ (Φ i (Sum.inl a)) (σ (Sum.inl p)) = (B i * E i) a p := by
    intro i hi a p
    have hb := scp_inv_block (hinj i hi) (hblock i hi) (hdec i hi) hH
    rw [Matrix.mul_apply]
    by_cases hc : ∃ c, σ (Sum.inl p) = Φ i (Sum.inr c)
    · obtain ⟨c₀, hc₀⟩ := hc
      rw [Finset.sum_eq_single c₀]
      · simp only [E, of_apply, hc₀, ite_true, mul_one, B]
        exact hb.1 _ _
      · intro c _ hne
        have : σ (Sum.inl p) ≠ Φ i (Sum.inr c) := by
          rw [hc₀]; intro h; exact hne (Sum.inr_injective (hinj i hi h)).symm
        simp only [E, of_apply, this, ite_false, mul_zero]
      · intro h; exact absurd (Finset.mem_univ c₀) h
    · push Not at hc
      have hnr : σ (Sum.inl p) ∉ Set.range (Φ i) := by
        rintro ⟨x | x, hx⟩
        · obtain ⟨u, hu⟩ := hint i hi x
          exact hσl p u (hx.symm.trans hu.symm)
        · exact hc x hx.symm
      rw [(hb.2 (Sum.inl a) _ hnr).1]
      symm
      refine Finset.sum_eq_zero fun c _ => ?_
      simp only [E, of_apply, hc c, ite_false, mul_zero]
  -- the Gram matrix in diagonal form
  set d : In → ℝ := fun u => scpInd (src u)
  set d' : In → ℝ := fun u => scpInd (src u ∧ ∃ i ∈ T, inRun i u)
  set di : Fin m → In → ℝ := fun i u => scpInd (src u ∧ inRun i u)
  have hgram : scwGram D (H⁻¹.submatrix σ σ) = Uᴴ * diagonal (fun u => (d u : ℂ)) * U := by
    rw [scwGram, hU, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Dᴴ,
      ← Matrix.mul_assoc Uᴴ]
    congr 2
    simp only [D, diagonal_conjTranspose, diagonal_mul_diagonal, d, scpInd]
    congr 1; funext u; by_cases h : src u <;> simp [h]
  have hgram' : Uᴴ * diagonal (fun u => (d u : ℂ)) * U = Uᴴ * diagonal (fun u => (d' u : ℂ)) * U := by
    ext p p'
    rw [scp_conj_diag_apply, scp_conj_diag_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : ∃ i ∈ T, inRun i u
    · simp only [d, d', scpInd, h, and_true]
    · simp only [hK1 u h p, hK1 u h p', star_zero, zero_mul, mul_zero]
  -- grouping by components
  set Y : Fin m → Matrix Pt Pt ℂ := fun i => Uᴴ * diagonal (fun u => (di i u : ℂ)) * U
  have hYpsd : ∀ i, (Y i).PosSemidef := fun i =>
    scp_posSemidef_conj_diag U fun u => scp_ind_nonneg _
  have hK3 : (∑ i ∈ T, Y i - Uᴴ * diagonal (fun u => (d' u : ℂ)) * U).PosSemidef := by
    have heq : ∑ i ∈ T, Y i - Uᴴ * diagonal (fun u => (d' u : ℂ)) * U =
        Uᴴ * diagonal (fun u => (((∑ i ∈ T, di i u) - d' u : ℝ) : ℂ)) * U := by
      ext p p'
      rw [Matrix.sub_apply, Matrix.sum_apply, scp_conj_diag_apply]
      simp only [Y, scp_conj_diag_apply]
      rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      push_cast; ring
    rw [heq]
    refine scp_posSemidef_conj_diag U fun u => ?_
    rw [sub_nonneg]
    by_cases h : src u ∧ ∃ i ∈ T, inRun i u
    · obtain ⟨hs, i, hi, hr⟩ := h
      have hle : di i u ≤ ∑ j ∈ T, di j u :=
        Finset.single_le_sum (f := fun j => di j u) (fun j _ => scp_ind_nonneg _) hi
      have h1 : di i u = 1 := by simp [di, scpInd, hs, hr]
      have h2 : d' u = 1 := by simp only [d', scpInd]; rw [ite_eq_left_iff.mpr]; intro h; exact absurd ⟨hs, i, hi, hr⟩ h
      linarith
    · have h2 : d' u = 0 := by simp only [d', scpInd]; exact ite_eq_right_iff.mpr fun h' => absurd h' h
      rw [h2]
      exact Finset.sum_nonneg fun j _ => scp_ind_nonneg _
  -- each component Gram matrix through the port embedding
  have hK4 : ∀ i ∈ T, Y i = (E i)ᴴ * scpCompGram σ src (Φ i) (M i) * E i := by
    intro i hi
    choose e he using hint i hi
    have heinj : Injective e := fun a a' h => by
      have := (he a).symm.trans ((congrArg (fun u => σ (Sum.inr u)) h).trans (he a'))
      exact Sum.inl_injective (hinj i hi this)
    ext p p'
    simp only [Y]
    rw [scp_conj_diag_apply]
    have hR : (E i)ᴴ * scpCompGram σ src (Φ i) (M i) * E i =
        (B i * E i)ᴴ * diagonal (fun a => (scpWeight σ src (Φ i) a : ℂ)) * (B i * E i) := by
      simp only [scpCompGram, conjTranspose_mul, Matrix.mul_assoc, B]
    rw [hR, scp_conj_diag_apply]
    refine (Fintype.sum_of_injective e heinj _ _ ?_ ?_).symm
    · intro u hu
      have : di i u = 0 := by
        simp only [di, scpInd]
        refine ite_eq_right_iff.mpr ?_
        rintro ⟨-, a, ha⟩
        exact absurd ⟨a, Sum.inr_injective (σ.injective (by rw [he a, ha]))⟩ hu
      simp [this]
    · intro a
      have hw : di i (e a) = scpWeight σ src (Φ i) a := by
        simp only [di, scpWeight, scpInd]
        congr 1
        apply propext
        constructor
        · rintro ⟨hs, -⟩; exact ⟨e a, hs, he a⟩
        · rintro ⟨u, hs, hu⟩
          have : u = e a := Sum.inr_injective (σ.injective (by rw [hu, he a]))
          subst this
          exact ⟨hs, a, he a⟩
      simp only [U, of_apply, he a, hK2 i hi, hw]
  -- the port embedding is an isometry
  have hEE : ∀ i ∈ T, E i * (E i)ᴴ = 1 := by
    intro i hi
    ext c c'
    rw [Matrix.mul_apply]
    obtain ⟨p₀, hp₀⟩ := hport i hi c
    rw [Finset.sum_eq_single p₀]
    · simp only [E, of_apply, conjTranspose_apply, hp₀, ite_true, one_mul, one_apply]
      by_cases hcc : c = c'
      · subst hcc; simp
      · have : Φ i (Sum.inr c) ≠ Φ i (Sum.inr c') := fun h =>
          hcc (Sum.inr_injective (hinj i hi h))
        simp [this, hcc]
    · intro p _ hne
      have : σ (Sum.inl p) ≠ Φ i (Sum.inr c) := by
        rw [← hp₀]; intro h; exact hne (Sum.inl_injective (σ.injective h))
      simp [E, of_apply, this]
    · intro h; exact absurd (Finset.mem_univ p₀) h
  have hK5 : ∀ i ∈ T, fracTrace q (Y i) = fracTrace q (scpCompGram σ src (Φ i) (M i)) := by
    intro i hi
    rw [hK4 i hi, Matrix.mul_assoc, scp_fracTrace_mul_comm_rect _ _ hq0, Matrix.mul_assoc,
      hEE i hi, Matrix.mul_one]
  -- conclusion
  rw [hGs, hgram, hgram']
  have hsumpsd : (∑ i ∈ T, Y i).PosSemidef := posSemidef_sum _ fun i _ => hYpsd i
  calc fracTrace q (Uᴴ * diagonal (fun u => (d' u : ℂ)) * U)
      ≤ fracTrace q (∑ i ∈ T, Y i) :=
        fracTrace_mono (scp_posSemidef_conj_diag U fun u => scp_ind_nonneg _).isHermitian
          hsumpsd.isHermitian hK3 hq0.le
    _ ≤ ∑ i ∈ T, fracTrace q (Y i) := rh_fracTrace_sum_le T Y (fun i _ => hYpsd i) hq0 hq1
    _ = ∑ i ∈ T, fracTrace q (scpCompGram σ src (Φ i) (M i)) :=
        Finset.sum_congr rfl fun i hi => hK5 i hi

end Main

end BlockBand.Endpoints
