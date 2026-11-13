module

public import BlockBand.Transmission.PassiveCovariance.SdSite

/-!
# Polynomial bounds in a weight `B ≥ 1`

Integrability bookkeeping for the first-letter expansion: functionals, matrices, bilinear forms
and entries bounded by `C B^k`, and their closure under sums, products and the self-energy
operator (`‖S[M]‖ ≤ 2‖M‖`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix.Norms.L2Operator

section Poly
variable {Ω : Type*} (B : Ω → ℝ)

/-- `|F| ≤ C B^k`. -/
def PolyB (F : Ω → ℂ) (k : ℕ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, ‖F ω‖ ≤ C * B ω ^ k

/-- `‖A‖ ≤ C B^k` (operator norm). -/
def PolyBM {n : Type*} [Fintype n] [DecidableEq n] (A : Ω → Matrix n n ℂ) (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, ‖A ω‖ ≤ C * B ω ^ k

variable {B} (hB : ∀ ω, 1 ≤ B ω)
include hB

theorem PolyB.mono {F : Ω → ℂ} {k l : ℕ} (h : PolyB B F k) (hkl : k ≤ l) : PolyB B F l := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun ω => (h ω).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hB ω) hkl) hC)⟩

omit hB in
theorem PolyB.mul {F G : Ω → ℂ} {k l : ℕ} (hF : PolyB B F k) (hG : PolyB B G l) :
    PolyB B (fun ω => F ω * G ω) (k + l) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C * D, mul_nonneg hC hD, fun ω => ?_⟩
  rw [norm_mul, pow_add]
  calc ‖F ω‖ * ‖G ω‖ ≤ (C * B ω ^ k) * (D * B ω ^ l) :=
        mul_le_mul (hF ω) (hG ω) (norm_nonneg _) ((norm_nonneg _).trans (hF ω))
    _ = C * D * (B ω ^ k * B ω ^ l) := by ring

omit hB in
theorem PolyB.add {F G : Ω → ℂ} {k : ℕ} (hF : PolyB B F k) (hG : PolyB B G k) :
    PolyB B (fun ω => F ω + G ω) k := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  exact ⟨C + D, add_nonneg hC hD, fun ω => (norm_add_le _ _).trans
    (by have := hF ω; have := hG ω; linarith)⟩

omit hB in
theorem PolyB.neg {F : Ω → ℂ} {k : ℕ} (hF : PolyB B F k) : PolyB B (fun ω => -F ω) k := by
  obtain ⟨C, hC, hF⟩ := hF
  exact ⟨C, hC, fun ω => by rw [norm_neg]; exact hF ω⟩

omit hB in
theorem PolyB.sub {F G : Ω → ℂ} {k : ℕ} (hF : PolyB B F k) (hG : PolyB B G k) :
    PolyB B (fun ω => F ω - G ω) k := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

omit hB in
theorem PolyB.const_mul {F : Ω → ℂ} {k : ℕ} (c : ℂ) (hF : PolyB B F k) :
    PolyB B (fun ω => c * F ω) k := by
  obtain ⟨C, hC, hF⟩ := hF
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun ω => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hF ω) (norm_nonneg _)

omit hB in
theorem PolyB.sum {ι : Type*} (s : Finset ι) {F : ι → Ω → ℂ} {k : ℕ}
    (hF : ∀ i ∈ s, PolyB B (F i) k) : PolyB B (fun ω => ∑ i ∈ s, F i ω) k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, fun ω => by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

omit hB in
theorem PolyB.const (c : ℂ) : PolyB B (fun _ => c) 0 := ⟨‖c‖, norm_nonneg _, fun ω => by simp⟩

omit hB in
theorem PolyB.of_le {F G : Ω → ℂ} {k : ℕ} (hG : PolyB B G k) (h : ∀ ω, ‖F ω‖ ≤ ‖G ω‖) :
    PolyB B F k := by
  obtain ⟨C, hC, hG⟩ := hG
  exact ⟨C, hC, fun ω => (h ω).trans (hG ω)⟩

section Mat
variable {n : Type*} [Fintype n] [DecidableEq n]

omit hB in
theorem PolyBM.mul {A A' : Ω → Matrix n n ℂ} {k l : ℕ} (hA : PolyBM B A k) (hA' : PolyBM B A' l) :
    PolyBM B (fun ω => A ω * A' ω) (k + l) := by
  obtain ⟨C, hC, hA⟩ := hA
  obtain ⟨D, hD, hA'⟩ := hA'
  refine ⟨C * D, mul_nonneg hC hD, fun ω => ?_⟩
  rw [pow_add]
  calc ‖A ω * A' ω‖ ≤ ‖A ω‖ * ‖A' ω‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (C * B ω ^ k) * (D * B ω ^ l) :=
        mul_le_mul (hA ω) (hA' ω) (norm_nonneg _) ((norm_nonneg _).trans (hA ω))
    _ = C * D * (B ω ^ k * B ω ^ l) := by ring

omit hB in
theorem PolyBM.const (M : Matrix n n ℂ) : PolyBM B (fun _ => M) 0 :=
  ⟨‖M‖, norm_nonneg _, fun ω => by simp⟩

theorem PolyBM.mono {A : Ω → Matrix n n ℂ} {k l : ℕ} (h : PolyBM B A k) (hkl : k ≤ l) :
    PolyBM B A l := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun ω => (h ω).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hB ω) hkl) hC)⟩

omit hB in
theorem PolyBM.add {A A' : Ω → Matrix n n ℂ} {k : ℕ} (hA : PolyBM B A k) (hA' : PolyBM B A' k) :
    PolyBM B (fun ω => A ω + A' ω) k := by
  obtain ⟨C, hC, hA⟩ := hA
  obtain ⟨D, hD, hA'⟩ := hA'
  exact ⟨C + D, add_nonneg hC hD, fun ω => (norm_add_le _ _).trans
    (by have := hA ω; have := hA' ω; linarith)⟩

omit hB in
theorem PolyBM.sub {A A' : Ω → Matrix n n ℂ} {k : ℕ} (hA : PolyBM B A k) (hA' : PolyBM B A' k) :
    PolyBM B (fun ω => A ω - A' ω) k := by
  obtain ⟨C, hC, hA⟩ := hA
  obtain ⟨D, hD, hA'⟩ := hA'
  exact ⟨C + D, add_nonneg hC hD, fun ω => (norm_sub_le _ _).trans
    (by have := hA ω; have := hA' ω; linarith)⟩

omit hB in
/-- Bilinear forms. -/
theorem PolyB.bilin {A : Ω → Matrix n n ℂ} {k : ℕ} (hA : PolyBM B A k) (x c : n → ℂ) :
    PolyB B (fun ω => star x ⬝ᵥ (A ω *ᵥ c)) k := by
  obtain ⟨C, hC, hA⟩ := hA
  refine ⟨vecNorm x * C * vecNorm c, by have := vecNorm_nonneg x; have := vecNorm_nonneg c; positivity,
    fun ω => ?_⟩
  have h := norm_bilinear_le x (A ω) c
  simp only [bilinear] at h
  calc ‖star x ⬝ᵥ (A ω *ᵥ c)‖ ≤ vecNorm x * ‖A ω‖ * vecNorm c := h
    _ ≤ vecNorm x * (C * B ω ^ k) * vecNorm c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA ω) (vecNorm_nonneg _))
          (vecNorm_nonneg _)
    _ = _ := by ring

omit hB in
/-- Entries of `A c`. -/
theorem PolyB.vecEntry {A : Ω → Matrix n n ℂ} {k : ℕ} (hA : PolyBM B A k) (c : n → ℂ) (γ : n) :
    PolyB B (fun ω => (A ω *ᵥ c) γ) k := by
  refine (PolyB.bilin hA (Pi.single γ 1) c).of_le fun ω => le_of_eq ?_
  congr 1
  simp [dotProduct, Pi.single_apply]

omit hB in
/-- Matrix entries. -/
theorem PolyB.entry {A : Ω → Matrix n n ℂ} {k : ℕ} (hA : PolyBM B A k) (γ δ : n) :
    PolyB B (fun ω => A ω γ δ) k := by
  obtain ⟨C, hC, hA⟩ := hA
  exact ⟨C, hC, fun ω => (norm_entry_le' _ γ δ).trans (hA ω)⟩

end Mat
end Poly

section Layer
variable {W : ℕ}

theorem card_layerSite : Fintype.card (LayerSite W .oneBlockOnePort) = 2 * W := by
  simp [LayerSite, PhysSite, PortSite]; ring

/-- `‖S[M]‖ ≤ 2‖M‖`. -/
theorem norm_sdiag_le (b : ℝ) (hb0 : 0 ≤ b) (hb : b < 1 / 2) (M : LayerMat W) :
    ‖sdiag b M‖ ≤ 2 * ‖M‖ := by
  refine norm_diagonal_le _ (by positivity) fun α => ?_
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ γ, ‖siteVar W b α γ * M γ γ‖ ≤ 1 / W * ‖M‖ := fun γ => by
    rw [norm_mul]
    exact mul_le_mul (norm_siteVar_le b hb0 hb α γ) (norm_entry_le' _ γ γ) (norm_nonneg _)
      (by positivity)
  refine (Finset.sum_le_sum fun γ _ => h γ).trans ?_
  rw [Finset.sum_const, Finset.card_univ, card_layerSite, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp
  · have hW' : (0 : ℝ) < W := by exact_mod_cast hW
    rw [show ((2 * W : ℕ) : ℝ) * (1 / W * ‖M‖) = 2 * ‖M‖ by push_cast; field_simp]

theorem PolyBM.sdiag {Ω : Type*} {B : Ω → ℝ} (b : ℝ) (hb0 : 0 ≤ b) (hb : b < 1 / 2)
    {A : Ω → LayerMat W} {k : ℕ} (hA : PolyBM B A k) : PolyBM B (fun ω => sdiag b (A ω)) k := by
  obtain ⟨C, hC, hA⟩ := hA
  exact ⟨2 * C, by positivity, fun ω => (norm_sdiag_le b hb0 hb _).trans (by
    have := hA ω; nlinarith)⟩

end Layer

end BlockBand.Transmission.PassiveCovariance
