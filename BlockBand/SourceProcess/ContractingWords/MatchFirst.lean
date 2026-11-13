module

public import BlockBand.SourceProcess.ContractingWords.MatchSecond

/-!
# Matching the first-order drift terms

Slot `p` of an ordinary word carries `σ_p = B_{s_p}`; `τ_p(X)` is the word with slot `p` replaced
by `X` (`pw σ (fun _ => X) {p}`), linear in `X` (`tau_add`, `tau_smul`), with `τ_p(B_σ') =
Tr(setSepAt w p σ')` (`tau_sep`) and `τ_p(σ_p) = Tr w`. `first_match`: if
`‖m_p - (ΩB_{a(s_p)} + Ω'B_{b(s_p)} - [s_p = P]γB_{s_p})‖ ≤ ρ` (`a(I) = P𝕊`, `a(P) = P𝕊P`,
`b(I) = 𝕊*P`, `b(P) = P𝕊*P`), then
`|Σ_p τ_p(m_p) + γ #P Tr w| ≤ (|Ω| + |Ω'|) Σ_{Z ∈ contrOne w}|Tr Z| + |w| Γ ρ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceGenerator BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι] {nT nI : ℕ}

/-- The contracting separator of the Ward-mean term `ΩP𝕊`. -/
def aSep (s : Separator) : Separator := if s = .proj then .projSProj else .projS

/-- The contracting separator of the Ward-mean term `Ω'𝕊*P`. -/
def bSep (s : Separator) : Separator := if s = .proj then .projSStarProj else .sStarProj

theorem aSep_mem (s : Separator) : aSep s ∈ contrSeps := by
  unfold aSep; split_ifs <;> simp [contrSeps]

theorem bSep_mem (s : Separator) : bSep s ∈ contrSeps := by
  unfold bSep; split_ifs <;> simp [contrSeps]

omit [Fintype ι] [DecidableEq ι] in
theorem pw_single_const {r : ℕ} (σ m : Fin r → Matrix ι ι ℂ) (p : Fin r) :
    pw σ m {p} = pw σ (fun _ => m p) {p} := by
  funext i; simp only [pw, Finset.mem_singleton]; split_ifs with h <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
theorem pw_single_self {r : ℕ} (σ : Fin r → Matrix ι ι ℂ) (p : Fin r) :
    pw σ (fun _ => σ p) {p} = σ := by
  funext i; simp only [pw, Finset.mem_singleton]; split_ifs with h <;> simp [h]

section Rep

variable {r : ℕ} {A : Fin r → Matrix ι ι ℂ} {κ : Type} [Fintype κ] {c : κ → ℂ}
  {x y : κ → Fin r → ι → ℂ}

theorem tau_rep (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (σ : Fin r → Matrix ι ι ℂ) (p : Fin r) (X : Matrix ι ι ℂ) :
    posTr A (pw σ (fun _ => X) {p}) = ∑ l, c l * (bilinear (x l p) X (y l p) *
      ∏ i ∈ Finset.univ \ {p}, bilinear (x l i) (σ i) (y l i)) := by
  rw [posTr_pw hrep]; simp only [Finset.prod_singleton]

theorem tau_add (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (σ : Fin r → Matrix ι ι ℂ) (p : Fin r) (X Y : Matrix ι ι ℂ) :
    posTr A (pw σ (fun _ => X + Y) {p}) =
      posTr A (pw σ (fun _ => X) {p}) + posTr A (pw σ (fun _ => Y) {p}) := by
  rw [tau_rep hrep, tau_rep hrep, tau_rep hrep, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [bilinear_add_mat]; ring

theorem tau_smul (hrep : ∀ T, posTr A T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (σ : Fin r → Matrix ι ι ℂ) (p : Fin r) (a : ℂ) (X : Matrix ι ι ℂ) :
    posTr A (pw σ (fun _ => a • X) {p}) = a * posTr A (pw σ (fun _ => X) {p}) := by
  rw [tau_rep hrep, tau_rep hrep, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [BlockBand.SourceProcess.CompleteSourceGap.bilinear_smul]; ring

end Rep

/-- `τ_p(B_{σ'}) = Tr(setSepAt w p σ')`. -/
theorem tau_sep (A : TraceLetter nT nI → Matrix ι ι ℂ) (B : Separator → Matrix ι ι ℂ)
    (w : TraceWord nT nI) (p : Fin w.length) (σ' : Separator) :
    posTr (wl A w) (pw (fun i => B (w.get i).2) (fun _ => B σ') {p}) =
      wval A B (setSepAt w p σ') := by
  obtain ⟨pv, hpv⟩ := p
  obtain ⟨L, R, x, hw, hL, -⟩ := exists_single_shape w hpv
  subst hw hL
  have e : pw (fun i => B ((L ++ x :: R).get i).2) (fun _ => B σ') {⟨L.length, hpv⟩} =
      fun i : Fin (L ++ x :: R).length => slot1 B L.length (B σ') i ((L ++ x :: R).get i).2 := by
    funext i
    simp only [pw, slot1, Finset.mem_singleton, Fin.ext_iff]
  have hm : ∀ (L : TraceWord nT nI), (L ++ x :: R).modify L.length (fun z => (z.1, σ')) =
      L ++ (x.1, σ') :: R := fun L => by
    induction L with
    | nil => simp
    | cons a L ih => simp [ih]
  rw [e, posTr_word_single, setSepAt, hm, wval]
  simp [Matrix.mul_assoc]

theorem sum_count (w : TraceWord nT nI) :
    ∑ p : Fin w.length, (if (w.get p).2 = .proj then (1 : ℂ) else 0) =
      ((w.countP fun x => decide (x.2 = Separator.proj) : ℕ) : ℂ) := by
  simp only [List.get_eq_getElem]
  rw [Fin.sum_univ_fun_getElem w (fun x => if x.2 = Separator.proj then (1 : ℂ) else 0)]
  induction w with
  | nil => simp
  | cons a w ih => by_cases h : a.2 = .proj <;> simp [h, ih]; ring

theorem le_contrOne_sum {nT nI W : ℕ}
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (B : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w : TraceWord nT nI)
    (τ : Fin w.length → Separator) (hτ : ∀ p, τ p ∈ contrSeps) :
    ∑ p : Fin w.length, ‖coreProd A B [setSepAt w p (τ p)]‖ ≤
      ((contrOne w).map fun Zs => ‖coreProd A B Zs‖).sum := by
  rw [contrOne_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_le_sum fun p _ => List.single_le_sum (fun z hz => ?_) _ ?_
  · obtain ⟨Zs, -, rfl⟩ := List.mem_map.mp hz; exact norm_nonneg _
  · exact List.mem_map_of_mem (List.mem_map_of_mem (hτ p))

/-- **The first-order terms.** -/
theorem first_match {W : ℕ} (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (B : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (w : TraceWord nT nI)
    {κ : Type} [Fintype κ] {c : κ → ℂ} {x y : κ → Fin w.length → Fin 2 × Fin W → ℂ}
    (hrep : ∀ T, posTr (wl A w) T = ∑ l, c l * ∏ p, bilinear (x l p) (T p) (y l p))
    (hxy : ∀ l p, vecNorm (x l p) ≤ 1 ∧ vecNorm (y l p) ≤ 1) {Γ : ℝ} (hc : ∑ l, ‖c l‖ ≤ Γ)
    (hσ : ∀ p, ‖B (w.get p).2‖ ≤ 1) (m : Fin w.length → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (Ω Ω' γ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hm : ∀ p, ‖m p - (Ω • B (aSep (w.get p).2) + Ω' • B (bSep (w.get p).2) -
      (if (w.get p).2 = .proj then γ else 0) • B (w.get p).2)‖ ≤ ρ) :
    ‖∑ p, posTr (wl A w) (pw (fun i => B (w.get i).2) m {p}) +
        γ * ((w.countP fun x => decide (x.2 = Separator.proj) : ℕ) : ℂ) * wval A B w‖ ≤
      (‖Ω‖ + ‖Ω'‖) * ((contrOne w).map fun Zs => ‖coreProd A B Zs‖).sum +
        w.length * (Γ * ρ) := by
  set σ : Fin w.length → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun i => B (w.get i).2
  set g : Fin w.length → ℂ := fun p => if (w.get p).2 = .proj then γ else 0
  set R : Fin w.length → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun p =>
    m p - (Ω • B (aSep (w.get p).2) + Ω' • B (bSep (w.get p).2) - g p • B (w.get p).2)
  have hdec : ∀ p, m p = Ω • B (aSep (w.get p).2) + Ω' • B (bSep (w.get p).2) +
      (-g p) • B (w.get p).2 + R p := fun p => by
    simp only [R, neg_smul]; abel
  have key : ∀ p, posTr (wl A w) (pw σ m {p}) =
      Ω * wval A B (setSepAt w p (aSep (w.get p).2)) +
        Ω' * wval A B (setSepAt w p (bSep (w.get p).2)) + (-g p) * wval A B w +
          posTr (wl A w) (pw σ (fun _ => R p) {p}) := fun p => by
    rw [pw_single_const, hdec p, tau_add hrep, tau_add hrep, tau_add hrep, tau_smul hrep,
      tau_smul hrep, tau_smul hrep, tau_sep, tau_sep, show B (w.get p).2 = σ p from rfl,
      pw_single_self, posTr_word_const]
  have hcount : ∑ p, (-g p) * wval A B w =
      -(γ * ((w.countP fun x => decide (x.2 = Separator.proj) : ℕ) : ℂ) * wval A B w) := by
    rw [← sum_count, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [g]; split_ifs <;> ring
  have e : ∑ p, posTr (wl A w) (pw σ m {p}) +
      γ * ((w.countP fun x => decide (x.2 = Separator.proj) : ℕ) : ℂ) * wval A B w =
      Ω * ∑ p : Fin w.length, wval A B (setSepAt w p (aSep (w.get p).2)) +
        Ω' * ∑ p : Fin w.length, wval A B (setSepAt w p (bSep (w.get p).2)) +
          ∑ p, posTr (wl A w) (pw σ (fun _ => R p) {p}) := by
    simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcount]; ring
  rw [e]
  have h1 := le_contrOne_sum A B w (fun p => aSep (w.get p).2) fun p => aSep_mem _
  have h2 := le_contrOne_sum A B w (fun p => bSep (w.get p).2) fun p => bSep_mem _
  simp only [coreProd_one] at h1 h2
  have h3 : ∀ p : Fin w.length, ‖posTr (wl A w) (pw σ (fun _ => R p) {p})‖ ≤ Γ * ρ := fun p => by
    refine (norm_posTr_pw_mean hrep hxy hσ (μ₀ := ρ) (fun _ => hm p) {p}).trans ?_
    rw [Finset.card_singleton, pow_one]
    exact mul_le_mul_of_nonneg_right hc hρ
  have h4 : ‖∑ p, posTr (wl A w) (pw σ (fun _ => R p) {p})‖ ≤ w.length * (Γ * ρ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p, ‖posTr (wl A w) (pw σ (fun _ => R p) {p})‖ ≤ ∑ _p : Fin w.length, Γ * ρ :=
          Finset.sum_le_sum fun p _ => h3 p
      _ = _ := by simp
  have h5 := norm_sum_le Finset.univ fun p : Fin w.length =>
    wval A B (setSepAt w p (aSep (w.get p).2))
  have h6 := norm_sum_le Finset.univ fun p : Fin w.length =>
    wval A B (setSepAt w p (bSep (w.get p).2))
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) h4)
  rw [norm_mul, norm_mul, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (h5.trans h1) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (h6.trans h2) (norm_nonneg _))

end BlockBand.SourceProcess.ContractingWords
