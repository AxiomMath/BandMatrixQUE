module

public import BlockBand.Layers.ComparisonBranch

/-!
# Deterministic stability of the residual pair mean equation

Setting (deterministic, uniform in `W` and the Hermitian `H` on `Fin 2 × Fin W`): weights
`α, β ≥ 0`, `s > 0` with `λ = α + β + s ≤ 1`; `a ∈ ℂ` with `|a| ≤ 1`, `-Im a ≥ y_lo > 0`; the
residual shift `σ(m)_k = s a + α m_k + β m_{1-k}` (`rlShift`), and the reference inverse
`R = (H - λ a)⁻¹` with `d ≥ max_j |W⁻¹Tr P_j R - a|`. Norms: complex modulus.

## Main result

`rl_stability`: if `m = tr(cmpInv H (σ(m))) + e` with `|e_j| ≤ η`, `Im m_j ≤ 0` and
`|m_j| ≤ (s y_lo)⁻¹`, then on `d ≤ rlDstar`, `η ≤ rlEtaStar`:
`|m_j - a| ≤ rlStabC (d + η)`.

## Method

No existence or branch statement is needed: `a` itself solves the equation up to `d`
(`σ(a) = λ a`). A lower bound `-Im m_j ≥ y₀` comes from `cmp_top_lower` (row comparison with `R`).
Then one weighted contraction (`cmp_trace_sub_weighted`, Cauchy–Schwarz with the two imaginary
identities) gives, for `T = max_l |m_l - a| / √(-Im m_l + η)`,
`T ≤ θ₀ T + (d + η)/√y₀` with `θ₀² = 1 - s/(2λ)`: the factor `(α + β)/λ = 1 - s/λ` is the stability
gap `s/(1-b)` of the paper (`λ = 1 - b` in the application).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Layers

/-- The residual self-energy shift `σ(m)_k = s a + α m_k + β m_{1-k}`. -/
def rlShift (s α β : ℝ) (a : ℂ) (m : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun k => (s : ℂ) * a + (α : ℂ) * m k + (β : ℂ) * m (1 - k)

theorem rlShift_im (s α β : ℝ) (a : ℂ) (m : Fin 2 → ℂ) (k : Fin 2) :
    -(rlShift s α β a m k).im = s * (-a.im) + α * (-(m k).im) + β * (-(m (1 - k)).im) := by
  simp only [rlShift, Complex.add_im, Complex.im_ofReal_mul]
  ring

theorem rlShift_sub (s α β : ℝ) (a : ℂ) (m : Fin 2 → ℂ) (k : Fin 2) :
    rlShift s α β a m k - ((α + β + s : ℝ) : ℂ) * a =
      (α : ℂ) * (m k - a) + (β : ℂ) * (m (1 - k) - a) := by
  simp only [rlShift]
  push_cast
  ring

/-- Two-term Cauchy–Schwarz: `(αu + βv)² ≤ (α + β)(αu² + βv²)`. -/
theorem rl_cs2 {α β u v : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (α * u + β * v) ^ 2 ≤ (α + β) * (α * u ^ 2 + β * v ^ 2) := by
  nlinarith [mul_nonneg (mul_nonneg hα hβ) (sq_nonneg (u - v))]

/-- `λ = α + β + s`. -/
def rlLam (s α β : ℝ) : ℝ := α + β + s

/-- The resolvent bound `K = (s y_lo)⁻¹`. -/
def rlK (s ylo : ℝ) : ℝ := (s * ylo)⁻¹

/-- The lower bound `L₀` of `-Im tr M` from `cmp_top_lower`. -/
def rlL0 (s α β ylo : ℝ) : ℝ :=
  s * ylo * (ylo / 2) / (2 * (1 + (rlK s ylo + 1) ^ 2 / (rlLam s α β * ylo) ^ 2))

/-- Closeness radius `d_* = y_lo s / (2λ)`. -/
def rlDstar (s α β ylo : ℝ) : ℝ := ylo * s / (2 * rlLam s α β)

/-- Residual radius `η_* = min(L₀/2, s y_lo, 1)`. -/
def rlEtaStar (s α β ylo : ℝ) : ℝ := min (min (rlL0 s α β ylo / 2) (s * ylo)) 1

/-- Contraction factor `θ₀ = √(1 - s/(2λ))`. -/
def rlTheta (s α β : ℝ) : ℝ := Real.sqrt (1 - s / (2 * rlLam s α β))

/-- The stability constant `√(K + 1) / ((1 - θ₀) √y₀)`, `y₀ = L₀/2`. -/
def rlStabC (s α β ylo : ℝ) : ℝ :=
  Real.sqrt (rlK s ylo + 1) / ((1 - rlTheta s α β) * Real.sqrt (rlL0 s α β ylo / 2))

section Consts

variable {s α β ylo : ℝ}

theorem rlLam_pos (hs : 0 < s) (hα : 0 ≤ α) (hβ : 0 ≤ β) : 0 < rlLam s α β := by
  unfold rlLam; linarith

theorem rlK_pos (hs : 0 < s) (hylo : 0 < ylo) : 0 < rlK s ylo := by
  unfold rlK; positivity

theorem rlL0_pos (hs : 0 < s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hylo : 0 < ylo) :
    0 < rlL0 s α β ylo := by
  have := rlLam_pos hs hα hβ
  unfold rlL0; positivity

theorem rlDstar_pos (hs : 0 < s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hylo : 0 < ylo) :
    0 < rlDstar s α β ylo := by
  have := rlLam_pos hs hα hβ
  unfold rlDstar; positivity

theorem rlEtaStar_pos (hs : 0 < s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hylo : 0 < ylo) :
    0 < rlEtaStar s α β ylo := by
  have := rlL0_pos hs hα hβ hylo
  unfold rlEtaStar
  refine lt_min (lt_min (by linarith) (by positivity)) one_pos

theorem rlTheta_lt_one (hs : 0 < s) (hα : 0 ≤ α) (hβ : 0 ≤ β) : rlTheta s α β < 1 := by
  have hl := rlLam_pos hs hα hβ
  unfold rlTheta
  rw [Real.sqrt_lt' one_pos, one_pow]
  have : 0 < s / (2 * rlLam s α β) := by positivity
  linarith

theorem rlStabC_pos (hs : 0 < s) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hylo : 0 < ylo) :
    0 < rlStabC s α β ylo := by
  have h1 := rlTheta_lt_one hs hα hβ
  have h2 := rlL0_pos hs hα hβ hylo
  have h3 := rlK_pos hs hylo
  unfold rlStabC
  have : 0 < 1 - rlTheta s α β := by linarith
  have : 0 < Real.sqrt (rlL0 s α β ylo / 2) := Real.sqrt_pos.mpr (by linarith)
  have : 0 < Real.sqrt (rlK s ylo + 1) := Real.sqrt_pos.mpr (by linarith)
  positivity

end Consts

/-- Division step of the contraction. -/
theorem rl_ratio_step {δ θT r yh y₀ : ℝ} (hy₀ : 0 < y₀) (hyh : y₀ ≤ yh) (hr : 0 ≤ r)
    (h : δ ≤ θT * Real.sqrt yh + r) : δ / Real.sqrt yh ≤ θT + r / Real.sqrt y₀ := by
  have hs0 : 0 < Real.sqrt y₀ := Real.sqrt_pos.mpr hy₀
  have hs1 : Real.sqrt y₀ ≤ Real.sqrt yh := Real.sqrt_le_sqrt hyh
  have hs : 0 < Real.sqrt yh := lt_of_lt_of_le hs0 hs1
  rw [div_le_iff₀ hs]
  have h1 : r ≤ r / Real.sqrt y₀ * Real.sqrt yh := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hs0]
    exact mul_le_mul_of_nonneg_left hs1 hr
  calc δ ≤ θT * Real.sqrt yh + r := h
    _ ≤ θT * Real.sqrt yh + r / Real.sqrt y₀ * Real.sqrt yh := by linarith
    _ = (θT + r / Real.sqrt y₀) * Real.sqrt yh := by ring

/-- Closing a linear contraction `T ≤ θ T + c`, `θ < 1`. -/
theorem rl_close {T θ c : ℝ} (hθ : θ < 1) (h : T ≤ θ * T + c) : T ≤ c / (1 - θ) := by
  rw [le_div_iff₀ (by linarith)]; linarith

/-- **Deterministic stability of the residual mean equation.** See the module docstring. -/
theorem rl_stability {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hH : H.IsHermitian) {s α β ylo : ℝ} (hs : 0 < s) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hlam1 : α + β + s ≤ 1) (hylo : 0 < ylo) {a : ℂ} (ha1 : ‖a‖ ≤ 1) (hya : ylo ≤ -a.im)
    {d η : ℝ}
    (hd : ∀ j, ‖blockTrace (cmpInv H (fun _ => ((α + β + s : ℝ) : ℂ) * a)) j - a‖ ≤ d)
    (hdsmall : d ≤ rlDstar s α β ylo) (hηsmall : η ≤ rlEtaStar s α β ylo)
    (m e : Fin 2 → ℂ) (heq : ∀ j, m j = blockTrace (cmpInv H (rlShift s α β a m)) j + e j)
    (he : ∀ j, ‖e j‖ ≤ η) (him : ∀ j, (m j).im ≤ 0) (hK : ∀ j, ‖m j‖ ≤ rlK s ylo) (j : Fin 2) :
    ‖m j - a‖ ≤ rlStabC s α β ylo * (d + η) := by
  set lam := rlLam s α β with hlam
  have hlam' : lam = α + β + s := rfl
  have hl0 : 0 < lam := rlLam_pos hs hα hβ
  set K := rlK s ylo with hKdef
  have hK0 : 0 < K := rlK_pos hs hylo
  set ya := -a.im with hyadef
  have hya0 : 0 < ya := lt_of_lt_of_le hylo hya
  have hya1 : ya ≤ 1 := by
    have := Complex.abs_im_le_norm a
    rw [hyadef]; linarith [neg_le_abs a.im]
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd 0)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (he 0)
  have hdst : d * (2 * lam) ≤ ylo * s := by
    have := hdsmall; unfold rlDstar at this; rwa [le_div_iff₀ (by positivity)] at this
  have hsl : s ≤ lam := by rw [hlam']; linarith
  have hd2 : d ≤ ylo / 2 := by nlinarith
  have hηL : η ≤ rlL0 s α β ylo / 2 :=
    hηsmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηs : η ≤ s * ylo := hηsmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hη1 : η ≤ 1 := hηsmall.trans (min_le_right _ _)
  set σ := rlShift s α β a m with hσdef
  set s₀ : ℂ := ((α + β + s : ℝ) : ℂ) * a with hs₀def
  have hs₀im : -s₀.im = lam * ya := by rw [hs₀def, Complex.im_ofReal_mul, hyadef, hlam']; ring
  set M := cmpInv H σ with hMdef
  set R := cmpInv H (fun _ => s₀) with hRdef
  set y : Fin 2 → ℝ := fun k => -(m k).im with hydef
  have hy0 : ∀ k, 0 ≤ y k := fun k => by simp only [hydef]; linarith [him k]
  have hσim : ∀ k, -(σ k).im = s * ya + α * y k + β * y (1 - k) := fun k => rlShift_im s α β a m k
  have hσlo : ∀ k, s * ylo ≤ -(σ k).im := fun k => by
    rw [hσim]
    have := mul_le_mul_of_nonneg_left hya hs.le
    nlinarith [mul_nonneg hα (hy0 k), mul_nonneg hβ (hy0 (1 - k))]
  have hσneg : ∀ k, (σ k).im < 0 := fun k => by
    have := hσlo k; have : 0 < s * ylo := by positivity
    linarith
  have hs₀neg : ∀ k : Fin 2, ((fun _ => s₀) k).im < 0 := fun _ => by
    simp only; have := hs₀im; nlinarith
  -- the lower bound `-Im tr M ≥ L₀`
  have hΔ : ∀ k, ‖σ k - s₀‖ ≤ K + 1 := fun k => by
    rw [hσdef, hs₀def, rlShift_sub]
    have hmk : ∀ l, ‖m l - a‖ ≤ K + 1 := fun l =>
      (norm_sub_le _ _).trans (by linarith [hK l])
    calc ‖(α : ℂ) * (m k - a) + (β : ℂ) * (m (1 - k) - a)‖
        ≤ α * (K + 1) + β * (K + 1) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [cmp_norm_real_mul hα]; exact mul_le_mul_of_nonneg_left (hmk k) hα
          · rw [cmp_norm_real_mul hβ]; exact mul_le_mul_of_nonneg_left (hmk _) hβ
      _ ≤ K + 1 := by nlinarith
  have hRim : ∀ i, -(blockTrace R i).im ≤ ya + d ∧ ylo / 2 ≤ -(blockTrace R i).im := fun i => by
    have h1 := hd i
    have h2 := Complex.abs_im_le_norm (blockTrace R i - a)
    rw [Complex.sub_im] at h2
    have h3 := abs_le.mp (h2.trans h1)
    rw [hyadef]
    constructor <;> linarith [h3.1, h3.2]
  have hlow : ∀ i, rlL0 s α β ylo ≤ -(blockTrace M i).im := fun i => by
    have := cmp_top_lower H hH σ s₀ (y₃ := s * ylo) (ζlo := lam * ylo) (Δ := K + 1)
      (vR := ylo / 2) (by positivity) (by positivity) (by rw [hs₀im]; nlinarith)
      (by rw [hs₀im]; nlinarith) hσlo hΔ i (hRim i).2
    unfold rlL0
    convert this using 1
  have hyl : ∀ k, rlL0 s α β ylo / 2 ≤ y k := fun k => by
    have h1 := hlow k
    have h2 : m k - e k = blockTrace M k := by rw [heq k]; ring
    have h3 := Complex.abs_im_le_norm (e k)
    have h4 : (blockTrace M k).im = (m k).im - (e k).im := by rw [← h2, Complex.sub_im]
    simp only [hydef]
    linarith [le_abs_self (e k).im, he k]
  set y₀ := rlL0 s α β ylo / 2 with hy₀def
  have hy₀ : 0 < y₀ := by have := rlL0_pos hs hα hβ hylo; rw [hy₀def]; linarith
  -- the weighted contraction
  set yh : Fin 2 → ℝ := fun k => y k + η with hyhdef
  have hyh0 : ∀ k, y₀ ≤ yh k := fun k => by simp only [hyhdef]; linarith [hyl k]
  have hyhpos : ∀ k, 0 < yh k := fun k => lt_of_lt_of_le hy₀ (hyh0 k)
  have hyhK : ∀ k, yh k ≤ K + 1 := fun k => by
    simp only [hyhdef, hydef]
    have := Complex.abs_im_le_norm (m k)
    linarith [neg_le_abs (m k).im, hK k]
  set δ : Fin 2 → ℝ := fun k => ‖m k - a‖ with hδdef
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = max (δ 0 / Real.sqrt (yh 0)) (δ 1 / Real.sqrt (yh 1)) :=
    ⟨_, rfl⟩
  have hsq : ∀ k, 0 < Real.sqrt (yh k) := fun k => Real.sqrt_pos.mpr (hyhpos k)
  have hδT : ∀ k, δ k ≤ T * Real.sqrt (yh k) := fun k => by
    have h : δ k / Real.sqrt (yh k) ≤ T := by
      rw [hT]; fin_cases k
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact (div_le_iff₀ (hsq k)).mp h
  have hT0 : 0 ≤ T := by
    rw [hT]; exact (div_nonneg (norm_nonneg _) (hsq 0).le).trans (le_max_left _ _)
  set S := T * Real.sqrt (α + β) / Real.sqrt (lam * ya) with hSdef
  have hlya : 0 < Real.sqrt (lam * ya) := Real.sqrt_pos.mpr (by positivity)
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hδσ : ∀ k, ‖σ k - (fun _ => s₀) k‖ ≤
      S * (Real.sqrt (-(σ k).im) * Real.sqrt (-((fun _ => s₀) k).im)) := fun k => by
    simp only
    rw [hs₀im, hσdef, hs₀def, rlShift_sub]
    have h1 : ‖(α : ℂ) * (m k - a) + (β : ℂ) * (m (1 - k) - a)‖ ≤
        α * (T * Real.sqrt (yh k)) + β * (T * Real.sqrt (yh (1 - k))) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [cmp_norm_real_mul hα]; exact mul_le_mul_of_nonneg_left (hδT k) hα
      · rw [cmp_norm_real_mul hβ]; exact mul_le_mul_of_nonneg_left (hδT _) hβ
    have h2 : α * Real.sqrt (yh k) + β * Real.sqrt (yh (1 - k)) ≤
        Real.sqrt (α + β) * Real.sqrt (-(σ k).im) := by
      rw [← Real.sqrt_mul (by linarith)]
      refine Real.le_sqrt_of_sq_le ?_
      refine (rl_cs2 hα hβ).trans ?_
      rw [Real.sq_sqrt (hyhpos k).le, Real.sq_sqrt (hyhpos _).le]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      rw [hσim]
      simp only [hyhdef]
      have : (α + β) * η ≤ s * ya := by
        have := mul_le_mul_of_nonneg_left hya hs.le
        nlinarith
      nlinarith
    calc ‖(α : ℂ) * (m k - a) + (β : ℂ) * (m (1 - k) - a)‖
        ≤ T * (α * Real.sqrt (yh k) + β * Real.sqrt (yh (1 - k))) := by linarith
      _ ≤ T * (Real.sqrt (α + β) * Real.sqrt (-(σ k).im)) := mul_le_mul_of_nonneg_left h2 hT0
      _ = S * (Real.sqrt (-(σ k).im) * Real.sqrt (lam * ya)) := by
          rw [hSdef]; field_simp
  have hθ : Real.sqrt (ya + d) * S ≤ rlTheta s α β * T := by
    rw [hSdef, rlTheta]
    have hab : 0 ≤ α + β := by linarith
    have hyd : 0 ≤ ya + d := by linarith
    rw [show Real.sqrt (ya + d) * (T * Real.sqrt (α + β) / Real.sqrt (lam * ya)) =
      T * Real.sqrt ((ya + d) * (α + β) / (lam * ya)) by
        rw [Real.sqrt_div (mul_nonneg hyd hab) (lam * ya), Real.sqrt_mul hyd (α + β)]; ring]
    rw [mul_comm (Real.sqrt _) T]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hT0
    rw [div_le_iff₀ (by positivity)]
    have hlb : lam - s = α + β := by rw [hlam']; ring
    have e1 : (1 - s / (2 * lam)) * (lam * ya) = lam * ya - s * ya / 2 := by
      field_simp
    rw [e1, ← hlb]
    have : d * lam ≤ ya * s / 2 := by nlinarith
    nlinarith
  -- close the contraction
  have hθ1 := rlTheta_lt_one hs hα hβ
  have hθ0 : 0 ≤ rlTheta s α β := Real.sqrt_nonneg _
  have hsy₀ : 0 < Real.sqrt y₀ := Real.sqrt_pos.mpr hy₀
  have hratio : ∀ k, δ k / Real.sqrt (yh k) ≤ rlTheta s α β * T + (d + η) / Real.sqrt y₀ := by
    intro k
    have hstepk : δ k ≤ rlTheta s α β * T * Real.sqrt (yh k) + (d + η) := by
      have hdec : m k - a = (blockTrace M k - blockTrace R k) + (blockTrace R k - a) + e k := by
        rw [heq k]; ring
      have hwk := cmp_trace_sub_weighted H hH σ (fun _ => s₀) hσneg hs₀neg hS0 hδσ k
      have hMk : -(blockTrace M k).im ≤ yh k := by
        have h2 : m k - e k = blockTrace M k := by rw [heq k]; ring
        have h4 : (blockTrace M k).im = (m k).im - (e k).im := by rw [← h2, Complex.sub_im]
        have h3 := Complex.abs_im_le_norm (e k)
        simp only [hyhdef, hydef]
        linarith [le_abs_self (e k).im, he k]
      have h1 : ‖blockTrace M k - blockTrace R k‖ ≤ rlTheta s α β * T * Real.sqrt (yh k) := by
        refine hwk.trans ?_
        have hA : Real.sqrt (-(blockTrace M k).im) ≤ Real.sqrt (yh k) := Real.sqrt_le_sqrt hMk
        have hB : Real.sqrt (-(blockTrace R k).im) ≤ Real.sqrt (ya + d) :=
          Real.sqrt_le_sqrt (hRim k).1
        calc Real.sqrt (-(blockTrace M k).im) * Real.sqrt (-(blockTrace R k).im) * S
            ≤ Real.sqrt (yh k) * Real.sqrt (ya + d) * S := by gcongr
          _ = Real.sqrt (yh k) * (Real.sqrt (ya + d) * S) := by ring
          _ ≤ Real.sqrt (yh k) * (rlTheta s α β * T) :=
              mul_le_mul_of_nonneg_left hθ (Real.sqrt_nonneg _)
          _ = rlTheta s α β * T * Real.sqrt (yh k) := by ring
      have hn : ‖m k - a‖ ≤ ‖blockTrace M k - blockTrace R k‖ + ‖blockTrace R k - a‖ +
          ‖e k‖ := by
        rw [hdec]
        exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      have h2 := hd k
      have h3 := he k
      change ‖m k - a‖ ≤ _
      linarith only [hn, h1, h2, h3]
    exact rl_ratio_step hy₀ (hyh0 k) (by linarith) hstepk
  have hTle : T ≤ rlTheta s α β * T + (d + η) / Real.sqrt y₀ := by
    have hm := max_le (hratio 0) (hratio 1)
    rw [← hT] at hm
    exact hm
  have hTb : T ≤ (d + η) / ((1 - rlTheta s α β) * Real.sqrt y₀) := by
    rw [mul_comm, ← div_div]
    exact rl_close hθ1 hTle
  have hfin : δ j ≤ T * Real.sqrt (K + 1) :=
    (hδT j).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hyhK j)) hT0)
  have hC : rlStabC s α β ylo * (d + η) =
      (d + η) / ((1 - rlTheta s α β) * Real.sqrt y₀) * Real.sqrt (K + 1) := by
    rw [rlStabC, hy₀def, hKdef]; ring
  rw [hC]
  exact hfin.trans (mul_le_mul_of_nonneg_right hTb (Real.sqrt_nonneg _))

end BlockBand.Layers
