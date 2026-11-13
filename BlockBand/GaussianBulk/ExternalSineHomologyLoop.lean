module

public import Mathlib

/-!
# Loop-independence of contour integrals with real poles

A `LoopCalculus I K B P` is a functional `I : (ℂ → ℂ) → ℂ` ("integrate over a closed loop with
range `K`") which depends only on values on `K`, is additive on functions continuous on `K` and
`ℂ`-homogeneous, kills every function holomorphic on the open set `B ⊇ K`, and gives `2πi` on
`(z-p)⁻¹` and `0` on `(z-p)^{-k}`, `k ≥ 2`, for each pole `p ∈ P ⊆ B \ K`.

`LoopCalculus.eval`: for every list of poles `D` in `P` (repetitions allowed) and every `H`
holomorphic on `B`, `I (H / ∏_{p∈D} (z-p)) = 2πi · dividedResidue H D`, where
`dividedResidue` is defined by dslope peeling and does not depend on the loop.
Hence two loop calculi with the same `B, P` agree on such functions (`LoopCalculus.eq_of_same`).
`circleLoopCalculus` is the instance for the counterclockwise circle `C(0,R)`.

All statements are exact.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set Filter Topology

/-- Abstract closed-loop integration functional with range `K`, holomorphy domain `B`
and poles `P`. -/
structure LoopCalculus (I : (ℂ → ℂ) → ℂ) (K B P : Set ℂ) : Prop where
  isOpen : IsOpen B
  range_sub : K ⊆ B
  poles_sub : P ⊆ B
  avoid : ∀ p ∈ P, p ∉ K
  congr : ∀ f g : ℂ → ℂ, EqOn f g K → I f = I g
  add : ∀ f g : ℂ → ℂ, ContinuousOn f K → ContinuousOn g K →
    I (fun z => f z + g z) = I f + I g
  smul : ∀ (c : ℂ) (f : ℂ → ℂ), I (fun z => c * f z) = c * I f
  holo : ∀ G : ℂ → ℂ, DifferentiableOn ℂ G B → I G = 0
  res : ∀ p ∈ P, I (fun z => (z - p)⁻¹) = 2 * Real.pi * Complex.I
  pow : ∀ p ∈ P, ∀ k : ℕ, 2 ≤ k → I (fun z => ((z - p) ^ k)⁻¹) = 0

/-- `∏_{p ∈ D} (z - p)` for a list of poles. -/
def poleProd (D : List ℂ) (z : ℂ) : ℂ := (D.map (fun p => z - p)).prod

/-- Weight of the last peeled pole: `1` if no pole remains, else `0`. -/
def residueWeight : List ℂ → ℂ
  | [] => 1
  | _ :: _ => 0

/-- Divided-difference residue functional (dslope peeling). -/
def dividedResidue : (ℂ → ℂ) → List ℂ → ℂ
  | _, [] => 0
  | H, p :: D => dividedResidue (dslope H p) D + H p * residueWeight D

/-- `2πi` if `n = 1`, else `0`. -/
def loopIndicator (n : ℕ) : ℂ := if n = 1 then 2 * Real.pi * Complex.I else 0

theorem loopIndicator_one : loopIndicator 1 = 2 * Real.pi * Complex.I := by
  simp [loopIndicator]

theorem loopIndicator_of_ne {n : ℕ} (h : n ≠ 1) : loopIndicator n = 0 := by
  simp [loopIndicator, h]

@[simp] theorem poleProd_nil (z : ℂ) : poleProd [] z = 1 := rfl

@[simp] theorem poleProd_cons (p : ℂ) (D : List ℂ) (z : ℂ) :
    poleProd (p :: D) z = (z - p) * poleProd D z := by
  simp [poleProd]

theorem poleProd_perm {D D' : List ℂ} (h : D.Perm D') (z : ℂ) : poleProd D z = poleProd D' z :=
  (h.map _).prod_eq

theorem poleProd_ne_zero {D : List ℂ} {z : ℂ} (h : ∀ p ∈ D, z ≠ p) : poleProd D z ≠ 0 := by
  induction D with
  | nil => simp
  | cons p D ih =>
    rw [poleProd_cons]
    exact mul_ne_zero (sub_ne_zero.mpr (h p (by simp)))
      (ih (fun q hq => h q (by simp [hq])))

theorem continuous_poleProd (D : List ℂ) : Continuous (poleProd D) := by
  induction D with
  | nil =>
    have : poleProd [] = fun _ => (1 : ℂ) := funext poleProd_nil
    rw [this]
    exact continuous_const
  | cons p D ih =>
    have : poleProd (p :: D) = fun z => (z - p) * poleProd D z := funext (poleProd_cons p D)
    rw [this]
    exact (continuous_id.sub continuous_const).mul ih

theorem poleProd_replicate (n : ℕ) (p z : ℂ) : poleProd (List.replicate n p) z = (z - p) ^ n := by
  simp [poleProd, List.map_replicate, List.prod_replicate]

variable {I : (ℂ → ℂ) → ℂ} {K B P : Set ℂ}

theorem LoopCalculus.sub (hL : LoopCalculus I K B P) (f g : ℂ → ℂ)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) :
    I (fun z => f z - g z) = I f - I g := by
  have h1 := hL.add f (fun z => (-1 : ℂ) * g z) hf (continuousOn_const.mul hg)
  rw [hL.smul] at h1
  rw [show (fun z => f z - g z) = fun z => f z + (-1 : ℂ) * g z by funext z; ring, h1]
  ring

theorem LoopCalculus.continuousOn_inv_poleProd (hL : LoopCalculus I K B P) {D : List ℂ}
    (hD : ∀ p ∈ D, p ∈ P) : ContinuousOn (fun z => (poleProd D z)⁻¹) K := by
  apply (continuous_poleProd D).continuousOn.inv₀
  intro z hz
  apply poleProd_ne_zero
  intro p hp hzp
  exact hL.avoid p (hD p hp) (hzp ▸ hz)

/-- Integral of `1 / ∏ (z - p)`: `2πi` for one pole, `0` otherwise. -/
theorem LoopCalculus.inv_poleProd (hL : LoopCalculus I K B P) :
    ∀ (n : ℕ) (D : List ℂ), D.length = n → (∀ p ∈ D, p ∈ P) →
      I (fun z => (poleProd D z)⁻¹) = loopIndicator n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hn hD
    match D, hn with
    | [], hn =>
      obtain rfl : n = 0 := by simpa using hn.symm
      rw [loopIndicator_of_ne (by omega)]
      simp only [poleProd_nil, inv_one]
      exact hL.holo _ (differentiableOn_const _)
    | [p], hn =>
      obtain rfl : n = 1 := by simpa using hn.symm
      rw [loopIndicator_one]
      have := hL.res p (hD p (by simp))
      rw [← this]
      apply hL.congr
      intro z _
      simp
    | p :: q :: D', hn =>
      have hn2 : 2 ≤ n := by rw [← hn]; simp
      have hn1 : n ≠ 1 := by omega
      rw [loopIndicator_of_ne hn1]
      by_cases hall : ∀ r ∈ p :: q :: D', r = p
      · have hrep : p :: q :: D' = List.replicate n p := by
          rw [← hn]; exact List.eq_replicate_iff.mpr ⟨rfl, hall⟩
        have := hL.pow p (hD p (by simp)) n hn2
        rw [← this]
        apply hL.congr
        intro z _
        simp only
        rw [hrep, poleProd_replicate]
      · simp only [not_forall, exists_prop] at hall
        obtain ⟨r, hr, hrp⟩ := hall
        have hr' : r ∈ q :: D' := by
          rcases List.mem_cons.mp hr with h | h
          · exact absurd h hrp
          · exact h
        set E : List ℂ := (q :: D').erase r with hE
        have hperm : (p :: q :: D').Perm (p :: r :: E) :=
          List.Perm.cons p (List.perm_cons_erase hr')
        have hEmem : ∀ s ∈ E, s ∈ P := fun s hs =>
          hD s (List.mem_cons_of_mem _ (List.mem_of_mem_erase hs))
        have hpP : p ∈ P := hD p (by simp)
        have hrP : r ∈ P := hD r hr
        have hlenE : E.length + 2 = n := by
          rw [← hn, hE, List.length_erase_of_mem hr']
          simp
        have hpr : p - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrp)
        have hsplit : EqOn (fun z => (poleProd (p :: q :: D') z)⁻¹)
            (fun z => (p - r)⁻¹ * (poleProd (p :: E) z)⁻¹ -
              (p - r)⁻¹ * (poleProd (r :: E) z)⁻¹) K := by
          intro z hz
          have hzp : z - p ≠ 0 := sub_ne_zero.mpr (fun h => hL.avoid p hpP (h ▸ hz))
          have hzr : z - r ≠ 0 := sub_ne_zero.mpr (fun h => hL.avoid r hrP (h ▸ hz))
          have hzE : poleProd E z ≠ 0 := poleProd_ne_zero
            (fun s hs h => hL.avoid s (hEmem s hs) (h ▸ hz))
          simp only
          rw [poleProd_perm hperm]
          simp only [poleProd_cons]
          field_simp
          ring
        have hpE : ∀ s ∈ p :: E, s ∈ P := by
          intro s hs; rcases List.mem_cons.mp hs with h | h
          · exact h ▸ hpP
          · exact hEmem s h
        have hrE : ∀ s ∈ r :: E, s ∈ P := by
          intro s hs; rcases List.mem_cons.mp hs with h | h
          · exact h ▸ hrP
          · exact hEmem s h
        rw [hL.congr _ _ hsplit,
          hL.sub (fun z => (p - r)⁻¹ * (poleProd (p :: E) z)⁻¹)
            (fun z => (p - r)⁻¹ * (poleProd (r :: E) z)⁻¹)
            (continuousOn_const.mul (hL.continuousOn_inv_poleProd hpE))
            (continuousOn_const.mul (hL.continuousOn_inv_poleProd hrE)),
          hL.smul, hL.smul,
          ih (E.length + 1) (by omega) (p :: E) (by simp) hpE,
          ih (E.length + 1) (by omega) (r :: E) (by simp) hrE]
        ring

/-- **Evaluation of a loop calculus** on `H / ∏_{p∈D}(z-p)`, `H` holomorphic on `B`. -/
theorem LoopCalculus.eval (hL : LoopCalculus I K B P) :
    ∀ (D : List ℂ) (H : ℂ → ℂ), (∀ p ∈ D, p ∈ P) → DifferentiableOn ℂ H B →
      I (fun z => H z * (poleProd D z)⁻¹) = 2 * Real.pi * Complex.I * dividedResidue H D := by
  intro D
  induction D with
  | nil =>
    intro H _ hH
    simp only [poleProd_nil, inv_one, mul_one, dividedResidue, mul_zero]
    exact hL.holo H hH
  | cons p D ih =>
    intro H hD hH
    have hpP : p ∈ P := hD p (by simp)
    have hDm : ∀ q ∈ D, q ∈ P := fun q hq => hD q (by simp [hq])
    have hpB : B ∈ 𝓝 p := hL.isOpen.mem_nhds (hL.poles_sub hpP)
    have hdH : DifferentiableOn ℂ (dslope H p) B := (Complex.differentiableOn_dslope hpB).mpr hH
    have hsplit : EqOn (fun z => H z * (poleProd (p :: D) z)⁻¹)
        (fun z => dslope H p z * (poleProd D z)⁻¹ + H p * (poleProd (p :: D) z)⁻¹) K := by
      intro z hz
      have hzp : z ≠ p := fun h => hL.avoid p hpP (h ▸ hz)
      have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
      have hzD : poleProd D z ≠ 0 := poleProd_ne_zero
        (fun s hs h => hL.avoid s (hDm s hs) (h ▸ hz))
      simp only
      rw [dslope_of_ne _ hzp, slope_def_field, poleProd_cons]
      field_simp
      ring
    rw [hL.congr _ _ hsplit,
      hL.add (fun z => dslope H p z * (poleProd D z)⁻¹) (fun z => H p * (poleProd (p :: D) z)⁻¹)
        ((hdH.continuousOn.mono hL.range_sub).mul (hL.continuousOn_inv_poleProd hDm))
        (continuousOn_const.mul (hL.continuousOn_inv_poleProd hD)),
      ih (dslope H p) hDm hdH, hL.smul,
      hL.inv_poleProd (D.length + 1) (p :: D) (by simp) hD]
    simp only [dividedResidue]
    cases D with
    | nil =>
      rw [show ([] : List ℂ).length + 1 = 1 from rfl, loopIndicator_one]
      simp only [residueWeight]
      ring
    | cons q D =>
      rw [loopIndicator_of_ne (by simp)]
      simp only [residueWeight]
      ring

/-- Two loop calculi with the same holomorphy domain and poles give the same value. -/
theorem LoopCalculus.eq_of_same {I₁ I₂ : (ℂ → ℂ) → ℂ} {K₁ K₂ : Set ℂ}
    (h₁ : LoopCalculus I₁ K₁ B P) (h₂ : LoopCalculus I₂ K₂ B P) (D : List ℂ) (H : ℂ → ℂ)
    (hD : ∀ p ∈ D, p ∈ P) (hH : DifferentiableOn ℂ H B) :
    I₁ (fun z => H z * (poleProd D z)⁻¹) = I₂ (fun z => H z * (poleProd D z)⁻¹) := by
  rw [h₁.eval D H hD hH, h₂.eval D H hD hH]

/-!
## The circle instance
-/

/-- The counterclockwise circle `C(0,R)` is a loop calculus for any open `B ⊇ closedBall 0 R`
and any poles in the open disc `ball 0 R`. -/
theorem circleLoopCalculus {R : ℝ} (hR : 0 < R) {B P : Set ℂ} (hB : IsOpen B)
    (hRB : Metric.closedBall (0 : ℂ) R ⊆ B) (hP : P ⊆ Metric.ball 0 R) :
    LoopCalculus (fun f => ∮ z in C(0, R), f z) (Metric.sphere 0 R) B P where
  isOpen := hB
  range_sub := Metric.sphere_subset_closedBall.trans hRB
  poles_sub := hP.trans (Metric.ball_subset_closedBall.trans hRB)
  avoid := by
    intro p hp hpK
    have h1 := hP hp
    rw [Metric.mem_ball] at h1
    rw [Metric.mem_sphere] at hpK
    linarith
  congr := fun f g h => circleIntegral.integral_congr hR.le h
  add := fun f g hf hg =>
    circleIntegral.integral_add (hf.circleIntegrable hR.le) (hg.circleIntegrable hR.le)
  smul := fun c f => circleIntegral.integral_smul c f 0 R
  holo := by
    intro G hG
    exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      Set.countable_empty (hG.continuousOn.mono hRB)
      (fun z hz => (hG.mono (Metric.ball_subset_closedBall.trans hRB)).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz.1))
  res := fun p hp => circleIntegral.integral_sub_inv_of_mem_ball (hP hp)
  pow := by
    intro p _ k hk
    have h := circleIntegral.integral_sub_zpow_of_ne (n := -(k : ℤ)) (by omega) 0 p R
    refine (circleIntegral.integral_congr hR.le ?_).trans h
    intro z _
    simp only
    rw [zpow_neg, zpow_natCast]

end BlockBand.GaussianBulk
